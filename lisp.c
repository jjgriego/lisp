#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <inttypes.h>


#define not_reached() __builtin_unreachable()

#define IMPLIES(x, y) (!(x) || (y))

/*
 * We're going to implement a simple lisp-like language interpreter, from
 * scratch, in C. This is more focused on a demonstration of basic ideas in
 * systems programming than it is a showcase of ideal language design, so hold
 * your objections until the end.
 */

////////////////////////////////////////////////////////////////////////////////
// Data definitions
////////////////////////////////////////////////////////////////////////////////

/*
 * First things first, we need to define what data in this language will look
 * like. We're going to create a notion of an s-expression just like in lisp.
 *
 * The most conventional way of accomplishing this is to create a discriminated
 * union--that is, we'll store the data value itself (an integer, pointer to
 * string data, pointer to a cons cell, etc) along with a single byte tag saying
 * what the data will be
 *
 * In C, we're also responsible for manually managing our memory--all of our
 * data structures are expected to be heap-allocated but we still need to know
 * when to free any given structure. We'll use ref counting to manage our heap
 * memory.
 */

/* Refcounts will be stored as signed ints; if the sign bit is set, we'll use
 * the sign bit to denote when an object is exempt from normal refcount
 * operations */
#define REFCOUNT_STATIC -1

////////////////////////////////////////////////////////////////////////////////

/*
 * This is the C type for our type tag--C supports enums which are just aliases
 * to an integer type
 */
enum datatype {
  DT_NIL,    // the null type, data member is invalid
  DT_BOOL,   // data member is a bool
  DT_STRING, // data member is pointer to string data
  DT_SYMBOL, // data member is pointer to symbol data
  DT_INT,    // data member is an int
  DT_PAIR,   // data member is a pointer to a pair
  DT_CLOSURE,// data member is a pointer to a closure
};


/* We need to forward-declare some structs to reference them before they are
 * declared in full */
struct string_data;
struct symbol_data;
struct pair_data;
struct fun_data;
struct closure_data;

typedef struct value {
  union {
    int64_t i;               // NIL, BOOL, INT
    struct string_data *str; // STRING
    struct symbol_data *sym; // SYM
    struct pair_data *pair;  // PAIR
    struct closure_data *cls;// CLOSURE
  } data;
  enum datatype type;
} value;

/* some helpers to make it easier to construct `value`s */

value make_nil() {
  value v;
  v.type = DT_NIL;
  v.data.i = 0;
  return v;
}

value make_bool(bool b) {
  value v;
  v.type = DT_BOOL;
  v.data.i = b;
  return v;
}

value make_int(int64_t i) {
  value v;
  v.type = DT_INT;
  v.data.i = i;
  return v;
}

value make_string(struct string_data* s) {
  value v;
  v.type = DT_STRING;
  v.data.str = s;
  return v;
}

value make_symbol(struct symbol_data* s) {
  value v;
  v.type = DT_SYMBOL;
  v.data.sym = s;
  return v;
}

value make_pair(struct pair_data* p) {
  value v;
  v.type = DT_PAIR;
  v.data.pair = p;
  return v;
}

value make_closure(struct closure_data* cls) {
  value v;
  v.type = DT_CLOSURE;
  v.data.cls = cls;
  return v;
}

////////////////////////////////////////////////////////////////////////////////

typedef int32_t refcount_t;
#define PERSISTENT_REFCOUNT -1;

int32_t incref(int32_t rc) {
  assert(rc != 0);
  if (rc < 0) return rc;
  return rc + 1;
}

int32_t decref(int32_t rc) {
  assert(rc != 0);
  if (rc < 0) return rc;
  return rc - 1;
}

/* Helper functions to manage refcount */
void incref_value(value val);
int  decref_value(value val);

void *checked_malloc(size_t size) {
  void *result = malloc(size);
  if (!result) {
    printf("panic: out of memory");
    abort();
  }
  return result;
}

////////////////////////////////////////////////////////////////////////////////

/*
 * Strings will be stored as a length-prefixed buffer of characters
 */
typedef struct string_data {
  refcount_t refcount;
  /* The real length of the string */
  size_t length;
  /* Declaring data as an array of unknown length is a dirty trick--it lets us
   * allocate extra space at the end of a `string_data` and access it by
   * indexing into the `data` field. In most contexts, the compiler behaves as
   * if the length is 1
   *
   * There's special restrictions around this idiom in the compiler but you
   * don't need to know about them now. (c.f. "flexible array members") You'll
   * still see this occasionally in practice */
  char data[];
} string_data;

/* Forward-declaring some utilities for string_data */
string_data *new_string(const char* buf, size_t len) {
  string_data *s = checked_malloc(sizeof(string_data) + len);
  memcpy(s->data, buf, len);
  s->length = len;
  s->refcount = 1;
  return s;
}

string_data *new_string_cstr(const char* buf) {
  return new_string(buf, strlen(buf));
}

void release_string(string_data *s) {
  free(s);
}

uint64_t string_hash(const string_data* str) {
  /* WARNING: very dumb hash algorithm ahead: */
  uint64_t val = 0;
  for (int i = 0; i < str->length; i++) {
    val = (val << 8) + str->data[i] * (val >> 56);
  }
  return val;
}

int string_equal(const string_data* str1, const string_data *str2) {
  if (str1->length != str2->length) return 0;
  return memcmp(str1->data, str2->data, str1->length) == 0;
}

////////////////////////////////////////////////////////////////////////////////

/*
 * Symbols are just interned strings. We'll add some machinery down the road to
 * accomplish this but for now, we can ignore this and just know that symbols
 * will also store a hash of their string data
 */
typedef struct symbol_data {
  size_t hash;
  string_data *str;
  struct symbol_data *next;
} symbol_data;

symbol_data *g_last_symbol = 0;

symbol_data *new_symbol(const char *buf, size_t len) {
  string_data *str = new_string(buf, len);
  int64_t hash = string_hash(str);
  for (symbol_data *sym = g_last_symbol; sym; sym = sym->next) {
    if (sym->hash == hash &&
        string_equal(sym->str, str)) {
      assert(str->refcount == 1);
      release_string(str);
      return sym;
    }
  }
  str->refcount = PERSISTENT_REFCOUNT;
  symbol_data *sym = checked_malloc(sizeof(symbol_data));
  sym->hash = hash;
  sym->str = str;
  sym->next = g_last_symbol;
  g_last_symbol = sym;
  return sym;
}

symbol_data *new_symbol_cstr(const char *buf) {
  return new_symbol(buf, strlen(buf));
}

////////////////////////////////////////////////////////////////////////////////

/* Pairs are pretty straightforward */
typedef struct pair_data {
  refcount_t refcount;
  value first;
  value second;
} pair_data;

pair_data *new_pair(value v1, value v2) {
  pair_data *p = checked_malloc(sizeof(pair_data));
  p->refcount = 1;
  p->first = v1;
  p->second = v2;
  return p;
}

void release_pair(pair_data *p) {
  decref_value(p->first);
  decref_value(p->second);
  free(p);
}

bool list_length(pair_data *list_head, size_t* result) {
  size_t tmp = 1;
  pair_data *p = list_head;
  while (1) {
    switch (p->second.type) {
    case DT_NIL:
      if (result) *result = tmp;
      return true;
    case DT_PAIR:
      p = p->second.data.pair;
      tmp += 1;
      continue;
    case DT_BOOL:
    case DT_STRING:
    case DT_SYMBOL:
    case DT_INT:
    case DT_CLOSURE:
      return false;
    }
    not_reached();
  }
}

////////////////////////////////////////////////////////////////////////////////

/* fun_data is a little more complicated since it has multiple slices of varying
 * length
 *
 * The layout of a fun is as follows:
 *
 * | 8 bytes | 1 byte | 8 bytes       | 8 bytes    | ... | 1 byte | ...
 * | name    | arity  | bytecode_size | param_name | ... | bytecode ...
 *
 *
 *
 * If the fun has a native implementation it looks like this instead:
 *
 * | 8 bytes | 1 byte | 8 bytes       |
 * | name    | arity  | impl address  |
 */

typedef uint8_t arity_t;
typedef struct fun_data {
  string_data *name;
  uint8_t captures;
  arity_t arity;
  size_t bytecode_size;
} fun_data;

#define MAX_ARITY 0x100

string_data **fun_param_names(fun_data *f) {
  return (string_data**)(f + 1);
}

char* fun_bytecode(fun_data *f) {
  return ((char*)(&fun_param_names(f)[f->arity]));
}

fun_data *new_fun(string_data *name,
                  arity_t arity, string_data **params,
                  uint8_t captures,
                  const char* bytecode,
                  size_t bytecode_size) {
  fun_data *f = checked_malloc(sizeof(fun_data) +
                              sizeof(string_data*) * arity +
                              bytecode_size);
  name->refcount = PERSISTENT_REFCOUNT;
  f->name = name;
  f->arity = arity;
  f->captures = captures;
  f->bytecode_size = bytecode_size;
  memcpy(fun_bytecode(f), bytecode, bytecode_size);

  for (int i = 0; i < arity; i++) {
    string_data *param_name = params[i];
    fun_param_names(f)[i] = param_name;
  }

  return f;
}

typedef struct native_fun {
  string_data *name;
  arity_t arity;
  void* impl;
} native_fun;

////////////////////////////////////////////////////////////////////////////////

typedef struct closure_data {
  refcount_t refcount;
  bool is_native;
  union {
    fun_data *bc_fun;
    native_fun *native_fun;
  } impl;
  value captures[];
} closure_data;

closure_data *new_closure(fun_data *impl,
                          value *captures) {
  closure_data *c = checked_malloc(sizeof(closure_data) +
                                  impl->captures * sizeof(value));
  c->refcount = 1;
  c->is_native = false;
  c->impl.bc_fun = impl;
  memcpy(c->captures, captures, sizeof(value) * impl->captures);
  return c;
}

closure_data *new_native_closure(native_fun *impl) {
  closure_data *c = checked_malloc(sizeof(closure_data));
  c->is_native = true;
  c->refcount = 1;
  c->impl.native_fun = impl;
  return c;
}

void release_closure(closure_data *c) {
  size_t captures = c->is_native ? 0 : c->impl.bc_fun->captures;
  for (int i = 0; i < captures; i++) {
    decref_value(c->captures[i]);
  }
  free(c);
}

////////////////////////////////////////////////////////////////////////////////

void incref_value(value val) {
  switch (val.type) {
    // These types are guaranteed not to be refcounted
  case DT_NIL:
  case DT_BOOL:
  case DT_INT:
  case DT_SYMBOL:
    return;
  case DT_STRING:
    val.data.str->refcount = incref(val.data.str->refcount);
    break;
  case DT_PAIR:
    val.data.pair->refcount = incref(val.data.pair->refcount);
    break;
  case DT_CLOSURE:
    val.data.cls->refcount = incref(val.data.cls->refcount);
    break;
  }
}

int decref_value(value val) {
  switch (val.type) {
    // These types are guaranteed not to be refcounted
  case DT_NIL:
  case DT_BOOL:
  case DT_INT:
  case DT_SYMBOL:
    break;
  case DT_STRING:
    val.data.str->refcount = decref(val.data.str->refcount);
    if (!val.data.str->refcount) {
      release_string(val.data.str);
      val.data.str = 0;
      return 1;
    }
    break;
  case DT_PAIR:
    val.data.pair->refcount = decref(val.data.pair->refcount);
    if (!val.data.pair->refcount) {
      release_pair(val.data.pair);
      val.data.pair = 0;
      return 1;
    }
    break;
  case DT_CLOSURE:
    val.data.cls->refcount = decref(val.data.cls->refcount);
    if (!val.data.cls->refcount) {
      release_closure(val.data.cls);
      val.data.cls = 0;
      return 1;
    }
    break;
  }
  return 0;
}

////////////////////////////////////////////////////////////////////////////////
// Parsing
////////////////////////////////////////////////////////////////////////////////

/*
 * Parsing is also a chore but the syntax is relatively simple:
 *
 * <s-expr> ::= <int>
 *            | <string-lit>
 *            | <id>
 *            | (<s-expr> ...)
 *            | '<s-expr>
 *
 * <int> ::= <digit> <digit> ...
 * <string-lit> ::= "([^"]|\")*"
 * <id>  ::= <non-digit> <non-whitespace> ..
 *
 * We're going to define the signature of the parser function as:
 *
 * int parse_sexpr(const char *buf, size_t len,
 *                 value *parse_result, struct parse_error *error)
 *
 * With the idea that the user passes in pointers to space where the error and
 * result structs must go--if the return is zero, the value struct is populated;
 * otherwise, the error struct is populated; which means.... we need to define
 * the error struct now:
 */

typedef struct srcloc {
  size_t off;
  uint32_t line;
  uint32_t column;
} srcloc;

typedef struct parse_error {
  string_data *message;
  srcloc loc;
} parse_error;

/* The approach here is going to be a pretty simple LL(2) parse
 *
 * We're going to store a parse stack of tuples of:
 *  - byte offset in the input
 *  - a token tag (defined below)
 *  - possibly some data member corresponding to a partial parse
 *
 * Then, the parse proceeds as:
 *  - peek at the first 1 or two charcters of the input stream
 *  - delegate to a parse helper (declared below) or push an LPAREN
 *  - right-paren consumes items off the stack until the previous LPAREN
 *    and groups them into a list which goes on the stack
 */

struct parse_state;
int parse_number(struct parse_state *s, int64_t *result);
int parse_string(struct parse_state *s, string_data **result);
int parse_symbol(struct parse_state *s, symbol_data **result);

/* A token that goes on the parser stack--either an lparen, quote, or some
 * complete expression */
typedef struct parse_tok {
  srcloc loc;
  enum tok_type {
    TOK_LPAREN,
    TOK_QUOTE,
    TOK_EXPR
  } type;
  value data; /* valid for TOK_EXPR */
} parse_tok;

/* The parse state, passed in and altered by all the helpers */

#define PARSE_STACK_LIMIT 1024

typedef struct parse_state {
  const char* buf;
  const size_t len;

  parse_error *err;
  int error_set; // nonzero if `err` has been assigned to

  srcloc loc; // the current parse location

  size_t stack_top; // the first invalid stack element
  parse_tok stack[PARSE_STACK_LIMIT];
} parse_state;

static int parse_should_continue(parse_state *s) {
  return !s->error_set && s->loc.off < s->len - 1;
}

static char parse_cur(parse_state *s) {
  return s->buf[s->loc.off];
}

static char parse_advance(parse_state *s) {
  char c = parse_cur(s);
  s->loc.off++;
  s->loc.column++;
  return c;
}

/* Halt with an error at the current srcloc */
static void parse_raise_error(parse_state *s, const char *msg) {
  s->error_set = 1;
  *s->err = (parse_error) {
    .message = new_string_cstr(msg),
    .loc     = s->loc
  };
}

/* Halt with an error at the given srcloc */
static void parse_error_at(parse_state *s,
                           srcloc loc, const char *msg) {
  s->error_set = 1;
  *s->err = (parse_error) {
    .message = new_string_cstr(msg),
    .loc     = loc
  };
}

/* Push to the parse stack */
static void parse_push(parse_state *s, enum tok_type typ) {
  if (s->stack_top >= PARSE_STACK_LIMIT - 1) {
    parse_raise_error(s, "Parsing stack overflow");
  }
  s->stack[s->stack_top++] = (parse_tok) {
    .type = typ,
    .loc  = s->loc
  };
}

/* Push to the parse stack, with an additional data member */
static void parse_push_expr(parse_state *s, srcloc start,
                       value v) {
  if (s->stack_top >= PARSE_STACK_LIMIT - 1) {
    parse_raise_error(s, "Parsing stack overflow");
  }
  s->stack[s->stack_top++] = (parse_tok) {
    .type = TOK_EXPR,
    .loc  = start,
    .data = v
  };
}

/* Assert the given stack element is a TOK_EXPR and extract its data */
static int parse_get_expr_at(parse_state *s,
                             value *v,
                             size_t stack_idx) {
  assert(stack_idx < s->stack_top);
  parse_tok *t = &s->stack[stack_idx];
  switch (t->type) {
  case TOK_EXPR:
    *v = t->data;
    return 1;
  case TOK_LPAREN:
    parse_error_at(s, t->loc, "Unmatched LPAREN");
    return 0;
  case TOK_QUOTE:
    parse_error_at(s, t->loc, "Unmatched QUOTE");
    return 0;
  default:
    not_reached();
  }
}

int is_digit(char c) {
  return (c >= '0' && c <= '9');
}

int is_symbol_start_char(char c) {
  switch (c) {
  case '!':
  case '$':
  case '%':
  case '&':
  case '*':
  case '+':
  case '-':
  case '/':
  case '?':
  case '<':
  case '>':
  case '^':
  case '_':
  case '~':
    return 1;
  default:
    return (c >= 'a' && c <= 'z') ||
           (c >= 'A' && c <= 'Z');
  }
}

/* Consume characters from the input stream to parse a number */
int parse_number(parse_state *s, int64_t *result) {
  assert(is_digit(parse_cur(s)));

  *result = 0;
  while (parse_should_continue(s)) {
    char c = parse_cur(s);
    if (is_digit(c)) {
      *result = (c - '0') + *result * 10;
      parse_advance(s);
    } else break;
  }

  return 1;
}

/* Consume characters from the input stream to parse a string */
int parse_string(parse_state *s, string_data **result) {
  size_t start = s->loc.off + 1;
  size_t end = 0;
  for (int i = 0; i < s->len; i++) {
    if (s->buf[i] == '\"') {
      end = i;
      break;
    }
  }
  if (!end) {
    parse_raise_error(s, "Unterminated string literal");
    return 0;
  } else {
    s->loc.off = end + 1;
    *result = new_string(&s->buf[start], end - start);
    return 1;
  }
}

/* Consume characters from the input stream to parse a symbol */
int parse_symbol(parse_state *s, symbol_data **result) {
  assert(is_symbol_start_char(parse_cur(s)));

  size_t start = s->loc.off;
  while (parse_should_continue(s)) {
    char c = parse_cur(s);
    if (!is_digit(c) && !is_symbol_start_char(c)) break;
    parse_advance(s);
  }

  *result = new_symbol(&s->buf[start], s->loc.off - start);
  return 1;
}

/* The our grammar is LL(2) (and mostly LL(1)) so we can parse things quickly
 * and easily by just peeking one character ahead and deciding which syntax rule
 * to use */
int parse_sexpr(parse_state *s, value *result) {
  char c;
  while (parse_should_continue(s)) {
    switch (c = parse_cur(s)) {
    case '\n':
      s->loc.line += 1;
      s->loc.column = 0;
      parse_advance(s);
      break;
    case '\t':
    case ' ':
      parse_advance(s);
      break;
    case '(':
      parse_push(s, TOK_LPAREN);
      parse_advance(s);
      break;
    case ')': {
      /* pop from the stack until we reach a TOK_LPAREN */
      size_t top = s->stack_top;
      size_t old_top = top;
      while (top > 0) {
        top--;
        if (s->stack[top].type == TOK_LPAREN) break;
      }
      if (s->stack[top].type != TOK_LPAREN) {
        parse_raise_error(s, "Unmatched RPAREN");
      } else {
        srcloc start = s->stack[top].loc;
        /* everything from (top + 1) to old_top needs to go into a list
         * now */
        value v = make_nil();
        for (int i = old_top - 1; i > top; i--) {
          /* assert the element at stack[i] is a TOK_EXPR */
          value v2;
          if (parse_get_expr_at(s, &v2, i)) {
            v = make_pair(new_pair(v2, v));
          }
        }
        s->stack_top = top;
        parse_push_expr(s, start, v);
        parse_advance(s);
      }
    }
      break;
    case '\"': {
      string_data *result;
      srcloc start = s->loc;
      if (parse_string(s, &result)) {
        parse_push_expr(s,
                        start,
                        make_string(result));
        parse_advance(s);
      }
      break;
    }
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9': {
      int64_t result;
      srcloc start = s->loc;
      if (parse_number(s, &result)) {
        parse_push_expr(s, start, make_int(result));
      }
      break;
    }
    case '-':
      /* dash is special because it can either lead off a number or a symbol,
       * we have to peak ahead one more char */
      if (s->loc.off + 1 < s->len) {
        if (is_digit(s->buf[s->loc.off + 1])) {
          int64_t result;
          srcloc start = s->loc;
          if (parse_number(s, &result)) {
            parse_push_expr(s, start, make_int(result));
          }
        } else {
          symbol_data *result;
          srcloc start = s->loc;
          if (parse_symbol(s, &result)) {
            parse_push_expr(s, start, make_symbol(result));
          }
        }
      }
      break;
    default: {
      if (is_symbol_start_char(c)) {
        symbol_data *result;
        srcloc start = s->loc;
        if (parse_symbol(s, &result)) {
          parse_push_expr(s, start, make_symbol(result));
        }
      } else {
        parse_raise_error(s, "Unexpected char");
      }
      break;
    }
    }
  }

  /* Assert that the parse result is a single TOK_EXPR */
  if (!s->error_set) {
    if (s->stack_top == 0) {
      parse_raise_error(s, "Unexpected EOF");
    } else {
      if (parse_get_expr_at(s, result, 0)) {
        if (s->stack_top > 1) {
          parse_error_at(s, s->stack[1].loc, "Unexpected token");
        } else {
          s->stack_top = 0;
        }
      }
    }
  }

  /* if there was an error, we need to walk the stack and free any data
   * left behind */
  if (s->error_set) {
    for (int i = 0; i < s->stack_top; i++) {
      switch (s->stack[i].type) {
      case TOK_EXPR:
        decref_value(s->stack[i].data);
        break;
      default:
        break;
      }
    }
    return 1;
  } else {
    /* otherwise, the stack should be empty */
    assert(s->stack_top == 0);
    return 0;
  }
}

int parse(const char *buf, size_t len,
          parse_error *err, value *result) {
  parse_state s = {
    .buf = buf,
    .len = len,
    .loc = { .line = 1, .column = 1, .off = 0},
    .err = err,
    .error_set = 0,
    .stack_top = 0,
  };
  return parse_sexpr(&s, result);
}

/* This is mostly hanging around for debugging, but it's nice to be able to
 * inspect s-expressions in an ad-hoc way */
void print(value v) {
  switch(v.type) {
  case DT_NIL:
    printf("nil");
    break;
  case DT_BOOL:
    if (v.data.i) {
      printf("true");
    } else {
      printf("false");
    }
    break;
  case DT_INT:
    printf("%ld", v.data.i);
    break;
  case DT_STRING:
    printf("\"");
    fwrite(v.data.str->data, sizeof(char), v.data.str->length, stdout);
    printf("\"");
    break;
  case DT_PAIR:
    printf("(");
    print(v.data.pair->first);
    printf(" . ");
    print(v.data.pair->second);
    printf(")");
    break;
  case DT_SYMBOL:
    fwrite(v.data.sym->str->data, sizeof(char), v.data.sym->str->length,
           stdout);
    break;
  case DT_CLOSURE:
    printf("<fun>");
    break;
  }
  fflush(stdout);
}

////////////////////////////////////////////////////////////////////////////////
// Bytecode compilation
////////////////////////////////////////////////////////////////////////////////

/* We have a small problem, namely, that if we do the ~traditional~ thing and
 * write a pair of functions along the lines of:
 *
 * void eval(value v);
 * void apply(fun_data *f, value *values);
 *
 * ... then we have an important and tricky optimization to do; namely,
 * tail-call elimination. If we do the naive thing, we'll end up re-using the
 * native call stack for our interpreter's call stack and that won't do since
 * there's no way for the C compiler to see the opportunities for TCE in our
 * interpreted code.
 *
 * To solve this problem without introducing wacky hacks, we'll first compile
 * our LISP source code into a simple bytecode, perform TCE at this level, and
 * then interpret that bytecode in a straightforward way.
 */

enum opcode {
  OP_RET,
  OP_NIL,
  OP_BOOL,
  OP_STRING,
  OP_SYMBOL,
  OP_INT,
  OP_PAIR,
  OP_CALL,
  OP_ID,
  OP_ALLOC_CLOSURE
};

typedef struct bytecode {
  enum opcode opc;
  union {
    arity_t arity;           // OP_CALL
    int64_t i;               // OP_INT, OP_BOOL
    string_data *str; // OP_STRING
    symbol_data *sym; // OP_SYMBOL, OP_ID
    pair_data *pair;  // OP_PAIR
    fun_data *fun;    // OP_ALLOC_CLOSURE
  } data;
} bytecode;

/* Bytecode emitter
 *
 * We need a quasi-reasonable way to write bytecode without having to worry
 * about the buffer size since the fun_data needs to be sized exactly.
 */

typedef struct bytecode_emitter {
  char *buf;
  char *start;
  size_t cap;
} bytecode_emitter;

void bce_init(bytecode_emitter *bce) {
  bce->start = (char *)checked_malloc(sizeof(char) * 16);
  bce->cap = 16;
  bce->buf = bce->start;
}

void bce_grow(bytecode_emitter *bce) {
  size_t off = bce->buf - bce->start;
  bce->cap *= 2;
  char* buf = realloc(bce->start, bce->cap);
  bce->start = buf;
  bce->buf = bce->start + off;
}

void bce_reset(bytecode_emitter *bce) {
  bce->buf = bce->start;
}

void bce_free(bytecode_emitter *bce) {
  if (bce->start) free(bce->start);
}

void bce_write(bytecode_emitter *bce, bytecode b) {
  if (bce->buf - bce->start <= sizeof(bytecode)) {
    bce_grow(bce);
  }
  *(bce->buf++) = b.opc;
  switch (b.opc) {
  case OP_NIL: break;
  case OP_RET: break;
  case OP_INT:
  case OP_BOOL:
    *(int64_t *)(bce->buf) = b.data.i;
    bce->buf += sizeof(int64_t);
    break;
  case OP_CALL:
    *(arity_t *)(bce->buf) = b.data.arity;
    bce->buf += sizeof(arity_t);
    break;
  case OP_STRING:
    assert(b.data.str->refcount == REFCOUNT_STATIC);
    *(string_data **)(bce->buf) = b.data.str;
    bce->buf += sizeof(string_data *);
    break;
  case OP_SYMBOL:
  case OP_ID:
    *(symbol_data **)(bce->buf) = b.data.sym;
    bce->buf += sizeof(symbol_data *);
    break;
  case OP_PAIR:
    assert(b.data.pair->refcount == REFCOUNT_STATIC);
    *(pair_data **)(bce->buf++) = b.data.pair;
    bce->buf += sizeof(pair_data *);
    break;
  case OP_ALLOC_CLOSURE:
    *(fun_data **)(bce->buf++) = b.data.fun;
    bce->buf += sizeof(fun_data *);
    break;
  default:
    not_reached();
  }
}

void emit_panic(const char* message) {
  printf("emit panic: %s\n", message);
  abort();
}

void emit_expr(bytecode_emitter *bce, value v);
void emit_funcall(bytecode_emitter *bce, value v);

void emit_expr(bytecode_emitter *bce, value v) {
  switch (v.type) {
  case DT_NIL:
    bce_write(bce, (bytecode){.opc = OP_NIL,});
    break;
  case DT_BOOL:
    bce_write(bce, (bytecode){
        .opc = OP_BOOL,
        .data = {.i = v.data.i}
      });
    break;
  case DT_STRING:
    bce_write(bce, (bytecode){
        .opc = OP_STRING,
        .data = {.str = v.data.str}
      });
    break;
  case DT_SYMBOL:
    bce_write(bce, (bytecode){
        .opc = OP_ID,
        .data = {.sym = v.data.sym}
      });
    break;
  case DT_INT:
    bce_write(bce, (bytecode){
        .opc = OP_INT,
        .data = { .i = v.data.i }
      });
    break;
  case DT_PAIR:
    emit_funcall(bce, v);
    break;
  case DT_CLOSURE:
    emit_panic("closure in emit syntax");
    break;
  default:
    not_reached();
  }
}

void emit_funcall(bytecode_emitter *bce, value v) {
  assert(v.type == DT_PAIR);
  emit_expr(bce, v.data.pair->first);
  size_t arity;
  if (!list_length(v.data.pair, &arity)) {
    emit_panic("funcall is improper list");
    return;
  }
  arity -= 1; /* don't count the fun expr */

  pair_data *p = v.data.pair;
  for (int i = 0; i < arity; i++) {
    assert(p);
    p = p->second.data.pair;
    emit_expr(bce, p->first);
  }

  if (arity >= MAX_ARITY) {
    emit_panic("funcall exceeds arity limits");
    return;
  }

  bce_write(bce, (bytecode) {
      .opc = OP_CALL,
      .data = { .arity = (arity_t)arity }
    });
}

const char* read_bytecode(const char* buf, bytecode* ret) {
  assert(ret);
  ret->opc = *(buf++);
  switch (ret->opc) {
  case OP_NIL: break;
  case OP_RET: break;
  case OP_BOOL:
  case OP_INT:
    ret->data.i = *(const int64_t*)buf;
    buf += sizeof(int64_t);
    break;
  case OP_STRING:
    ret->data.str = *(string_data * const *)buf;
    buf += sizeof(string_data*);
    break;
  case OP_SYMBOL:
  case OP_ID:
    ret->data.sym = *(symbol_data * const *)buf;
    buf += sizeof(symbol_data*);
    break;
  case OP_PAIR:
    ret->data.pair = *(pair_data * const *)buf;
    buf += sizeof(pair_data*);
    break;
  case OP_CALL:
    ret->data.arity = *(const arity_t*)buf;
    buf += sizeof(arity_t);
    break;
  case OP_ALLOC_CLOSURE:
    ret->data.fun = *(fun_data * const *)buf;
    buf += sizeof(fun_data*);
    break;
  }
  return buf;
}

void dump_opcode(bytecode b) {
  switch (b.opc) {
  case OP_NIL:
    printf("nil");
    break;
  case OP_RET:
    printf("ret");
    break;
  case OP_BOOL:
    printf("bool 0x%" PRIx64, b.data.i);
    break;
  case OP_STRING:
    printf("string 0x%" PRIxPTR " # ", (uintptr_t)b.data.str);
    print(make_string(b.data.str));
    break;
  case OP_ID:
    printf("id 0x%" PRIxPTR " # ", (uintptr_t)b.data.sym);
    print(make_symbol(b.data.sym));
    break;
  case OP_SYMBOL:
    printf("symbol 0x%" PRIxPTR " # ", (uintptr_t)b.data.sym);
    print(make_symbol(b.data.sym));
    break;
  case OP_INT:
    printf("int 0x%" PRIx64, b.data.i);
    break;
  case OP_PAIR:
    printf("pair 0x%" PRIxPTR " # ", (uintptr_t)b.data.pair);
    print(make_pair(b.data.pair));
    break;
  case OP_CALL:
    printf("call %d", b.data.arity);
    break;
  case OP_ALLOC_CLOSURE:
    printf("alloc_closure 0x%" PRIxPTR, (uintptr_t)b.data.fun);
    break;
  }
}

void dump_bytecode(const char* buf, size_t len) {
  bytecode b;
  const char* data = buf;
  printf("------------------------------------------------\n");
  printf("bytecode (start %" PRIxPTR ", length %" PRIx64 ")\n",
         (uintptr_t)buf, len);
  while (data < buf + len) {
    data = read_bytecode(data, &b);
    printf("%zu\t", data - buf);
    dump_opcode(b);
    printf("\n");
  }
  printf("\n------------------------------------------------\n\n");
  printf("\n");
  fflush(stdout);
}

////////////////////////////////////////////////////////////////////////////////
// Bytecode interpreter
////////////////////////////////////////////////////////////////////////////////

bool lookup_binding(const pair_data *bindings, const symbol_data *name, value *result) {
  assert(result);

  const pair_data *p = bindings;
  if (!p) return false;
  while (1) {
    assert(p->first.type == DT_PAIR);
    const pair_data *assoc = p->first.data.pair;
    assert(assoc->first.type == DT_SYMBOL);
    if (assoc->first.data.sym == name) {
      *result = assoc->second;
      return true;
    } else {
      if (p->second.type == DT_PAIR) {
        p = p->second.data.pair;
      } else {
        assert(p->second.type == DT_NIL);
        return false;
      }
    }
  }
}

void install_global_binding(pair_data **bindings, symbol_data* name, value val) {
  incref_value(val);
  pair_data *assoc = new_pair(make_symbol(name), val);
  value rest = *bindings ? make_pair(*bindings) : make_nil();
  pair_data *p = new_pair(make_pair(assoc), rest);
  *bindings = p;
}

////////////////////////////////////////////////////////////////////////////////

enum frame_flags {
  FRAME_INVALID = 1 << 0,
  /* indicates the frame is completely invalid */

  FRAME_NATIVE = 1 << 1,
  /* the frame was installed by native code--its `previous` is a native stack
   * pointer or is completely invalid and its callee is a native_fun */

  FRAME_ENTRY = 1 << 2,
  /* the frame is a VM entry  */
};

/* a frame that will live on the VM stack--it's intentionally meant to be
 * similar in flavor to a native x64 frame, at least to the extent that it
 * can be backtraced through `previous` */
typedef struct frame {
  struct frame *previous;
  const char* saved_pc;
  enum frame_flags flags;
  union {
    fun_data *fun;
    native_fun *native;
  } callee;
} frame;

/* local ids involve several hacks--the first few locals alias into the frame
 * so we must be careful not to access them */
#define FIRST_VALID_LOCAL 2
typedef int16_t local_t;

/* a typical activation record of a function looks like this. Note that the
 * negative local IDs correspond to arguments; the posive ones, to true locals.
 * local IDs 0 and 1 are reserved since they alias the frame
 *
 *                  local ID
 * +--------------+
 * |  arg 0       |   -3
 * |              |
 * |              |
 * |              |
 * +--------------+ - - - - - -
 * |  arg 1       |    -2
 * |              |
 * |              |
 * |              |
 * +--------------+ - - - - - -
 * |  arg 2       |    -1
 * |              |
 * |              |
 * |              |
 * +--------------+ - - - - - -
 * | saved frame  |     0
 * |              |
 * +--------------+
 * | saved pc     |
 * |              |
 * +--------------+ - - - - - -
 * | flags        |     1
 * | and padding  |
 * +--------------+
 * | callee       |
 * |              |
 * +--------------+ - - - - - -
 * |  local 0     |     2
 * |              |
 * |              |
 * |              |
 * +--------------+ - - - - - -
 * |  local 1     |     3
 * |              |
 * |              |
 * |              |
 * +--------------+ - - - - - -
 */

arity_t frame_callee_arity(const frame* f) {
  return (f->flags & FRAME_NATIVE)
    ? f->callee.native->arity
    : f->callee.fun->arity;
}

typedef struct interp_state {
  pair_data* global_bindings;
  const char* pc;
  value* sp;
  frame* fp;
  /* an allocation to hold the VM stack--note that the call stack need not
   * contain only a single segment from this allocation--VM frames can
   * interleave with native frames */
  char* stack;
  size_t stack_size;
} interp_state;

#define interp_panic(...)                 \
  do {                                    \
    printf("interp panic: " __VA_ARGS__); \
    printf("\n");                         \
    fflush(stdout);                       \
    abort();                              \
  } while (0)

bool interp_check_invariants(const interp_state *is) {
  // stack ptr is in range:
  assert((char*)is->sp >= is->stack &&
         (char*)is->sp < is->stack + is->stack_size - sizeof(value));
  // frame ptr is in range:
  assert((char*)is->fp >= is->stack &&
         (char*)is->fp < is->stack + is->stack_size - sizeof(frame));
  // stack ptr is advanced past frame
  assert((char*)is->sp >= (char*)(is->fp + 1));
  // frame is not invalid:
  assert(!(is->fp->flags & FRAME_INVALID));
  // if frame isn't native, pc points into callee's bytecode
  if (!(is->fp->flags & (FRAME_NATIVE | FRAME_ENTRY))) {
    const char *pc = is->pc;
    fun_data *f = is->fp->callee.fun;
    const char* bc = fun_bytecode(f);
    // note the pc is allowed to be just past-the-end because a trailing `ret`
    // will leave it in that position
    assert(pc >= bc && pc <= (bc + f->bytecode_size));
  }
  return true;
}

value interp_native_add(value v1, value v2) {
  if (v1.type != DT_INT) interp_panic("type error");
  if (v2.type != DT_INT) interp_panic("type error");
  return make_int(v1.data.i + v2.data.i);
}

value interp_native_mul(value v1, value v2) {
  if (v1.type != DT_INT) interp_panic("type error");
  if (v2.type != DT_INT) interp_panic("type error");
  return make_int(v1.data.i * v2.data.i);
}

value interp_native_sub(value v1, value v2) {
  if (v1.type != DT_INT) interp_panic("type error");
  if (v2.type != DT_INT) interp_panic("type error");
  return make_int(v1.data.i - v2.data.i);
}


void interp_init_kernel(interp_state *is);

#define INTERP_STACK_SIZE 4096
void interp_init(interp_state* is) {
  // alloc the stack area
  is->stack = checked_malloc(INTERP_STACK_SIZE);
  is->stack_size = INTERP_STACK_SIZE;
  // initialize the vm regs
  is->sp = (value*)is->stack;
  is->fp = (frame*)is->stack;
  is->global_bindings = 0;
  is->pc = 0;

  // load the global namespace
  interp_init_kernel(is);
}

void interp_free(interp_state* is) {
}

void interp_push(interp_state *is, value v) {
  *(is->sp++) = v;
  assert(interp_check_invariants(is));
}

value interp_peek(interp_state *is, size_t offset) {
  assert(interp_check_invariants(is));
  return *(is->sp - offset - 1);
}

value interp_get_local(interp_state *is, local_t idx) {
  assert(interp_check_invariants(is));
  assert(idx != 0 && idx != 1);
  assert(IMPLIES(idx < 0, -idx < frame_callee_arity(is->fp)));
  return *((value*)(is->fp) + idx);
}

value interp_pop(interp_state *is) {
  value ret = *(--is->sp);
  assert(interp_check_invariants(is));
  return ret;
}

void interp_push_frame(interp_state *is) {
  frame* last = is->fp;
  is->fp = (frame*)is->sp;
  is->fp->flags = 0;
  is->fp->previous = last;
  is->fp->saved_pc = is->pc;
  is->sp = (value*)(is->fp + 1); // TODO locals
  // NB. the interp state is in an invalid state immediately after return--it is
  // the caller's responsibility to fix the pc and frame's flags and callee to
  // make the state valid again
}

void interp_pop_frame(interp_state *is) {
  frame* old = is->fp;
  is->fp = old->previous;
  is->pc = old->saved_pc;
  is->sp = (value*)old;

  // if the frame wasn't an entry--tweak the stack by removing (but not
  // decreffing) the closure and arguments
  if (!(old->flags & FRAME_ENTRY)) {
    is->sp -= frame_callee_arity(old) + 1;
  }

  // mark the old frame as explicitly dirty
  old->flags = FRAME_INVALID;

  assert(interp_check_invariants(is));
}

bool interp_one(interp_state *is);

/* Configure the vm stack to call the given function with no arguments and then
 * run the interpreter until the function returns */
value interp_enter(interp_state* is, fun_data* callee) {
  assert(callee->arity == 0);

  interp_push_frame(is);
  is->fp->flags = FRAME_ENTRY;
  frame* entry = is->fp;

  interp_push(is, make_nil()); // push the "callee closure"
  interp_push_frame(is);
  is->fp->flags = 0;
  is->fp->callee.fun = callee;
  is->pc = fun_bytecode(callee);

  while (!(is->fp->flags & FRAME_ENTRY)) {
    interp_one(is);
  }

  value ret = interp_pop(is);

  assert(is->fp == entry);
  // we would call interp_pop_frame here but we know this is the entry frame,
  // which means:
  // - there might not be a valid frame underneath
  // - there are no locals nor parameters to move past
  is->fp = entry->previous;
  is->pc = entry->saved_pc;
  is->sp = (value*)entry;

  return ret;
}


void interp_call(interp_state *is, arity_t arity);

bool interp_one(interp_state *is) {
  bytecode b;
  is->pc = read_bytecode(is->pc, &b);
  printf("interp: ");
  dump_opcode(b);
  printf("\n");
  switch (b.opc) {
  case OP_NIL:
    interp_push(is, make_nil());
    break;
  case OP_RET: {
    // decref locals (TODO) and params

    // top of stack is the return value
    value v = interp_pop(is);
    interp_pop_frame(is);
    interp_push(is, v);
    break;
  }
  case OP_INT:
    interp_push(is, make_int(b.data.i));
    break;
  case OP_ID: {
    value v;
    if (!lookup_binding(is->global_bindings, b.data.sym, &v)) {
      interp_panic("no binding for %*s",
                   (int)b.data.sym->str->length, // XXX
                   b.data.sym->str->data);
    }
    interp_push(is, v);
  } break;
  case OP_BOOL:
  case OP_STRING:
  case OP_SYMBOL:
  case OP_PAIR:
  case OP_CALL:
    interp_call(is, b.data.arity);
    break;
  case OP_ALLOC_CLOSURE:
    interp_panic("unimplemented opcode 0x%x", b.opc);
    break;
  }
  return false;
}

value interp_invoke_native(interp_state *is, closure_data *cls, arity_t arity) {
  assert(cls->is_native);
  native_fun *f = cls->impl.native_fun;
  if (arity != f->arity) {
    interp_panic("arity mismatch: %d given, %d expected (in native call to %*s)",
                 arity,
                 f->arity,
                 (int)f->name->length, // XXX
                 f->name->data);
  }
  switch (arity) {
  case 0:
    return ((value (*)())f->impl)();
  case 1:
    return ((value (*)(value))f->impl)(interp_peek(is, 0));
  case 2:
    return ((value (*)(value, value))f->impl)(interp_peek(is, 0),
                                              interp_peek(is, 1));
  default:
    interp_panic("nyi: higher arities");
    break;
  }
}

void interp_call(interp_state *is, arity_t arity) {
  // XXX
  value fn = interp_peek(is, arity);
  if (fn.type != DT_CLOSURE) {
    interp_panic("invalid type for call: 0x%x", fn.type);
  }

  if (fn.data.cls->is_native) {
    value ret = interp_invoke_native(is, fn.data.cls, arity);
    for (int i = 0; i < arity + 1; i++) {
      interp_pop(is);
    }
    interp_push(is, ret);
  } else {
    interp_panic("nyi: non-native impls");
  }
}

typedef struct native_fn_table_entry {
  const char *name;
  arity_t arity;
  void *impl;
} native_fn_table_entry;
const native_fn_table_entry s_native_fn_table[] =
  {{"+", 2, interp_native_add},
   {"-", 2, interp_native_sub},
   {"*", 2, interp_native_mul},
   {0}};

void interp_init_kernel(interp_state *is) {
  for (const native_fn_table_entry *entry = s_native_fn_table;
       entry->name;
       entry++) {
    native_fun *f = (native_fun *)checked_malloc(sizeof(native_fun));
    f->name = new_string_cstr(entry->name);
    f->arity = entry->arity;
    f->impl = entry->impl;
    install_global_binding(&is->global_bindings,
                           new_symbol_cstr(entry->name),
                           make_closure(new_native_closure(f)));
  }
}


int main(int argc, char** argv) {
  parse_error err;
  value val;

  while (1) {
    char *line = NULL;
    size_t cap = 0;
    size_t len = 0;
    if ((len = getline(&line, &cap, stdin)) < 0) {
      if (feof(stdin)) break;
      perror("could not read line");
      abort();
    }

    if (parse(line, len, &err, &val)) {
      printf("error at (line %d, col %d, offset %ld)\n",
             err.loc.line, err.loc.column, err.loc.off);
      if (fwrite(err.message->data, 1, err.message->length, stdout) <
          err.message->length) {
        perror("write");
        abort();
      }
      printf("\n");
      fflush(stdin);
    } else {
      print(val);
      printf("\n");
      bytecode_emitter bce;
      bce_init(&bce);
      emit_expr(&bce, val);
      bce_write(&bce, (bytecode){ .opc = OP_RET });


      fun_data *f = new_fun(new_string_cstr("<eval>"),
                            0, /*arity*/
                            0, /*params*/
                            0, /*captures*/
                            bce.start,
                            bce.buf - bce.start);
      dump_bytecode(fun_bytecode(f), f->bytecode_size);

      interp_state is;
      interp_init(&is);

      value ret = interp_enter(&is, f);
      print(ret);
      printf("\n");
      decref_value(val);
      bce_free(&bce);
    }
    free(line);
  }
}

