#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#define not_reached() __builtin_unreachable()

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

/*
 * This is the C type for our type tag--C supports enums which are just aliases
 * to an integer type
.
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

struct value {
  union {
    int64_t i;               // NIL, BOOL, INT
    struct string_data *str; // STRING
    struct symbol_data *sym; // SYM
    struct pair_data *pair;  // PAIR
    struct closure_data *cls;// CLOSURE
  } data;
  enum datatype type;
};

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
void incref_value(struct value val);
int  decref_value(struct value val);

/*
 * Strings will be stored as a length-prefixed buffer of characters
 */
struct string_data {
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
   * still see this occasionally in practice
   */
  char data[];
};

/* Forward-declaring some utilities for string_data */
struct string_data *new_string(const char* buf, size_t len) {
  struct string_data *s = malloc(sizeof(struct string_data) + len);
  memcpy(s->data, buf, len);
  s->length = len;
  s->refcount = 1;
  return s;
}

struct string_data *new_string_cstr(const char* buf) {
  return new_string(buf, strlen(buf));
}

void release_string(struct string_data *s) {
  free(s);
}

uint64_t string_hash(const struct string_data* str) {
  /* WARNING: very dumb hash algorithm ahead: */
  uint64_t val = 0;
  for (int i = 0; i < str->length; i++) {
    val = (val << 8) + str->data[i] * (val >> 56);
  }
  return val;
}

int string_equal(const struct string_data* str1, const struct string_data *str2) {
  if (str1->length != str2->length) return 0;
  return memcmp(str1->data, str2->data, str1->length) == 0;
}

/*
 * Symbols are just interned strings. We'll add some machinery down the road to
 * accomplish this but for now, we can ignore this and just know that symbols
 * will also store a hash of ti heir string data
 */
struct symbol_data {
  size_t hash;
  struct string_data *str;
  struct symbol_data *next;
};

struct symbol_data *g_last_symbol = 0;

struct symbol_data *new_symbol(const char *buf, size_t len) {
  struct string_data *str = new_string(buf, len);
  int64_t hash = string_hash(str);
  for (struct symbol_data *sym = g_last_symbol; sym; sym = sym->next) {
    if (sym->hash == hash &&
        string_equal(sym->str, str)) {
      assert(str->refcount == 1);
      release_string(str);
      return sym;
    }
  }
  str->refcount = PERSISTENT_REFCOUNT;
  struct symbol_data *sym = malloc(sizeof(struct symbol_data));
  sym->hash = hash;
  sym->str = str;
  sym->next = g_last_symbol;
  g_last_symbol = sym;
  return sym;
}

struct symbol_data *new_symbol_cstr(const char *buf, size_t len) {
  return new_symbol(buf, strlen(buf));
}

/* Pairs are pretty straightforward */
struct pair_data {
  refcount_t refcount;
  struct value first;
  struct value second;
};

struct pair_data *new_pair(struct value v1, struct value v2) {
  struct pair_data *p = malloc(sizeof(struct pair_data));
  p->refcount = 1;
  p->first = v1;
  p->second = v2;
  return p;
}

void release_pair(struct pair_data *p) {
  decref_value(p->first);
  decref_value(p->second);
  free(p);
}

/* fun_data is a little more complicated since it has multiple slices of varying
 * length
 *
 * The layout of a fun is as follows:
 *
 * | 8 bytes | 1 byte | 8 bytes       | 8 bytes    | ... | 1 byte | ...
 * | name    | arity  | bytecode_size | param_name | ... | bytecode ...
 */

struct fun_data {
  struct string_data *name;
  size_t bytecode_size;
  uint8_t captures;
  uint8_t arity;
};

struct string_data **fun_param_names(struct fun_data *f) {
  return (struct string_data**)(f + 1);
}

char* fun_bytecode(struct fun_data *f) {
  return ((char*)(fun_param_names(f)[f->arity]));
}

struct fun_data *new_fun(struct string_data *name,
                         uint8_t arity, struct string_data **params,
                         uint8_t captures,
                         size_t bytecode_size) {
  struct fun_data *f = malloc(sizeof(struct fun_data) +
                              sizeof(struct string_data*) * arity +
                              bytecode_size);
  name->refcount = PERSISTENT_REFCOUNT;
  f->name = name;
  f->arity = arity;
  f->captures = captures;
  f->bytecode_size = bytecode_size;

  for (int i = 0; i < arity; i++) {
    struct string_data *param_name = params[i];
    fun_param_names(f)[i] = param_name;
  }

  return f;
}

struct closure_data {
  refcount_t refcount;
  struct fun_data *impl;
  struct value captures[];
};

struct closure_data *new_closure(struct fun_data *impl,
                                 struct value *captures) {
  struct closure_data *c = malloc(sizeof(struct closure_data) +
                                  impl->captures * sizeof(struct value));
  c->refcount = 1;
  c->impl = impl;
  memcpy(c->captures, captures, sizeof(struct value) * impl->captures);
  return c;
}

void release_closure(struct closure_data *c) {
  for (int i = 0; i < c->impl->captures; i++) {
    decref_value(c->captures[i]);
  }
  free(c);
}

void incref_value(struct value val) {
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

int decref_value(struct value val) {
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
 *                 struct value *parse_result, struct parse_error *error)
 *
 * With the idea that the user passes in pointers to space where the error and
 * result structs must go--if the return is zero, the value struct is populated;
 * otherwise, the error struct is populated; which means.... we need to define
 * the error struct now:
 */

struct srcloc {
  size_t off;
  uint32_t line;
  uint32_t column;
};

struct parse_error {
  struct string_data *message;
  struct srcloc loc;
};

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
 */

struct parse_state;
int parse_number(struct parse_state *s, int64_t *result);
int parse_string(struct parse_state *s, struct string_data **result);
int parse_symbol(struct parse_state *s, struct symbol_data **result);

struct parse_tok {
  struct srcloc loc;
  enum tok_type {
    TOK_LPAREN,
    TOK_QUOTE,
    TOK_EXPR
  } type;
  struct value data; /* valid for TOK_EXPR */
};

/* The parse state, passed in an altered by all the helpers */

#define PARSE_STACK_LIMIT 1024

struct parse_state {
  const char* buf;
  const size_t len;

  struct parse_error *err;
  int error_set; // nonzero if `err` has been assigned to

  struct srcloc loc; // the current parse location

  size_t stack_top; // the first invalid stack element
  struct parse_tok stack[PARSE_STACK_LIMIT];
};

static int parse_should_continue(struct parse_state *s) {
  return !s->error_set && s->loc.off < s->len;
}

static char parse_cur(struct parse_state *s) {
  return s->buf[s->loc.off];
}

static char parse_advance(struct parse_state *s) {
  char c = parse_cur(s);
  s->loc.off++;
  s->loc.column++;
  return c;
}

/* Halt with an error at the current srcloc */
static void parse_error(struct parse_state *s, const char *msg) {
  s->error_set = 1;
  *s->err = (struct parse_error) {
    .message = new_string_cstr(msg),
    .loc     = s->loc
  };
}

/* Halt with an error at the given srcloc */
static void parse_error_at(struct parse_state *s,
                           struct srcloc loc, const char *msg) {
  s->error_set = 1;
  *s->err = (struct parse_error) {
    .message = new_string_cstr(msg),
    .loc     = loc
  };
}

/* Push to the parse stack */
static void parse_push(struct parse_state *s, enum tok_type typ) {
  if (s->stack_top >= PARSE_STACK_LIMIT - 1) {
    parse_error(s, "Parsing stack overflow");
  }
  s->stack[s->stack_top++] = (struct parse_tok) {
    .type = typ,
    .loc  = s->loc
  };
}

/* Push to the parse stack, with an additional data member */
static void parse_push_expr(struct parse_state *s, struct srcloc start,
                       struct value v) {
  if (s->stack_top >= PARSE_STACK_LIMIT - 1) {
    parse_error(s, "Parsing stack overflow");
  }
  s->stack[s->stack_top++] = (struct parse_tok) {
    .type = TOK_EXPR,
    .loc  = start,
    .data = v
  };
}

/* Assert the given stack element is a TOK_EXPR and extract its data */
static int parse_get_expr_at(struct parse_state *s,
                             struct value *v,
                             size_t stack_idx) {
  assert(stack_idx < s->stack_top);
  struct parse_tok *t = &s->stack[stack_idx];
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
int parse_number(struct parse_state *s, int64_t *result) {
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
int parse_string(struct parse_state *s, struct string_data **result) {
  size_t start = s->loc.off + 1;
  size_t end = 0;
  for (int i = 0; i < s->len; i++) {
    if (s->buf[i] == '\"') {
      end = i;
      break;
    }
  }
  if (!end) {
    parse_error(s, "Unterminated string literal");
    return 0;
  } else {
    s->loc.off = end + 1;
    *result = new_string(&s->buf[start], end - start);
    return 1;
  }
}

/* Consume characters from the input stream to parse a symbol */
int parse_symbol(struct parse_state *s, struct symbol_data **result) {
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

int parse_sexpr(struct parse_state *s, struct value *result) {
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
        parse_error(s, "Unmatched RPAREN");
      } else {
        struct srcloc start = s->stack[top].loc;
        /* everything from (top + 1) to old_top needs to go into a list
         * now */
        struct value v = { .type = DT_NIL };
        for (int i = old_top - 1; i > top; i--) {
          /* assert the element at stack[i] is a TOK_EXPR */
          struct value v2;
          if (parse_get_expr_at(s, &v2, i)) {
            v = (struct value) {
              .type = DT_PAIR,
              .data = { .pair = new_pair(v2, v) },
            };
          }
        }
        s->stack_top = top;
        parse_push_expr(s, start, v);
        parse_advance(s);
      }
    }
      break;
    case '\"': {
      struct string_data *result;
      struct srcloc start = s->loc;
      if (parse_string(s, &result)) {
        parse_push_expr(s,
                        start,
                        (struct value) { .type = DT_STRING,
                                         .data = { .str = result } });
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
      struct srcloc start = s->loc;
      if (parse_number(s, &result)) {
        parse_push_expr(s,
                        start,
                        (struct value) { .type = DT_INT,
                                         .data = { .i = result } });
      }
      break;
    }
    case '-':
      /* dash is special because it can either lead off a number or a symbol,
       * we have to peak ahead one more char */
      if (s->loc.off + 1 < s->len) {
        if (is_digit(s->buf[s->loc.off + 1])) {
          int64_t result;
          struct srcloc start = s->loc;
          if (parse_number(s, &result)) {
            parse_push_expr(s,
                            start,
                            (struct value) { .type = DT_INT,
                                             .data = { .i = result } });
          }
        } else {
          struct symbol_data *result;
          struct srcloc start = s->loc;
          if (parse_symbol(s, &result)) {
            parse_push_expr(s,
                            start,
                            (struct value) { .type = DT_SYMBOL,
                                             .data = { .sym = result } });
          }
        }
      }
      break;
    default: {
      if (is_symbol_start_char(c)) {
        struct symbol_data *result;
        struct srcloc start = s->loc;
        if (parse_symbol(s, &result)) {
          parse_push_expr(s,
                          start,
                          (struct value) { .type = DT_SYMBOL,
                                           .data = { .sym = result } });
        }
      } else {
        parse_error(s, "Unexpected char");
      }
      break;
    }
    }
  }

  /* Assert that the parse result is a single TOK_EXPR */
  if (!s->error_set) {
    if (s->stack_top == 0) {
      parse_error(s, "Unexpected EOF");
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
          struct parse_error *err, struct value *result) {
  struct parse_state s = {
    .buf = buf,
    .len = len,
    .loc = { .line = 1, .column = 1, .off = 0},
    .err = err,
    .error_set = 0,
    .stack_top = 0,
  };
  return parse_sexpr(&s, result);
}

void print(struct value v) {
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
 * void eval(struct value v);
 * void apply(struct fun_data *f, struct value *values);
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


int main(int argc, char** argv) {
  struct parse_error err;
  struct value val;

  const char *test = "(def (hello there) (+ 2 3))";
  if (parse(test, strlen(test), &err, &val)) {
    printf("error at (line %d, col %d, offset %ld)\n",
           err.loc.line, err.loc.column, err.loc.off);
    if (write(0, err.message->data, err.message->length) < 0) {
      perror("write");
    }
  } else {
    print(val);
  }
}

