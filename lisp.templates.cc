#include <stdio.h>

// Datatype of Sexprs. None of this is typechecked, because C++ only has one
// kind with "first-class values", the kind of types. There are function kinds,
// but they are not "first-class" because there are no higher-order function
// kinds. "Concepts" from C++0x would have added something akin to
// user-defined kinds, in the sense of statically checking the suitability of
// template argument types, but they were dropped from the standard. :-(
struct True { static void print() { printf("True"); } };
struct Nil { static void print() { printf("Nil"); } };
template <typename car, typename cdr> struct Cons {
  static void print() {
    printf("Cons(");
    car::print();
    printf(", ");
    cdr::print();
    printf(")");
  }
};
template <int n> struct Int {
  static void print() { printf("Int(%d)", n); } };
template <char name[80]> struct Sym {
  static void print() { printf("Sym(%s)", name); } };
template <int ctr> struct Gensym {
  static void print() { printf("Gensym(%d)", ctr); } };
template <typename env, typename params, typename body> struct Func {
  static void print() { printf("<function>"); } };

// Predefined symbols
// Note that Sym("true") != True, and Sym("nil") != Nil. *shrug*.
#define SYM(x) char x[] = #x
SYM(car);
SYM(cdr);
SYM(progn);
SYM(lambda);
SYM(define);
SYM(quote);
SYM(cond);
SYM(eq);
SYM(cons);
#undef SYM(x)
#define SYM(x, y) char x[] = #y
SYM(plus, +);
SYM(minus, -);
SYM(times, *);
#undef SYM(x, y)

// Helpers

template <typename x, typename y> struct eq_internal {
  typedef Nil r_val;
};
template <typename x> struct eq_internal<x, x> {
  typedef True r_val;
};

template <int ctr> struct gensym {
  static const int r_val = ctr;
  static const int r_ctr = ctr + 1;
};

template <typename k, typename pairlist> struct lookup {};
template <typename k, typename v, typename rest>
struct lookup<k, Cons<Cons<k, v>, rest> > {
  typedef v r_val;
};
template <typename k1, typename k2, typename v, typename rest>
struct lookup<k1, Cons<Cons<k2, v>, rest> > {
  typedef struct lookup<k1, rest>::r_val r_val;
};

template <typename k, typename v, typename pairlist> struct bind {
  typedef Cons<Cons<k, v>, pairlist> r_val;
};

template <typename k, typename env, typename heap> struct env_lookup {
  typedef typename lookup<k, env>::r_val k2;
  typedef typename lookup<k2, heap>::r_val r_val;
};

template <typename name, typename value, typename env, typename heap, int ctr>
struct extend_env {
  typedef gensym<ctr> gensym_result;
  typedef bind<name, typename gensym_result::r_val, env> r_env;
  typedef bind<typename gensym_result::r_val, value, heap> r_heap;
  static const int r_ctr = gensym_result::r_ctr;
};

template <typename key, typename value, typename heap> struct modify_heap {};
template <typename key, typename value, typename oldvalue, typename rest>
struct modify_heap<key, value, Cons<Cons<key, oldvalue>, rest> > {
  typedef Cons<Cons<key, value>, rest> r_heap;
};
template <typename key, typename value, typename key2, typename somevalue, typename rest> 
struct modify_heap<key, value, Cons<Cons<key2, somevalue>, rest> > {
  typedef typename modify_heap<key, value, rest>::r_heap newrest;
  typedef Cons<Cons<key2, somevalue>, newrest> r_heap;
};

template <typename name, typename value, typename env, typename heap>
struct mutate {
  typedef typename lookup<name, env>::r_val key;
  typedef typename modify_heap<key, value, heap>::r_heap r_heap;
};

// Forward declare eval for use in special forms:

template <typename exp, typename env, typename heap, int ctr> struct eval;

// Special forms

template <typename body, typename env, typename heap, int ctr> struct do_progn {};
template <typename env, typename heap, int ctr>
struct do_progn<Nil, env, heap, ctr> {
  typedef Nil r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename first, typename env, typename heap, int ctr>
struct do_progn<Cons<first, Nil>, env, heap, ctr> {
  typedef eval<first, env, heap, ctr> result; 
  typedef typename result::r_val r_val;
  typedef typename result::r_env r_env;
  typedef typename result::r_heap r_heap;
  static const int r_ctr = ctr;
};
template <typename first, typename rest, typename env, typename heap, int ctr>
struct do_progn<Cons<first, rest>, env, heap, ctr> {
  typedef eval<first, env, heap, ctr> first_result; 
  // Discard result::r_val per the contract of progn.
  typedef typename first_result::r_env new_env;
  typedef typename first_result::r_heap new_heap;
  static const int new_ctr = first_result::r_ctr;

  typedef do_progn<rest, new_env, new_heap, new_ctr> final_result;
  typedef typename final_result::r_val r_val;
  typedef typename final_result::r_env r_env;
  typedef typename final_result::r_heap r_heap;
  static const int r_ctr = final_result::r_ctr;
};

template <typename params, typename body, typename env, typename heap, int ctr>
struct do_lambda {
  typedef Func<env, params, body> r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};

template <typename name, typename exp, typename env, typename heap, int ctr>
struct do_define {
  typedef eval<exp, env, heap, ctr> result;
  typedef extend_env<name,
                     typename result::r_val, 
                     typename result::r_env,
                     typename result::r_heap,
                     result::r_ctr> extended;
  typedef typename result::r_val r_val;
  typedef typename extended::r_env r_env;
  typedef typename extended::r_heap r_heap;
  static const int r_ctr = extended::r_ctr;
};

template <typename name, typename params, typename body, typename env, typename heap, int ctr>
struct do_define_func {
  typedef extend_env<name, Nil, env, heap, ctr> extended;
  typedef typename extended::r_env newenv;
  typedef typename extended::r_heap newheap;
  static const int newctr = extended::r_ctr;
  typedef do_lambda<params, body, newenv, newheap, newctr> lambda;
  typedef typename lambda::r_val r_val;
  typedef typename lambda::r_env r_env;
  typedef typename lambda::r_heap newheap2;
  static const int r_ctr = lambda::r_ctr;
  // Backpatching like a motherfucker
  typedef typename mutate<name, r_val, r_env, newheap2>::r_heap r_heap;
};

template <typename exp, typename env, typename heap, int ctr> struct eval {};
template <typename env, typename heap, int ctr> struct eval<True, env, heap, ctr> {
  typedef True r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename env, typename heap, int ctr> struct eval<Nil, env, heap, ctr> {
  typedef Nil r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename env, typename heap, int ctr, int i> struct eval<Int<i>, env, heap, ctr> {
  typedef Int<i> r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename env, typename heap, int ctr, char name[]> struct eval<Sym<name>, env, heap, ctr> {
  typedef typename env_lookup<Sym<name>, env, heap>::r_val r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};

// Helper macro for the special form cases below. Normally it would be bad form
// not to wrap this in do{}while(0) or ({}), except these are typedefs so none
// of that would be valid here, and you can't really use this wrong anyway
// since you can't put it in a block.
#define RETURN(x) \
  typedef typename x::r_val r_val; \
  typedef typename x::r_env r_env; \
  typedef typename x::r_heap r_heap; \
  static const int r_ctr = x::r_ctr

// No eval case for Gensym, because we only use them as heap keys; they should
// never appear in code.
// No eval case for Func either. In real Lisp they evaluate to themselves, but
// they should never appear in code either, unless you abuse #., which I
// haven't got.
template <typename body, typename env, typename heap, int ctr>
struct eval<Cons<Sym<progn>, body>, env, heap, ctr> {
  typedef do_progn<body, env, heap, ctr> result;
  RETURN(result);
};
template <typename params, typename body, typename env, typename heap, int ctr>
struct eval<Cons<Sym<lambda>, Cons<params, body> >, env, heap, ctr> {
  typedef do_lambda<params, body, env, heap, ctr> result;
  RETURN(result);
};
template <char name[], typename exp, typename env, typename heap, int ctr>
struct eval<Cons<Sym<define>, Cons<Sym<name>, Cons<exp, Nil> > >, env, heap, ctr> {
  typedef do_define<Sym<name>, exp, env, heap, ctr> result;
  RETURN(result);
};
template <char name[], typename params, typename body, typename env, typename heap, int ctr>
struct eval<Cons<Sym<define>, Cons<Cons<Sym<name>, params>, body> >, env, heap, ctr> {
  typedef do_define_func<Sym<name>, params, body, env, heap, ctr> result;
  RETURN(result);
};

/*
Structure of the heap: map gensymm'ed keys lead to values
Structure of the environment: map symbols to gensymmed keys. This indirection
is necessary! Otherwise you can't properly do update of state shared between
two closures. (If a closure side-effects its own environment, the other one
won't see. But if it side-effects the global heap, everybody sees.)
*/


char hello[] = "hello";

int main() {
  eval<Nil, Nil, Nil, 0>::r_val a;
  //a.print();
  //eq_internal<Cons<True, True>, Cons<True, True> >::r_val::print();
  Cons<True, True>::print();

  //lookup<Gensym<1>, Cons<Cons<Gensym<2>, True>, Cons<Cons<Gensym<3>, True>, Nil> > >::r_val y;
  //y.print();

  printf("\n");

  //Sym<hello> x;
}
