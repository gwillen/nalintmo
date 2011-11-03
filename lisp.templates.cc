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

template <typename k, typename heap> struct lookup {};
template <typename k, typename v, typename rest>
struct lookup<k, Cons<Cons<k, v>, rest> > {
  typedef v r_val;
};
template <typename k1, typename k2, typename v, typename rest>
struct lookup<k1, Cons<Cons<k2, v>, rest> > {
  typedef struct lookup<k1, rest>::r_val r_val;
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
/*
template <typename env, typename heap, int ctr> struct eval<Int<i>, env, heap, ctr> {
  typedef Int<i> r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
*/

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
