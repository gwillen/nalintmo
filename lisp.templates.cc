#include <stdio.h>

struct True { void print() { printf("True"); } };
struct Nil { void print() { printf("Nil"); } };
template <typename car, typename cdr> struct Cons {};
template <int n> struct Int {};
template <char name[80]> struct Sym {};
template <int ctr> struct Gensym {};
template <typename env, typename params, typename body> struct Func {};

template <typename x, typename y> struct eq {
  typedef Nil r_val;
};
template <typename x> struct eq<x, x> {
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
template <typename env, typename heap, int ctr> struct eval<Nil, env, heap, ctr> {
  typedef Nil r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};

char hello[] = "hello";

int main() {
  eval<Nil, Nil, Nil, 0>::r_val a;
  //a.print();
  eq<Cons<True, True>, Cons<True, True> >::r_val b;
  //b.print();

  //lookup<Gensym<1>, Cons<Cons<Gensym<2>, True>, Cons<Cons<Gensym<3>, True>, Nil> > >::r_val y;
  y.print();

  printf("\n");

  Sym<hello> x;
}
