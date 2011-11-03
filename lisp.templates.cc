#include <stdio.h>

struct Nil { void print() { printf("Nil"); } };
template <typename car, typename cdr> struct Cons {};
template <int n> struct Int {};
template <char name[80]> struct Sym {};
template <int ctr> struct Gensym {};
template <typename env, typename params, typename body> struct Func {};

template <int ctr> struct gensym {
  static const int r_val = ctr;
  static const int r_ctr = ctr + 1;
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
  a.print();

  Sym<hello> x;
}
