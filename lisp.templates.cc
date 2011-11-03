#include <stdio.h>

struct Nil { void print() { printf("Nil"); } };
template <typename car, typename cdr> struct Cons {};
template <int n> struct Int {};
template <char name[80]> struct Sym {};
template <typename env, typename params, typename body> struct Func {};

template <typename exp, typename env, typename heap> struct eval {};
template <typename env, typename heap> struct eval<Nil, env, heap> { typedef Nil rv; };

char hello[] = "hello";

int main() {
  eval<Nil, Nil, Nil>::rv a;
  a.print();

  Sym<hello> x;
}
