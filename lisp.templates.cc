#include <stdio.h>

// Datatype of Sexprs. None of this is typechecked, because C++ only has one
// kind with "first-class values", the kind of types. There are function kinds,
// but they are not "first-class" because there are no higher-order function
// kinds. "Concepts" from C++0x would have added something akin to
// user-defined kinds, in the sense of statically checking the suitability of
// template argument types, but they were dropped from the standard. :-(
struct True { static void print() { printf("True"); } };
struct Nil {
  static void print() {
    printf("Nil");
  }
  static void pretty() {
    printf("()");
  }
  static void prettylist() {
    printf(")");
  }
};
template <typename car, typename cdr> struct Cons {
  static void print() {
    printf("Cons(");
    car::print();
    printf(", ");
    cdr::print();
    printf(")");
  }
  static void pretty() {
    printf("(");
    car::pretty();
    cdr::prettylist();
  }
  static void prettylist() {
    printf(" ");
    car::print();
    cdr::prettylist();
  }
};
template <int n> struct Int {
  static void print() { printf("Int(%d)", n); }
  static void pretty() { printf("%d", n); }
  static void prettylist() {
    printf(" . ");
    pretty();
    printf(")");
  }
};
template <char name[80]> struct Sym {
  static void print() { printf("Sym(%s)", name); }
  static void pretty() { printf("%s", name); }
  static void prettylist() {
    printf(" . ");
    pretty();
    printf(")");
  }
};
template <int ctr> struct Gensym {
  static void print() { printf("Gensym(%d)", ctr); }
  static void pretty() { printf("<generated symbol %d>", ctr); }
  static void prettylist() {
    printf(" . ");
    pretty();
    printf(")");
  }
};
template <typename env, typename params, typename body> struct Func {
  static void print() {
    printf("Func(");
    params::print();
    printf(" -> ");
    body::print();
    printf(")");
  }
  static void pretty() {
    printf("<function ");
    params::pretty();
    printf(" -> ");
    body::pretty();
    printf(">");
  }
  static void prettylist() {
    printf(" . ");
    pretty();
    printf(")");
  }
};
template <char name[80]> struct Prim {
  static void print() { printf("<primitive function %s>"); }
  static void pretty() { print(); }
  static void prettylist() {
    printf(" . ");
    pretty();
    printf(")");
  }
};

// Predefined symbols
// Note that Sym("true") != True, and Sym("nil") != Nil. *shrug*.
#define SYM(x) char x[] = #x

// Builtins
SYM(progn);
SYM(lambda);
SYM(define);
SYM(quote);
SYM(cond);

// Primitive functions
SYM(car);
SYM(cdr);
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
  typedef Gensym<ctr> r_val;
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

// Helper macro for the special form cases of eval, and the cond helpers.
// Normally it would be bad form not to wrap this in do{}while(0) or ({}),
// except these are typedefs so none of that would be valid here, and you can't
// really use this wrong anyway since you can't put it in a block.
#define RETURN(x) \
  typedef typename x::r_val r_val; \
  typedef typename x::r_env r_env; \
  typedef typename x::r_heap r_heap; \
  static const int r_ctr = x::r_ctr

// Somehow do_cond snick into the middle of eval. I dunno man. I just work
// here.

template <typename cond_val, typename result, typename rest, typename env, typename heap, int ctr>
struct do_cond_case;

template <typename body, typename env, typename heap, int ctr> struct do_cond {};
template <typename env, typename heap, int ctr>
struct do_cond<Nil, env, heap, ctr> {
  typedef Nil r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename condition, typename result, typename rest, typename env, typename heap, int ctr>
struct do_cond<Cons<Cons<condition, Cons<result, Nil> >, rest>, env, heap, ctr> {
  typedef eval<condition, env, heap, ctr> cond_eval;
  typedef typename cond_eval::r_val cond_val;
  typedef typename cond_eval::r_env newenv;
  typedef typename cond_eval::r_heap newheap;
  static const int newctr = cond_eval::r_ctr;
  typedef do_cond_case<cond_val, result, rest, newenv, newheap, newctr> final_result;
  RETURN(final_result);
};

template <typename cond_val, typename result, typename rest, typename env, typename heap, int ctr>
struct do_cond_case {
  // Because of the specialization below, this will fire if cond_val is
  // non-nil.
  typedef eval<result, env, heap, ctr> final_result;
  RETURN(final_result);
};
template <typename result, typename rest, typename env, typename heap, int ctr>
struct do_cond_case<Nil, result, rest, env, heap, ctr> {
  typedef do_cond<rest, env, heap, ctr> final_result;
  RETURN(final_result);
};

template <typename list, typename env, typename heap, int ctr> struct map_eval {};
template <typename env, typename heap, int ctr>
struct map_eval <Nil, env, heap, ctr> {
  typedef Nil r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename x, typename xs, typename env, typename heap, int ctr>
struct map_eval <Cons <x, xs>, env, heap, ctr> {
  typedef eval<x, env, heap, ctr> result;
  typedef typename result::r_val result_val;
  typedef typename result::r_env newenv;
  typedef typename result::r_heap newheap;
  static const int newctr = result::r_ctr;
  typedef map_eval<xs, newenv, newheap, newctr> result2;
  typedef Cons <result_val, typename result2::r_val> r_val;
  typedef typename result2::r_env r_env;
  typedef typename result2::r_heap r_heap;
  static const int r_ctr = result2::r_ctr;
};

template <typename params, typename args, typename env, typename heap, int ctr>
struct bind_params {};
template <typename env, typename heap, int ctr>
struct bind_params<Nil, Nil, env, heap, ctr> {
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename k, typename params, typename v, typename args, typename env, typename heap, int ctr>
struct bind_params<Cons<k, params>, Cons<v, args>, env, heap, ctr> {
  typedef extend_env<k, v, env, heap, ctr> extended;
  typedef typename extended::r_env newenv;
  typedef typename extended::r_heap newheap;
  static const int newctr = extended::r_ctr;
  typedef bind_params<params, args, newenv, newheap, newctr> result;
  RETURN(result);
};

#define PASS_ENV_THROUGH \
  typedef env r_env; \
  typedef heap r_heap; \
  static const int r_ctr = ctr

template <typename arg, typename env, typename heap, int ctr> struct do_prim_car {};
template <typename x, typename y, typename env, typename heap, int ctr>
struct do_prim_car<Cons<x, y>, env, heap, ctr> {
  typedef x r_val;
  PASS_ENV_THROUGH;
};
template <typename arg, typename env, typename heap, int ctr> struct do_prim_cdr {};
template <typename x, typename y, typename env, typename heap, int ctr>
struct do_prim_cdr<Cons<x, y>, env, heap, ctr> {
  typedef y r_val;
  PASS_ENV_THROUGH;
};
template <typename arg, typename env, typename heap, int ctr> struct do_prim_eq{};
template <typename x, typename y, typename env, typename heap, int ctr>
struct do_prim_eq<Cons<x, Cons<y, Nil> >, env, heap, ctr> {
  typedef Nil r_val;
  PASS_ENV_THROUGH;
};
template <typename x, typename env, typename heap, int ctr>
struct do_prim_eq<Cons<x, Cons<x, Nil> >, env, heap, ctr> {
  typedef True r_val;
  PASS_ENV_THROUGH;
};
template <typename arg, typename env, typename heap, int ctr> struct do_prim_plus {};
template <int x, int y, typename env, typename heap, int ctr>
struct do_prim_plus<Cons<Int<x>, Cons<Int<y>, Nil> >, env, heap, ctr> {
  typedef Int<x+y> r_val;
  PASS_ENV_THROUGH;
};
template <typename arg, typename env, typename heap, int ctr> struct do_prim_minus {};
template <int x, int y, typename env, typename heap, int ctr>
struct do_prim_minus<Cons<Int<x>, Cons<Int<y>, Nil> >, env, heap, ctr> {
  typedef Int<x-y> r_val;
  PASS_ENV_THROUGH;
};
template <typename arg, typename env, typename heap, int ctr> struct do_prim_times {};
template <int x, int y, typename env, typename heap, int ctr>
struct do_prim_times<Cons<Int<x>, Cons<Int<y>, Nil> >, env, heap, ctr> {
  typedef Int<x*y> r_val;
  PASS_ENV_THROUGH;
};
template <typename arg, typename env, typename heap, int ctr> struct do_prim_cons {};
template <typename x, typename y, typename env, typename heap, int ctr>
struct do_prim_cons<Cons<x, Cons<y, Nil> >, env, heap, ctr> {
  typedef Cons<x, y> r_val;
  PASS_ENV_THROUGH;
};


template <typename f, typename args, typename env, typename heap, int ctr>
struct do_apply_actual {};
template <typename stored_env, typename params, typename body, typename args, typename env, typename heap, int ctr>
struct do_apply_actual <Func <stored_env, params, body>, args, env, heap, ctr> {
  typedef bind_params<params, args, stored_env, heap, ctr> params_result;
  typedef typename params_result::r_env newenv;
  typedef typename params_result::r_heap newheap;
  static const int newctr = params_result::r_ctr;
  typedef Cons<Sym<progn>, body> body_progn;
  typedef eval<body_progn, newenv, newheap, newctr> result;
  RETURN(result);
};
#define DO_APPLY_PRIM(x) \
template <typename args, typename env, typename heap, int ctr> \
struct do_apply_actual <Prim<x>, args, env, heap, ctr> { \
  typedef do_prim_##x<args, env, heap, ctr> result; \
  RETURN(result); \
}
DO_APPLY_PRIM(car);
DO_APPLY_PRIM(cdr);
DO_APPLY_PRIM(eq);
DO_APPLY_PRIM(cons);
DO_APPLY_PRIM(plus);
DO_APPLY_PRIM(minus);
DO_APPLY_PRIM(times);

template <typename fun, typename args, typename env, typename heap, int ctr>
struct do_apply_internal {
  typedef eval<fun, env, heap, ctr> fun_result;
  typedef typename fun_result::r_val f;
  typedef typename fun_result::r_env newenv;
  typedef typename fun_result::r_heap newheap;
  static const int newctr = fun_result::r_ctr;
  typedef map_eval<args, newenv, newheap, newctr> args_result;
  typedef typename args_result::r_val args_actual;
  typedef typename args_result::r_env newenv2;
  typedef typename args_result::r_heap newheap2;
  static const int newctr2 = args_result::r_ctr;
  typedef do_apply_actual<f, args_actual, newenv2, newheap2, newctr2> final_result;
  RETURN(final_result);
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
template <typename exp, typename env, typename heap, int ctr>
struct eval<Cons<Sym<quote>, Cons<exp, Nil> >, env, heap, ctr> {
  typedef exp r_val;
  typedef env r_env;
  typedef heap r_heap;
  static const int r_ctr = ctr;
};
template <typename body, typename env, typename heap, int ctr>
struct eval<Cons<Sym<cond>, body>, env, heap, ctr> {
  typedef do_cond<body, env, heap, ctr> result;
  RETURN(result);
};
template <typename fun, typename args, typename env, typename heap, int ctr>
struct eval<Cons<fun, args>, env, heap, ctr> {
  typedef do_apply_internal<fun, args, env, heap, ctr> result;
  RETURN(result);
};


#define EXTEND(env_pkg, new_pkg, k, v) \
typedef extend_env<k, v, env_pkg::r_env, env_pkg::r_heap, env_pkg::r_ctr> new_pkg

typedef extend_env<Sym<car>, Prim<car>, Nil, Nil, 0> e1;
EXTEND(e1, e2, Sym<cdr>, Prim<cdr>);
EXTEND(e2, e3, Sym<eq>, Prim<eq>);
EXTEND(e3, e4, Sym<plus>, Prim<plus>);
EXTEND(e4, e5, Sym<minus>, Prim<minus>);
EXTEND(e5, e6, Sym<times>, Prim<times>);
EXTEND(e6, e7, Sym<cons>, Prim<cons>);

typedef e7 initial_env;

/*
Structure of the heap: map gensymm'ed keys lead to values
Structure of the environment: map symbols to gensymmed keys. This indirection
is necessary! Otherwise you can't properly do update of state shared between
two closures. (If a closure side-effects its own environment, the other one
won't see. But if it side-effects the global heap, everybody sees.)
*/

int main() {
  eval<Nil, Nil, Nil, 0>::r_val a;
  //a.print();
  //eq_internal<Cons<True, True>, Cons<True, True> >::r_val::print();
  Cons<True, True>::print();

  //lookup<Gensym<1>, Cons<Cons<Gensym<2>, True>, Cons<Cons<Gensym<3>, True>, Nil> > >::r_val y;
  //y.print();

  printf("\n");
}
