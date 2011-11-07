datatype sexp_i = NIL_I
  | TRUE_I
  (* No dotted lists. Because fuck you, that's why. *)
  | LIST_I of sdata list
  | NUM_I of int
  | SYM_I of string
  | GENSYM_I of int
  | FUNC_I of (map * sdata list * sexp_i) (* localenv * params * body; only in VAL, never in EXP *)
  | PRIM_I of (context -> sdata list -> (context * sdata))
and sdata = EXP of sexp_i
  | VAL of sexp_i
withtype map = (sexp_i * sexp_i) list
(* (globalenv * localenv) * heap * ctr *) 
and context = ((map * map) * map * int)

exception Unimplemented;
exception Already_done;
exception Cant_happen;
exception Not_found;

(* map_lookup : map -> sexp_i -> sexp_i option *)
fun map_lookup [] k = NONE
  | map_lookup ((k1, v1) :: rest) k =
      if k = k1 then SOME v1 
      else map_lookup rest k

(* map_set : map -> sexp_i -> sexp_i -> map *)
fun map_set [] k v = []
  | map_set ((k1, v1) :: rest) k v =
      if k = k1 then ((k, v) :: rest)
      else ((k1, v1) :: (map_set rest k v))

(* map_bind : map -> sexp_i -> sexp_i -> map *)
fun map_bind m k v = (k, v) :: m

(* env_set : ctx -> sexp_i -> sexp_i -> ctx *)
fun env_set ((globalenv, localenv), heap, ctr) k v =
  let
    val heapk = 
      case map_lookup localenv k of
          SOME heapk => heapk
        | NONE => (case map_lookup globalenv k of
            SOME heapk => heapk
          | NONE => raise Not_found)
    val heap' = map_set heap heapk v 
  in
    ((globalenv, localenv), heap', ctr)
  end

(* single_env_lookup : map -> map -> sexp_i -> sexp_i option *)
fun single_env_lookup env heap k = 
  case map_lookup env k of
      NONE => NONE
    | SOME heapk => map_lookup heap heapk 

(* env_lookup : context -> sexp_i -> val sdata *)
fun env_lookup ((globalenv, localenv), heap, ctr) sym =
  case single_env_lookup localenv heap sym of
      SOME v => VAL v
    | NONE =>
        case single_env_lookup globalenv heap sym of
            SOME v => VAL v
          | NONE => raise Not_found

(* gensym : int -> sexp_i -> int *)
fun gensym ctr = (GENSYM_I ctr, ctr + 1);

(* bind_env : map -> map -> int -> sexp_i -> sexp_i -> (map * map * int)  *)
fun bind_env env heap ctr name value =
  let
    (heapk, ctr') = gensym ctr;
    env' = map_bind env name heapk;
    heap' = map_bind heap heapk value;
  in
    (env', heap', ctr')
  end

(* set_env : map -> map -> int -> sexp_i -> sexp_i -> (map * map * int) *)
fun set_env env heap ctr name value =
  case map_lookup heap name of
      NONE => raise Not_found
    | SOME heapk => let
          val heap' = map_set heap name value
        in
          (env, heap', ctr)
        end

(* bind_or_set_env : map -> map -> int -> sexp_i -> sexp_i -> (map * map * int) *)
fun bind_or_set_env env heap ctr name value = 
  case single_env_lookup env heap name of
      SOME _ => set_env env heap ctr name value
    | NONE => bind_env env heap ctr name value

(* do_lambda : ctx -> sdata list -> sexp_i -> val sdata *)
fun do_lambda ((globalenv, localenv), heap, ctr) params body =
  VAL (FUN_I (localenv, params, EXP (LIST_I ( (EXP (SYM_I "progn")) :: body ))));

(* do_define : ctx -> sexp_i -> sexp_i -> ctx *)
fun do_define ((globalenv, localenv), heap, ctr) name value =
  let
    val (globalenv', heap', ctr') = bind_or_set_env globalenv heap ctr name value
  in
    ((globalenv', localenv), heap', ctr')
  end

(* do_define_func : ctx -> sexp_i -> sexp_i -> ctx *)
(* No backpatching required due to dynamic global scope! *)
fun do_define_func ctx name params body = do_define ctx name (do_lambda ctx params body)

(* bind_params : ctx -> (exp sdata) list -> (val sdata) list -> ctx *)
fun bind_params ctx [] [] = ctx
  | bind_params ((globalenv, localenv), heap, ctr) ((EXP k)::params) ((VAL v)::args) = 
      let val (localenv', heap', ctr') = bind_env localenv heap ctr k v
      in bind_params ((globalenv, localenv'), heap', ctr') params args end

(* do_apply : ctx -> (prim | func) sexp_i -> (val sdata) list -> (ctx * sdata) *)
fun do_apply ctx (PRIM_I f) args = f ctx args
  | do_apply ((globalenv, localenv), heap, ctr) (FUNC_I (closureenv, params, body)) args = 
      let val ctx' = bind_params ((globalenv, closureenv), heap, ctr) params args
      in (ctx', body) end

fun smallstep_arglist ctx [] = (true, ctx, [])
  | smallstep_arglist ctx ((EXP x) :: xs) =
      let (ctx', result) = smallstep ctx (EXP x) in
        (ctx', (result :: xs))
      end
  | smallstep_arglist ctx ((VAL x) :: xs) =
      let (done, ctx', result) = smallstep_arglist ctx xs in
        (done, ctx', ((VAL x) :: result))
      end

(* smallstep : context -> exp sdata -> ctx * sdata *)
fun smallstep ctx (VAL x) = raise Already_done
  | smallstep ctx (EXP (FUNC_I f)) = raise Cant_happen
  | smallstep ctx (EXP (NUM_I x)) = (ctx, (VAL (NUM_I x)))
  | smallstep ctx (EXP (SYM_I s)) = (ctx, env_lookup ctx (SYM_I s))
  | smallstep ctx (EXP NIL_I) = (ctx, VAL NIL_I)

  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "progn")])) = (ctx, VAL NIL_I)
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "progn"), EXP x])) = (ctx, EXP x)
  | smallstep ctx (EXP (LIST_I ((EXP (SYM_I "progn")) :: EXP x :: xs))) =
      let (ctx', result) = (smallstep ctx (EXP x)) in
        (ctx', (EXP (LIST_I ((EXP (SYM_I "progn")) :: result :: xs))))
      end
  | smallstep ctx (EXP (LIST_I ((EXP (SYM_I "progn")) :: VAL x :: xs))) = 
      (ctx, (EXP (LIST_I ((EXP (SYM_I "progn")) :: xs))))

  | smallstep ctx (EXP (LIST_I ((EXP (SYM_I "lambda")) :: (EXP (LIST_I params)) :: body))) =
      (ctx, do_lambda ctx params body)

  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "define"), EXP (SYM_I name), EXP value])) = 
      let (ctx', result) = (smallstep ctx (EXP value)) in
        (ctx', (EXP (LIST_I [EXP (SYM_I "define"), EXP (SYM_I name), result])))
      end
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "define"), EXP (SYM_I name), VAL value])) = 
      (do_define ctx (SYM_I name) value, VAL value)

  | smallstep (ctx as (globalenv, env, heap, ctr)) (EXP (LIST_I ( (EXP (SYM_I "define")) :: (EXP (LIST_I ( (SYM_I name) :: params))) :: body))) = 
      (do_define_func ctx (SYM_I name) params body, VAL NIL_I)

  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "quote"), EXP x])) = (ctx, VAL x)
  
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "cond")])) = (ctx, VAL NIL_I)
  | smallstep ctx (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [EXP c, EXP r])) :: rest))) =
      let (ctx', result) = (smallstep ctx (EXP c)) in
        (ctx', (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [result, EXP r])) :: rest))))
      end
  | smallstep ctx (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [VAL NIL_I, EXP r])) :: rest))) =
      (ctx, (EXP (LIST_I ( (EXP (SYM_I "cond")) :: rest ))))
  | smallstep ctx (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [VAL _, EXP r])) :: rest))) =
      (ctx, EXP r)

  (* Baby's first macro! :D *)
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "setq"), EXP k, EXP v])) =
      (ctx, (EXP (LIST_I [EXP (SYM_I "set"),
                          EXP (LIST_I [EXP (SYM_I "quote"), EXP k]),
                          EXP v])))

  | smallstep ctx (EXP (LIST_I ( (EXP f) :: args ))) =
      let (ctx', result) = (smallstep ctx (EXP f)) in
        (ctx', (EXP (LIST_I ( result :: args ))))
      end
  | smallstep ctx (EXP (LIST_I ( (VAL f) :: args ))) =
      case smallstep_arglist ctx args of
        (false, ctx', result) => (ctx', (EXP (LIST_I ( (VAL f) :: result))))
      | (true, ctx', result) => do_apply ctx' f result

(* prim_xxx : ctx -> sdata list -> (ctx * sdata) *)
fun prim_car ctx [VAL (LIST_I (x::xs))] = (ctx, x)
fun prim_cdr ctx [VAL (LIST_I (x::xs))] = (ctx, VAL (LIST_I xs))
fun prim_eq ctx [VAL a, VAL b] = (ctx, if a = b then VAL TRUE_I else VAL NIL_I)
fun prim_cons ctx [VAL a, VAL (LIST_I b)] = (ctx, VAL (LIST_I (a :: b)))
fun prim_set ctx [VAL a, VAL b] = (env_set ctx a b, VAL b)

val init_ctx =
  let 
    fun defprim (env, heap, ctr) k v = bind_env env heap ctr (SYM_I k) (PRIM_I v)
    val ctx = ([], [], 0)
    val ctx = defprim ctx "car" prim_car
    val ctx = defprim ctx "cdr" prim_cdr
    val ctx = defprim ctx "eq" prim_eq
    val ctx = defprim ctx "cons" prim_cons
    val ctx = defprim ctx "set" prim_set
    val (globalenv, heap, ctr) = ctx
  in 
    ((globalenv, []), heap, ctr)
  end

(* eval : ctx -> exp sdata -> val sdata *)
fun eval ctx x = 
  case smallstep ctx x of
      VAL v => VAL v
    | EXP e => eval ctx (EXP e)
