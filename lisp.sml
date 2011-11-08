exception Unimplemented;
exception Already_done;
exception Cant_happen;
exception Not_found;
exception Bad_key;

Control.Print.stringDepth := 9999;

datatype sexp_i =
    TRUE_I
  (* No dotted lists. Because fuck you, that's why. *)
  | LIST_I of sdata list
  | NUM_I of int
  | SYM_I of string
  | GENSYM_I of int
  | FUNC_I of (sexp_i * map * sdata list * sexp_i) (* name *localenv * params * body; only in VAL, never in EXP *)
  | PRIM_I of (string * (context -> sdata list -> (context * sdata)))
and sdata = EXP of sexp_i
  | VAL of sexp_i
and key = SYM_K of string | GENSYM_K of int
withtype map = (key * sexp_i) list
(* (globalenv * localenv) * heap * ctr *) 
and context = ((map * map) * map * int)

datatype input_sexp = 
    TRUE
  | LIST of input_sexp list
  | NUM of int
  | SYM of string


fun sdata_to_string (VAL x) = "(# " ^ (sexp_i_to_string x) ^ " #)"
  | sdata_to_string (EXP x) = (sexp_i_to_string x)
and sexp_i_to_string TRUE_I = "true"
  | sexp_i_to_string (NUM_I n) = Int.toString n
  | sexp_i_to_string (SYM_I s) = s
  | sexp_i_to_string (GENSYM_I n) = "<gensym " ^ (Int.toString n) ^ ">"
  | sexp_i_to_string (FUNC_I (name, _, _, _)) = "<function " ^ (sexp_i_to_string name) ^ ">"
  | sexp_i_to_string (PRIM_I (name, _)) = "<primitive function " ^ name ^ ">"
  | sexp_i_to_string (LIST_I l) = "(" ^ (sexp_i_list_to_string l)
and sexp_i_list_to_string [] = ")"
  | sexp_i_list_to_string (x::xs) = (sdata_to_string x) ^ " " ^ (sexp_i_list_to_string xs)

and ctx_to_string ((globalenv, localenv), heap, ctr) = 
    (map_to_string localenv) ^ "; " ^
    (map_to_string globalenv) ^ "; " ^
    (map_to_string heap) ^ "; " ^ (Int.toString ctr)
and map_to_string [] = ""
  | map_to_string ((k, v) :: rest) = (key_to_string k) ^ "->" ^ 
                                     (sexp_i_to_string v) ^ ", " ^
                                     (map_to_string rest)
and key_to_string (SYM_K s) = s
  | key_to_string (GENSYM_K i) = "<gensym " ^ (Int.toString i) ^ ">"


fun to_sdata TRUE = EXP TRUE_I
  | to_sdata (NUM n) = EXP (NUM_I n)
  | to_sdata (SYM s) = EXP (SYM_I s)
  | to_sdata (LIST []) = EXP (LIST_I [])
  | to_sdata (LIST (x::xs)) =
      let val (EXP (LIST_I rest)) = to_sdata (LIST xs)
      in EXP (LIST_I ((to_sdata x) :: rest)) end

fun make_key (SYM_I s) = SYM_K s
  | make_key (GENSYM_I n) = GENSYM_K n
  | make_key _ = raise Bad_key;

fun sexp_eq TRUE_I TRUE_I = true
  | sexp_eq (NUM_I m) (NUM_I n) = m = n
  | sexp_eq (SYM_I r) (SYM_I s) = r = s
  | sexp_eq (GENSYM_I m) (GENSYM_I n) = m = n
  | sexp_eq (LIST_I []) (LIST_I []) = true
  | sexp_eq (LIST_I ((VAL x) :: rest1)) (LIST_I ((VAL y) :: rest2)) =
      (sexp_eq x y) andalso (sexp_eq (LIST_I rest1) (LIST_I rest2)) 
  | sexp_eq _ _ = false

(* map_lookup : map -> sexp_i -> sexp_i option *)
fun map_lookup [] k = NONE
  | map_lookup ((k1, v1) :: rest) k =
      if (make_key k) = k1 then SOME v1 
      else map_lookup rest k

(* map_set : map -> sexp_i -> sexp_i -> map *)
fun map_set [] (k:sexp_i) (v:sexp_i) = []
  | map_set ((k1, v1) :: rest) k v =
      if (make_key k) = k1 then ((k1, v) :: rest)
      else ((k1, v1) :: (map_set rest k v))

(* map_bind : map -> sexp_i -> sexp_i -> map *)
fun map_bind m k v = ((make_key k), v) :: m

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
    val (heapk, ctr') = gensym ctr;
    val env' = map_bind env name heapk;
    val heap' = map_bind heap heapk value;
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
fun do_lambda name ((globalenv, localenv), heap, ctr) params body =
  VAL (FUNC_I (name, localenv, params, LIST_I ( (EXP (SYM_I "progn")) :: body )));

(* do_define : ctx -> sexp_i -> sexp_i -> ctx *)
fun do_define ((globalenv, localenv), heap, ctr) name value =
  let
    val (globalenv', heap', ctr') = bind_or_set_env globalenv heap ctr name value
  in
    ((globalenv', localenv), heap', ctr')
  end

(* do_define_func : ctx -> sexp_i -> sexp_i -> ctx *)
(* No backpatching required due to dynamic global scope! *)
fun do_define_func ctx name params body = let
  val VAL f = do_lambda name ctx params body
  in do_define ctx name f end

(* bind_params : ctx -> (exp sdata) list -> (val sdata) list -> ctx *)
fun bind_params ctx [] [] = ctx
  | bind_params ((globalenv, localenv), heap, ctr) ((EXP k)::params) ((VAL v)::args) = 
      let val (localenv', heap', ctr') = bind_env localenv heap ctr k v
      in bind_params ((globalenv, localenv'), heap', ctr') params args end

(* do_apply : ctx -> (prim | func) sexp_i -> (val sdata) list -> (ctx * sdata) *)
fun do_apply ctx (PRIM_I (_, f)) args = f ctx args
  | do_apply ((globalenv, localenv), heap, ctr) (FUNC_I (_, closureenv, params, body)) args = 
      let val ctx' = bind_params ((globalenv, closureenv), heap, ctr) params args
      in (ctx', EXP body) end

(* smallstep_arglist : ctx -> sdata list -> (bool * ctx * sdata list) *)
fun smallstep_arglist ctx [] = (true, ctx, [])
  | smallstep_arglist ctx ((EXP x) :: xs) =
      let val (ctx', result) = smallstep ctx (EXP x) in
        (false, ctx', (result :: xs))
      end
  | smallstep_arglist ctx ((VAL x) :: xs) =
      let val (done, ctx', result) = smallstep_arglist ctx xs in
        (done, ctx', ((VAL x) :: result))
      end

(* smallstep : context -> exp sdata -> ctx * sdata *)
and smallstep ctx (VAL x) = raise Already_done
  | smallstep ctx (EXP (FUNC_I f)) = raise Cant_happen
  | smallstep ctx (EXP TRUE_I) = (ctx, VAL TRUE_I)
  | smallstep ctx (EXP (NUM_I x)) = (ctx, (VAL (NUM_I x)))
  | smallstep ctx (EXP (SYM_I s)) = (ctx, env_lookup ctx (SYM_I s))
  | smallstep ctx (EXP (LIST_I [])) = (ctx, VAL (LIST_I []))

  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "progn")])) = (ctx, VAL (LIST_I []))
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "progn"), EXP x])) = (ctx, EXP x)
  | smallstep ctx (EXP (LIST_I ((EXP (SYM_I "progn")) :: EXP x :: xs))) =
      let val (ctx', result) = (smallstep ctx (EXP x)) in
        (ctx', (EXP (LIST_I ((EXP (SYM_I "progn")) :: result :: xs))))
      end
  | smallstep ctx (EXP (LIST_I ((EXP (SYM_I "progn")) :: VAL x :: xs))) = 
      (ctx, (EXP (LIST_I ((EXP (SYM_I "progn")) :: xs))))

  | smallstep ctx (EXP (LIST_I ((EXP (SYM_I "lambda")) :: (EXP (LIST_I params)) :: body))) =
      (ctx, do_lambda (SYM_I "*anonymous closure*") ctx params body)

  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "define"), EXP (SYM_I name), EXP value])) = 
      let val (ctx', result) = (smallstep ctx (EXP value)) in
        (ctx', (EXP (LIST_I [EXP (SYM_I "define"), EXP (SYM_I name), result])))
      end
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "define"), EXP (SYM_I name), VAL value])) = 
      (do_define ctx (SYM_I name) value, VAL value)

  | smallstep ctx (EXP (LIST_I ( (EXP (SYM_I "define")) :: (EXP (LIST_I ( (EXP (SYM_I name)) :: params))) :: body))) = 
      (do_define_func ctx (SYM_I name) params body, VAL (LIST_I []))

  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "quote"), EXP x])) = (ctx, VAL x)
  
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "cond")])) = (ctx, VAL (LIST_I []))
  | smallstep ctx (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [EXP c, EXP r])) :: rest))) =
      let val (ctx', result) = (smallstep ctx (EXP c)) in
        (ctx', (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [result, EXP r])) :: rest))))
      end
  | smallstep ctx (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [VAL (LIST_I []), EXP r])) :: rest))) =
      (ctx, (EXP (LIST_I ( (EXP (SYM_I "cond")) :: rest ))))
  | smallstep ctx (EXP (LIST_I ( (EXP (SYM_I "cond")) :: (EXP (LIST_I [VAL _, EXP r])) :: rest))) =
      (ctx, EXP r)

  (* Baby's first macro! :D *)
  | smallstep ctx (EXP (LIST_I [EXP (SYM_I "setq"), EXP k, EXP v])) =
      (ctx, (EXP (LIST_I [EXP (SYM_I "set"),
                          EXP (LIST_I [EXP (SYM_I "quote"), EXP k]),
                          EXP v])))

  | smallstep ctx (EXP (LIST_I ( (EXP f) :: args ))) =
      let val (ctx', result) = (smallstep ctx (EXP f)) in
        (ctx', (EXP (LIST_I ( result :: args ))))
      end
  | smallstep ctx (EXP (LIST_I ( (VAL f) :: args ))) =
      case smallstep_arglist ctx args of
        (false, ctx', result) => (ctx', (EXP (LIST_I ( (VAL f) :: result))))
      | (true, ctx', result) => do_apply ctx' f result

(* prim_xxx : ctx -> sdata list -> (ctx * sdata) *)
fun prim_car ctx [VAL (LIST_I (x::xs))] = (ctx, x)
fun prim_cdr ctx [VAL (LIST_I (x::xs))] = (ctx, VAL (LIST_I xs))
fun prim_eq ctx [VAL a, VAL b] = (ctx, if (sexp_eq a b) then VAL TRUE_I else VAL (LIST_I []))
fun prim_cons ctx [VAL a, VAL (LIST_I b)] = (ctx, VAL (LIST_I ((VAL a) :: b)))
fun prim_set ctx [VAL a, VAL b] = (env_set ctx a b, VAL b)
fun prim_plus ctx [VAL (NUM_I a), VAL (NUM_I b)] = (ctx, VAL (NUM_I (a + b)))
fun prim_minus ctx [VAL (NUM_I a), VAL (NUM_I b)] = (ctx, VAL (NUM_I (a - b)))
fun prim_times ctx [VAL (NUM_I a), VAL (NUM_I b)] = (ctx, VAL (NUM_I (a * b)))

val init_ctx =
  let 
    fun defprim (env, heap, ctr) k v = bind_env env heap ctr (SYM_I k) (PRIM_I (k, v))
    val ctx = ([], [], 0)
    val ctx = defprim ctx "car" prim_car
    val ctx = defprim ctx "cdr" prim_cdr
    val ctx = defprim ctx "eq" prim_eq
    val ctx = defprim ctx "cons" prim_cons
    val ctx = defprim ctx "set" prim_set
    val ctx = defprim ctx "+" prim_plus
    val ctx = defprim ctx "-" prim_minus
    val ctx = defprim ctx "*" prim_times
    val (globalenv, heap, ctr) = ctx
  in 
    ((globalenv, ([]:map)), heap, ctr)
  end

(* eval : ctx -> exp sdata -> val sdata *)
fun eval ctx x =
  let
    val _ = print ("EVAL: " ^ (sdata_to_string x) (*^ "  --- IN: " ^
    (ctx_to_string ctx) *)^ "\n")
  in
    case smallstep ctx x of
        (_, VAL v) => VAL v
      | (ctx, EXP e) => eval ctx (EXP e)
  end

(* Sample program: factorial

(progn
  (define (fact n)
    (cond
      ((eq n 0) 1)
      ((quote otherwise) ( * n (fact (- n 1))))))
  (fact 5))

*)

val sample = to_sdata (
  LIST [SYM "progn",
    LIST [SYM "define", LIST [SYM "fact", SYM "n"],
      LIST [SYM "cond",
        LIST [LIST [SYM "eq", SYM "n", NUM 0], NUM 1],
        LIST [TRUE, LIST [SYM "*", SYM "n", LIST [SYM "fact", LIST [SYM "-", SYM "n", NUM 1]]]]]],
    LIST [SYM "fact", NUM 5]]);
     
