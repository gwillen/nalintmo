{-# LANGUAGE FlexibleInstances #-}
import Data.Maybe

instance Show (Sexp -> Sexp) where
  show _ = "<function>"
instance Eq (Sexp -> Sexp) where
  (==) _ _ = False
data Sexp = Nil | Cons Sexp Sexp | Num Int | Sym String | Func (Sexp -> Sexp) deriving (Show, Eq)
type Env = [(String, Sexp)]

get_var :: String -> Env -> Maybe Sexp
get_var _ [] = Nothing
get_var s ((k,v):xs)
  | s == k = Just v
  | otherwise = get_var s xs

mapcar_internal :: (Sexp -> Sexp) -> Sexp -> [Sexp]
mapcar_internal _ Nil = []
mapcar_internal f (Cons x xs) = (f x):(mapcar_internal f xs)
mapcar_internal _ _ = error "bad mapcar_internal"

do_progn :: Sexp -> Env -> (Sexp, Env)
do_progn Nil env = (Nil, env)
do_progn (Cons x Nil) env = do_eval x env
do_progn (Cons x xs) env = let (_, env') = do_eval x env in do_progn xs env'

do_apply :: Sexp -> Sexp -> Env -> (Sexp, Env)
do_apply (Func f) args env = (f args, env) 

bind_params :: Sexp -> Sexp -> Env -> Env
bind_params Nil Nil env = env
bind_params (Cons (Sym p) ps) (Cons a as) env = (p, a) : (bind_params ps as env) 

-- There's something wrong with my environment handling here, but iono if it
--  matters in the absence of setq. Fst discards the returned environment from
--  the function body, so defines in function bodies will have no effect.
do_lambda :: Sexp -> Sexp -> Env -> (Sexp, Env)
do_lambda params body env = (Func (\args -> fst $do_eval (Cons (Sym "progn") body)
                                                         (bind_params params args env)),
                             env) 

-- As above we discard the environment resulting from the body of the define.
do_define :: String -> Sexp -> Env -> (Sexp, Env)
do_define name val env = (Nil, (name, fst $ do_eval val env) : env)

-- Here we are doing a clever haskellism defining evn' recursively in terms of
--  itself. I have no idea whether that works.
do_define_func :: String -> Sexp -> Sexp -> Env -> (Sexp, Env)
do_define_func name params body env =
  let env' = (name, fst $ do_lambda params body env') : env
  in (Nil, env')

do_car :: Sexp -> Sexp
do_car (Cons x _) = x
do_car _ = error "bad car"

do_cdr :: Sexp -> Sexp
do_cdr (Cons _ x) = x
do_cdr _ = error "bad cdr"

-- I'm tired. No bools tonight. Also we throw away env again. Because I said
--  so.
do_cond :: Sexp -> Env -> (Sexp, Env)
do_cond Nil env = (Nil, env)
do_cond (Cons (Cons cond (Cons result Nil)) rest) env =
  case do_eval cond env of
    (Nil, _) -> do_cond rest env
    (_, _) -> do_eval result env

do_eq :: Sexp -> Sexp -> Env -> (Sexp, Env)
do_eq lhs rhs env = let
  (lhs', _) = do_eval lhs env
  (rhs', _) = do_eval rhs env
  in case lhs == rhs of
    False -> (Nil, env)
    True -> ((Sym "true"), env)
    
do_eval :: Sexp -> Env -> (Sexp, Env)
do_eval (Num n) env = (Num n, env)
do_eval (Sym s) env = (case get_var s env of Just x -> x ; Nothing -> error "Bad var", env)
do_eval Nil env = (Nil, env)
do_eval (Cons (Sym "car") (Cons x Nil)) env = let (r, env') = do_eval x env in (do_car r, env')
do_eval (Cons (Sym "cdr") (Cons x Nil)) env = let (r, env') = do_eval x env in (do_cdr r, env')
do_eval (Cons (Sym "progn") x) env = do_progn x env
do_eval (Cons (Sym "lambda") (Cons params body)) env = do_lambda params body env
do_eval (Cons (Sym "define") (Cons (Sym name) val)) env = do_define name val env
do_eval (Cons (Sym "define") (Cons (Cons (Sym name) params) body)) env = do_define_func name params body env
do_eval (Cons (Sym "quote") (Cons arg Nil)) env = (arg, env)
do_eval (Cons (Sym "cond") body) env = do_cond body env
do_eval (Cons (Sym "eq") (Cons lhs (Cons rhs Nil))) env = do_eq rhs lhs env
do_eval (Cons (Sym f) args) env = do_apply (Data.Maybe.fromJust $ get_var f env) args env


{- Sample program: factorial

(progn
  (define (fact n)
    (cond
      ((eq n 0)
-}
