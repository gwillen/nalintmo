{-# LANGUAGE FlexibleInstances #-}
instance Show (Sexp -> Sexp) where
  show _ = "<function>"
data Sexp = Nil | Cons Sexp Sexp | Num Int | Sym String | Func (Sexp -> Sexp) deriving (Show)
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

do_apply :: Sexp -> Sexp
do_apply _ = Nil

bind_params :: Sexp -> Sexp -> Env -> Env
bind_params Nil Nil env = env
bind_params (Cons (Sym p) ps) (Cons a as) env = (p, a) : (bind_params ps as env) 

do_lambda :: Sexp -> Sexp -> Env -> (Sexp, Env)
do_lambda params body env = (Func (\args -> do_eval (Cons (Sym "progn") body)
                                                    (bind_params params args env)),
                             env) 

do_define :: Sexp -> Sexp
do_define _ = Nil

do_car :: Sexp -> Sexp
do_car (Cons x _) = x
do_car _ = error "bad car"

do_cdr :: Sexp -> Sexp
do_cdr (Cons _ x) = x
do_cdr _ = error "bad cdr"

do_eval :: Sexp -> Env -> (Sexp, Env)
do_eval (Num n) env = (Num n, env)
do_eval (Sym s) env = (case get_var s env of Just x -> x ; Nothing -> error "Bad var", env)
do_eval Nil env = (Nil, env)
do_eval (Cons (Sym "car") (Cons x Nil)) env = let (r, env') = do_eval x env in (do_car r, env')
do_eval (Cons (Sym "cdr") (Cons x Nil)) env = let (r, env') = do_eval x env in (do_cdr r, env')
do_eval (Cons (Sym "progn") x) env = do_progn x env
do_eval (Cons (Sym "lambda") (Cons params body)) env = do_lambda params body env
