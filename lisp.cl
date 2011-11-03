(defvar global-env nil)

(defun do-eval (exp env)
  (princ "eval ")
  (princ exp)
  (princ " [with ")
  (princ env)
  (princ "]")
  (terpri)
  (cond
    ((numberp exp) exp)
    ((atom exp) (get-var exp env))
    (t
      (case (car exp)
        (lambda (do-lambda (cadr exp) (cddr exp) env))
        (define (do-define (cadr exp) (cddr exp) env))
        (setq (do-setq (cadr exp) (cddr exp) env))
        (car (car (do-eval (cadr exp) env)))
        (cdr (cdr (do-eval (cadr exp) env)))
        (cadr (cadr (do-eval (cadr exp) env)))
        (quote (cadr exp))
        (progn (do-progn (cdr exp) env))
        (otherwise (do-apply (car exp) (cdr exp) env))))))

(defun do-progn (exps env)
  (car (last (mapcar (curry-eval env) exps))))

(defun curry-eval (env)
  (lambda (exp) (do-eval exp env)))
  
(defun do-apply (f args env)
  (apply (do-eval f env) (mapcar (curry-eval env) args)))

(defun do-define (var rest env)
  (def-var-global var (do-eval (car rest) env)))

(defun do-setq (var rest env)
  (set-var var (do-eval (car rest) env) env))

(defun do-lambda (params body env)
  (lambda (&rest args)
    (do-eval (cons 'progn body)
             (bind-params params args env))))

(defun bind-params (params args env) 
  (cond
    ((null params) env)
    (t (def-var (car params)
                (car args)
                (bind-params (cdr params) (cdr args) env)))))

(defun def-var-global (var val)
  (setf global-env (def-var (var val global-env))))

(defun def-var (var val env)
  (cons (cons var val) env))

(defun set-var (var val env)
  (cond
    ((null env) nil)
    ((eq (caar env) var) (setf (cdar env) val))
    (t (set-var var val (cdr env)))))

(defun get-var (var env)
  (cond
    ((null env) nil)
    ((eq (caar env) var) (cdar env))
    (t (get-var var (cdr env)))))
