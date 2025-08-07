#lang racket

(require dcc019/exercise/logic/ast
         racket/list
         racket/match)

(provide eval-query)

;; Ambiente: lista de pares (variável . valor)
(define empty-env '())

;; ===========================
;; Função auxiliar para garantir que args sejam listas
;; ===========================
(define (list->proper cons-pair)
  (if (pair? cons-pair)
      (cons (car cons-pair) (list->proper (cdr cons-pair)))
      (if (null? cons-pair) '() (list cons-pair))))

;; ===========================
;; Unificação de termos
;; ===========================
(define (unify t1 t2 env)
  (match* (t1 t2)
    [((ast:var v1) (ast:var v2))
     (if (equal? v1 v2)
         env
         (extend-env v1 t2 env))]

    [((ast:var v) term)
     (extend-env v term env)]

    [(term (ast:var v))
     (extend-env v term env)]

    [((ast:atom a1) (ast:atom a2))
     (if (equal? a1 a2) env #f)]

    [((ast:functor f1 args1) (ast:functor f2 args2))
     (let ([args1-list (if (list? args1) args1 (list->proper args1))]
           [args2-list (if (list? args2) args2 (list->proper args2))])
       (if (and (equal? f1 f2) (= (length args1-list) (length args2-list)))
           (unify-lists args1-list args2-list env)
           #f))]

    [(_ _) #f]))

(define (unify-lists l1 l2 env)
  (if (null? l1)
      env
      (let ([new-env (unify (car l1) (car l2) env)])
        (if new-env
            (unify-lists (cdr l1) (cdr l2) new-env)
            #f))))

(define (extend-env var val env)
  (let ([bound (assoc var env)])
    (if bound
        (if (equal? (cdr bound) val)
            env
            #f) ; conflito
        (cons (cons var val) env))))

;; ===========================
;; Aplicar substituição
;; ===========================
(define (apply-subst term env)
  (match term
    [(ast:var v)
     (let ([b (assoc v env)])
       (if b (apply-subst (cdr b) env) term))]

    [(ast:functor f args)
     (ast:functor f (map (λ (arg) (apply-subst arg env))
                         (if (list? args) args (list->proper args))))]

    [_ term]))

;; ===========================
;; Resolução SLD
;; ===========================
(define (resolve goal prog env)
  (define (step goal clauses)
    (if (null? clauses)
        '()
        (let* ([cl (car clauses)]
               [head (ast:clause-head cl)]
               [body (ast:clause-body cl)]
               [new-env (unify goal head env)])
          (if new-env
              (resolve-list (if (list? body) body (list->proper body)) prog new-env)
              (step goal (cdr clauses))))))

  (step goal prog))

(define (resolve-list goals prog env)
  (cond
    [(null? goals) (list env)] ; sucesso
    [else
     (let* ([first (car goals)]
            [rest (cdr goals)]
            [matches (resolve first prog env)])
       (apply append
              (map (λ (e) (resolve-list rest prog e)) matches)))]))

;; ===========================
;; Função principal
;; ===========================
(define (eval-query prog query)
  (define goals (if (list? query) query (list query)))
  (define results (resolve-list goals prog empty-env))

  (if (null? results)
      '()
      (map show-subst results)))

;; Impressão do ambiente
(define (show-subst env)
  (map (λ (pair)
         (cons (car pair) (apply-subst (cdr pair) env)))
       env))
