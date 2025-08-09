#lang racket
(require racket/match
         racket/list
         racket/pretty
         dcc019/exercise/logic/ast)

(provide eval-query)

;; =========================================================
;; Normalização de nomes
;; =========================================================
(define (name->sym x)
  (cond [(symbol? x) x]
        [(string? x) (string->symbol x)]
        [else (string->symbol (~a x))]))

;; =========================================================
;; Helpers para sequências "lista pontuada" (par encadeado)
;; =========================================================

;; Converte sequência encadeada para lista "normal".
;; Funciona para lista normal (termina em '()) e lista pontuada (termina em valor).
(define (seq->list s)
  (let loop ([p s] [acc '()])
    (cond
      [(null? p) (reverse acc)]               ; lista normal terminou em '()
      [(pair? p) (loop (cdr p) (cons (car p) acc))] ; ainda tem pares
      [else (reverse (cons p acc))])) )       ; lista pontuada: inclui último elemento


;; Map preservando forma de "lista pontuada" nos args
(define (args-map f args)
  (cond
    [(pair? args) (cons (f (car args)) (args-map f (cdr args)))]
    [else (f args)]))

;; Converte args p/ lista normal
(define (args->list args) (seq->list args))

;; Conta aridade em estrutura encadeada
(define (args-length args) (length (args->list args)))

;; =========================================================
;; Utilitários de AST
;; =========================================================
(define (atom=? a b)
  (and (ast:atom? a) (ast:atom? b)
       (equal? (name->sym (ast:atom-name a))
               (name->sym (ast:atom-name b)))))

(define (functor-same-signature? f1 f2)
  (and (ast:functor? f1) (ast:functor? f2)
       (equal? (name->sym (ast:functor-name f1))
               (name->sym (ast:functor-name f2)))
       (= (args-length (ast:functor-args f1))
          (args-length (ast:functor-args f2)))))

;; =========================================================
;; Substituições
;; =========================================================

(define (lookup-subst s x)
  (cond [(assq x s) => cdr]
        [else #f]))

(define (extend-subst s x v)
  (cons (cons x v) s))

;; aplica substituição recursivamente
(define (apply-subst s t)
  (cond
    [(ast:var? t)
     (define name (ast:var-name t))
     (define b (lookup-subst s name))
     (if b (apply-subst s b) t)]
    [(ast:unknow-var? t) t]
    [(ast:functor? t)
     (ast:functor (ast:functor-name t)
                  (args-map (λ (a) (apply-subst s a))
                            (ast:functor-args t)))]
    [else t]))

;; ocorre-checagem leve para evitar x = f(x)
(define (occurs-in? x t s)
  (define t* (apply-subst s t))
  (cond
    [(ast:var? t*) (equal? (ast:var-name t*) x)]
    [(ast:functor? t*)
     (for/or ([a (in-list (args->list (ast:functor-args t*)))])
       (occurs-in? x a s))]
    [else #f]))

;; =========================================================
;; Unificação
;; =========================================================

(define (unify t1 t2 s)
  (let ([u1 (apply-subst s t1)]
        [u2 (apply-subst s t2)])
    (cond
      [(and (ast:atom? u1) (ast:atom? u2))
       (if (atom=? u1 u2) s #f)]
      [(and (ast:functor? u1) (ast:functor? u2))
       (if (functor-same-signature? u1 u2)
           (unify-args (args->list (ast:functor-args u1))
                       (args->list (ast:functor-args u2)) s)
           #f)]
      [(ast:unknow-var? u1) s]
      [(ast:unknow-var? u2) s]
      [(ast:var? u1)
       (define x (ast:var-name u1))
       (cond
         [(equal? u1 u2) s]
         [(occurs-in? x u2 s) #f]
         [else (extend-subst s x u2)])]
      [(ast:var? u2)
       (unify u2 u1 s)]
      [else #f])))

(define (unify-args as bs s)
  (if (null? as) s
      (let ([s1 (unify (car as) (car bs) s)])
        (and s1 (unify-args (cdr as) (cdr bs) s1)))))

;; =========================================================
;; Padronização de variáveis por cláusula
;; =========================================================

(define (rename-vars/term t renv)
  (cond
    [(ast:var? t)
     (define old (ast:var-name t))
     (ast:var (hash-ref renv old old))]
    [(ast:unknow-var? t) t]
    [(ast:functor? t)
     (ast:functor (ast:functor-name t)
                  (args-map (λ (a) (rename-vars/term a renv))
                            (ast:functor-args t)))]
    [else t]))

(define (rename-vars/body b renv)
  (cond
    [(ast:eq? b)
     (ast:eq (rename-vars/term (ast:eq-lterm b) renv)
             (rename-vars/term (ast:eq-rterm b) renv))]
    [(ast:neq? b)
     (ast:neq (rename-vars/term (ast:neq-lterm b) renv)
              (rename-vars/term (ast:neq-rterm b) renv))]
    [else (rename-vars/term b renv)]))

(define (standardize-apart clause)
  (define ren (make-hash))
  (define (fresh sym)
    (string->symbol (format "~a@~a" sym (gensym ""))))
  (define (walk t)
    (cond
      [(ast:var? t)
       (define n (ast:var-name t))
       (hash-ref! ren n (λ () (fresh n)))]
      [(ast:functor? t)
       (for-each walk (args->list (ast:functor-args t)))]
      [(ast:eq? t) (begin (walk (ast:eq-lterm t))
                          (walk (ast:eq-rterm t)))]
      [(ast:neq? t) (begin (walk (ast:neq-lterm t))
                           (walk (ast:neq-rterm t)))]
      [else (void)]))
  (walk (ast:clause-head clause))
  (for-each walk (seq->list (ast:clause-body clause)))
  (values
   (ast:clause (rename-vars/term (ast:clause-head clause) ren)
               (map (λ (b) (rename-vars/body b ren))
                    (seq->list (ast:clause-body clause))))))

;; =========================================================
;; Coleta de variáveis
;; =========================================================

(define (collect-vars-in-term t)
  (cond
    [(ast:var? t) (list (ast:var-name t))]
    [(ast:unknow-var? t) '()]
    [(ast:functor? t)
     (apply append (map collect-vars-in-term
                        (args->list (ast:functor-args t))))]
    [(ast:atom? t) '()]
    [else '()]))

(define (collect-vars-in-goal g)
  (cond
    [(or (ast:eq? g) (ast:neq? g))
     (append (collect-vars-in-term (if (ast:eq? g) (ast:eq-lterm g) (ast:neq-lterm g)))
             (collect-vars-in-term (if (ast:eq? g) (ast:eq-rterm g) (ast:neq-rterm g))))]
    [else (collect-vars-in-term g)]))

(define (vars-in-query q)
  (remove-duplicates
   (cond
     [(pair? q) (apply append (map collect-vars-in-goal (seq->list q)))]
     [(list? q) (apply append (map collect-vars-in-goal q))]
     [else (collect-vars-in-goal q)])))

;; =========================================================
;; Resolução SLD (DFS)
;; =========================================================

;; Converte o "programa" em uma lista de cláusulas, mesmo que ele venha
;; como lista pontuada, lista normal, ou até single clause.
(define (program-clauses prog)
  (cond
    [(and (list? prog) (andmap ast:clause? prog)) prog]
    [(pair? prog) (filter ast:clause? (seq->list prog))]
    [(ast:clause? prog) (list prog)]
    [else '()]))

(define (resolve prog goals subst k-emit)
  (cond
    [(null? goals) (k-emit subst)]
    [else
     (define g (car goals))
     (cond
       [(ast:eq? g)
        (define s1 (unify (ast:eq-lterm g) (ast:eq-rterm g) subst))
        (when s1 (resolve prog (cdr goals) s1 k-emit))]
       [(ast:neq? g)
        (define s1 (unify (ast:neq-lterm g) (ast:neq-rterm g) subst))
        (when (not s1) (resolve prog (cdr goals) subst k-emit))]
       [else
        (for ([cl (in-list (program-clauses prog))])
          (define-values (cl*) (standardize-apart cl))
          (define s1 (unify (ast:clause-head cl*) g subst))
          (when s1
            (define new-goals (append (seq->list (ast:clause-body cl*))
                                      (cdr goals)))
            (resolve prog new-goals s1 k-emit)))] )]))

;; =========================================================
;; Pretty print de termos/soluções
;; =========================================================

(define (symish x)
  (cond
    [(symbol? x) x]
    [(string? x) (string->symbol x)]
    [else (string->symbol (~a x))]))

(define (term->string t)
  (cond
    [(ast:atom? t) (~a (symish (ast:atom-name t)))]
    [(ast:var? t)  (~a (symish (ast:var-name t)))]
    [(ast:unknow-var? t) "_"]
    [(ast:functor? t)
     (define name (~a (symish (ast:functor-name t))))
     (define args (map term->string (args->list (ast:functor-args t))))
     (format "~a(~a)" name (string-join args ", "))]
    [else (~a t)]))

(define (solution->string sol)
  ;; sol = '((X . term) (Y . term) ...)
  (if (null? sol)
      "#t"
      (string-join
       (for/list ([kv (in-list sol)])
         (format "~a = ~a" (car kv) (term->string (cdr kv))))
       ", ")))

;; =========================================================
;; eval-query
;; =========================================================

(define (normalize-goals q)
  (cond
    [(pair? q) (seq->list q)]
    [(list? q) q]
    [else (list q)]))

(define (eval-query prog query)
  (define goals (normalize-goals query))
  (define qvars (vars-in-query query))
  (define out '())
  (resolve prog goals '()
           (λ (s)
             (set! out
                   (cons (for/list ([vn (in-list qvars)])
                           (cons vn (apply-subst s (or (lookup-subst s vn)
                                                       (ast:var vn)))))
                         out))))
  (set! out (reverse out))

  ;; Gera as linhas a imprimir
  (define lines
    (cond
      [(null? qvars) (list (if (pair? out) "true" "false"))]
      [else
       (if (null? out)
           (list "false")
           (map solution->string out))]))

  ;; Retorna um syntax que imprime as linhas (sem backquotes aninhados)
  (datum->syntax
   #f
   (cons 'begin
         (for/list ([s (in-list lines)])
           (list 'displayln s)))))
