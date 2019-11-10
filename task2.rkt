#lang racket
;-- intp
(define (make-ctx prg input)
   (map list (cdar prg) (map (lambda (v) `',v) input)))

(define (find-block label prg)
  (car (filter
        (lambda (block) (equal? (car block) label))
        prg)))

(define (run-block label ctx prg)
  (let ([block (find-block label prg)])
    (run-commands ctx (cdr block) prg)))

(define (update-ctx asgn ctx)
  (let ([name (cadr asgn)]
        [value (run-expr (caddr asgn) ctx)])
    (cons (list name `',value) (filter (lambda (p)
           (not (equal? name (car p)))) ctx))))


(define (run-expr e ctx)
  ;(printf "~a\n~e\n\n" ctx e)
  (eval `(let ,ctx ,e)))


(define (run-commands ctx commands prg)
  (let ([cmd (car commands)])
    (match (car cmd)
      [':= (run-commands (update-ctx cmd ctx) (cdr commands) prg)]
      ['goto (run-block (cadr cmd) ctx prg)]
      ['if (if (run-expr (cadr cmd) ctx)
               (run-block (caddr cmd) ctx prg)
               (run-block (cadddr cmd) ctx prg))]
      ['return (run-expr (cadr cmd) ctx)])))



(define (run prg input)
  (let ([ctx (make-ctx prg input)]
        [start-label (caadr prg)])
   (run-block start-label ctx prg)))
;-- TM

(define (set-helper p l i v)
  (if (equal? 0 (length l))
      p
      (if (equal? i 0)
          (append p (cons v (cdr l)))
          (set-helper (append p (list (car l))) (cdr l) (- i 1) v))))

(define (setnth l i v)
  (set-helper '() l i v))

(define tm-prg '([if 1 goto 4]
                 [write 1]
                 [right]
                 [goto 0]
                 [write 0]))
(define tape '(0 0 0 1 0 1))
(define tm-in `(,tape ,tm-prg))

(define find_name
  '((read name namelist valuelist)
    (search (if (equal? name (car namelist)) found cont))
    (cont (:= valuelist (cdr valuelist))
          (:= namelist (cdr namelist))
          (goto search))
    (found (return (car valuelist)))
    ))

(define tm `((read tape p)
             ["init" [:= ti 0]
                     [:= pi 0]
                     [goto "loop"]]
             ["loop" [:= inst (list-ref p pi)] [goto "ifl"]]
             ["ifl" (if (equal? (car inst) 'left) "left" "ifr")]
             ["left" [:= ti (- ti 1)] (goto "next")]
             ["ifr" (if (equal? (car inst) 'right) "right" "ifw")]
             ["right" [:= ti (+ ti 1)] (goto "next")]
             ["ifw" (if (equal? (car inst) 'write) "write" "ifgt")]
             ["write" [:= tape (setnth tape ti (cadr inst))] (goto "next")]
             ["ifgt" (if (equal? (car inst) 'goto) "goto" "ifif")]
             ["goto" [:= pi (cadr inst)] (goto "loop")]
             ["ifif" (if (equal? (car inst) 'if) "if" "exit")]
             ["if" (if (equal? (list-ref tape ti) (cadr inst)) "lb" "next")]
             ["lb" [:= pi (cadddr inst)] (goto "loop")]
             ["next" (if (equal? (+ 1 pi) (length p)) "exit" "next1")]
             ["next1" [:= pi (+ 1 pi)] (goto "loop")]
             ["exit" (return tape)]))

;-- mix

(define (is-static division var)
  (member var (car division)))

(define (reduce expr vs)
   `(let ,vs ,expr))

(define (is-static-expr division expr)
  (if (list? expr)
      (if (empty? expr) #t
          (andmap (lambda (a) (is-static-expr division a)) (cdr expr)))
      (not (member expr (cadr division)))))

(define mix '((read program division vs0)
              (init          [:= pending (list (list (cadr program) vs0))]
                             [:= residual '()]
                             [:= marked '()]
                             [goto mainloop])
              (mainloop      [if (null? pending) exit initblock])
              (initblock     [:= pp (caar pending)]
                             [:= vs (cadar pending)]
                             [:= pending (cdr pending)]
                             [:= bb (cdr (find-block pp program))]
                             [:= lbl (list pp vs)]
                             [:= code (list lbl)]
                             [goto cmd-loop])
              (cmd-loop      [if (null? bb) add-block cmd-init])
              (cmd-init      [:= command (car bb)]
                             [:= cmd (car command)]
                             [:= bb (cdr bb)]
                             [goto check-asgn])
              (check-asgn    [if (equal? ':= cmd) mix-asgn check-goto])
              (mix-asgn      [if (is-static division (cadr command)) s-asgn d-asgn])
              (s-asgn        [:= vs (update-ctx (caddr command) vs)]
                             [goto cmd-loop])
              (d-asgn        [:= code (append code (list (':= (cadr command) (reduce (caddr command) vs))))]
                             [goto cmd-loop])
              
              (check-goto    [if (equal? goto cmd) mix-goto check-if])
              (mix-goto      [:= bb (cdr (find-block (cadr command) program))]
                             [goto cmd-loop])
              
              (check-if      [if (equal? if cmd) mix-if check-return])
              (mix-if        [:= expr (cadr command)]
                             [:= ppt (caddr command)]
                             [:= ppf (cadddr command)]
                             [if (is-static-expr division expr) s-if d-if])
              (s-if          [:= ppr (if (run-expr expr vs) ppt ppf)]
                             [:= bb (cdr (find-block ppr program))]
                             [goto cmd-loop])
              (d-if          [:= pending (append pending (new-pending marked (list ppt vs) (list ppf vs)))]
                             [:= code (append code (list 'if reduce(expr, vs) (list ppt vs) (list ppf vs)))]
                             [goto cmd-loop])
              
              (check-return  [if (equal? goto cmd) mix-return check-if])
              (mix-return    [:= code (append code (list 'return reduce(expr, vs)))]
                             [goto cmd-loop])

              (add-block     [:= residual (append residual (list code))]
                             [goto mainloop])
              (exit          [return residual])
              (error         [return 'ERROR])))

(define p-fc '((read a b)
               (l1 [:= b 3]
                   [goto l2])
               (l2 [return (+ a b)])))

(define p-div '((a) (b)))
(define p-vs0 '((a 1) (b 3)))
               