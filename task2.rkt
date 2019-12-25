#lang racket

(provide main)


(define-namespace-anchor anc)
(define ns (namespace-anchor->namespace anc))

;-- intp
(define (make-ctx prg input)
   (map list (cdar prg) (map (lambda (v) `',v) input)))

(define (find-block label prg)
  (car (filter
        (lambda (block) (equal? (car block) label))
        prg)))

(define (run-block label ctx prg)
  (let ([block (find-block label prg)])
    ;(printf ">~e\n" label)
    (run-commands ctx (cdr block) prg)))

(define (update-ctx asgn ctx)
  (let ([name (cadr asgn)]
        [value (run-expr (caddr asgn) ctx)])
    (out "name" name)
    (out "value" value)
    (cons (list name `',value) (filter (lambda (p)
           (not (equal? name (car p)))) ctx))))

(define (run-expr e ctx)
  (out "ctx" ctx)
  (out "e" e)
  (eval `(let ,ctx ,e) ns)
  )


(define (run-commands ctx commands prg)
  (let ([cmd (car commands)])
    ;(printf ">>~e\n" cmd)
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

(define tm-prg '([0 write 1]))
(define tape '(0 0 0 1 0 1))
(define tm-in `(,tm-prg ,tape))

(define find_name
  '((read name namelist valuelist)
    (search (if (equal? name (car namelist)) found cont))
    (cont (:= valuelist (cdr valuelist))
          (:= namelist (cdr namelist))
          (goto search))
    (found (return (car valuelist)))
    ))

(define tm-int
  '((read Q Right)
    (init (:= Qtail Q) (:= Left (list)) (goto loop))
    (loop (if (equal? Qtail (list)) end exec))
    (exec (:= cmd (car Qtail))
          (:= Qtail (cdr Qtail))
          (:= op (cadr cmd))
          (goto match1))
    (match1 (if (equal? op 'right) exec-right match2))
    (match2 (if (equal? op 'left) exec-left match3))
    (match3 (if (equal? op 'write) exec-write match4))
    (match4 (if (equal? op 'goto) exec-goto match5))
    (match5 (if (equal? op 'if) exec-if err))

    (exec-right (:= Left (cons (car Right) Left))
                (:= Right (cdr Right))
                (goto loop))
    (exec-left (:= Right (cons (car Left) Right))
               (:= Left (cdr Left))
               (goto loop))
    (exec-write (:= Right (cons (caddr cmd) (cdr Right)))
                (goto loop))
    (exec-goto (:= Qtail (memf (λ (bmd) (equal? (car bmd) (caddr cmd))) Q))
                (goto loop))
    (exec-if (if (equal? (caddr cmd) (car Right)) jmp loop))
    (jmp (:= Qtail (memf (λ (bmd) (equal? (cadddr (cdr cmd)) (car bmd))) Q))
         (goto loop))
    
    (err (return `unexpected ,cmd))
    (end (return Right))
    )
  )

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

(define tm-div
  '((p pi inst) (ti tape)))

;-- mix

(define (is-static division var)
  (member var (car division)))

(define (reduce expr vs)
  (define (handle-error e) 
    (match e
      [(list es ...) (map do-eval e)]
      [_  e]))
  (define (do-eval e)
    (with-handlers
      ([exn:fail? (λ (err) (handle-error e))])
      `',(run-expr e vs)))
  (do-eval expr))

;(define (reduce expr vs)
;   (eval `(let ,vs ,expr)))

(define (is-static-expr division expr)
  (if (list? expr)
      (if (empty? expr) #t
          (andmap (lambda (a) (is-static-expr division a)) (cdr expr)))
      (not (member expr (cadr division)))))

(define (out s ex)
  ;(printf "!~e: ~e\n" s ex)
  ex)

(define (new-pending marked p)
  (if (member p marked) '() (list p)))

(define mix '((read program division vs0)
              (init          [:= pending (list (list (caadr program) vs0))]
                             [:= residual (list (append (list 'read) (cadr division)))]
                             [:= marked '()]
                             [goto mainloop])
              (mainloop      [if (null? pending) exit initblock])
              (initblock     [:= tmp (out "pending" pending)]
                             [:= pp (caar pending)]
                             [:= vs (cadar pending)]
                             [:= marked (append marked (car pending))]
                             [:= tmp (out "marked" marked)]
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
              (s-asgn        ;[:= tmp (out "ctx" vs)]
                             [:= newvar (list ':= (cadr command) (reduce (caddr command) vs))]
                             ;[:= tmp (out "ctx" vs)]
                             ;[:= tmp (out "nv" newvar)]
                             [:= vs (update-ctx newvar vs)]
                             [goto cmd-loop])
              (d-asgn        [:= tmp (out ""  (reduce (caddr command) vs))]
                             [:= code (append code (list (list ':= (cadr command) (reduce (caddr command) vs))))]
                             [goto cmd-loop])
              
              (check-goto    [if (equal? 'goto cmd) mix-goto check-if])
              (mix-goto      [:= bb (cdr (find-block (cadr command) program))]
                             [goto cmd-loop])
              
              (check-if      [if (equal? 'if cmd) mix-if check-return])
              (mix-if        [:= expr (cadr command)]
                             [:= ppt (caddr command)]
                             [:= ppf (cadddr command)]
                             [if (is-static-expr division expr) s-if d-if])
              (s-if          ;[:= tmp (out "expr" expr)]
                             [:= ppr (if (run-expr expr vs) ppt ppf)]
                             [:= bb (cdr (find-block ppr program))]
                             [goto cmd-loop])
              (d-if          [:= pending (append pending (new-pending marked (list ppt vs)))]
                             [:= pending (append pending (new-pending marked (list ppf vs)))]
                             [:= code (append code (list (list 'if (reduce expr vs) (list ppt vs) (list ppf vs))))]
                             [goto cmd-loop])
              
              (check-return  [if (equal? 'return cmd) mix-return error])
              (mix-return    [:= expr (cadr command)]
                             [:= tmp (out "expr" expr)]
                             [:= tmp (out "vs" vs)]
                             [:= code (append code (list (list 'return (reduce expr vs))))]
                             [goto cmd-loop])

              (add-block     [:= residual (append residual (list code))]
                             [goto mainloop])
              (exit          [return residual])
              (error         [return 'ERROR])))

(define p-fc '((read a c)
               (l1 [:= c (+ a c)] [goto l2])
               (l2 [return c])))

(define p-div '((a) (c)))
(define p-vs0 '((a 3)))

(define p-in `(,p-fc ,p-div ,p-vs0))

(define (pprint prg)
  (printf "\n\n")
  (for-each (lambda (cmd) (printf "~e\n" cmd)) prg))
  (printf "\n\n")

(define (mix-and-run mix-input run-input)
  (let ([mixed (run mix mix-input)])
    (pprint mixed)
    
    (run mixed run-input)))

(define (futamura-1-naive-simple)
  (mix-and-run p-in '(3)))

(define (futamura-1-naive)
  (let* ([p-fc tm-int]
         [p-div '((Q Qtail op cmd) (Right))]
         [p-vs0 `((Q ',tm-prg))]
         [p-in `(,p-fc ,p-div ,p-vs0)])
  (mix-and-run p-in (list tape))))

(define (main)
  (futamura-1-naive))
