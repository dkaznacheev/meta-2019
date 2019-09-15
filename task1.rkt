#lang racket

(define p1 '((read x y z)
             (["l1" ([:= x (+ 1 2)]) (return x)])))

(define (make-ctx prg)
   (map (lambda (v) (list v 0)) (cdar prg)))

(define (first-label prg) (caadr prg))

(define (find-block label blocks)
  (car (find-first (lambda (b) (equal? label (car b))) blocks)))

(define (find-first f l) (car (filter f l)))

(define (run-expr e ctx)
    (eval (list 'let ctx e)))

(define (find-and-update name value prev ctx)
  (cond
    [(empty? ctx) prev]
    [else
     (let* ([elm (car ctx)]
            [cname (car elm)]
            [cvalue (cdr elm)])
       (if (equal? name cname)
              (append prev (list (list name value)) (cdr ctx))
              (find-and-update name (run-expr value ctx) (append prev (list elm)) (cdr ctx))))]))

(define (update-ctx asgn ctx)
  (let ([name (cadr asgn)]
        [value (eval (caddr asgn))])
    (find-and-update name
                     value;(run-expr value ctx)
                     '()
                     ctx)))

(define (next-label jmp ctx)
  (let ([e (cadr jmp)])
    (match (car jmp)
      ['return (list 'return (run-expr e ctx))]
      ['goto jmp]
      ['if ('goto (if (run-expr e ctx) (caddr jmp) (cadddr jmp)))])))

(define (run-block label ctx blocks)
  (let* ([start-block (find-block label blocks)]
         [asgns (cadr start-block)]
         [jmp (caddr start-block)]
         [new-ctx (foldl update-ctx ctx asgns)]
         [res (next-label jmp new-ctx)])
    (match (car res)
      ['return (cadr res)]
      ['goto (run-block (cadr res) new-ctx blocks)])))

(define (run prg)
  (let ([ctx (make-ctx prg)]
        [start (first-label prg)])
    (run-block start ctx (cdr prg))))

(define p2 '((read x)
             ([1 ([:= x 100]) (goto 3)]
              [2 ([:= x 400]) (goto 3)]
              [3 () (return x)])))