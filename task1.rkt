#lang racket

(define (make-ctx prg)
   (map (lambda (v) (list v 0)) (cdar prg)))

(define (first-label prg) (caaadr prg))

(define (find-block label blocks)
  (find-first (lambda (b) (equal? label (car b))) blocks))

(define (find-first f l) (car (filter f l)))

(define (run-expr e ctx)
  (eval `(let ,ctx ,e)))

(define (find-and-update name value prev ctx)
  (cond
    [(empty? ctx) prev]
    [else
     (let* ([elm (car ctx)]
            [cname (car elm)])
       (if (equal? name cname)
              (append prev (list (list name `',value)) (cdr ctx))
              (find-and-update name value (append prev (list elm)) (cdr ctx))))]))

(define (update-ctx asgn ctx)
  (let ([name (cadr asgn)]
        [value (caddr asgn)])
    (find-and-update name
                     (run-expr value ctx)
                     '()
                     ctx)))

(define (next-label jmp ctx)
  (let ([e (cadr jmp)])
    (match (car jmp)
      ['return (list 'return (run-expr e ctx))]
      ['goto jmp]
      ['if (list 'goto (if (run-expr e ctx) (caddr jmp) (cadddr jmp)))])))

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
    (run-block start ctx (cadr prg))))

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


(define p1 '((read)
             (["l1" () (if (equal? 1 1) "l2" "l3")]
              ["l2" () (return '(1 2 3))]
              ["l3" () (return '(4 5 6))])))

(define tape '(0 0 0 1 0 1))
(define tm `((read p pi ti tape inst)
             (["init" ([:= p ',tm-prg]
                     [:= ti 0]
                     [:= pi 0]
                     [:= tape ',tape]) (goto "loop")]
              ["loop" ([:= inst (list-ref p pi)]) (goto "ifl")]
              ["ifl" () (if (equal? (car inst) 'left) "left" "ifr")]
              ["left" ([:= ti (- ti 1)]) (goto "next")]
              ["ifr" () (if (equal? (car inst) 'right) "right" "ifw")]
              ["right" ([:= ti (+ ti 1)]) (goto "next")]
              ["ifw" () (if (equal? (car inst) 'write) "write" "ifgt")]
              ["write" ([:= tape (setnth tape ti (cadr inst))]) (goto "next")]
              ["ifgt" () (if (equal? (car inst) 'goto) "goto" "ifif")]
              ["goto" ([:= pi (cadr inst)]) (goto "loop")]
              ["ifif" () (if (equal? (car inst) 'if) "if" "exit")]
              ["if" () (if (equal? (list-ref tape ti) (cadr inst)) "lb" "next")]
              ["lb" ([:= pi (cadddr inst)]) (goto "loop")]
              ["next" () (if (equal? (+ 1 pi) (length p)) "exit" "next1")]
              ["next1" ([:= pi (+ 1 pi)]) (goto "loop")]
              ["exit" () (return tape)])))