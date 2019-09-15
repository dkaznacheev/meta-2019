#lang racket

(define p1 '((read x y z)
             (["l1" ([:= x 200]) (return x)])))

(define (make-ctx prg)
   (map (lambda (v) (cons v 1)) (cdar prg)))

(define (first-label prg) (caadr prg))

(define (find-block label blocks)
  (caar (filter (lambda (b) (equal? label (car b))) blocks)))

(define (run-block label ctx blocks)
  (let ([start-block (find-block label blocks)])
    start-block))

(define (run prg)
  (let ([ctx (make-ctx prg)]
        [start (first-label prg)])
    (run-block start ctx (cdr prg))))