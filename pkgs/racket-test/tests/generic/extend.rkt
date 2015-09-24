#lang racket/base

(require racket/generic rackunit)

(define-generics getter
  (get getter target))

(define-generics pattern
  (has? pattern target)
  #:extends gen:getter)

(struct car* ()
  #:methods gen:pattern
  [(define (has? this target) (pair? target))
   (define (get this target) (car target))])

(check-false (has? (car*) 1) #f)
(check-true (has? (car*) '(1 . 2)) #t)
(check-equal? (get (car*) '(1 . 2)) 1)
