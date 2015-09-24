#lang racket/base

(require racket/generic rackunit racket/private/generic-methods
         syntax/macro-testing
         (for-syntax racket/base syntax/parse))

(define-generics getter
  (get getter target))

(define-generics pattern
  (has? pattern target)
  #:extends gen:getter)

(generic-methods
 gen:pattern
 (define (has? this target) (pair? target))) ; this works fine

(convert-compile-time-error
 (generic-methods
  gen:pattern
  (define (get this target) (car target)))) ; this gives an ambiguous binding error
