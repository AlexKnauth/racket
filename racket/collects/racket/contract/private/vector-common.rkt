#lang racket/base

(require "blame.rkt")

(provide (struct-out base-vectorof)
         (struct-out base-vector/c)
         do-check-vectorof
         check-vector/c)

;; Vector contracts need to guard element values on both reads and writes.
;; These contracts allow it to use a different contracts for those two modes.
;; The `write` element-contract is contravariant, and the `read`
;; element-contract is covariant.
;; These are distinguished by either a `-w` or a `-r` on the end.

;; eager is one of:
;; - #t: always perform an eager check of the elements of an immutable vector
;; - #f: never  perform an eager check of the elements of an immutable vector
;; - N (for N>=0): perform an eager check of immutable vectors size <= N
(define-struct base-vectorof (elem-w elem-r immutable eager))

(define-struct base-vector/c (elems-w elems-r immutable))


(define (do-check-vectorof val immutable blame neg-party raise-blame?)
  (cond
    [(vector? val)
     (cond
       [(eq? immutable #t)
        (cond
          [(immutable? val) #t]
          [raise-blame?
           (raise-blame-error
            blame
            #:missing-party neg-party
            val
            '(expected "an immutable vector" given: "~e")
            val)]
          [else #f])]
       [(eq? immutable #f)
        (cond
          [(not (immutable? val)) #t]
          [raise-blame?
           (raise-blame-error
            blame
            #:missing-party neg-party
            val
            '(expected "an mutable vector" given: "~e")
            val)]
          [else #f])]
       [else #t])]
    [raise-blame?
     (raise-blame-error
      blame
      #:missing-party neg-party
      val
      '(expected "an immutable vector" given: "~e")
      val)]
    [else #f]))

(define (check-vector/c val blame immutable length neg-party)
  (define (raise-blame val . args)
    (apply raise-blame-error blame #:missing-party neg-party val args))
  (do-check-vectorof val immutable blame neg-party #t)
  (unless (or (not length) (= (vector-length val) length))
    (raise-blame-error
     blame
     #:missing-party neg-party
     val
     '(expected: "a vector of ~a element~a" given: "~e")
     length
     (if (= length 1) "" "s")
     val)))
