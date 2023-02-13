
;; A PartialOrdering is a Real where:
;;  - zero?     represents =~
;;  - negative? represents <~
;;  - positive? represents >~
;;  - nan?      represents incomparable

;; partial-ordering-normalize : PartialOrdering -> PartialOrdering
(define (partial-ordering-normalize c)
  (cond
    [(zero? c) 0]
    [(negative? c) -1]
    [(positive? c) 1]
    [(nan? c) +nan.0]
    [else (raise-argument-error 'partial-compare "real?" c)]))

;; ord-and/prod2 : PartialOrdering PartialOrdering -> PartialOrdering
(define (ord-and/prod2 c0 c1)
  (cond
    [(zero? c0) c1]
    [(zero? c1) c0]
    [(and (negative? c0) (negative? c1)) -1]
    [(and (positive? c0) (positive? c1)) 1]
    [else +nan.0]))

;; A Realish is one of:
;;  - Real
;;  - Extflonum
(define (realish? v) (real? v))

;; realish-key : Realish -> Real
(define (realish-key x)
  (cond
    [(eq? x +inf.0) +inf.0]
    [(eq? x -inf.0) -inf.0]
    [(eq? x +nan.0) +nan.0]
    [else (inexact->exact x)]))

;; partial-compare-realish : Realish Realish -> PartialOrdering
(define (partial-compare-realish a b)
  (cond
    [(and (real? a) (real? b)) (partial-compare-real a b)]
    [else (partial-compare-real (realish-key a) (realish-key b))]))

;; partial-compare-real : Real Real -> PartialOrdering
(define (partial-compare-real a b)
  (cond
    [(= a b) 0]
    [(< a b) -1]
    [(> a b) 1]
    [else +nan.0]))

;; product-compare/recur : Any Any [Any Any -> PartialOrdering] -> PartialOrdering
(define (product-compare/recur a b cmp)
  (cond
    [(eq? a b) 0]
    [(flvector? a)
     (cond
       [(and (flvector? b) (= (flvector-length a) (flvector-length b)))
        (let loop ([acc 0] [i 0])
          (cond
            [(nan? acc) acc]
            [(<= (flvector-length a) i) acc]
            [else
             (loop (ord-and/prod2 acc (cmp (flvector-ref a i) (flvector-ref b i)))
                   (add1 i))]))]
       [else +nan.0])]
    [else
     (let ([<=? (lambda (ai bi) (<= (cmp ai bi) 0))]
           [>=? (lambda (ai bi) (>= (cmp ai bi) 0))])
       (let ([le (equal?/recur a b <=?)]
             [ge (equal?/recur a b >=?)])
         (cond
           [(and le ge) 0]
           [le -1]
           [ge 1]
           [else +nan.0])))]))

;; --------------------------------------------------------

(define-values (prop:partial-order partial-order? partial-order-ref)
  (make-struct-type-property 'partial-order
                             (lambda (val info)
                               (check 'guard-for-prop:partial-order
                                      :test (and (list? val)
                                                 (= 2 (length val))
                                                 (procedure? (car val))
                                                 (procedure? (cadr val))
                                                 (procedure-arity-includes? (car val) 3)
                                                 (procedure-arity-includes? (cadr val) 2))
                                      :contract (string-append
                                                 "(list/c (procedure-arity-includes/c 3)\n"
                                                 "        (procedure-arity-includes/c 2))")
                                      val)
                               ;; a `cons` here creates a unique identity for each time the
                               ;; property is attached to a structure type
                               (cons (car val) (cdr val)))))

;; --------------------------------------------------------

;; partial-compare/recur : Any Any [Any Any -> PartialOrder] -> PartialOrder
(define (partial-compare/recur a b recur)
  (let ([cmp (lambda (ai bi) (partial-ordering-normalize (recur ai bi)))])
    (cond
      [(partial-order? a)
       (cond
         [(partial-order? b)
          (let ([av (partial-order-ref a)])
            (cond
              [(eq? av (partial-order-ref b))
               (partial-ordering-normalize ((car av) a b cmp))]
              [else +nan.0]))]
         [else +nan.0])]
      [(realish? a)
       (cond
         [(realish? b) (partial-compare-realish a b)]
         [else +nan.0])]
      [else
       (product-compare/recur a b cmp)])))

;; partial-compare : Any Any -> PartialOrder
(define (partial-compare a b)
  (partial-compare/recur a b partial-compare))

;; PartialOrder -> PartialOrder
(define (early-nan/= c) (if (zero? c) 0 +nan.0))
(define (early-nan/<= c) (if (<= c 0) c +nan.0))
(define (early-nan/>= c) (if (>= c 0) c +nan.0))

;; Any Any -> PartialOrder
(define (partial-compare/= a b)
  (early-nan/= (partial-compare/recur a b partial-compare/=)))

(define (partial-compare/<= a b)
  (early-nan/<= (partial-compare/recur a b partial-compare/<=)))

(define (partial-compare/>= a b)
  (early-nan/>= (partial-compare/recur a b partial-compare/>=)))

;; Any Any -> Boolean
(define (=~ a b) (zero? (partial-compare/= a b)))
(define (!=~ a b) (not (zero? (partial-compare/= a b))))

(define (<~ a b) (negative? (partial-compare/<= a b)))
(define (>~ a b) (positive? (partial-compare/>= a b)))
(define (<=~ a b) (<= (partial-compare/<= a b) 0))
(define (>=~ a b) (>= (partial-compare/>= a b) 0))

;; --------------------------------------------------------

;; Any -> Fixnum
(define (compare-hash-code x)
  (cond
    [(partial-order? x)
     (->fx/checked 'compare-hash-code ((cadr (partial-order-ref x)) x compare-hash-code))]
    [(realish? x) (equal-hash-code (realish-key x))]
    [(flvector? x)
     (let loop ([acc (equal-hash (make-flvector 0))] [i 0])
       (cond
         [(<= (flvector-length x) i) acc]
         [else
          (loop (hash-code-combine acc (compare-hash-code (flvector-ref x i)))
                (add1 i))]))]
    [else (equal-hash-code/recur x compare-hash-code)]))
