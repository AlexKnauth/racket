#lang racket/base

(require (for-syntax racket/base)
         "guts.rkt"
         "prop.rkt"
         "blame.rkt"
         "misc.rkt"
         "collapsible-common.rkt"
         (submod "collapsible-common.rkt" properties)
         "vector-common.rkt"
         "vector-collapsible.rkt")

(provide (rename-out [wrap-vectorof vectorof]
                     [wrap-vector/c vector/c]
                     [wrap-vector*/c vector*/c])
         vector-immutable/c vector-immutableof)

(define-for-syntax (convert-args args this-one)
  (let loop ([args args]
             [new-args null])
    (cond
      [(null? args) (reverse new-args)]
      [(keyword? (syntax-e (car args)))
       (if (null? (cdr args))
           (reverse (cons (car args) new-args))
           (loop (cddr args)
                 (list* (cadr args) (car args) new-args)))]
      [else
       (loop (cdr args)
             (cons (syntax-property
                    (syntax-property
                     (car args)
                     'racket/contract:positive-position
                     this-one)
                    'racket/contract:negative-position
                    this-one)
                   new-args))])))

(define (vectorof-name c)
  (let ([immutable (base-vectorof-immutable c)]
        [elem-w (base-vectorof-elem-w c)]
        [elem-r (base-vectorof-elem-r c)])
    (apply build-compound-type-name 'vectorof
           (contract-name elem-w)
           (append
            (if (not (equal? elem-w elem-r))
                (list (contract-name elem-r))
                null)
            (if (and (flat-vectorof? c)
                     (not (eq? immutable #t)))
                (list '#:flat? #t)
                null)
            (if (not (eq? immutable 'dont-care))
                (list '#:immutable immutable)
                null)))))

;; check-vectorof only does first-order checks, so it only uses read
(define (check-vectorof elem-r-ctc immutable val blame neg-party first-order? raise-blame?)
  (and
   (do-check-vectorof val immutable blame neg-party raise-blame?)
   (if first-order?
       (let loop ([n 0])
         (cond
           [(= n (vector-length val)) #t]
           [else
            (define e (vector-ref val n))
            (cond
              [(contract-first-order-passes? elem-r-ctc e)
               (contract-first-order-try-less-hard (loop (+ n 1)))]
              [raise-blame?
               (raise-blame-error
                blame
                #:missing-party neg-party
                val
                '(expected: "~s for element ~s" given: "~e")
                (contract-name elem-r-ctc)
                n
                e)]
              [else #f])]))
       #t)))

(define (check-late-neg-vectorof c)
  (define immutable (base-vectorof-immutable c))
  (λ (val blame neg-party)
    (cond
      [(vector? val)
       (cond
         [(eq? immutable #t)
          (cond
            [(immutable? val) #f]
            [else
             (raise-blame-error blame #:missing-party neg-party
                                val '(expected "an immutable vector" given: "~e") val)])]
         [(eq? immutable #f)
          (cond
            [(immutable? val)
             (raise-blame-error blame #:missing-party neg-party
                                val '(expected "a mutable vector" given: "~e") val)]
            [else #f])]
         [else #f])]
      [else
       (raise-blame-error blame #:missing-party neg-party
                          val
                          '(expected "a vector," given: "~e")
                          val)])))

(define (vectorof-first-order ctc)
  (let ([elem-r-ctc (base-vectorof-elem-r ctc)]
        [immutable (base-vectorof-immutable ctc)])
    (λ (val)
      (check-vectorof elem-r-ctc immutable val #f #f #t #f))))

(define (vectorof-stronger this that)
  (define this-elem-w (base-vectorof-elem-w this))
  (define this-elem-r (base-vectorof-elem-r this))
  (define this-immutable (base-vectorof-immutable this))
  (cond
    [(base-vectorof? that)
     (define that-elem-w (base-vectorof-elem-w that))
     (define that-elem-r (base-vectorof-elem-r that))
     (define that-immutable (base-vectorof-immutable that))
     (cond
       [(and (equal? this-immutable #t)
             (equal? that-immutable #t))
        ; r is covariant
        (contract-struct-stronger? this-elem-r that-elem-r)]
       [else
        (and (or (equal? that-immutable 'dont-care)
                 (equal? this-immutable that-immutable))
             ; r is covariant
             (contract-struct-stronger? this-elem-r that-elem-r)
             ; w is contravariant
             (contract-struct-stronger? that-elem-w this-elem-w))])]
    [else #f]))

(define (vectorof-equivalent this that)
  (cond
    [(base-vectorof? that)
     (and (equal? (base-vectorof-immutable this)
                  (base-vectorof-immutable that))
          (contract-struct-equivalent? (base-vectorof-elem-w this)
                                       (base-vectorof-elem-w that))
          (contract-struct-equivalent? (base-vectorof-elem-r this)
                                       (base-vectorof-elem-r that)))]
    [else #f]))

(define-struct (flat-vectorof base-vectorof) ()
  #:property prop:custom-write custom-write-property-proc
  #:property prop:flat-contract
  (build-flat-contract-property
   #:trusted trust-me
   #:name vectorof-name
   #:first-order vectorof-first-order
   #:late-neg-projection (λ (ctc)
                           (define check (check-late-neg-vectorof ctc))
                           ;; flat, only read mode
                           (define elem-r (base-vectorof-elem-r ctc))
                           (define vfp-r (get/build-late-neg-projection elem-r))
                           (λ (blame)
                             (define ele-blame (blame-add-element-of-context blame))
                             (define vfp-r+blame (vfp-r ele-blame))
                             (λ (val neg-party)
                               (check val blame neg-party)
                               (for ([x (in-vector val)])
                                 (vfp-r+blame x neg-party))
                               val)))
   #:equivalent vectorof-equivalent
   #:stronger vectorof-stronger))

(define (blame-add-element-of-context blame #:swap? [swap? #f])
  (blame-add-context blame "an element of" #:swap? swap?))

(define (vectorof-collapsible-late-neg-ho-projection chap-not-imp?)
  (define chaperone-or-impersonate-vector
    (if chap-not-imp? chaperone-vector impersonate-vector))
  (λ (ctc)
    (define elem-w (base-vectorof-elem-w ctc))
    (define elem-r (base-vectorof-elem-r ctc))
    (define flat-subcontract?
      (and (flat-contract-struct? elem-w) (flat-contract-struct? elem-r)))
    (define eager (base-vectorof-eager ctc))
    (define immutable (base-vectorof-immutable ctc))
    (define vfp-w (get/build-collapsible-late-neg-projection elem-w))
    (define vfp-r (get/build-collapsible-late-neg-projection elem-r))
    (λ (blame)
      ;; use vfp-r for pos blame, use vfp-w for neg blame
      (define pos-blame (blame-add-element-of-context blame))
      (define neg-blame (blame-add-element-of-context blame #:swap? #t))
      (define-values (filled? maybe-elem-pos-proj maybe-c-c-pos maybe-elem-neg-proj maybe-c-c-neg)
        (contract-pos/neg-doubling.2 (vfp-r pos-blame) (vfp-w neg-blame)))
      (define-values (fetch-tc-pos fetch-tc-neg)
        (cond
          [filled? (values #f #f)]
          [else
           (define tc-pos (make-thread-cell #f))
           (define tc-neg (make-thread-cell #f))
           (define (fetch-from-tc tc maybe-elem-proj maybe-c-c)
             (cond
               [(thread-cell-ref tc) => values]
               [else
                (define-values (elem-proj c-c) (maybe-elem-proj))
                (define pr (cons elem-proj c-c))
                (thread-cell-set! tc pr)
                pr]))
           (values (λ () (fetch-from-tc tc-pos maybe-elem-pos-proj maybe-c-c-pos))
                   (λ () (fetch-from-tc tc-neg maybe-elem-neg-proj maybe-c-c-neg)))]))
      (define c-c-vector
        (cond
          [filled? (build-collapsible-vector maybe-c-c-pos maybe-c-c-neg ctc blame chap-not-imp?)]
          [else
           (build-doubling-collapsible-vector (λ () (cdr (fetch-tc-pos)))
                                              (λ () (cdr (fetch-tc-neg)))
                                              ctc blame chap-not-imp?)]))

      (define checked-ref
        (cond
          [filled?
           (λ (neg-party)
             (define blame+neg-party (cons pos-blame neg-party))
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 (maybe-elem-pos-proj val neg-party))))]
          [else
           (λ (neg-party)
             (define blame+neg-party (cons pos-blame neg-party))
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 (define elem-pos-proj (car (fetch-tc-pos)))
                 (elem-pos-proj val neg-party))))]))
      (define checked-set
        (cond
          [filled?
           (λ (neg-party)
             (define blame+neg-party (cons neg-blame neg-party))
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 (maybe-elem-neg-proj val neg-party))))]
          [else
           (λ (neg-party)
             (define blame+neg-party (cons neg-blame neg-party))
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 (define elem-neg-proj (car (fetch-tc-neg)))
                 (elem-neg-proj val neg-party))))]))
      (define p-r? (and (flat-contract-struct? elem-r)
                        (flat-contract-predicate elem-r)))
      (define late-neg-proj
        (λ (val neg-party)
          (check-vectorof elem-r immutable val blame neg-party #f #t)
          (define immutable-non-chaperone?
            (and (immutable? val) (not (chaperone? val))))
          ;; avoid traversing large vectors
          ;; unless `eager` is specified
          (cond
            [(and flat-subcontract?
                  immutable-non-chaperone?
                  (or (equal? eager #t)
                      (and eager (<= (vector-length val) eager))))
             (define elem-pos-proj (if filled?
                                       maybe-elem-pos-proj
                                       (car (fetch-tc-pos))))
             (for ([e (in-vector val)])
               (unless (p-r? e)
                 (elem-pos-proj e neg-party)))
             val]
            [(and (not flat-subcontract?) immutable-non-chaperone?)
             (define elem-pos-proj (if filled?
                                       maybe-elem-pos-proj
                                       (car (fetch-tc-pos))))
             (vector->immutable-vector
              (for/vector #:length (vector-length val) ([e (in-vector val)])
                (elem-pos-proj e neg-party)))]
            [else
             (define old-c-c-prop (get-impersonator-prop:collapsible val #f))
             (define safe-for-c-c?
               (if old-c-c-prop
                   (and (collapsible-property? old-c-c-prop)
                        (eq? (collapsible-property-ref old-c-c-prop) val))
                   (not (impersonator? val))))
             (define wrapper-count
               (if (collapsible-count-property? old-c-c-prop)
                   (collapsible-count-property-count old-c-c-prop)
                   0))
             (cond
               [(not safe-for-c-c?)
                (chaperone-or-impersonate-vector
                 val
                 (checked-ref neg-party)
                 (checked-set neg-party)
                 impersonator-prop:contracted ctc
                 impersonator-prop:blame (cons blame neg-party))]
               [(wrapper-count . >= . COLLAPSIBLE-LIMIT)
                (vector-enter-collapsible-mode/collapse
                 c-c-vector
                 val
                 neg-party
                 old-c-c-prop
                 chap-not-imp?)]
               [(collapsible-wrapper-property? old-c-c-prop)
                (vector-enter-collapsible-mode/continue
                 c-c-vector
                 val
                 neg-party
                 (collapsible-property-c-c old-c-c-prop)
                 (collapsible-property-neg-party old-c-c-prop)
                 (collapsible-wrapper-property-checking-wrapper old-c-c-prop)
                 chap-not-imp?)]
               [else
                (define c-c-prop
                  (collapsible-count-property
                   c-c-vector
                   neg-party
                   #f
                   (add1 wrapper-count)
                   (or old-c-c-prop val)))
                (define wrapped
                  (chaperone-or-impersonate-vector
                   val
                   (checked-ref neg-party)
                   (checked-set neg-party)
                   impersonator-prop:collapsible c-c-prop))
                (set-collapsible-property-ref! c-c-prop wrapped)
                wrapped])])))
      (values
       late-neg-proj
       c-c-vector))))

(define-values (prop:neg-blame-party prop:neg-blame-party? prop:neg-blame-party-get)
  (make-impersonator-property 'prop:neg-blame-party))

(define-struct (chaperone-vectorof base-vectorof) ()
  #:property prop:custom-write custom-write-property-proc
  #:property prop:chaperone-contract
  (build-chaperone-contract-property
   #:trusted trust-me
   #:name vectorof-name
   #:first-order vectorof-first-order
   #:equivalent vectorof-equivalent
   #:stronger vectorof-stronger
   #:collapsible-late-neg-projection (vectorof-collapsible-late-neg-ho-projection #t)))

(define-struct (impersonator-vectorof base-vectorof) ()
  #:property prop:custom-write custom-write-property-proc
  #:property prop:contract
  (build-contract-property
   #:trusted trust-me
   #:name vectorof-name
   #:first-order vectorof-first-order
   #:equivalent vectorof-equivalent
   #:stronger vectorof-stronger
   #:collapsible-late-neg-projection (vectorof-collapsible-late-neg-ho-projection #f)))

(define-syntax (wrap-vectorof stx)
  (syntax-case stx ()
    [x
     (identifier? #'x)
     (syntax-property
      (syntax/loc stx vectorof)
      'racket/contract:contract
      (vector (gensym 'ctc) (list #'x) null))]
    [(vecof arg ...)
     (let ([args (syntax->list #'(arg ...))]
           [this-one (gensym 'vectorof-ctc)])
       (with-syntax ([(new-arg ...) (convert-args args this-one)])
         (syntax-property
          (syntax/loc stx
            (vectorof new-arg ...))
          'racket/contract:contract
          (vector this-one (list #'vecof) null))))]))

(define/subexpression-pos-prop (vectorof c-w
                                         [c-r c-w]
                                         #:immutable [immutable 'dont-care]
                                         #:flat? [flat? #f]
                                         #:eager [eager #t])
  (define-values [ctc-w ctc-r]
    (if flat?
        (values (coerce-flat-contract 'vectorof c-w)
                (coerce-flat-contract 'vectorof c-r))
        (values (coerce-contract 'vectorof c-w)
                (coerce-contract 'vectorof c-r))))
  (unless (or (boolean? eager)
              (exact-nonnegative-integer? eager))
    (raise-argument-error 'vectorof
                          "(or/c #t #f exact-nonnegative-integer?)"
                          eager))
  (cond
    [(and flat? (not (equal? eager #t)))
     (raise-arguments-error 'vectorof "flat? cannot be true unless eager is true"
                            "flat?" flat?
                            "eager" eager)]
    [(or (and flat? (equal? eager #t))
         (and (equal? immutable #t)
              (equal? eager #t)
              (flat-contract? ctc-w)
              (flat-contract? ctc-r)))
     (make-flat-vectorof ctc-w ctc-r immutable eager)]
    [(and (chaperone-contract? ctc-w)
          (chaperone-contract? ctc-r))
     (make-chaperone-vectorof ctc-w ctc-r immutable eager)]
    [else
     (make-impersonator-vectorof ctc-w ctc-r immutable eager)]))

(define/subexpression-pos-prop (vector-immutableof c)
  (vectorof c #:immutable #t))

(define (vector/c-name c)
  (let ([immutable (base-vector/c-immutable c)]
        [elems-w (base-vector/c-elems-w c)]
        [elems-r (base-vector/c-elems-r c)])
    (cond
      [(equal? elems-w elems-r)
       (apply build-compound-type-name 'vector/c
              (append
               (map contract-name elems-w)
               (if (and (flat-vector/c? c)
                        (not (eq? immutable #t)))
                   (list '#:flat? #t)
                   null)
               (if (not (eq? immutable 'dont-care))
                   (list '#:immutable immutable)
                   null)))]
      [else
       (apply build-compound-type-name 'vector*/c
              (cons 'list (map contract-name elems-w))
              (cons 'list (map contract-name elems-r))
              (append
               (if (and (flat-vector/c? c)
                        (not (eq? immutable #t)))
                   (list '#:flat? #t)
                   null)
               (if (not (eq? immutable 'dont-care))
                   (list '#:immutable immutable)
                   null)))])))

(define (vector/c-first-order ctc)
  (define elem-ctcs (base-vector/c-elems-r ctc))
  (define immutable (base-vector/c-immutable ctc))
  (λ (val)
    (and (vector? val)
         (cond
          [(eq? immutable #t) (immutable? val)]
          [(eq? immutable #f) (not (immutable? val))]
          [else #t])
         (= (vector-length val) (length elem-ctcs))
         (for/and ([e (in-vector val)]
                   [c (in-list elem-ctcs)])
           (contract-first-order-passes? c e)))))

(define (vector/c-stronger this that)
  (define this-elems-w (base-vector/c-elems-w this))
  (define this-elems-r (base-vector/c-elems-r this))
  (define this-immutable (base-vector/c-immutable this))
  (cond
    [(base-vector/c? that)
     (define that-elems-w (base-vector/c-elems-w that))
     (define that-elems-r (base-vector/c-elems-r that))
     (define that-immutable (base-vector/c-immutable that))
     (cond
       [(and (equal? this-immutable #t)
             (equal? that-immutable #t))
        (and (= (length this-elems-r) (length that-elems-r))
             (for/and ([this-elem-r (in-list this-elems-r)]
                       [that-elem-r (in-list that-elems-r)])
               ;; r is covariant
               (contract-struct-stronger? this-elem-r that-elem-r)))]
       [(or (equal? that-immutable 'dont-care)
            (equal? this-immutable that-immutable))
        (and (= (length this-elems-w) (length that-elems-w)
                (length this-elems-r) (length that-elems-r))
             (for/and ([this-elem-w (in-list this-elems-w)]
                       [this-elem-r (in-list this-elems-r)]
                       [that-elem-w (in-list that-elems-w)]
                       [that-elem-r (in-list that-elems-r)])
               (and
                ;; r is covariant
                (contract-struct-stronger? this-elem-r that-elem-r)
                ;; w is contravariant
                (contract-struct-stronger? that-elem-w this-elem-w))))]
       [else #f])]
    [(base-vectorof? that)
     (define that-elem-w (base-vectorof-elem-w that))
     (define that-elem-r (base-vectorof-elem-r that))
     (define that-immutable (base-vectorof-immutable that))
     (cond
       [(and (equal? this-immutable #t)
             (equal? that-immutable #t))
        (for/and ([this-elem-r (in-list this-elems-w)])
          ;; r is covariant
          (contract-struct-stronger? this-elem-r that-elem-r))]
       [(or (equal? that-immutable 'dont-care)
            (equal? this-immutable that-immutable))
        (for/and ([this-elem-w (in-list this-elems-w)]
                  [this-elem-r (in-list this-elems-r)])
          (and
           ;; r is covariant
           (contract-struct-stronger? this-elem-r that-elem-r)
           ;; w is contravariant
           (contract-struct-stronger? that-elem-w this-elem-w)))]
       [else #f])]
    [else #f]))

(define (vector/c-equivalent this that)
  (cond
    [(base-vector/c? that)
     (and (equal? (base-vector/c-immutable this)
                  (base-vector/c-immutable that))
          (pairwise-equivalent-contracts? (base-vector/c-elems-w this)
                                          (base-vector/c-elems-w that))
          (pairwise-equivalent-contracts? (base-vector/c-elems-r this)
                                          (base-vector/c-elems-r that)))]
    [else #f]))

(define-struct (flat-vector/c base-vector/c) ()
  #:property prop:custom-write custom-write-property-proc
  #:property prop:flat-contract
  (build-flat-contract-property
   #:trusted trust-me
   #:name vector/c-name
   #:first-order vector/c-first-order
   #:stronger vector/c-stronger
   #:equivalent vector/c-equivalent
   #:late-neg-projection
   (λ (ctc)
     ;; flat, only read
     (define elems-r (base-vector/c-elems-r ctc))
     (define immutable (base-vector/c-immutable ctc))
     (λ (blame)
       (define blame+ctxt (blame-add-element-of-context blame))
       (define val+np-acceptors
         (for/list ([c (in-list elems-r)])
           ((get/build-late-neg-projection c) blame+ctxt)))
       (λ (val neg-party)
         (check-vector/c val blame immutable (length elems-r) neg-party)
         (for ([e (in-vector val)]
               [p (in-list val+np-acceptors)])
           (p e neg-party))
         val)))))

(define (vector/c-collapsible-late-neg-ho-projection chap-not-imp?)
  (define vector-wrapper (if chap-not-imp? chaperone-vector impersonate-vector))
  (λ (ctc)
    (define elems-w (base-vector/c-elems-w ctc))
    (define elems-r (base-vector/c-elems-r ctc))
    (define immutable (base-vector/c-immutable ctc))
    (define elems-length (length elems-w))
    (define selnps-w
      (for/list ([elem-w (in-list elems-w)])
        (get/build-collapsible-late-neg-projection elem-w)))
    (define selnps-r
      (for/list ([elem-r (in-list elems-r)])
        (get/build-collapsible-late-neg-projection elem-r)))
    (λ (blame)
      (define-values (filled? maybe-elem-pos-projs maybe-c-c-poss maybe-elem-neg-projs maybe-c-c-negs)
        (contract-pos/neg-doubling.2
         (let ()
           ;; pos blame, r contract
           (define elem-pos-projs (make-vector elems-length #f))
           (define elem-c-c-poss (make-vector elems-length #f))
           (for ([selnp (in-list selnps-r)]
                 [i (in-naturals)])
             (define pos-blame (blame-add-context blame (nth-element-of i)))
             (define-values (elem-pos-proj elem-c-c-pos) (selnp pos-blame))
             (vector-set! elem-pos-projs i elem-pos-proj)
             (vector-set! elem-c-c-poss i elem-c-c-pos))
           (values elem-pos-projs elem-c-c-poss))
         (let ()
           ;; neg blame, w contract
           (define elem-neg-projs (make-vector elems-length #f))
           (define elem-c-c-negs (make-vector elems-length #f))
           (for ([selnp (in-list selnps-w)]
                 [i (in-naturals)])
             (define neg-blame (blame-add-context blame (nth-element-of i)
                                                  #:swap? #t))
             (define-values (elem-neg-proj elem-c-c-neg) (selnp neg-blame))
             (vector-set! elem-neg-projs i elem-neg-proj)
             (vector-set! elem-c-c-negs i elem-c-c-neg))
           (values elem-neg-projs elem-c-c-negs))))

      (define-values (fetch-tc-pos fetch-tc-neg)
        (cond
          [filled? (values (void) (void))]
          [else
           (define tc-pos (make-thread-cell #f))
           (define tc-neg (make-thread-cell #f))
           (values (λ ()
                     (cond
                       [(thread-cell-ref tc-pos) => values]
                       [else
                        (define-values (elem-pos-projs maybe-c-c-pos) (maybe-elem-pos-projs))
                        (define pr (cons elem-pos-projs maybe-c-c-pos))
                        (thread-cell-set! tc-pos pr)
                        pr]))
                   (λ ()
                     (cond
                       [(thread-cell-ref tc-neg) => values]
                       [else
                        (define-values (elem-neg-projs maybe-c-c-neg) (maybe-elem-neg-projs))
                        (define pr (cons elem-neg-projs maybe-c-c-neg))
                        (thread-cell-set! tc-neg pr)
                        pr])))]))
      (define c-c-vector
        (cond
          [filled?
           (build-collapsible-vector maybe-c-c-poss maybe-c-c-negs ctc blame chap-not-imp?)]
          [else
           (build-doubling-collapsible-vector (λ () (cdr (fetch-tc-pos)))
                                              (λ () (cdr (fetch-tc-neg)))
                                              ctc blame chap-not-imp?)]))

      (define chaperone-get-proc
        (cond
          [filled?
           (λ (neg-party blame+neg-party)
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 ((vector-ref maybe-elem-pos-projs i) val neg-party))))]
          [else
           (λ (neg-party blame+neg-party)
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 (define elem-pos-projs (car (fetch-tc-pos)))
                 ((vector-ref elem-pos-projs i) val neg-party))))]))
      (define chaperone-set-proc
        (cond
          [filled?
           (λ (neg-party blame+neg-party)
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 ((vector-ref maybe-elem-neg-projs i) val neg-party))))]
          [else
           (λ (neg-party blame+neg-party)
             (λ (vec i val)
               (with-contract-continuation-mark
                   blame+neg-party
                 (define elem-neg-projs (car (fetch-tc-neg)))
                 ((vector-ref elem-neg-projs i) val neg-party))))]))

      (define late-neg-proj
        (λ (val neg-party)
          (define old-c-c-prop (get-impersonator-prop:collapsible val #f))
          (define safe-for-c-c
            (if old-c-c-prop
                (and (collapsible-property? old-c-c-prop)
                     (eq? (collapsible-property-ref old-c-c-prop) val))
                (not (impersonator? val))))
          (define wrapper-count
            (if (collapsible-count-property? old-c-c-prop)
                (collapsible-count-property-count old-c-c-prop)
                0))
          (check-vector/c val blame immutable elems-length neg-party)
          (define blame+neg-party (cons blame neg-party))
          (cond
            [(and (immutable? val) (not (chaperone? val)))
             (define elem-pos-projs
               (if filled?
                   maybe-elem-pos-projs
                   (car (fetch-tc-pos))))
             (apply vector-immutable
                    (for/list ([i (in-naturals)]
                               [elem-val (in-vector val)])
                      ((vector-ref elem-pos-projs i) elem-val neg-party)))]
            [(not safe-for-c-c)
             (vector-wrapper
              val
              (chaperone-get-proc neg-party blame+neg-party)
              (chaperone-set-proc neg-party blame+neg-party)
              ;; TODO: should this be a collapsible property instead??
              impersonator-prop:contracted ctc
              impersonator-prop:blame blame+neg-party)]
            [(wrapper-count . >= . COLLAPSIBLE-LIMIT)
             (vector-enter-collapsible-mode/collapse
              c-c-vector
              val
              neg-party
              old-c-c-prop
              chap-not-imp?)]
            [(collapsible-wrapper-property? old-c-c-prop)
             (vector-enter-collapsible-mode/continue
              c-c-vector
              val
              neg-party
              (collapsible-property-c-c old-c-c-prop)
              (collapsible-property-neg-party old-c-c-prop)
              (collapsible-wrapper-property-checking-wrapper old-c-c-prop)
              chap-not-imp?)]
            [else
             (define c-c-prop
               (collapsible-count-property
                c-c-vector
                neg-party
                #f
                (add1 wrapper-count)
                (or old-c-c-prop val)))
             (define wrapped
               (vector-wrapper
                val
                (chaperone-get-proc neg-party blame+neg-party)
                (chaperone-set-proc neg-party blame+neg-party)
                impersonator-prop:collapsible c-c-prop))
             (set-collapsible-property-ref! c-c-prop wrapped)
             wrapped])))
      (values
       late-neg-proj
       c-c-vector))))

(define-struct (chaperone-vector/c base-vector/c) ()
  #:property prop:custom-write custom-write-property-proc
  #:property prop:chaperone-contract
  (build-chaperone-contract-property
   #:trusted trust-me
   #:name vector/c-name
   #:first-order vector/c-first-order
   #:stronger vector/c-stronger
   #:collapsible-late-neg-projection (vector/c-collapsible-late-neg-ho-projection #t)
   #:equivalent vector/c-equivalent))

(define-struct (impersonator-vector/c base-vector/c) ()
  #:property prop:custom-write custom-write-property-proc
  #:property prop:contract
  (build-contract-property
   #:trusted trust-me
   #:name vector/c-name
   #:first-order vector/c-first-order
   #:stronger vector/c-stronger
   #:collapsible-late-neg-projection (vector/c-collapsible-late-neg-ho-projection #f)
   #:equivalent vector/c-equivalent))

(define-syntax (wrap-vector/c stx)
  (syntax-case stx ()
    [x
     (identifier? #'x)
     (syntax-property
      (syntax/loc stx vector/c)
      'racket/contract:contract
      (vector (gensym 'ctc) (list #'x) null))]
    [(vec/c arg ...)
     (let ([args (syntax->list #'(arg ...))]
           [this-one (gensym 'vector/c-ctc)])
       (with-syntax ([(new-arg ...) (convert-args args this-one)])
         (syntax-property
          (syntax/loc stx
            (vector/c new-arg ...))
          'racket/contract:contract
          (vector this-one (list #'vec/c) null))))]))

(define-syntax (wrap-vector*/c stx)
  (syntax-case stx ()
    [x
     (identifier? #'x)
     (syntax-property
      (syntax/loc stx vector*/c)
      'racket/contract:contract
      (vector (gensym 'ctc) (list #'x) null))]
    [(vec*/c arg ...)
     (let ([args (syntax->list #'(arg ...))]
           [this-one (gensym 'vector*/c-ctc)])
       (with-syntax ([(new-arg ...) (convert-args args this-one)])
         (syntax-property
          (syntax/loc stx
            (vector*/c new-arg ...))
          'racket/contract:contract
          (vector this-one (list #'vec*/c) null))))]))

(define (vector*/c #:immutable [immutable 'dont-care] #:flat? [flat? #f]
                   cs-w
                   [cs-r cs-w])
  (unless (= (length cs-w) (length cs-r))
    (error 'vector*/c
           "expected two lists of the same length, given ~v and ~v"
           cs-w
           cs-r))
  (define-values [ctcs-w ctcs-r]
    (if flat?
        (values (map (λ (c) (coerce-flat-contract 'vector/c c)) cs-w)
                (map (λ (c) (coerce-flat-contract 'vector/c c)) cs-r))
        (values (map (λ (c) (coerce-contract 'vector/c c)) cs-w)
                (map (λ (c) (coerce-contract 'vector/c c)) cs-r))))
  (cond
    [(or flat?
         (and (eq? immutable #t)
              (andmap flat-contract? ctcs-w)
              (andmap flat-contract? ctcs-r)))
     (make-flat-vector/c ctcs-w ctcs-r immutable)]
    [(and (andmap chaperone-contract? ctcs-w)
          (andmap chaperone-contract? ctcs-r))
     (make-chaperone-vector/c ctcs-w ctcs-r immutable)]
    [else
     (make-impersonator-vector/c ctcs-w ctcs-r immutable)]))

(define (vector/c #:immutable [immutable 'dont-care] #:flat? [flat? #f] . cs)
  (vector*/c #:immutable immutable #:flat? flat? cs))

(define/subexpression-pos-prop (vector-immutable/c . args)
  (apply vector/c args #:immutable #t))
