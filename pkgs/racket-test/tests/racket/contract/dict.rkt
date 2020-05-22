#lang racket/base
(require racket/dict
         "test-util.rkt")

(define (make-basic-dict-contract-namespace)
  (define n
    (make-basic-contract-namespace 'racket/dict 'racket/dict/contract))
  (parameterize ([current-namespace n])
    (eval
     `(begin
        (struct immutable-dict [hash]
          #:methods gen:dict
          [(define (dict-ref self k [d (λ () (error "key not found" k))])
             (hash-ref (immutable-dict-hash self) k d))
           (define (dict-set self k v)
             (immutable-dict (hash-set (immutable-dict-hash self) k v)))
           (define (dict-remove self k)
             (immutable-dict (hash-remove (immutable-dict-hash self) k)))
           (define (dict-count self)
             (hash-count (immutable-dict-hash self)))
           (define (dict-iterate-first self)
             (hash-iterate-first (immutable-dict-hash self)))
           (define (dict-iterate-next self p)
             (hash-iterate-next (immutable-dict-hash self) p))
           (define (dict-iterate-key self p)
             (hash-iterate-key (immutable-dict-hash self) p))
           (define (dict-iterate-value self p)
             (hash-iterate-value (immutable-dict-hash self) p))])

        (struct mutable-dict [hash]
          #:methods gen:dict
          [(define (dict-ref self k [d (λ () (error "key not found" k))])
             (hash-ref (mutable-dict-hash self) k d))
           (define (dict-set! self k v)
             (hash-set! (mutable-dict-hash self) k v))
           (define (dict-remove! self k)
             (hash-remove! (mutable-dict-hash self) k))
           (define (dict-count self)
             (hash-count (mutable-dict-hash self)))
           (define (dict-iterate-first self)
             (hash-iterate-first (mutable-dict-hash self)))
           (define (dict-iterate-next self p)
             (hash-iterate-next (mutable-dict-hash self) p))
           (define (dict-iterate-key self p)
             (hash-iterate-key (mutable-dict-hash self) p))
           (define (dict-iterate-value self p)
             (hash-iterate-value (mutable-dict-hash self) p))])

        (define (write-dict d out)
          (cond [(dict-can-functional-set? d) (write-string "(idict" out)]
                [(dict-mutable? d) (write-string "(mdict" out)])
          (for ([(k v) (in-dict d)])
            (fprintf out " ~v ~v" k v))
          (write-string ")" out)
          (void))

        (define (make-mdict [l '()]) (mutable-dict (make-hash l)))
        (define (make-idict [l '()]) (immutable-dict (make-immutable-hash l)))
        (define (idict . kvs) (immutable-dict (apply hash kvs))))))
  n)

(parameterize ([current-contract-namespace (make-basic-dict-contract-namespace)])
  (test/spec-passed
   'dict/c1
   '(contract (dict/c symbol? boolean?)
              (make-mdict)
              'pos
              'neg))

  (test/spec-passed
   'dict/c1b
   '(contract (dict/c symbol? boolean? #:flat? #t)
              (make-mdict)
              'pos
              'neg))

  (test/spec-passed
   'dict/c1c
   '(let ([h (contract (dict/c symbol? boolean?)
                       (make-mdict)
                       'pos
                       'neg)])
      (dict-set! h 'x #t)
      (dict-ref h 'x)))

  (test/neg-blame
   'dict/c1d
   '(let ([h (contract (dict/c symbol? boolean?)
                       (make-mdict)
                       'pos
                       'neg)])
      (dict-set! h 3 #t)))

  (test/neg-blame
   'dict/c1e
   '(let ([h (contract (dict/c symbol? boolean?)
                       (make-mdict)
                       'pos
                       'neg)])
      (dict-set! h 'x 3)))

  (test/neg-blame
   'dict/c1f
   '(let ([h (contract (dict/c symbol? boolean?)
                       (make-mdict)
                       'pos
                       'neg)])
      (dict-ref h 3)))

  (test/spec-passed
   'dict/c2
   '(contract (dict/c symbol? boolean?)
              (let ([h (make-mdict)])
                (dict-set! h 'x #t)
                h)
              'pos
              'neg))

  (test/pos-blame
   'dict/c3
   '(write-dict (contract (dict/c symbol? boolean?)
                          (let ([h (make-mdict)])
                            (dict-set! h 'x 'x)
                            h)
                          'pos
                          'neg)
                (open-output-string)))

  ;; no io, so failure undetected
  (test/spec-passed
   'dict/c3b
   '(contract (dict/c symbol? boolean?)
              (let ([h (make-mdict)])
                (dict-set! h 'x 'x)
                h)
              'pos
              'neg))

  (test/pos-blame
   'dict/c4
   '(write-dict (contract (dict/c symbol? boolean?)
                          (let ([h (make-mdict)])
                            (dict-set! h #t #f)
                            h)
                          'pos
                          'neg)
                (open-output-string)))

  ;; no io, so failure undetected
  (test/spec-passed
   'dict/c4b
   '(contract (dict/c symbol? boolean?)
              (let ([h (make-mdict)])
                (dict-set! h #t #f)
                h)
              'pos
              'neg))

  (test/pos-blame
   'dict/c5
   '(contract (dict/c symbol? boolean? #:immutable #t)
              (let ([h (make-mdict)])
                (dict-set! h 'x #f)
                h)
              'pos
              'neg))

  (test/spec-passed
   'dict/c6
   '(contract (dict/c symbol? boolean? #:immutable #t)
              (make-idict '((x . #f)))
              'pos
              'neg))

  (test/spec-passed
   'dict/c7
   '(contract (dict/c symbol? boolean? #:immutable #f)
              (let ([h (make-mdict)])
                (dict-set! h 'x #f)
                h)
              'pos
              'neg))

  (test/pos-blame
   'dict/c8
   '(contract (dict/c symbol? boolean? #:immutable #f)
              (make-idict '((x . #f)))
              'pos
              'neg))

  (test/spec-passed
   'dict/c9
   '(contract (dict/c symbol? boolean? #:immutable 'dont-care)
              (make-idict '((x . #f)))
              'pos
              'neg))

  (test/spec-passed
   'dict/c10
   '(contract (dict/c symbol? boolean? #:immutable 'dont-care)
              (let ([h (make-mdict)])
                (dict-set! h 'x #f)
                h)
              'pos
              'neg))

  (test/spec-passed/result
   'dict/c11
   '(dict-ref (contract (dict/c symbol? number? #:immutable #t)
                        (make-idict '((x . 1)))
                        'pos
                        'neg)
              'x)
   1)

  (test/spec-passed/result
   'dict/c12
   '(dict-ref (contract (dict/c symbol? number?)
                        (let ([ht (make-mdict)])
                          (dict-set! ht 'x 1)
                          ht)
                        'pos
                        'neg)
              'x)
   1)

  (test/pos-blame
   'dict/c13a
   ; eq-based hashes can't deal with chaperoned keys
   '(contract (dict/c (hash/c number? number?) number?)
              (make-hasheq)
              'pos
              'neg))

  (test/pos-blame
   'hash/c13b
   ; eqv-based hashes can't deal with chaperoned keys
   '(contract (dict/c (hash/c number? number?) number?)
              (make-hasheqv)
              'pos
              'neg))

  (test/neg-blame
   'dict/c13c
   ; other dicts can deal with chaperoned keys including chaperoned hashes,
   ; so this blames 'neg and not 'pos
   '(let ([h (contract (dict/c (hash/c number? number?) number?)
                       (make-mdict)
                       'pos
                       'neg)])
      (dict-set! h (make-hash '((2 . 3))) 2)
      (dict-set! h (make-hash '((3 . #t))) 3)
      (for ([(k v) (in-dict h)])
        (dict-ref k v))))

  (test/neg-blame ; unlike the hash case, this should fail and blame 'neg
   'dict/c14-on-struct-dict
   '(let ()
      (define h (idict 1 #f))
      (dict-set (contract (dict/c integer? boolean?) h 'pos 'neg)
                1 "x")))

  (test/spec-passed ; but if the dict is an immutable hash it should pass
   'dict/c14-on-immutable-hash
   '(let ()
      (define h (hash 1 #f))
      (dict-set (contract (dict/c integer? boolean?) h 'pos 'neg)
                1 "x")))

  (test/spec-passed ; and if the dict is an assoc it should pass
   'dict/c14-on-assoc
   '(let ()
      (define h '((1 . #f)))
      (dict-set (contract (dict/c integer? boolean?) h 'pos 'neg)
                1 "x")))

  (test/spec-passed/result
   'dict/c15
   '(let ()
      (define h (idict 1 #f))
      (chaperone-of? (contract (dict/c integer? boolean?) h 'pos 'neg)
                     h))
   #t)

  (test/neg-blame ; unlike the hash case, this should fail and blame 'neg
   'dict/c16-on-struct-dict
   '(let ()
      (define h (idict 1 #f))
      (define c-h (contract (dict/c any/c any/c) h 'pos 'neg))
      (dict-set (contract (dict/c integer? boolean?) c-h 'pos 'neg)
                1 "x")))

  (test/spec-passed ; but if the dict is an immutable hash it should pass
   'dict/c16-on-immutable-hash
   '(let ()
      (define h (hash 1 #f))
      (define c-h
        (chaperone-hash
         h
         (λ (h k) (values k (λ (h k v) v)))
         (λ (h k v) (values k v))
         (λ (h k) k)
         (λ (h k) k)))
      (dict-set (contract (dict/c integer? boolean?) c-h 'pos 'neg)
                1 "x")))

  (test/spec-passed/result
   'dict/c17
   '(let ()
      (define h (hash 1 #f))
      (define c-h
        (contract (dict/c any/c any/c) h 'pos 'neg))
      (chaperone-of? (contract (dict/c integer? boolean?) c-h 'pos 'neg)
                     c-h))
   #t)

  (test/pos-blame
   'dict/c18
   '(let ()
      (define N 40)
      (define c
        (for/fold ([c (-> integer? integer?)])
                  ([i (in-range N)])
          (dict/c c integer?)))
      (define h
        (for/fold ([h 0])
                  ([i (in-range N)])
          (idict h i)))
      (immutable-dict? h)

      (for/fold ([h (contract c h 'pos 'neg)])
                ([i (in-range N)])
        (dict-iterate-key h (dict-iterate-first h)))))

  (test/no-error
   '(let ([v (chaperone-hash (make-immutable-hash (list (cons 1 2)))
                             (λ (hash k) (values k (λ (h k v) v)))
                             (λ (hash k v) (values k v))
                             (λ (hash k) k)
                             (λ (hash k) k))])
      (contract (dict/c any/c any/c) v 'pos 'neg)))

  (test/no-error
   '(let ([v (chaperone-hash (make-immutable-hasheq (list (cons 1 2)))
                             (λ (hash k) (values k (λ (h k v) v)))
                             (λ (hash k v) (values k v))
                             (λ (hash k) k)
                             (λ (hash k) k))])
      (contract (dict/c any/c any/c) v 'pos 'neg)))

  (test/no-error
   '(let ([v (chaperone-hash (make-immutable-hasheqv (list (cons 1 2)))
                             (λ (hash k) (values k (λ (h k v) v)))
                             (λ (hash k v) (values k v))
                             (λ (hash k) k)
                             (λ (hash k) k))])
      (contract (dict/c any/c any/c) v 'pos 'neg))))
