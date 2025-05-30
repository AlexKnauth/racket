(define-values
 (prop:procedure-accessor procedure-accessor? procedure-accessor-ref)
 (make-struct-type-property
  'procedure
  (lambda (v_0 info-l_0)
    (if (exact-integer? v_0)
      (make-struct-field-accessor (list-ref info-l_0 3) v_0)
      #f))))
(define-values
 (new-prop:procedure new-procedure? new-procedure-ref)
 (make-struct-type-property
  'procedure
  #f
  (list (cons prop:procedure values) (cons prop:procedure-accessor values))
  #t))
(define check-struct-type
  (lambda (name_0 what_0)
    (begin
      (if what_0
        (if (struct-type? what_0)
          (void)
          (raise-argument-error name_0 "(or/c struct-type? #f)" what_0))
        (void))
      what_0)))
(define raise-argument-error$1
  (|#%name|
   raise-argument-error
   (lambda (who_0 . args_0)
     (apply raise-argument-error* who_0 'racket/primitive args_0))))
(define-values
 (prop:stream stream-via-prop? stream-ref)
 (make-struct-type-property
  'stream
  (lambda (v_0 si_0)
    (begin
      (if (if (vector? v_0)
            (if (= 3 (vector-length v_0))
              (if (procedure? (vector-ref v_0 0))
                (if (procedure-arity-includes? (vector-ref v_0 0) 1)
                  (if (procedure? (vector-ref v_0 1))
                    (if (procedure-arity-includes? (vector-ref v_0 1) 1)
                      (if (procedure? (vector-ref v_0 2))
                        (procedure-arity-includes? (vector-ref v_0 2) 1)
                        #f)
                      #f)
                    #f)
                  #f)
                #f)
              #f)
            #f)
        (void)
        (raise-argument-error$1
         'guard-for-prop:stream
         (string-append
          "(vector/c (procedure-arity-includes/c 1)\n"
          "          (procedure-arity-includes/c 1)\n"
          "          (procedure-arity-includes/c 1))")
         v_0))
      (vector->immutable-vector v_0)))
  '()
  #t))
(define-values
 (prop:gen-sequence sequence-via-prop? sequence-ref)
 (make-struct-type-property
  'sequence
  (lambda (v_0 si_0)
    (begin
      (if (if (procedure? v_0) (procedure-arity-includes? v_0 1) #f)
        (void)
        (raise-argument-error$1
         'guard-for-prop:sequence
         "(procedure-arity-includes/c 1)"
         v_0))
      v_0))))
(define-values
 (struct:range make-range range? range-ref range-set!)
 (make-struct-type
  'stream
  #f
  3
  0
  #f
  (list
   (cons
    prop:stream
    (vector
     (lambda (v_0)
       (let ((cont?_0 (|#%app| range-ref v_0 2)))
         (if cont?_0 (not (|#%app| cont?_0 (|#%app| range-ref v_0 0))) #f)))
     (lambda (v_0) (|#%app| range-ref v_0 0))
     (lambda (v_0)
       (let ((app_0
              (let ((app_0 (|#%app| range-ref v_0 1)))
                (|#%app| app_0 (|#%app| range-ref v_0 0)))))
         (let ((app_1 (|#%app| range-ref v_0 1)))
           (make-range app_0 app_1 (|#%app| range-ref v_0 2)))))))
   (cons
    prop:gen-sequence
    (lambda (v_0)
      (let ((app_0 (|#%app| range-ref v_0 1)))
        (let ((app_1 (|#%app| range-ref v_0 0)))
          (values values #f app_0 app_1 (|#%app| range-ref v_0 2) #f #f))))))))
(define-values
 (struct:list-stream
  make-list-stream
  list-stream?
  list-stream-ref
  list-stream-set!)
 (make-struct-type
  'stream
  #f
  1
  0
  #f
  (list
   (cons
    prop:stream
    (vector
     (lambda (v_0) (not (pair? (|#%app| list-stream-ref v_0 0))))
     (lambda (v_0) (car (|#%app| list-stream-ref v_0 0)))
     (lambda (v_0) (make-list-stream (cdr (|#%app| list-stream-ref v_0 0))))))
   (cons
    prop:gen-sequence
    (lambda (v_0)
      (values car cdr values (|#%app| list-stream-ref v_0 0) pair? #f #f))))))
(define-values
 (struct:do-stream make-do-stream do-stream? do-stream-ref do-stream-set!)
 (make-struct-type
  'stream
  #f
  3
  0
  #f
  (list
   (cons
    prop:stream
    (vector
     (lambda (v_0) (|#%app| (|#%app| do-stream-ref v_0 0)))
     (lambda (v_0) (|#%app| (|#%app| do-stream-ref v_0 1)))
     (lambda (v_0) (|#%app| (|#%app| do-stream-ref v_0 2))))))))
(define empty-stream (make-do-stream (lambda () #t) void void))
(define print-value-columns
  (make-parameter
   +inf.0
   (lambda (c_0)
     (if (let ((or-part_0 (eqv? c_0 +inf.0)))
           (if or-part_0 or-part_0 (if (exact-integer? c_0) (> c_0 5) #f)))
       c_0
       (raise-argument-error
        'print-value-columns
        "(or/c +inf.0 (and/c exact-integer? (>/c 5)))"
        c_0)))
   'print-value-columns))
(define finish_2045
  (make-struct-type-install-properties
   '(known-constant)
   0
   0
   #f
   null
   'prefab
   #f
   '()
   #f
   'known-constant))
(define struct:known-constant
  (make-record-type-descriptor
   'known-constant
   #f
   (structure-type-lookup-prefab-uid 'known-constant #f 0 0 #f '())
   #f
   #f
   '(0 . 0)))
(define effect_2537 (finish_2045 struct:known-constant))
(define known-constant
  (|#%name|
   known-constant
   (record-constructor
    (make-record-constructor-descriptor struct:known-constant #f #f))))
(define known-constant?_2598
  (|#%name| known-constant? (record-predicate struct:known-constant)))
(define known-constant?
  (|#%name|
   known-constant?
   (lambda (v)
     (if (known-constant?_2598 v)
       #t
       ($value
        (if (impersonator? v)
          (known-constant?_2598 (impersonator-val v))
          #f))))))
(define finish_2081
  (make-struct-type-install-properties
   '(known-consistent)
   0
   0
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   null
   'prefab
   #f
   '()
   #f
   'known-consistent))
(define struct:known-consistent
  (make-record-type-descriptor
   'known-consistent
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   (structure-type-lookup-prefab-uid
    'known-consistent
    (if (struct-type? struct:known-constant)
      struct:known-constant
      (check-struct-type 'struct struct:known-constant))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2382 (finish_2081 struct:known-consistent))
(define known-consistent
  (|#%name|
   known-consistent
   (record-constructor
    (make-record-constructor-descriptor struct:known-consistent #f #f))))
(define known-consistent?_3048
  (|#%name| known-consistent? (record-predicate struct:known-consistent)))
(define known-consistent?
  (|#%name|
   known-consistent?
   (lambda (v)
     (if (known-consistent?_3048 v)
       #t
       ($value
        (if (impersonator? v)
          (known-consistent?_3048 (impersonator-val v))
          #f))))))
(define finish_2443
  (make-struct-type-install-properties
   '(known-authentic)
   0
   0
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   null
   'prefab
   #f
   '()
   #f
   'known-authentic))
(define struct:known-authentic
  (make-record-type-descriptor
   'known-authentic
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   (structure-type-lookup-prefab-uid
    'known-authentic
    (if (struct-type? struct:known-constant)
      struct:known-constant
      (check-struct-type 'struct struct:known-constant))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2570 (finish_2443 struct:known-authentic))
(define known-authentic
  (|#%name|
   known-authentic
   (record-constructor
    (make-record-constructor-descriptor struct:known-authentic #f #f))))
(define known-authentic?_3119
  (|#%name| known-authentic? (record-predicate struct:known-authentic)))
(define known-authentic?
  (|#%name|
   known-authentic?
   (lambda (v)
     (if (known-authentic?_3119 v)
       #t
       ($value
        (if (impersonator? v)
          (known-authentic?_3119 (impersonator-val v))
          #f))))))
(define finish_2536
  (make-struct-type-install-properties
   '(known-copy)
   1
   0
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   null
   'prefab
   #f
   '(0)
   #f
   'known-copy))
(define struct:known-copy
  (make-record-type-descriptor
   'known-copy
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   (structure-type-lookup-prefab-uid
    'known-copy
    (if (struct-type? struct:known-constant)
      struct:known-constant
      (check-struct-type 'struct struct:known-constant))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2542 (finish_2536 struct:known-copy))
(define known-copy
  (|#%name|
   known-copy
   (record-constructor
    (make-record-constructor-descriptor struct:known-copy #f #f))))
(define known-copy?_2832
  (|#%name| known-copy? (record-predicate struct:known-copy)))
(define known-copy?
  (|#%name|
   known-copy?
   (lambda (v)
     (if (known-copy?_2832 v)
       #t
       ($value
        (if (impersonator? v) (known-copy?_2832 (impersonator-val v)) #f))))))
(define known-copy-id_2721
  (|#%name| known-copy-id (record-accessor struct:known-copy 0)))
(define known-copy-id
  (|#%name|
   known-copy-id
   (lambda (s)
     (if (known-copy?_2832 s)
       (known-copy-id_2721 s)
       ($value
        (impersonate-ref known-copy-id_2721 struct:known-copy 0 s 'id))))))
(define finish_2861
  (make-struct-type-install-properties
   '(known-literal)
   1
   0
   (if (struct-type? struct:known-consistent)
     struct:known-consistent
     (check-struct-type 'struct struct:known-consistent))
   null
   'prefab
   #f
   '(0)
   #f
   'known-literal))
(define struct:known-literal
  (make-record-type-descriptor
   'known-literal
   (if (struct-type? struct:known-consistent)
     struct:known-consistent
     (check-struct-type 'struct struct:known-consistent))
   (structure-type-lookup-prefab-uid
    'known-literal
    (if (struct-type? struct:known-consistent)
      struct:known-consistent
      (check-struct-type 'struct struct:known-consistent))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2788 (finish_2861 struct:known-literal))
(define known-literal
  (|#%name|
   known-literal
   (record-constructor
    (make-record-constructor-descriptor struct:known-literal #f #f))))
(define known-literal?_2305
  (|#%name| known-literal? (record-predicate struct:known-literal)))
(define known-literal?
  (|#%name|
   known-literal?
   (lambda (v)
     (if (known-literal?_2305 v)
       #t
       ($value
        (if (impersonator? v)
          (known-literal?_2305 (impersonator-val v))
          #f))))))
(define known-literal-value_2398
  (|#%name| known-literal-value (record-accessor struct:known-literal 0)))
(define known-literal-value
  (|#%name|
   known-literal-value
   (lambda (s)
     (if (known-literal?_2305 s)
       (known-literal-value_2398 s)
       ($value
        (impersonate-ref
         known-literal-value_2398
         struct:known-literal
         0
         s
         'value))))))
(define finish_1929
  (make-struct-type-install-properties
   '(known-ctype)
   1
   0
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   null
   'prefab
   #f
   '(0)
   #f
   'known-ctype))
(define struct:known-ctype
  (make-record-type-descriptor
   'known-ctype
   (if (struct-type? struct:known-constant)
     struct:known-constant
     (check-struct-type 'struct struct:known-constant))
   (structure-type-lookup-prefab-uid
    'known-ctype
    (if (struct-type? struct:known-constant)
      struct:known-constant
      (check-struct-type 'struct struct:known-constant))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2479 (finish_1929 struct:known-ctype))
(define known-ctype
  (|#%name|
   known-ctype
   (record-constructor
    (make-record-constructor-descriptor struct:known-ctype #f #f))))
(define known-ctype?_2499
  (|#%name| known-ctype? (record-predicate struct:known-ctype)))
(define known-ctype?
  (|#%name|
   known-ctype?
   (lambda (v)
     (if (known-ctype?_2499 v)
       #t
       ($value
        (if (impersonator? v) (known-ctype?_2499 (impersonator-val v)) #f))))))
(define known-ctype-rep_2319
  (|#%name| known-ctype-rep (record-accessor struct:known-ctype 0)))
(define known-ctype-rep
  (|#%name|
   known-ctype-rep
   (lambda (s)
     (if (known-ctype?_2499 s)
       (known-ctype-rep_2319 s)
       ($value
        (impersonate-ref known-ctype-rep_2319 struct:known-ctype 0 s 'rep))))))
(define finish_2897
  (make-struct-type-install-properties
   '(known-procedure)
   1
   0
   (if (struct-type? struct:known-consistent)
     struct:known-consistent
     (check-struct-type 'struct struct:known-consistent))
   null
   'prefab
   #f
   '(0)
   #f
   'known-procedure))
(define struct:known-procedure
  (make-record-type-descriptor
   'known-procedure
   (if (struct-type? struct:known-consistent)
     struct:known-consistent
     (check-struct-type 'struct struct:known-consistent))
   (structure-type-lookup-prefab-uid
    'known-procedure
    (if (struct-type? struct:known-consistent)
      struct:known-consistent
      (check-struct-type 'struct struct:known-consistent))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2677 (finish_2897 struct:known-procedure))
(define known-procedure
  (|#%name|
   known-procedure
   (record-constructor
    (make-record-constructor-descriptor struct:known-procedure #f #f))))
(define known-procedure?_2612
  (|#%name| known-procedure? (record-predicate struct:known-procedure)))
(define known-procedure?
  (|#%name|
   known-procedure?
   (lambda (v)
     (if (known-procedure?_2612 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure?_2612 (impersonator-val v))
          #f))))))
(define known-procedure-arity-mask_2503
  (|#%name|
   known-procedure-arity-mask
   (record-accessor struct:known-procedure 0)))
(define known-procedure-arity-mask
  (|#%name|
   known-procedure-arity-mask
   (lambda (s)
     (if (known-procedure?_2612 s)
       (known-procedure-arity-mask_2503 s)
       ($value
        (impersonate-ref
         known-procedure-arity-mask_2503
         struct:known-procedure
         0
         s
         'arity-mask))))))
(define finish_2542
  (make-struct-type-install-properties
   '(known-procedure/single-valued)
   0
   0
   (if (struct-type? struct:known-procedure)
     struct:known-procedure
     (check-struct-type 'struct struct:known-procedure))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/single-valued))
(define struct:known-procedure/single-valued
  (make-record-type-descriptor
   'known-procedure/single-valued
   (if (struct-type? struct:known-procedure)
     struct:known-procedure
     (check-struct-type 'struct struct:known-procedure))
   (structure-type-lookup-prefab-uid
    'known-procedure/single-valued
    (if (struct-type? struct:known-procedure)
      struct:known-procedure
      (check-struct-type 'struct struct:known-procedure))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2532 (finish_2542 struct:known-procedure/single-valued))
(define known-procedure/single-valued
  (|#%name|
   known-procedure/single-valued
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/single-valued
     #f
     #f))))
(define known-procedure/single-valued?_3105
  (|#%name|
   known-procedure/single-valued?
   (record-predicate struct:known-procedure/single-valued)))
(define known-procedure/single-valued?
  (|#%name|
   known-procedure/single-valued?
   (lambda (v)
     (if (known-procedure/single-valued?_3105 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/single-valued?_3105 (impersonator-val v))
          #f))))))
(define finish_2099
  (make-struct-type-install-properties
   '(known-procedure/no-prompt)
   0
   0
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/no-prompt))
(define struct:known-procedure/no-prompt
  (make-record-type-descriptor
   'known-procedure/no-prompt
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   (structure-type-lookup-prefab-uid
    'known-procedure/no-prompt
    (if (struct-type? struct:known-procedure/single-valued)
      struct:known-procedure/single-valued
      (check-struct-type 'struct struct:known-procedure/single-valued))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_1771 (finish_2099 struct:known-procedure/no-prompt))
(define known-procedure/no-prompt
  (|#%name|
   known-procedure/no-prompt
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/no-prompt
     #f
     #f))))
(define known-procedure/no-prompt?_2036
  (|#%name|
   known-procedure/no-prompt?
   (record-predicate struct:known-procedure/no-prompt)))
(define known-procedure/no-prompt?
  (|#%name|
   known-procedure/no-prompt?
   (lambda (v)
     (if (known-procedure/no-prompt?_2036 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/no-prompt?_2036 (impersonator-val v))
          #f))))))
(define finish_2719
  (make-struct-type-install-properties
   '(known-procedure/no-prompt/multi)
   0
   0
   (if (struct-type? struct:known-procedure)
     struct:known-procedure
     (check-struct-type 'struct struct:known-procedure))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/no-prompt/multi))
(define struct:known-procedure/no-prompt/multi
  (make-record-type-descriptor
   'known-procedure/no-prompt/multi
   (if (struct-type? struct:known-procedure)
     struct:known-procedure
     (check-struct-type 'struct struct:known-procedure))
   (structure-type-lookup-prefab-uid
    'known-procedure/no-prompt/multi
    (if (struct-type? struct:known-procedure)
      struct:known-procedure
      (check-struct-type 'struct struct:known-procedure))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2793 (finish_2719 struct:known-procedure/no-prompt/multi))
(define known-procedure/no-prompt/multi
  (|#%name|
   known-procedure/no-prompt/multi
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/no-prompt/multi
     #f
     #f))))
(define known-procedure/no-prompt/multi?_2394
  (|#%name|
   known-procedure/no-prompt/multi?
   (record-predicate struct:known-procedure/no-prompt/multi)))
(define known-procedure/no-prompt/multi?
  (|#%name|
   known-procedure/no-prompt/multi?
   (lambda (v)
     (if (known-procedure/no-prompt/multi?_2394 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/no-prompt/multi?_2394 (impersonator-val v))
          #f))))))
(define finish_2574
  (make-struct-type-install-properties
   '(known-procedure/no-return)
   0
   0
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/no-return))
(define struct:known-procedure/no-return
  (make-record-type-descriptor
   'known-procedure/no-return
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   (structure-type-lookup-prefab-uid
    'known-procedure/no-return
    (if (struct-type? struct:known-procedure/single-valued)
      struct:known-procedure/single-valued
      (check-struct-type 'struct struct:known-procedure/single-valued))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2517 (finish_2574 struct:known-procedure/no-return))
(define known-procedure/no-return
  (|#%name|
   known-procedure/no-return
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/no-return
     #f
     #f))))
(define known-procedure/no-return?_1763
  (|#%name|
   known-procedure/no-return?
   (record-predicate struct:known-procedure/no-return)))
(define known-procedure/no-return?
  (|#%name|
   known-procedure/no-return?
   (lambda (v)
     (if (known-procedure/no-return?_1763 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/no-return?_1763 (impersonator-val v))
          #f))))))
(define finish_2190
  (make-struct-type-install-properties
   '(known-procedure/parameter)
   0
   0
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/parameter))
(define struct:known-procedure/parameter
  (make-record-type-descriptor
   'known-procedure/parameter
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   (structure-type-lookup-prefab-uid
    'known-procedure/parameter
    (if (struct-type? struct:known-procedure/single-valued)
      struct:known-procedure/single-valued
      (check-struct-type 'struct struct:known-procedure/single-valued))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2451 (finish_2190 struct:known-procedure/parameter))
(define known-procedure/parameter
  (|#%name|
   known-procedure/parameter
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/parameter
     #f
     #f))))
(define known-procedure/parameter?_2642
  (|#%name|
   known-procedure/parameter?
   (record-predicate struct:known-procedure/parameter)))
(define known-procedure/parameter?
  (|#%name|
   known-procedure/parameter?
   (lambda (v)
     (if (known-procedure/parameter?_2642 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/parameter?_2642 (impersonator-val v))
          #f))))))
(define finish_2550
  (make-struct-type-install-properties
   '(known-procedure/can-inline)
   1
   0
   (if (struct-type? struct:known-procedure)
     struct:known-procedure
     (check-struct-type 'struct struct:known-procedure))
   null
   'prefab
   #f
   '(0)
   #f
   'known-procedure/can-inline))
(define struct:known-procedure/can-inline
  (make-record-type-descriptor
   'known-procedure/can-inline
   (if (struct-type? struct:known-procedure)
     struct:known-procedure
     (check-struct-type 'struct struct:known-procedure))
   (structure-type-lookup-prefab-uid
    'known-procedure/can-inline
    (if (struct-type? struct:known-procedure)
      struct:known-procedure
      (check-struct-type 'struct struct:known-procedure))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2308 (finish_2550 struct:known-procedure/can-inline))
(define known-procedure/can-inline
  (|#%name|
   known-procedure/can-inline
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/can-inline
     #f
     #f))))
(define known-procedure/can-inline?_2843
  (|#%name|
   known-procedure/can-inline?
   (record-predicate struct:known-procedure/can-inline)))
(define known-procedure/can-inline?
  (|#%name|
   known-procedure/can-inline?
   (lambda (v)
     (if (known-procedure/can-inline?_2843 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/can-inline?_2843 (impersonator-val v))
          #f))))))
(define known-procedure/can-inline-expr_2497
  (|#%name|
   known-procedure/can-inline-expr
   (record-accessor struct:known-procedure/can-inline 0)))
(define known-procedure/can-inline-expr
  (|#%name|
   known-procedure/can-inline-expr
   (lambda (s)
     (if (known-procedure/can-inline?_2843 s)
       (known-procedure/can-inline-expr_2497 s)
       ($value
        (impersonate-ref
         known-procedure/can-inline-expr_2497
         struct:known-procedure/can-inline
         0
         s
         'expr))))))
(define finish_1976
  (make-struct-type-install-properties
   '(known-procedure/can-inline/need-imports)
   1
   0
   (if (struct-type? struct:known-procedure/can-inline)
     struct:known-procedure/can-inline
     (check-struct-type 'struct struct:known-procedure/can-inline))
   null
   'prefab
   #f
   '(0)
   #f
   'known-procedure/can-inline/need-imports))
(define struct:known-procedure/can-inline/need-imports
  (make-record-type-descriptor
   'known-procedure/can-inline/need-imports
   (if (struct-type? struct:known-procedure/can-inline)
     struct:known-procedure/can-inline
     (check-struct-type 'struct struct:known-procedure/can-inline))
   (structure-type-lookup-prefab-uid
    'known-procedure/can-inline/need-imports
    (if (struct-type? struct:known-procedure/can-inline)
      struct:known-procedure/can-inline
      (check-struct-type 'struct struct:known-procedure/can-inline))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2618
  (finish_1976 struct:known-procedure/can-inline/need-imports))
(define known-procedure/can-inline/need-imports
  (|#%name|
   known-procedure/can-inline/need-imports
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/can-inline/need-imports
     #f
     #f))))
(define known-procedure/can-inline/need-imports?_2059
  (|#%name|
   known-procedure/can-inline/need-imports?
   (record-predicate struct:known-procedure/can-inline/need-imports)))
(define known-procedure/can-inline/need-imports?
  (|#%name|
   known-procedure/can-inline/need-imports?
   (lambda (v)
     (if (known-procedure/can-inline/need-imports?_2059 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/can-inline/need-imports?_2059 (impersonator-val v))
          #f))))))
(define known-procedure/can-inline/need-imports-needed_2435
  (|#%name|
   known-procedure/can-inline/need-imports-needed
   (record-accessor struct:known-procedure/can-inline/need-imports 0)))
(define known-procedure/can-inline/need-imports-needed
  (|#%name|
   known-procedure/can-inline/need-imports-needed
   (lambda (s)
     (if (known-procedure/can-inline/need-imports?_2059 s)
       (known-procedure/can-inline/need-imports-needed_2435 s)
       ($value
        (impersonate-ref
         known-procedure/can-inline/need-imports-needed_2435
         struct:known-procedure/can-inline/need-imports
         0
         s
         'needed))))))
(define finish_1734
  (make-struct-type-install-properties
   '(known-procedure/folding)
   0
   0
   (if (struct-type? struct:known-procedure/no-prompt)
     struct:known-procedure/no-prompt
     (check-struct-type 'struct struct:known-procedure/no-prompt))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/folding))
(define struct:known-procedure/folding
  (make-record-type-descriptor
   'known-procedure/folding
   (if (struct-type? struct:known-procedure/no-prompt)
     struct:known-procedure/no-prompt
     (check-struct-type 'struct struct:known-procedure/no-prompt))
   (structure-type-lookup-prefab-uid
    'known-procedure/folding
    (if (struct-type? struct:known-procedure/no-prompt)
      struct:known-procedure/no-prompt
      (check-struct-type 'struct struct:known-procedure/no-prompt))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2478 (finish_1734 struct:known-procedure/folding))
(define known-procedure/folding
  (|#%name|
   known-procedure/folding
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/folding
     #f
     #f))))
(define known-procedure/folding?_2882
  (|#%name|
   known-procedure/folding?
   (record-predicate struct:known-procedure/folding)))
(define known-procedure/folding?
  (|#%name|
   known-procedure/folding?
   (lambda (v)
     (if (known-procedure/folding?_2882 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/folding?_2882 (impersonator-val v))
          #f))))))
(define finish_2008
  (make-struct-type-install-properties
   '(known-procedure/folding/limited)
   1
   0
   (if (struct-type? struct:known-procedure/folding)
     struct:known-procedure/folding
     (check-struct-type 'struct struct:known-procedure/folding))
   null
   'prefab
   #f
   '(0)
   #f
   'known-procedure/folding/limited))
(define struct:known-procedure/folding/limited
  (make-record-type-descriptor
   'known-procedure/folding/limited
   (if (struct-type? struct:known-procedure/folding)
     struct:known-procedure/folding
     (check-struct-type 'struct struct:known-procedure/folding))
   (structure-type-lookup-prefab-uid
    'known-procedure/folding/limited
    (if (struct-type? struct:known-procedure/folding)
      struct:known-procedure/folding
      (check-struct-type 'struct struct:known-procedure/folding))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2518 (finish_2008 struct:known-procedure/folding/limited))
(define known-procedure/folding/limited
  (|#%name|
   known-procedure/folding/limited
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/folding/limited
     #f
     #f))))
(define known-procedure/folding/limited?_2382
  (|#%name|
   known-procedure/folding/limited?
   (record-predicate struct:known-procedure/folding/limited)))
(define known-procedure/folding/limited?
  (|#%name|
   known-procedure/folding/limited?
   (lambda (v)
     (if (known-procedure/folding/limited?_2382 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/folding/limited?_2382 (impersonator-val v))
          #f))))))
(define known-procedure/folding/limited-kind_2789
  (|#%name|
   known-procedure/folding/limited-kind
   (record-accessor struct:known-procedure/folding/limited 0)))
(define known-procedure/folding/limited-kind
  (|#%name|
   known-procedure/folding/limited-kind
   (lambda (s)
     (if (known-procedure/folding/limited?_2382 s)
       (known-procedure/folding/limited-kind_2789 s)
       ($value
        (impersonate-ref
         known-procedure/folding/limited-kind_2789
         struct:known-procedure/folding/limited
         0
         s
         'kind))))))
(define finish_2826
  (make-struct-type-install-properties
   '(known-procedure/succeeds)
   0
   0
   (if (struct-type? struct:known-procedure/no-prompt)
     struct:known-procedure/no-prompt
     (check-struct-type 'struct struct:known-procedure/no-prompt))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/succeeds))
(define struct:known-procedure/succeeds
  (make-record-type-descriptor
   'known-procedure/succeeds
   (if (struct-type? struct:known-procedure/no-prompt)
     struct:known-procedure/no-prompt
     (check-struct-type 'struct struct:known-procedure/no-prompt))
   (structure-type-lookup-prefab-uid
    'known-procedure/succeeds
    (if (struct-type? struct:known-procedure/no-prompt)
      struct:known-procedure/no-prompt
      (check-struct-type 'struct struct:known-procedure/no-prompt))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2467 (finish_2826 struct:known-procedure/succeeds))
(define known-procedure/succeeds
  (|#%name|
   known-procedure/succeeds
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/succeeds
     #f
     #f))))
(define known-procedure/succeeds?_3041
  (|#%name|
   known-procedure/succeeds?
   (record-predicate struct:known-procedure/succeeds)))
(define known-procedure/succeeds?
  (|#%name|
   known-procedure/succeeds?
   (lambda (v)
     (if (known-procedure/succeeds?_3041 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/succeeds?_3041 (impersonator-val v))
          #f))))))
(define finish_2544
  (make-struct-type-install-properties
   '(known-procedure/then-pure)
   0
   0
   (if (struct-type? struct:known-procedure/succeeds)
     struct:known-procedure/succeeds
     (check-struct-type 'struct struct:known-procedure/succeeds))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/then-pure))
(define struct:known-procedure/then-pure
  (make-record-type-descriptor
   'known-procedure/then-pure
   (if (struct-type? struct:known-procedure/succeeds)
     struct:known-procedure/succeeds
     (check-struct-type 'struct struct:known-procedure/succeeds))
   (structure-type-lookup-prefab-uid
    'known-procedure/then-pure
    (if (struct-type? struct:known-procedure/succeeds)
      struct:known-procedure/succeeds
      (check-struct-type 'struct struct:known-procedure/succeeds))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_1957 (finish_2544 struct:known-procedure/then-pure))
(define known-procedure/then-pure
  (|#%name|
   known-procedure/then-pure
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/then-pure
     #f
     #f))))
(define known-procedure/then-pure?_2475
  (|#%name|
   known-procedure/then-pure?
   (record-predicate struct:known-procedure/then-pure)))
(define known-procedure/then-pure?
  (|#%name|
   known-procedure/then-pure?
   (lambda (v)
     (if (known-procedure/then-pure?_2475 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/then-pure?_2475 (impersonator-val v))
          #f))))))
(define finish_2400
  (make-struct-type-install-properties
   '(known-procedure/then-pure/folding-unsafe)
   1
   0
   (if (struct-type? struct:known-procedure/then-pure)
     struct:known-procedure/then-pure
     (check-struct-type 'struct struct:known-procedure/then-pure))
   null
   'prefab
   #f
   '(0)
   #f
   'known-procedure/then-pure/folding-unsafe))
(define struct:known-procedure/then-pure/folding-unsafe
  (make-record-type-descriptor
   'known-procedure/then-pure/folding-unsafe
   (if (struct-type? struct:known-procedure/then-pure)
     struct:known-procedure/then-pure
     (check-struct-type 'struct struct:known-procedure/then-pure))
   (structure-type-lookup-prefab-uid
    'known-procedure/then-pure/folding-unsafe
    (if (struct-type? struct:known-procedure/then-pure)
      struct:known-procedure/then-pure
      (check-struct-type 'struct struct:known-procedure/then-pure))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2700
  (finish_2400 struct:known-procedure/then-pure/folding-unsafe))
(define known-procedure/then-pure/folding-unsafe
  (|#%name|
   known-procedure/then-pure/folding-unsafe
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/then-pure/folding-unsafe
     #f
     #f))))
(define known-procedure/then-pure/folding-unsafe?_3036
  (|#%name|
   known-procedure/then-pure/folding-unsafe?
   (record-predicate struct:known-procedure/then-pure/folding-unsafe)))
(define known-procedure/then-pure/folding-unsafe?
  (|#%name|
   known-procedure/then-pure/folding-unsafe?
   (lambda (v)
     (if (known-procedure/then-pure/folding-unsafe?_3036 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/then-pure/folding-unsafe?_3036 (impersonator-val v))
          #f))))))
(define known-procedure/then-pure/folding-unsafe-safe_2633
  (|#%name|
   known-procedure/then-pure/folding-unsafe-safe
   (record-accessor struct:known-procedure/then-pure/folding-unsafe 0)))
(define known-procedure/then-pure/folding-unsafe-safe
  (|#%name|
   known-procedure/then-pure/folding-unsafe-safe
   (lambda (s)
     (if (known-procedure/then-pure/folding-unsafe?_3036 s)
       (known-procedure/then-pure/folding-unsafe-safe_2633 s)
       ($value
        (impersonate-ref
         known-procedure/then-pure/folding-unsafe-safe_2633
         struct:known-procedure/then-pure/folding-unsafe
         0
         s
         'safe))))))
(define finish_2051
  (make-struct-type-install-properties
   '(known-procedure/allocates)
   0
   0
   (if (struct-type? struct:known-procedure/succeeds)
     struct:known-procedure/succeeds
     (check-struct-type 'struct struct:known-procedure/succeeds))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/allocates))
(define struct:known-procedure/allocates
  (make-record-type-descriptor
   'known-procedure/allocates
   (if (struct-type? struct:known-procedure/succeeds)
     struct:known-procedure/succeeds
     (check-struct-type 'struct struct:known-procedure/succeeds))
   (structure-type-lookup-prefab-uid
    'known-procedure/allocates
    (if (struct-type? struct:known-procedure/succeeds)
      struct:known-procedure/succeeds
      (check-struct-type 'struct struct:known-procedure/succeeds))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2336 (finish_2051 struct:known-procedure/allocates))
(define known-procedure/allocates
  (|#%name|
   known-procedure/allocates
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/allocates
     #f
     #f))))
(define known-procedure/allocates?_2244
  (|#%name|
   known-procedure/allocates?
   (record-predicate struct:known-procedure/allocates)))
(define known-procedure/allocates?
  (|#%name|
   known-procedure/allocates?
   (lambda (v)
     (if (known-procedure/allocates?_2244 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/allocates?_2244 (impersonator-val v))
          #f))))))
(define finish_2724
  (make-struct-type-install-properties
   '(known-procedure/pure)
   0
   0
   (if (struct-type? struct:known-procedure/allocates)
     struct:known-procedure/allocates
     (check-struct-type 'struct struct:known-procedure/allocates))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/pure))
(define struct:known-procedure/pure
  (make-record-type-descriptor
   'known-procedure/pure
   (if (struct-type? struct:known-procedure/allocates)
     struct:known-procedure/allocates
     (check-struct-type 'struct struct:known-procedure/allocates))
   (structure-type-lookup-prefab-uid
    'known-procedure/pure
    (if (struct-type? struct:known-procedure/allocates)
      struct:known-procedure/allocates
      (check-struct-type 'struct struct:known-procedure/allocates))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_3058 (finish_2724 struct:known-procedure/pure))
(define known-procedure/pure
  (|#%name|
   known-procedure/pure
   (record-constructor
    (make-record-constructor-descriptor struct:known-procedure/pure #f #f))))
(define known-procedure/pure?_2240
  (|#%name|
   known-procedure/pure?
   (record-predicate struct:known-procedure/pure)))
(define known-procedure/pure?
  (|#%name|
   known-procedure/pure?
   (lambda (v)
     (if (known-procedure/pure?_2240 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/pure?_2240 (impersonator-val v))
          #f))))))
(define finish_2466
  (make-struct-type-install-properties
   '(known-procedure/pure/folding)
   0
   0
   (if (struct-type? struct:known-procedure/pure)
     struct:known-procedure/pure
     (check-struct-type 'struct struct:known-procedure/pure))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/pure/folding))
(define struct:known-procedure/pure/folding
  (make-record-type-descriptor
   'known-procedure/pure/folding
   (if (struct-type? struct:known-procedure/pure)
     struct:known-procedure/pure
     (check-struct-type 'struct struct:known-procedure/pure))
   (structure-type-lookup-prefab-uid
    'known-procedure/pure/folding
    (if (struct-type? struct:known-procedure/pure)
      struct:known-procedure/pure
      (check-struct-type 'struct struct:known-procedure/pure))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2264 (finish_2466 struct:known-procedure/pure/folding))
(define known-procedure/pure/folding
  (|#%name|
   known-procedure/pure/folding
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/pure/folding
     #f
     #f))))
(define known-procedure/pure/folding?_2719
  (|#%name|
   known-procedure/pure/folding?
   (record-predicate struct:known-procedure/pure/folding)))
(define known-procedure/pure/folding?
  (|#%name|
   known-procedure/pure/folding?
   (lambda (v)
     (if (known-procedure/pure/folding?_2719 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/pure/folding?_2719 (impersonator-val v))
          #f))))))
(define finish_3128
  (make-struct-type-install-properties
   '(known-procedure/has-unsafe)
   1
   0
   (if (struct-type? struct:known-procedure/no-prompt)
     struct:known-procedure/no-prompt
     (check-struct-type 'struct struct:known-procedure/no-prompt))
   null
   'prefab
   #f
   '(0)
   #f
   'known-procedure/has-unsafe))
(define struct:known-procedure/has-unsafe
  (make-record-type-descriptor
   'known-procedure/has-unsafe
   (if (struct-type? struct:known-procedure/no-prompt)
     struct:known-procedure/no-prompt
     (check-struct-type 'struct struct:known-procedure/no-prompt))
   (structure-type-lookup-prefab-uid
    'known-procedure/has-unsafe
    (if (struct-type? struct:known-procedure/no-prompt)
      struct:known-procedure/no-prompt
      (check-struct-type 'struct struct:known-procedure/no-prompt))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_1752 (finish_3128 struct:known-procedure/has-unsafe))
(define known-procedure/has-unsafe
  (|#%name|
   known-procedure/has-unsafe
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/has-unsafe
     #f
     #f))))
(define known-procedure/has-unsafe?_2703
  (|#%name|
   known-procedure/has-unsafe?
   (record-predicate struct:known-procedure/has-unsafe)))
(define known-procedure/has-unsafe?
  (|#%name|
   known-procedure/has-unsafe?
   (lambda (v)
     (if (known-procedure/has-unsafe?_2703 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/has-unsafe?_2703 (impersonator-val v))
          #f))))))
(define known-procedure/has-unsafe-alternate_2847
  (|#%name|
   known-procedure/has-unsafe-alternate
   (record-accessor struct:known-procedure/has-unsafe 0)))
(define known-procedure/has-unsafe-alternate
  (|#%name|
   known-procedure/has-unsafe-alternate
   (lambda (s)
     (if (known-procedure/has-unsafe?_2703 s)
       (known-procedure/has-unsafe-alternate_2847 s)
       ($value
        (impersonate-ref
         known-procedure/has-unsafe-alternate_2847
         struct:known-procedure/has-unsafe
         0
         s
         'alternate))))))
(define finish_2439
  (make-struct-type-install-properties
   '(known-procedure/has-unsafe/folding)
   0
   0
   (if (struct-type? struct:known-procedure/has-unsafe)
     struct:known-procedure/has-unsafe
     (check-struct-type 'struct struct:known-procedure/has-unsafe))
   null
   'prefab
   #f
   '()
   #f
   'known-procedure/has-unsafe/folding))
(define struct:known-procedure/has-unsafe/folding
  (make-record-type-descriptor
   'known-procedure/has-unsafe/folding
   (if (struct-type? struct:known-procedure/has-unsafe)
     struct:known-procedure/has-unsafe
     (check-struct-type 'struct struct:known-procedure/has-unsafe))
   (structure-type-lookup-prefab-uid
    'known-procedure/has-unsafe/folding
    (if (struct-type? struct:known-procedure/has-unsafe)
      struct:known-procedure/has-unsafe
      (check-struct-type 'struct struct:known-procedure/has-unsafe))
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2489 (finish_2439 struct:known-procedure/has-unsafe/folding))
(define known-procedure/has-unsafe/folding
  (|#%name|
   known-procedure/has-unsafe/folding
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/has-unsafe/folding
     #f
     #f))))
(define known-procedure/has-unsafe/folding?_2169
  (|#%name|
   known-procedure/has-unsafe/folding?
   (record-predicate struct:known-procedure/has-unsafe/folding)))
(define known-procedure/has-unsafe/folding?
  (|#%name|
   known-procedure/has-unsafe/folding?
   (lambda (v)
     (if (known-procedure/has-unsafe/folding?_2169 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/has-unsafe/folding?_2169 (impersonator-val v))
          #f))))))
(define finish_2602
  (make-struct-type-install-properties
   '(known-procedure/has-unsafe/folding/limited)
   1
   0
   (if (struct-type? struct:known-procedure/has-unsafe/folding)
     struct:known-procedure/has-unsafe/folding
     (check-struct-type 'struct struct:known-procedure/has-unsafe/folding))
   null
   'prefab
   #f
   '(0)
   #f
   'known-procedure/has-unsafe/folding/limited))
(define struct:known-procedure/has-unsafe/folding/limited
  (make-record-type-descriptor
   'known-procedure/has-unsafe/folding/limited
   (if (struct-type? struct:known-procedure/has-unsafe/folding)
     struct:known-procedure/has-unsafe/folding
     (check-struct-type 'struct struct:known-procedure/has-unsafe/folding))
   (structure-type-lookup-prefab-uid
    'known-procedure/has-unsafe/folding/limited
    (if (struct-type? struct:known-procedure/has-unsafe/folding)
      struct:known-procedure/has-unsafe/folding
      (check-struct-type 'struct struct:known-procedure/has-unsafe/folding))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2512
  (finish_2602 struct:known-procedure/has-unsafe/folding/limited))
(define known-procedure/has-unsafe/folding/limited
  (|#%name|
   known-procedure/has-unsafe/folding/limited
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-procedure/has-unsafe/folding/limited
     #f
     #f))))
(define known-procedure/has-unsafe/folding/limited?_2926
  (|#%name|
   known-procedure/has-unsafe/folding/limited?
   (record-predicate struct:known-procedure/has-unsafe/folding/limited)))
(define known-procedure/has-unsafe/folding/limited?
  (|#%name|
   known-procedure/has-unsafe/folding/limited?
   (lambda (v)
     (if (known-procedure/has-unsafe/folding/limited?_2926 v)
       #t
       ($value
        (if (impersonator? v)
          (known-procedure/has-unsafe/folding/limited?_2926
           (impersonator-val v))
          #f))))))
(define known-procedure/has-unsafe/folding/limited-kind_1942
  (|#%name|
   known-procedure/has-unsafe/folding/limited-kind
   (record-accessor struct:known-procedure/has-unsafe/folding/limited 0)))
(define known-procedure/has-unsafe/folding/limited-kind
  (|#%name|
   known-procedure/has-unsafe/folding/limited-kind
   (lambda (s)
     (if (known-procedure/has-unsafe/folding/limited?_2926 s)
       (known-procedure/has-unsafe/folding/limited-kind_1942 s)
       ($value
        (impersonate-ref
         known-procedure/has-unsafe/folding/limited-kind_1942
         struct:known-procedure/has-unsafe/folding/limited
         0
         s
         'kind))))))
(define finish_2844
  (make-struct-type-install-properties
   '(known-struct-type)
   4
   0
   (if (struct-type? struct:known-consistent)
     struct:known-consistent
     (check-struct-type 'struct struct:known-consistent))
   null
   'prefab
   #f
   '(0 1 2 3)
   #f
   'known-struct-type))
(define struct:known-struct-type
  (make-record-type-descriptor
   'known-struct-type
   (if (struct-type? struct:known-consistent)
     struct:known-consistent
     (check-struct-type 'struct struct:known-consistent))
   (structure-type-lookup-prefab-uid
    'known-struct-type
    (if (struct-type? struct:known-consistent)
      struct:known-consistent
      (check-struct-type 'struct struct:known-consistent))
    4
    0
    #f
    '(0 1 2 3))
   #f
   #f
   '(4 . 15)))
(define effect_2667 (finish_2844 struct:known-struct-type))
(define known-struct-type
  (|#%name|
   known-struct-type
   (record-constructor
    (make-record-constructor-descriptor struct:known-struct-type #f #f))))
(define known-struct-type?_2572
  (|#%name| known-struct-type? (record-predicate struct:known-struct-type)))
(define known-struct-type?
  (|#%name|
   known-struct-type?
   (lambda (v)
     (if (known-struct-type?_2572 v)
       #t
       ($value
        (if (impersonator? v)
          (known-struct-type?_2572 (impersonator-val v))
          #f))))))
(define known-struct-type-type_1931
  (|#%name|
   known-struct-type-type
   (record-accessor struct:known-struct-type 0)))
(define known-struct-type-type
  (|#%name|
   known-struct-type-type
   (lambda (s)
     (if (known-struct-type?_2572 s)
       (known-struct-type-type_1931 s)
       ($value
        (impersonate-ref
         known-struct-type-type_1931
         struct:known-struct-type
         0
         s
         'type))))))
(define known-struct-type-field-count_2903
  (|#%name|
   known-struct-type-field-count
   (record-accessor struct:known-struct-type 1)))
(define known-struct-type-field-count
  (|#%name|
   known-struct-type-field-count
   (lambda (s)
     (if (known-struct-type?_2572 s)
       (known-struct-type-field-count_2903 s)
       ($value
        (impersonate-ref
         known-struct-type-field-count_2903
         struct:known-struct-type
         1
         s
         'field-count))))))
(define known-struct-type-pure-constructor?_2541
  (|#%name|
   known-struct-type-pure-constructor?
   (record-accessor struct:known-struct-type 2)))
(define known-struct-type-pure-constructor?
  (|#%name|
   known-struct-type-pure-constructor?
   (lambda (s)
     (if (known-struct-type?_2572 s)
       (known-struct-type-pure-constructor?_2541 s)
       ($value
        (impersonate-ref
         known-struct-type-pure-constructor?_2541
         struct:known-struct-type
         2
         s
         'pure-constructor?))))))
(define known-struct-type-sealed?_2229
  (|#%name|
   known-struct-type-sealed?
   (record-accessor struct:known-struct-type 3)))
(define known-struct-type-sealed?
  (|#%name|
   known-struct-type-sealed?
   (lambda (s)
     (if (known-struct-type?_2572 s)
       (known-struct-type-sealed?_2229 s)
       ($value
        (impersonate-ref
         known-struct-type-sealed?_2229
         struct:known-struct-type
         3
         s
         'sealed?))))))
(define finish_2453
  (make-struct-type-install-properties
   '(known-constructor)
   1
   0
   (if (struct-type? struct:known-procedure/allocates)
     struct:known-procedure/allocates
     (check-struct-type 'struct struct:known-procedure/allocates))
   null
   'prefab
   #f
   '(0)
   #f
   'known-constructor))
(define struct:known-constructor
  (make-record-type-descriptor
   'known-constructor
   (if (struct-type? struct:known-procedure/allocates)
     struct:known-procedure/allocates
     (check-struct-type 'struct struct:known-procedure/allocates))
   (structure-type-lookup-prefab-uid
    'known-constructor
    (if (struct-type? struct:known-procedure/allocates)
      struct:known-procedure/allocates
      (check-struct-type 'struct struct:known-procedure/allocates))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_1913 (finish_2453 struct:known-constructor))
(define known-constructor
  (|#%name|
   known-constructor
   (record-constructor
    (make-record-constructor-descriptor struct:known-constructor #f #f))))
(define known-constructor?_2802
  (|#%name| known-constructor? (record-predicate struct:known-constructor)))
(define known-constructor?
  (|#%name|
   known-constructor?
   (lambda (v)
     (if (known-constructor?_2802 v)
       #t
       ($value
        (if (impersonator? v)
          (known-constructor?_2802 (impersonator-val v))
          #f))))))
(define known-constructor-type_2993
  (|#%name|
   known-constructor-type
   (record-accessor struct:known-constructor 0)))
(define known-constructor-type
  (|#%name|
   known-constructor-type
   (lambda (s)
     (if (known-constructor?_2802 s)
       (known-constructor-type_2993 s)
       ($value
        (impersonate-ref
         known-constructor-type_2993
         struct:known-constructor
         0
         s
         'type))))))
(define finish_2917
  (make-struct-type-install-properties
   '(known-predicate)
   1
   0
   (if (struct-type? struct:known-procedure/pure)
     struct:known-procedure/pure
     (check-struct-type 'struct struct:known-procedure/pure))
   null
   'prefab
   #f
   '(0)
   #f
   'known-predicate))
(define struct:known-predicate
  (make-record-type-descriptor
   'known-predicate
   (if (struct-type? struct:known-procedure/pure)
     struct:known-procedure/pure
     (check-struct-type 'struct struct:known-procedure/pure))
   (structure-type-lookup-prefab-uid
    'known-predicate
    (if (struct-type? struct:known-procedure/pure)
      struct:known-procedure/pure
      (check-struct-type 'struct struct:known-procedure/pure))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2144 (finish_2917 struct:known-predicate))
(define known-predicate
  (|#%name|
   known-predicate
   (record-constructor
    (make-record-constructor-descriptor struct:known-predicate #f #f))))
(define known-predicate?_2903
  (|#%name| known-predicate? (record-predicate struct:known-predicate)))
(define known-predicate?
  (|#%name|
   known-predicate?
   (lambda (v)
     (if (known-predicate?_2903 v)
       #t
       ($value
        (if (impersonator? v)
          (known-predicate?_2903 (impersonator-val v))
          #f))))))
(define known-predicate-type_2853
  (|#%name| known-predicate-type (record-accessor struct:known-predicate 0)))
(define known-predicate-type
  (|#%name|
   known-predicate-type
   (lambda (s)
     (if (known-predicate?_2903 s)
       (known-predicate-type_2853 s)
       ($value
        (impersonate-ref
         known-predicate-type_2853
         struct:known-predicate
         0
         s
         'type))))))
(define finish_2548
  (make-struct-type-install-properties
   '(known-accessor)
   1
   0
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   null
   'prefab
   #f
   '(0)
   #f
   'known-accessor))
(define struct:known-accessor
  (make-record-type-descriptor
   'known-accessor
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   (structure-type-lookup-prefab-uid
    'known-accessor
    (if (struct-type? struct:known-procedure/single-valued)
      struct:known-procedure/single-valued
      (check-struct-type 'struct struct:known-procedure/single-valued))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2905 (finish_2548 struct:known-accessor))
(define known-accessor
  (|#%name|
   known-accessor
   (record-constructor
    (make-record-constructor-descriptor struct:known-accessor #f #f))))
(define known-accessor?_2710
  (|#%name| known-accessor? (record-predicate struct:known-accessor)))
(define known-accessor?
  (|#%name|
   known-accessor?
   (lambda (v)
     (if (known-accessor?_2710 v)
       #t
       ($value
        (if (impersonator? v)
          (known-accessor?_2710 (impersonator-val v))
          #f))))))
(define known-accessor-type_2147
  (|#%name| known-accessor-type (record-accessor struct:known-accessor 0)))
(define known-accessor-type
  (|#%name|
   known-accessor-type
   (lambda (s)
     (if (known-accessor?_2710 s)
       (known-accessor-type_2147 s)
       ($value
        (impersonate-ref
         known-accessor-type_2147
         struct:known-accessor
         0
         s
         'type))))))
(define finish_2552
  (make-struct-type-install-properties
   '(known-mutator)
   1
   0
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   null
   'prefab
   #f
   '(0)
   #f
   'known-mutator))
(define struct:known-mutator
  (make-record-type-descriptor
   'known-mutator
   (if (struct-type? struct:known-procedure/single-valued)
     struct:known-procedure/single-valued
     (check-struct-type 'struct struct:known-procedure/single-valued))
   (structure-type-lookup-prefab-uid
    'known-mutator
    (if (struct-type? struct:known-procedure/single-valued)
      struct:known-procedure/single-valued
      (check-struct-type 'struct struct:known-procedure/single-valued))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2521 (finish_2552 struct:known-mutator))
(define known-mutator
  (|#%name|
   known-mutator
   (record-constructor
    (make-record-constructor-descriptor struct:known-mutator #f #f))))
(define known-mutator?_2993
  (|#%name| known-mutator? (record-predicate struct:known-mutator)))
(define known-mutator?
  (|#%name|
   known-mutator?
   (lambda (v)
     (if (known-mutator?_2993 v)
       #t
       ($value
        (if (impersonator? v)
          (known-mutator?_2993 (impersonator-val v))
          #f))))))
(define known-mutator-type_2618
  (|#%name| known-mutator-type (record-accessor struct:known-mutator 0)))
(define known-mutator-type
  (|#%name|
   known-mutator-type
   (lambda (s)
     (if (known-mutator?_2993 s)
       (known-mutator-type_2618 s)
       ($value
        (impersonate-ref
         known-mutator-type_2618
         struct:known-mutator
         0
         s
         'type))))))
(define finish_2184
  (make-struct-type-install-properties
   '(known-struct-constructor)
   1
   0
   (if (struct-type? struct:known-constructor)
     struct:known-constructor
     (check-struct-type 'struct struct:known-constructor))
   null
   'prefab
   #f
   '(0)
   #f
   'known-struct-constructor))
(define struct:known-struct-constructor
  (make-record-type-descriptor
   'known-struct-constructor
   (if (struct-type? struct:known-constructor)
     struct:known-constructor
     (check-struct-type 'struct struct:known-constructor))
   (structure-type-lookup-prefab-uid
    'known-struct-constructor
    (if (struct-type? struct:known-constructor)
      struct:known-constructor
      (check-struct-type 'struct struct:known-constructor))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_3238 (finish_2184 struct:known-struct-constructor))
(define known-struct-constructor
  (|#%name|
   known-struct-constructor
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-struct-constructor
     #f
     #f))))
(define known-struct-constructor?_2705
  (|#%name|
   known-struct-constructor?
   (record-predicate struct:known-struct-constructor)))
(define known-struct-constructor?
  (|#%name|
   known-struct-constructor?
   (lambda (v)
     (if (known-struct-constructor?_2705 v)
       #t
       ($value
        (if (impersonator? v)
          (known-struct-constructor?_2705 (impersonator-val v))
          #f))))))
(define known-struct-constructor-type-id_2882
  (|#%name|
   known-struct-constructor-type-id
   (record-accessor struct:known-struct-constructor 0)))
(define known-struct-constructor-type-id
  (|#%name|
   known-struct-constructor-type-id
   (lambda (s)
     (if (known-struct-constructor?_2705 s)
       (known-struct-constructor-type-id_2882 s)
       ($value
        (impersonate-ref
         known-struct-constructor-type-id_2882
         struct:known-struct-constructor
         0
         s
         'type-id))))))
(define finish_2304
  (make-struct-type-install-properties
   '(known-struct-predicate)
   3
   0
   (if (struct-type? struct:known-predicate)
     struct:known-predicate
     (check-struct-type 'struct struct:known-predicate))
   null
   'prefab
   #f
   '(0 1 2)
   #f
   'known-struct-predicate))
(define struct:known-struct-predicate
  (make-record-type-descriptor
   'known-struct-predicate
   (if (struct-type? struct:known-predicate)
     struct:known-predicate
     (check-struct-type 'struct struct:known-predicate))
   (structure-type-lookup-prefab-uid
    'known-struct-predicate
    (if (struct-type? struct:known-predicate)
      struct:known-predicate
      (check-struct-type 'struct struct:known-predicate))
    3
    0
    #f
    '(0 1 2))
   #f
   #f
   '(3 . 7)))
(define effect_2384 (finish_2304 struct:known-struct-predicate))
(define known-struct-predicate
  (|#%name|
   known-struct-predicate
   (record-constructor
    (make-record-constructor-descriptor struct:known-struct-predicate #f #f))))
(define known-struct-predicate?_2418
  (|#%name|
   known-struct-predicate?
   (record-predicate struct:known-struct-predicate)))
(define known-struct-predicate?
  (|#%name|
   known-struct-predicate?
   (lambda (v)
     (if (known-struct-predicate?_2418 v)
       #t
       ($value
        (if (impersonator? v)
          (known-struct-predicate?_2418 (impersonator-val v))
          #f))))))
(define known-struct-predicate-type-id_2101
  (|#%name|
   known-struct-predicate-type-id
   (record-accessor struct:known-struct-predicate 0)))
(define known-struct-predicate-type-id
  (|#%name|
   known-struct-predicate-type-id
   (lambda (s)
     (if (known-struct-predicate?_2418 s)
       (known-struct-predicate-type-id_2101 s)
       ($value
        (impersonate-ref
         known-struct-predicate-type-id_2101
         struct:known-struct-predicate
         0
         s
         'type-id))))))
(define known-struct-predicate-authentic?_2155
  (|#%name|
   known-struct-predicate-authentic?
   (record-accessor struct:known-struct-predicate 1)))
(define known-struct-predicate-authentic?
  (|#%name|
   known-struct-predicate-authentic?
   (lambda (s)
     (if (known-struct-predicate?_2418 s)
       (known-struct-predicate-authentic?_2155 s)
       ($value
        (impersonate-ref
         known-struct-predicate-authentic?_2155
         struct:known-struct-predicate
         1
         s
         'authentic?))))))
(define known-struct-predicate-sealed?_2251
  (|#%name|
   known-struct-predicate-sealed?
   (record-accessor struct:known-struct-predicate 2)))
(define known-struct-predicate-sealed?
  (|#%name|
   known-struct-predicate-sealed?
   (lambda (s)
     (if (known-struct-predicate?_2418 s)
       (known-struct-predicate-sealed?_2251 s)
       ($value
        (impersonate-ref
         known-struct-predicate-sealed?_2251
         struct:known-struct-predicate
         2
         s
         'sealed?))))))
(define finish_3014
  (make-struct-type-install-properties
   '(known-field-accessor)
   4
   0
   (if (struct-type? struct:known-accessor)
     struct:known-accessor
     (check-struct-type 'struct struct:known-accessor))
   null
   'prefab
   #f
   '(0 1 2 3)
   #f
   'known-field-accessor))
(define struct:known-field-accessor
  (make-record-type-descriptor
   'known-field-accessor
   (if (struct-type? struct:known-accessor)
     struct:known-accessor
     (check-struct-type 'struct struct:known-accessor))
   (structure-type-lookup-prefab-uid
    'known-field-accessor
    (if (struct-type? struct:known-accessor)
      struct:known-accessor
      (check-struct-type 'struct struct:known-accessor))
    4
    0
    #f
    '(0 1 2 3))
   #f
   #f
   '(4 . 15)))
(define effect_2259 (finish_3014 struct:known-field-accessor))
(define known-field-accessor
  (|#%name|
   known-field-accessor
   (record-constructor
    (make-record-constructor-descriptor struct:known-field-accessor #f #f))))
(define known-field-accessor?_2878
  (|#%name|
   known-field-accessor?
   (record-predicate struct:known-field-accessor)))
(define known-field-accessor?
  (|#%name|
   known-field-accessor?
   (lambda (v)
     (if (known-field-accessor?_2878 v)
       #t
       ($value
        (if (impersonator? v)
          (known-field-accessor?_2878 (impersonator-val v))
          #f))))))
(define known-field-accessor-type-id_2744
  (|#%name|
   known-field-accessor-type-id
   (record-accessor struct:known-field-accessor 0)))
(define known-field-accessor-type-id
  (|#%name|
   known-field-accessor-type-id
   (lambda (s)
     (if (known-field-accessor?_2878 s)
       (known-field-accessor-type-id_2744 s)
       ($value
        (impersonate-ref
         known-field-accessor-type-id_2744
         struct:known-field-accessor
         0
         s
         'type-id))))))
(define known-field-accessor-authentic?_2286
  (|#%name|
   known-field-accessor-authentic?
   (record-accessor struct:known-field-accessor 1)))
(define known-field-accessor-authentic?
  (|#%name|
   known-field-accessor-authentic?
   (lambda (s)
     (if (known-field-accessor?_2878 s)
       (known-field-accessor-authentic?_2286 s)
       ($value
        (impersonate-ref
         known-field-accessor-authentic?_2286
         struct:known-field-accessor
         1
         s
         'authentic?))))))
(define known-field-accessor-pos_2482
  (|#%name|
   known-field-accessor-pos
   (record-accessor struct:known-field-accessor 2)))
(define known-field-accessor-pos
  (|#%name|
   known-field-accessor-pos
   (lambda (s)
     (if (known-field-accessor?_2878 s)
       (known-field-accessor-pos_2482 s)
       ($value
        (impersonate-ref
         known-field-accessor-pos_2482
         struct:known-field-accessor
         2
         s
         'pos))))))
(define known-field-accessor-known-immutable?_2377
  (|#%name|
   known-field-accessor-known-immutable?
   (record-accessor struct:known-field-accessor 3)))
(define known-field-accessor-known-immutable?
  (|#%name|
   known-field-accessor-known-immutable?
   (lambda (s)
     (if (known-field-accessor?_2878 s)
       (known-field-accessor-known-immutable?_2377 s)
       ($value
        (impersonate-ref
         known-field-accessor-known-immutable?_2377
         struct:known-field-accessor
         3
         s
         'known-immutable?))))))
(define finish_2908
  (make-struct-type-install-properties
   '(known-field-mutator)
   3
   0
   (if (struct-type? struct:known-mutator)
     struct:known-mutator
     (check-struct-type 'struct struct:known-mutator))
   null
   'prefab
   #f
   '(0 1 2)
   #f
   'known-field-mutator))
(define struct:known-field-mutator
  (make-record-type-descriptor
   'known-field-mutator
   (if (struct-type? struct:known-mutator)
     struct:known-mutator
     (check-struct-type 'struct struct:known-mutator))
   (structure-type-lookup-prefab-uid
    'known-field-mutator
    (if (struct-type? struct:known-mutator)
      struct:known-mutator
      (check-struct-type 'struct struct:known-mutator))
    3
    0
    #f
    '(0 1 2))
   #f
   #f
   '(3 . 7)))
(define effect_2603 (finish_2908 struct:known-field-mutator))
(define known-field-mutator
  (|#%name|
   known-field-mutator
   (record-constructor
    (make-record-constructor-descriptor struct:known-field-mutator #f #f))))
(define known-field-mutator?_2222
  (|#%name|
   known-field-mutator?
   (record-predicate struct:known-field-mutator)))
(define known-field-mutator?
  (|#%name|
   known-field-mutator?
   (lambda (v)
     (if (known-field-mutator?_2222 v)
       #t
       ($value
        (if (impersonator? v)
          (known-field-mutator?_2222 (impersonator-val v))
          #f))))))
(define known-field-mutator-type-id_2433
  (|#%name|
   known-field-mutator-type-id
   (record-accessor struct:known-field-mutator 0)))
(define known-field-mutator-type-id
  (|#%name|
   known-field-mutator-type-id
   (lambda (s)
     (if (known-field-mutator?_2222 s)
       (known-field-mutator-type-id_2433 s)
       ($value
        (impersonate-ref
         known-field-mutator-type-id_2433
         struct:known-field-mutator
         0
         s
         'type-id))))))
(define known-field-mutator-authentic?_2735
  (|#%name|
   known-field-mutator-authentic?
   (record-accessor struct:known-field-mutator 1)))
(define known-field-mutator-authentic?
  (|#%name|
   known-field-mutator-authentic?
   (lambda (s)
     (if (known-field-mutator?_2222 s)
       (known-field-mutator-authentic?_2735 s)
       ($value
        (impersonate-ref
         known-field-mutator-authentic?_2735
         struct:known-field-mutator
         1
         s
         'authentic?))))))
(define known-field-mutator-pos_2749
  (|#%name|
   known-field-mutator-pos
   (record-accessor struct:known-field-mutator 2)))
(define known-field-mutator-pos
  (|#%name|
   known-field-mutator-pos
   (lambda (s)
     (if (known-field-mutator?_2222 s)
       (known-field-mutator-pos_2749 s)
       ($value
        (impersonate-ref
         known-field-mutator-pos_2749
         struct:known-field-mutator
         2
         s
         'pos))))))
(define finish_2543
  (make-struct-type-install-properties
   '(known-struct-constructor/need-imports)
   1
   0
   (if (struct-type? struct:known-struct-constructor)
     struct:known-struct-constructor
     (check-struct-type 'struct struct:known-struct-constructor))
   null
   'prefab
   #f
   '(0)
   #f
   'known-struct-constructor/need-imports))
(define struct:known-struct-constructor/need-imports
  (make-record-type-descriptor
   'known-struct-constructor/need-imports
   (if (struct-type? struct:known-struct-constructor)
     struct:known-struct-constructor
     (check-struct-type 'struct struct:known-struct-constructor))
   (structure-type-lookup-prefab-uid
    'known-struct-constructor/need-imports
    (if (struct-type? struct:known-struct-constructor)
      struct:known-struct-constructor
      (check-struct-type 'struct struct:known-struct-constructor))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2146 (finish_2543 struct:known-struct-constructor/need-imports))
(define known-struct-constructor/need-imports
  (|#%name|
   known-struct-constructor/need-imports
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-struct-constructor/need-imports
     #f
     #f))))
(define known-struct-constructor/need-imports?_2300
  (|#%name|
   known-struct-constructor/need-imports?
   (record-predicate struct:known-struct-constructor/need-imports)))
(define known-struct-constructor/need-imports?
  (|#%name|
   known-struct-constructor/need-imports?
   (lambda (v)
     (if (known-struct-constructor/need-imports?_2300 v)
       #t
       ($value
        (if (impersonator? v)
          (known-struct-constructor/need-imports?_2300 (impersonator-val v))
          #f))))))
(define known-struct-constructor/need-imports-needed_2757
  (|#%name|
   known-struct-constructor/need-imports-needed
   (record-accessor struct:known-struct-constructor/need-imports 0)))
(define known-struct-constructor/need-imports-needed
  (|#%name|
   known-struct-constructor/need-imports-needed
   (lambda (s)
     (if (known-struct-constructor/need-imports?_2300 s)
       (known-struct-constructor/need-imports-needed_2757 s)
       ($value
        (impersonate-ref
         known-struct-constructor/need-imports-needed_2757
         struct:known-struct-constructor/need-imports
         0
         s
         'needed))))))
(define finish_2626
  (make-struct-type-install-properties
   '(known-struct-predicate/need-imports)
   1
   0
   (if (struct-type? struct:known-struct-predicate)
     struct:known-struct-predicate
     (check-struct-type 'struct struct:known-struct-predicate))
   null
   'prefab
   #f
   '(0)
   #f
   'known-struct-predicate/need-imports))
(define struct:known-struct-predicate/need-imports
  (make-record-type-descriptor
   'known-struct-predicate/need-imports
   (if (struct-type? struct:known-struct-predicate)
     struct:known-struct-predicate
     (check-struct-type 'struct struct:known-struct-predicate))
   (structure-type-lookup-prefab-uid
    'known-struct-predicate/need-imports
    (if (struct-type? struct:known-struct-predicate)
      struct:known-struct-predicate
      (check-struct-type 'struct struct:known-struct-predicate))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_3156 (finish_2626 struct:known-struct-predicate/need-imports))
(define known-struct-predicate/need-imports
  (|#%name|
   known-struct-predicate/need-imports
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-struct-predicate/need-imports
     #f
     #f))))
(define known-struct-predicate/need-imports?_2911
  (|#%name|
   known-struct-predicate/need-imports?
   (record-predicate struct:known-struct-predicate/need-imports)))
(define known-struct-predicate/need-imports?
  (|#%name|
   known-struct-predicate/need-imports?
   (lambda (v)
     (if (known-struct-predicate/need-imports?_2911 v)
       #t
       ($value
        (if (impersonator? v)
          (known-struct-predicate/need-imports?_2911 (impersonator-val v))
          #f))))))
(define known-struct-predicate/need-imports-needed_2072
  (|#%name|
   known-struct-predicate/need-imports-needed
   (record-accessor struct:known-struct-predicate/need-imports 0)))
(define known-struct-predicate/need-imports-needed
  (|#%name|
   known-struct-predicate/need-imports-needed
   (lambda (s)
     (if (known-struct-predicate/need-imports?_2911 s)
       (known-struct-predicate/need-imports-needed_2072 s)
       ($value
        (impersonate-ref
         known-struct-predicate/need-imports-needed_2072
         struct:known-struct-predicate/need-imports
         0
         s
         'needed))))))
(define finish_2444
  (make-struct-type-install-properties
   '(known-field-accessor/need-imports)
   1
   0
   (if (struct-type? struct:known-field-accessor)
     struct:known-field-accessor
     (check-struct-type 'struct struct:known-field-accessor))
   null
   'prefab
   #f
   '(0)
   #f
   'known-field-accessor/need-imports))
(define struct:known-field-accessor/need-imports
  (make-record-type-descriptor
   'known-field-accessor/need-imports
   (if (struct-type? struct:known-field-accessor)
     struct:known-field-accessor
     (check-struct-type 'struct struct:known-field-accessor))
   (structure-type-lookup-prefab-uid
    'known-field-accessor/need-imports
    (if (struct-type? struct:known-field-accessor)
      struct:known-field-accessor
      (check-struct-type 'struct struct:known-field-accessor))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2513 (finish_2444 struct:known-field-accessor/need-imports))
(define known-field-accessor/need-imports
  (|#%name|
   known-field-accessor/need-imports
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-field-accessor/need-imports
     #f
     #f))))
(define known-field-accessor/need-imports?_2679
  (|#%name|
   known-field-accessor/need-imports?
   (record-predicate struct:known-field-accessor/need-imports)))
(define known-field-accessor/need-imports?
  (|#%name|
   known-field-accessor/need-imports?
   (lambda (v)
     (if (known-field-accessor/need-imports?_2679 v)
       #t
       ($value
        (if (impersonator? v)
          (known-field-accessor/need-imports?_2679 (impersonator-val v))
          #f))))))
(define known-field-accessor/need-imports-needed_2087
  (|#%name|
   known-field-accessor/need-imports-needed
   (record-accessor struct:known-field-accessor/need-imports 0)))
(define known-field-accessor/need-imports-needed
  (|#%name|
   known-field-accessor/need-imports-needed
   (lambda (s)
     (if (known-field-accessor/need-imports?_2679 s)
       (known-field-accessor/need-imports-needed_2087 s)
       ($value
        (impersonate-ref
         known-field-accessor/need-imports-needed_2087
         struct:known-field-accessor/need-imports
         0
         s
         'needed))))))
(define finish_2153
  (make-struct-type-install-properties
   '(known-field-mutator/need-imports)
   1
   0
   (if (struct-type? struct:known-field-mutator)
     struct:known-field-mutator
     (check-struct-type 'struct struct:known-field-mutator))
   null
   'prefab
   #f
   '(0)
   #f
   'known-field-mutator/need-imports))
(define struct:known-field-mutator/need-imports
  (make-record-type-descriptor
   'known-field-mutator/need-imports
   (if (struct-type? struct:known-field-mutator)
     struct:known-field-mutator
     (check-struct-type 'struct struct:known-field-mutator))
   (structure-type-lookup-prefab-uid
    'known-field-mutator/need-imports
    (if (struct-type? struct:known-field-mutator)
      struct:known-field-mutator
      (check-struct-type 'struct struct:known-field-mutator))
    1
    0
    #f
    '(0))
   #f
   #f
   '(1 . 1)))
(define effect_2273 (finish_2153 struct:known-field-mutator/need-imports))
(define known-field-mutator/need-imports
  (|#%name|
   known-field-mutator/need-imports
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-field-mutator/need-imports
     #f
     #f))))
(define known-field-mutator/need-imports?_2495
  (|#%name|
   known-field-mutator/need-imports?
   (record-predicate struct:known-field-mutator/need-imports)))
(define known-field-mutator/need-imports?
  (|#%name|
   known-field-mutator/need-imports?
   (lambda (v)
     (if (known-field-mutator/need-imports?_2495 v)
       #t
       ($value
        (if (impersonator? v)
          (known-field-mutator/need-imports?_2495 (impersonator-val v))
          #f))))))
(define known-field-mutator/need-imports-needed_2344
  (|#%name|
   known-field-mutator/need-imports-needed
   (record-accessor struct:known-field-mutator/need-imports 0)))
(define known-field-mutator/need-imports-needed
  (|#%name|
   known-field-mutator/need-imports-needed
   (lambda (s)
     (if (known-field-mutator/need-imports?_2495 s)
       (known-field-mutator/need-imports-needed_2344 s)
       ($value
        (impersonate-ref
         known-field-mutator/need-imports-needed_2344
         struct:known-field-mutator/need-imports
         0
         s
         'needed))))))
(define finish_2492
  (make-struct-type-install-properties
   '(known-struct-type-property/immediate-guard)
   0
   0
   #f
   null
   'prefab
   #f
   '()
   #f
   'known-struct-type-property/immediate-guard))
(define struct:known-struct-type-property/immediate-guard
  (make-record-type-descriptor
   'known-struct-type-property/immediate-guard
   #f
   (structure-type-lookup-prefab-uid
    'known-struct-type-property/immediate-guard
    #f
    0
    0
    #f
    '())
   #f
   #f
   '(0 . 0)))
(define effect_2294
  (finish_2492 struct:known-struct-type-property/immediate-guard))
(define known-struct-type-property/immediate-guard
  (|#%name|
   known-struct-type-property/immediate-guard
   (record-constructor
    (make-record-constructor-descriptor
     struct:known-struct-type-property/immediate-guard
     #f
     #f))))
(define known-struct-type-property/immediate-guard?_2536
  (|#%name|
   known-struct-type-property/immediate-guard?
   (record-predicate struct:known-struct-type-property/immediate-guard)))
(define known-struct-type-property/immediate-guard?
  (|#%name|
   known-struct-type-property/immediate-guard?
   (lambda (v)
     (if (known-struct-type-property/immediate-guard?_2536 v)
       #t
       ($value
        (if (impersonator? v)
          (known-struct-type-property/immediate-guard?_2536
           (impersonator-val v))
          #f))))))
(define a-known-constant (known-constant))
(define a-known-consistent (known-consistent))
