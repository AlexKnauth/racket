#lang racket/base
(require (for-syntax racket/base)
         racket/syntax
         racket/string
         (only-in racket/private/template
                  metafunction))
(provide (rename-out [syntax template]
                     [syntax/loc template/loc]
                     [quasisyntax quasitemplate]
                     [quasisyntax/loc quasitemplate/loc]
                     [~? ??]
                     [~@ ?@])
         define-template-metafunction)

;; ============================================================
;; Metafunctions

(define-syntax (define-template-metafunction stx)
  (syntax-case stx ()
    [(dsm (id arg ...) . body)
     #'(dsm id (lambda (arg ...) . body))]
    [(dsm id expr)
     (identifier? #'id)
     (with-syntax ([(internal-id) (generate-temporaries #'(id))])
       #'(begin (define internal-id (make-hygienic-metafunction expr))
                (define-syntax id (metafunction (quote-syntax internal-id)))))]))

(define current-template-metafunction-introducer
  (make-parameter (lambda (stx) (if (syntax-transforming?) (syntax-local-introduce stx) stx))))

(define ((make-hygienic-metafunction transformer) stx)
  (define mark (make-syntax-introducer))
  (define old-mark (current-template-metafunction-introducer))
  (parameterize ((current-template-metafunction-introducer mark))
    (define r (call-with-continuation-barrier (lambda () (transformer (mark (old-mark stx))))))
    (unless (syntax? r)
      (raise-syntax-error #f "result of template metafunction was not syntax" stx))
    (old-mark (mark r))))

;; ---------------------------

;; #'(~dot-id a b c) = #'a.b.c

(define-template-metafunction ~dot-id
  (lambda (stx)
    (syntax-case stx ()
      [(_ x y ...)
       (let ([ys (syntax->list #'(y ...))])
         (define not-id
           (ormap (λ (x) (and (not (identifier? x)) x)) (cons #'x ys)))
         (when not-id
           (raise-syntax-error #f "expected an identifier" stx not-id))
         (format-id #'x "~a~a" #'x
                    (string-append*
                     (for/list ([y (in-list ys)])
                       (format ".~s" (syntax-e y))))
                    #:source stx
                    #:props stx))])))

