#lang racket/base
(require "prefix-dispatcher.rkt"
         racket/cmdline
         (for-syntax racket/base
                     racket/syntax))

(provide svn-style-command-line
         current-svn-style-command)

;; implements an "svn-style" command-line interface as a wrapper around racket/cmdline. At the moment,
;; it is light on error-checking and makes choices that are somewhat specific to the PLaneT commandline
;; tool, thus its inclusion in planet/private rather than somewhere more visible. The idea is that you
;; write
#|

(svn-style-command-line
   #:program <name-of-the-program-string>
   #:argv <argument vector, generally (current-command-line-arguments)>
   <program-general-description string>
   [<command1> <brief-help-string> <long-help-description-string>
    ... arguments just like the command-line macro takes, until ...
    #:args formals
    body-expr] ...)
|#

;; This macro turns that into a command-line type of thing that implements
;;    program command1 ... args ...
;;    program command2 ... args ...
;; etc.
;; It provides three nonobvious features:
;;   1. It automatically includes a help feature that prints out all available subcommands
;;   2. It automatically lets users use any unambiguous prefix of any command.
;;      This means that no command name may be a prefix of any other command name, because it
;;      would mean there was no way to unambiguously name the shorter one.
;;   3. A clause [#:alias <command-name> <redirect-to>] automatically forwards
;;      arguments from "program command-name args …" to "program redirect-to args …".

(define current-svn-style-command (make-parameter #f))

(define-syntax (svn-style-command-line stx)
  (syntax-case stx ()
    [(_ #:program prog
        #:argv args
        general-description
        clause ...)
     (with-syntax* ([impl-table (generate-temporary #'impl-table)]
                    [(((name description long-description body ...)
                       accum formals arg-help-strs final-expr
                       input argv)
                      ...)
                     (map (lambda (clause)
                            (syntax-case clause ()
                              [[#:alias alias invoke]
                               #'((alias ,(format "Redirects to ~a ~a" p invoke)
                                         (format "Redirects to ~a ~a" p invoke)
                                         #| no command-line body |#)
                                  ignored remainder '("remainder")
                                  (begin
                                    (eprintf "Redirecting to `~a ~a`\n" p invoke)
                                    ((hash-ref impl-table invoke) remainder))
                                  remainder (cons "--" remainder))]
                              [[name description long-description body ...
                                     #:args formals final-expr]
                               #'((name description long-description body ...)
                                  ignored formals (pimap symbol->string 'formals) final-expr
                                  remainder remainder)]
                              [(name description long-description body ...
                                     #:handlers (lambda (accum . formals) final-expr) arg-help-strs)
                               #'((name description long-description body ...)
                                  accum formals arg-help-strs final-expr
                                  remainder remainder)]))
                          (syntax->list #'(clause ...)))]
                    [(n ...) (generate-temporaries #'(name ...))]
                    [(impl ...) (generate-temporaries #'(name ...))])
       #'(letrec ([p prog]
                  [a args]
                  [n name] ...
                  [impl
                   (λ (input)
                     (parameterize ([current-svn-style-command n])
                       (command-line
                        #:program (format "~a ~a" p n)
                        #:argv argv
                        body ...
                        #:handlers
                        (λ (accum . formals) final-expr)
                        arg-help-strs
                        (λ (help-string)
                          (for-each displayln (wrap-to-count long-description 80))
                          (newline)
                          (display help-string)
                          (exit)))))]
                  ...
                  [impl-table (make-immutable-hash (list (cons n impl) ...))]
                  [argslist (cond
                             [(list? a) a]
                             [(vector? a) (vector->list a)]
                             [else (error 'command "expected a vector or list for arguments, received ~e" a)])]
                  [help (λ () (display-help-message p general-description `((name description) ...)))])
           (let-values ([(the-command remainder)
                         (if (null? argslist)
                             (values "help" '())
                             (values (car argslist) (cdr argslist)))])
             (prefix-case the-command
                          #:ambiguous (lambda (opts)
                                        (raise-user-error
                                         (string->symbol (format "~a ~a" p the-command))
                                         (string-append "does not identify a unique subcommand;\n"
                                                        " please use a longer name for the intended subcommand\n"
                                                        "  given: " the-command "\n"
                                                        "  subcommands with a matching prefix:"
                                                        (apply
                                                         string-append
                                                         (for/list ([opt (in-list opts)])
                                                           (format "\n   ~a" opt))))))
                          [n (impl remainder)]
                          ...
                          ["help" (help)]
                          [else (begin (help) (exit 1))]))))]))


;; display-help-message : string string (listof (list string string)) -> void
;; prints out the help message
(define (display-help-message prog general-description commands)
  (let* ([maxlen (apply max (map (λ (p) (string-length (car p))) commands))]
         [message-lines
          `(,(format "Usage: ~a <subcommand> [option ...] <arg ...>" prog)
            ,(format "  where any unambiguous prefix can be used for a subcommand")
            ""
            ,@(wrap-to-count general-description 80)
            ""
            ,(format "For help on a particular subcommand, use '~a <subcommand> --help'" prog)
            ,@(map (λ (command)
                     (let* ([padded-name (pad (car command) maxlen)]
                            [desc        (cadr command)]
                            [msg         (format "  ~a ~a    ~a" prog padded-name desc)])
                       msg))
                   commands))])
    (for-each (λ (line) (display line) (newline)) message-lines)))

;; ----------------------------------------
;; utility

;; pad : string nat[>= string-length str] -> string
;; pads the given string up to the given length.
(define (pad str n)
  (let* ([l (string-length str)]
         [extra (build-string (- n l) (λ (n) #\space))])
    (string-append str extra)))

;; pimap : (A -> B) improper-listof A -> listof B
(define (pimap f pil)
  (cond
    [(null? pil) '()]
    [(pair? pil) (cons (f (car pil))
                       (pimap f (cdr pil)))]
    [else (list (f pil))]))

;; wrap-to-count : string nat -> (listof string)
;; breaks str into substrings such that no substring
;; is longer than n characters long. Only breaks on spaces, which
;; are eaten in the process.
(define (wrap-to-count str n)
  (cond
    [(<= (string-length str) n) (list str)]
    [(regexp-match-positions #rx"\n" str 0 n)
     =>
     (λ (posn)
       (let-values ([(x y) (values (car (car posn)) (cdr (car posn)))])
         (cons (substring str 0 x) (wrap-to-count (substring str y) n))))]
    [else
     ;; iterate backwards from char n looking for a good break
     (let loop ([k n])
       (cond
         [(= k 0) (error wrap-to-count "could not break string")]
         [(char=? (string-ref str k) #\space)
          (cons (substring str 0 k) (wrap-to-count (substring str (add1 k)) n))]
         [else (loop (sub1 k))]))]))
