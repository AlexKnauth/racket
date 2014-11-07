#lang racket/base

(provide configure)

(require (only-in scribble/reader make-at-readtable))

(define (configure data)
  (current-readtable (make-at-readtable #:readtable (current-readtable))))
