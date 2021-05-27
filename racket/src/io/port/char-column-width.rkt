#lang racket/base

(provide char-column-width)

;; Based on a discussion with SamPh on the Racket Discord in #help on 2021-05-25:
;; https://discord.com/channels/571040468092321801/667522224823205889/846880307293585469

(require ffi/unsafe)

(define-cpointer-type _locale)

;; FYI: newlocale doesn't work on windows
(define newlocale
  (get-ffi-obj 'newlocale #f
               (_fun
                ; hotwired based on what CPP spit out for the constant LC_ALL_MASK
                [_int = 2]
                ; may want to find an actual better locale to use
                [_string = "en_US.UTF-8"]
                [_pointer = #f]
                ->
                _locale)))

;; TODO: don't forget to set up some way to free the locale or somesuch
(define loc (newlocale))

;; wcwidth doesn't work on windows
;; ALTERNATIVE:
;;   could port this which is used as the basis for go and rust implementations of wcwidth
;;   https://www.cl.cam.ac.uk/~mgk25/ucs/wcwidth.c
(define wcwidth_l
  (get-ffi-obj 'wcwidth_l #f  (_fun _wchar _locale -> _int)))

;; char-column-width : Char -> [Maybe Nat]
(define (char-column-width c)
  (define w (wcwidth_l (char->integer c) loc))
  (and (not (negative? w)) w))
