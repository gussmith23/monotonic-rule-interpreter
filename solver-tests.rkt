#lang racket

(module+ test
  (require "interpreter.rkt"
           rosette
           rackunit)

  (define (make-rule ins outs bw)
    (list (map (lambda (v) (bv v bw)) ins) (map (lambda (v) (bv v bw)) outs)))

  (test-begin ;
   ;;; List of rewrites, where each rewrite is toggled by a boolean.
   (define rws (list (make-rule '(0 1) '(2 3) 6) (make-rule '(2 3) '(0 1) 6)))
   (displayln rws)
   ;;; List of booleans, each of which enables or disables its corresponding rewrites.
   (define rw-enables
     (for/list ([_ (range (length rws))])
       (define-symbolic* rw-enable boolean?)
       rw-enable))
   (displayln rw-enables)
   ;;; Apply enables to rewrites.
   (define filtered-rws (filter-map (lambda (rw enable) (if enable rw #false)) rws rw-enables))
   (displayln (union-contents (first (cdr (first (union-contents filtered-rws))))))
   (displayln (interpreter (bv #b000011 6) filtered-rws 1))
   (displayln (optimize #:minimize (list (length filtered-rws))
                        #:guarantee (assert (bveq (bv #b001111 6)
                                                  (interpreter (bv #b000011 6) filtered-rws 1)))))))
