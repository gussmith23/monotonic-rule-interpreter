#lang errortrace racket

(module+ test
  (require "interpreter.rkt"
           rosette
           rackunit
           rosette/solver/smt/boolector)

  (define (make-rule ins outs bw)
    (list (map (lambda (v) (bv v bw)) ins) (map (lambda (v) (bv v bw)) outs)))

  ;;; Simple test.
  (test-begin ;
   ;;; List of rewrites.
   (define rws (list (make-rule '(0 1) '(2 3) 6) (make-rule '(2 3) '(0 1) 6)))
   ;;; List of booleans, each of which enables or disables its corresponding rewrites.
   (define rw-enables
     (for/list ([_ (range (length rws))])
       (define-symbolic* rw-enable boolean?)
       rw-enable))
   ;;; Apply enables to rewrites.
   (define filtered-rws (filter-map (lambda (rw enable) (if enable rw #false)) rws rw-enables))
   (check-true (sat? (optimize #:minimize (list (length filtered-rws))
                               #:guarantee
                               (assert (bveq (bv #b001111 6)
                                             (interpreter (bv #b000011 6) filtered-rws 1)))))))

  ;;; Simple test.
  (test-begin ;
   (current-solver (boolector))
   (define (make-symbolic-rule bw)
     (define-symbolic* a b x y (bitvector bw))
     (list (list a b) (list x y)))
   ;;; List of rewrites.
   (define rws (list (make-symbolic-rule 6)))
   (define-symbolic i0 i1 i2 i3 (bitvector 1))
   (define state (concat i0 i1 i2 i3 (bv #b0000 4)))
   (define soln
     (synthesize #:forall (list i0 i1 i2 i3)
                 #:guarantee (begin
                               (define final-state (interpreter state rws 100))
                               (define o0 (bit 0 final-state))
                               (define o1 (bit 1 final-state))
                               (define o2 (bit 2 final-state))
                               (define o3 (bit 3 final-state))
                               (assert (bveq o0 (bvand i0 i1))))))
   (pretty-print (evaluate rws soln)))

  ;;;
  (define (helper #:inputs inputs
                  #:outputs outputs
                  #:intermediates num-intermediates
                  #:bw bw
                  #:gates num-gates
                  #:wires num-wires
                  #:iters iters)

    ;;; Our state bitvector.
    (define state
      (apply concat
             (append inputs
                     (for/list ([_ (range num-intermediates)])
                       (bv 0 (bitvector 1)))
                     (map (lambda (output)
                            (define len (length (bitvector->bits output)))
                            (when (not (concrete? len))
                              (error "Outputs must be of concrete length"))
                            (bv 0 (bitvector len)))
                          outputs))))

    (define (make-symbolic-gate bw)
      (define-symbolic* a b x y (bitvector bw))
      (list (list a b) (list x y)))

    (define (make-symbolic-wire bw)
      (define-symbolic* a x (bitvector bw))
      (list (list a) (list x)))

    (define gates
      (for/list ([_ (range num-gates)])
        (make-symbolic-gate bw)))
    (define wires
      (for/list ([_ (range num-wires)])
        (make-symbolic-wire bw)))

    (define final-state (interpreter state (append gates wires) iters))

    (define soln
      (synthesize #:forall inputs
                  #:guarantee
                  (begin

                    (foldr (lambda (output start-idx)
                             (define end-idx (+ (length (bitvector->bits output)) start-idx))
                             (assert (bveq (extract (sub1 end-idx) start-idx final-state) output))
                             end-idx)
                           0
                           outputs))))

    (when (sat? soln)
      (displayln (format "implemented function(s)\n~a\nwith gates:\n~a\nand wires:\n~a\n"
                         (pretty-format outputs)
                         (pretty-format (evaluate gates soln))
                         (pretty-format (evaluate wires soln)))))

    soln)

  (test-begin ;
   (define-symbolic a b c (bitvector 1))
   (define-symbolic a-8 b-8 (bitvector 8))
   (define-symbolic a-2 b-2 (bitvector 2))
   ;;; We can implement an and with a single gate.
   (check-true (sat? (helper #:inputs (list a b)
                             #:outputs (list (bvand a b))
                             #:intermediates 0
                             #:bw 3
                             #:gates 1
                             #:wires 0
                             #:iters 1)))
   ;;; We can't implement or with a gate.
   (check-false (sat? (helper #:inputs (list a b)
                              #:outputs (list (bvor a b))
                              #:intermediates 0
                              #:bw 3
                              #:gates 1
                              #:wires 0
                              #:iters 1)))
   ;;; We can't implement or with a single wire.
   (check-false (sat? (helper #:inputs (list a b)
                              #:outputs (list (bvor a b))
                              #:intermediates 0
                              #:bw 3
                              #:gates 0
                              #:wires 1
                              #:iters 1)))
   ;;; But we can implement or with two wires!
   (check-true (sat? (helper #:inputs (list a b)
                             #:outputs (list (bvor a b))
                             #:intermediates 0
                             #:bw 3
                             #:gates 0
                             #:wires 2
                             #:iters 1)))
   ;;; Implementing two functions.
   (check-true (sat? (helper #:inputs (list a b c)
                             #:outputs (list (bvor a b) (bvand a c))
                             #:intermediates 0
                             #:bw 3
                             #:gates 1
                             #:wires 2
                             #:iters 1)))
   ;;; Implementing operations over multibit bitvectors.
   (check-true (sat? (helper #:inputs (list a-8 b-8)
                             #:outputs (list (bvand a-8 b-8))
                             #:intermediates 0
                             #:bw 6
                             #:gates 8
                             #:wires 0
                             #:iters 1)))))
