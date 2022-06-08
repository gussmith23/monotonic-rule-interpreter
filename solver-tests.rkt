#lang errortrace racket

(module+ test
  (require "interpreter.rkt"
           rosette
           rackunit
           rosette/solver/smt/boolector)

  ;;; Simple test.
  (with-vc ;
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
    (pretty-print (evaluate rws soln))))

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

  (with-vc ;
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

  (define (helper2 #:inputs logical-inputs
                   #:outputs logical-outputs
                   #:intermediates num-intermediates
                   #:bw bw
                   #:gates num-gates
                   #:wires num-wires
                   #:iters iters)

    (define inputs
      (for/list ([input logical-inputs])
        (define len (length (bitvector->bits input)))
        ;;; The indicator indicating whether the bits are set to 0.
        (define-symbolic* inputs-0 (bitvector len))
        ;;; The indicator indicating whether the bits are set to 1.
        (define-symbolic* inputs-1 (bitvector len))

        (list inputs-0 inputs-1)))

    ;;; Intermediates are a list of 1-bit bitvectors used as intermediate states.
    (define intermediates
      (for/list ([_ (range num-intermediates)])
        (bv 0 (bitvector 1))))

    (define outputs
      (for/list ([output logical-outputs])
        (define len (length (bitvector->bits output)))
        (when (not (concrete? len))
          (error "Outputs must be of concrete length"))
        (bv 0 (bitvector (* 2 len)))))

    ;;; Our state bitvector.
    (define state (apply concat (append (apply append inputs) intermediates outputs)))

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
      (synthesize
       #:forall (append logical-inputs (apply append inputs))
       #:guarantee
       (begin

         (for ([input inputs] [logical-input logical-inputs])

           ;;; Dual-rail assumptions.
           ;;; These assertions ensure the dual-rail encoding matches the single-rail encoding.
           ;(assert (bveq (bvnot (first input)) logical-input))
           (assume (bveq (bvnot (first input)) logical-input))
           (assume (bveq (second input) logical-input)))

         (foldr (lambda (output start-idx)
                  (define end-idx-0s (+ (length (bitvector->bits output)) start-idx))
                  (define end-idx-1s (+ (length (bitvector->bits output)) end-idx-0s))
                  (define output-0s (extract (sub1 end-idx-0s) start-idx final-state))
                  (define output-1s (extract (sub1 end-idx-1s) end-idx-0s final-state))

                  ;;; Dual-rail assertions.
                  (assert (bveq (bvnot output-0s) output))
                  (assert (bveq output-1s output))

                  end-idx-1s)
                0
                logical-outputs))))

    (when (sat? soln)
      (displayln (format "implemented function(s)\n~a\nwith gates:\n~a\nand wires:\n~a\n"
                         (pretty-format logical-outputs)
                         (pretty-format (evaluate gates soln))
                         (pretty-format (evaluate wires soln)))))

    soln)

  (test-begin ;
   (define-symbolic a b c (bitvector 1))
   (define-symbolic a-8 b-8 (bitvector 8))
   (define-symbolic a-2 b-2 (bitvector 2))
   ;;; Dual-rail add is implemented with a minimum of 2 gates and 1 wire.
   (check-false (sat? (helper2 #:inputs (list a b)
                               #:outputs (list (bvand a b))
                               #:intermediates 0
                               #:bw 3
                               #:gates 2
                               #:wires 0
                               #:iters 10)))
   (check-false (sat? (helper2 #:inputs (list a b)
                               #:outputs (list (bvand a b))
                               #:intermediates 0
                               #:bw 3
                               #:gates 1
                               #:wires 1
                               #:iters 10)))
   (check-true (sat? (helper2 #:inputs (list a b)
                              #:outputs (list (bvand a b))
                              #:intermediates 0
                              #:bw 3
                              #:gates 2
                              #:wires 1
                              #:iters 10)))
   ;;; Or requires 2 gates and 1 wire.
   (check-true (sat? (helper2 #:inputs (list a b)
                              #:outputs (list (bvor a b))
                              #:intermediates 0
                              #:bw 3
                              #:gates 2
                              #:wires 1
                              #:iters 10)))
   (check-false (sat? (helper2 #:inputs (list a b)
                               #:outputs (list (bvor a b))
                               #:intermediates 0
                               #:bw 3
                               #:gates 1
                               #:wires 1
                               #:iters 10)))
   (check-false (sat? (helper2 #:inputs (list a b)
                               #:outputs (list (bvor a b))
                               #:intermediates 0
                               #:bw 3
                               #:gates 2
                               #:wires 0
                               #:iters 1)))
   ;;; Implementing two functions.
   (check-true (sat? (helper2 #:inputs (list a b c)
                              #:outputs (list (bvor a b) (bvand a c))
                              #:intermediates 0
                              #:bw 4
                              #:gates 4
                              #:wires 2
                              #:iters 5)))
   ;;; Implementing operations over multibit bitvectors.
   (check-true (sat? (helper2 #:inputs (list a-8 b-8)
                              #:outputs (list (bvand a-8 b-8))
                              #:intermediates 0
                              #:bw 6
                              #:gates 8
                              #:wires 0
                              #:iters 1)))))
