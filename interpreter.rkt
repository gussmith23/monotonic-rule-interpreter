#lang errortrace racket

(provide interpreter)

(require rosette)

;;; Returns the new state after applying all rules.
;;;
;;; state: A bitvector.
;;;
;;; rules: A list of rules. Rules take the form: (list ins outs). ins is a list of bitvectors, where
;;; the unsigned value of each bitvector indicates the index of a bit in the state bitvector that must
;;; be set to 1 for this rule to fire. outs is a list of bitvectors, where each bitvector indicates
;;; the index of a bit which will be set to 1 when this rule fires.
;;;
;;; iters: The number of iterations to run.
(define (interpreter state rules iters)
  (if (zero? iters) state (interpreter (apply-rules state rules) rules (sub1 iters))))

(module+ test
  (require rackunit)
  (define rws
    (list ;
     ;;; Turns on 1 given 3.
     (list (list (bv 3 2)) (list (bv 1 2)))
     ;;; Turns on 2 given 1 and 3.
     (list (list (bv 1 2) (bv 3 2)) (list (bv 2 2)))
     ;;; Turns on 0 given 1, 2, and 3.
     (list (list (bv 1 2) (bv 2 2) (bv 3 2)) (list (bv 0 2)))))

  (check-equal? (interpreter (bv #b0000 4) rws 0) (bv #b0000 4))
  (check-equal? (interpreter (bv #b0000 4) rws 1000) (bv #b0000 4))
  (check-equal? (interpreter (bv #b1000 4) rws 1) (bv #b1010 4))
  (check-equal? (interpreter (bv #b1000 4) rws 2) (bv #b1110 4))
  (check-equal? (interpreter (bv #b1000 4) rws 3) (bv #b1111 4))
  (check-equal? (interpreter (bv #b1000 4) rws 4) (bv #b1111 4))
  (check-equal? (interpreter (bv #b1000 4) rws 1000) (bv #b1111 4))
  (check-equal? (interpreter (bv #b0001 4) rws 1000) (bv #b0001 4)))

;;; Returns the new state after applying all rules.
(define (apply-rules state rules)
  (apply bvor state (map (lambda (rule) (apply-rule state rule)) rules)))

(module+ test
  (require rackunit)
  (check-equal?
   (apply-rules (bv #b1001 4)
                (list (list (list (bv 0 2)) (list (bv 1 2))) (list (list (bv 3 2)) (list (bv 2 2)))))
   (bv #b1111 4)))

;;; Returns the new state after applying a rule.
(define (apply-rule state rule)
  (match-let*
   ([state-bvlen (length (bitvector->bits state))]
    [(list rule-ins rule-outs) rule]
    ;;; Is idx turned on? Returns a one-bit bitvector.
    [enabled (lambda (idx) (bit 0 (bvlshr state (zero-extend idx (bitvector state-bvlen)))))]
    ;;; Are the required signals turned on? Returns a one-bit bitvector.
    ;;; We include the (bv 1 1) so that we default to true in the case that rules-in is empty.
    [ins-present (apply bvand (bv 1 1) (map enabled rule-ins))]
    ;;; Makes a new bitvector of the same length as `state`, where the bit for idx is on if the rule
    ;;; fired, and off otherwise. All other bits are off.
    [make-new-state-for-idx
     (lambda (idx)
       (bvshl (zero-extend ins-present (bitvector state-bvlen))
              (zero-extend idx (bitvector state-bvlen))))]
    [new-state (apply bvor state (map make-new-state-for-idx rule-outs))])
   new-state))

(module+ test
  (require rackunit)

  (check-equal? (apply-rule (bv #b0 1) (list (list) (list (bv 0 1)))) (bv #b1 1))
  (check-equal? (apply-rule (bv #b1 1) (list (list) (list (bv 0 1)))) (bv #b1 1))
  (check-equal? (apply-rule (bv #b1 1) (list (list) (list))) (bv #b1 1))
  (check-equal? (apply-rule (bv #b0 1) (list (list) (list))) (bv #b0 1))

  (check-equal? (apply-rule (bv #b0000 4) (list (list (bv 0 2)) (list (bv 1 2)))) (bv #b0000 4))
  (check-equal? (apply-rule (bv #b0001 4) (list (list (bv 0 2)) (list (bv 1 2)))) (bv #b0011 4))
  (check-equal? (apply-rule (bv #b0001 4) (list (list (bv 0 2) (bv 1 2)) (list (bv 1 2))))
                (bv #b0001 4))
  (check-equal? (apply-rule (bv #b1001 4) (list (list (bv 0 2) (bv 3 2)) (list (bv 1 2))))
                (bv #b1011 4))
  (check-equal? (apply-rule (bv #b1001 4) (list (list (bv 0 2) (bv 3 2) (bv 2 2)) (list (bv 1 2))))
                (bv #b1001 4))
  (check-equal? (apply-rule (bv #b1101 4) (list (list (bv 0 2) (bv 3 2) (bv 2 2)) (list (bv 1 2))))
                (bv #b1111 4)))
