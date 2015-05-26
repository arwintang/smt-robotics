(set-logic QF_NRA_ODE)

(declare-fun x_a () Real)
(declare-fun x_b () Real)
(declare-fun P () Real)

(assert (and 
    (= x_a -10.0)
    (= x_b 0.0)
    (>= P 0.0)
    (>= 1.0 P)
    (= P (- (/ (+ 1 (/ (+ (- (+ (- (/ (- x_b 0.0) (^ (* 1.0 2.0) 0.5)) (/ (^ (/ (- x_b 0.0) (^ (* 1.0 2.0) 0.5)) 3) 3)) (/ (^ (/ (- x_b 0.0) (^ (* 1.0 2.0) 0.5)) 5) 10)) (/ (^ (/ (- x_b 0.0) (^ (* 1.0 2.0) 0.5)) 7) 42)) (/ (^ (/ (- x_b 0.0) (^ (* 1.0 2.0) 0.5)) 9) 216)) (^ 3.1415926 0.5))) 2) (/ (+ 1 (/ (+ (- (+ (- (/ (- x_a 0.0) (^ (* 1.0 2.0) 0.5)) (/ (^ (/ (- x_a 0.0) (^ (* 1.0 2.0) 0.5)) 3) 3)) (/ (^ (/ (- x_a 0.0) (^ (* 1.0 2.0) 0.5)) 5) 10)) (/ (^ (/ (- x_a 0.0) (^ (* 1.0 2.0) 0.5)) 7) 42)) (/ (^ (/ (- x_a 0.0) (^ (* 1.0 2.0) 0.5)) 9) 216)) (^ 3.1415926 0.5))) 2)))
))

(check-sat)
(exit)