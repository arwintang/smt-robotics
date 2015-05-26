(set-logic QF_NRA_ODE)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun P () Real)

(declare-fun x_0 () Real)
(declare-fun x_t () Real)

(declare-fun y_0 () Real)
(declare-fun y_t () Real)

(declare-fun P_0 () Real)
(declare-fun P_t () Real)

(declare-fun time_0 () Real)

(define-ode flow_1 (
(= d/dt[x] 1.0) 
(= d/dt[y] 1.0)
(= d/dt[P] (* (/ 0.5 (* (* 3.141592653 (^ 2 0.5)) (^ 0.75 0.5))) (exp (* (/ -0.5 0.75) (- (+ (/ (^ x 2) 1) (/ (^ (- y 1) 2) 2)) (/ x (/ (- y 1) (^ 2 0.5))))))))
))

(assert (<= -100.0 x_0))
(assert (<= x_0 100.0))

(assert (<= -100.0 x_t))
(assert (<= x_t 100.0))

(assert (<= -100.0 y_0))
(assert (<= y_0 100.0))

(assert (<= -100.0 y_t))
(assert (<= y_t 100.0))

(assert (<= 0.0 P_0))
(assert (<= P_0 1.0))

(assert (<= 0.0 P_t))
(assert (<= P_t 1.0))

(assert (<= 0.0 time_0))
(assert (<= time_0 40.0))

(assert (and
                (= x_0 -2.0)
				(= y_0 1.0)
                (= P_0 0.0)
                (= x_t 2.0)
				(= y_t 10.0)
                (= [x_t y_t P_t] (integral 0. time_0 [x_0 y_0 P_0] flow_1))
))

(check-sat)
(exit)