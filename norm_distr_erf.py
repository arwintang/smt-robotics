#!/usr/bin/python

import sys
import os

# constants
mean = 0.0
variance = 1.0
x_a = -10.0
x_b = 0.0

# functions
norm_distr = "(/ (exp (/ (^ (- {x} {mean}) 2) (* {variance} -2.0))) (^ (* {variance} (* 3.1415926 2.0)) 0.5))"
erf = "(/ (* 2 (+ (- (+ (- {z} (/ (^ {z} 3) 3)) (/ (^ {z} 5) 10)) (/ (^ {z} 7) 42)) (/ (^ {z} 9) 216))) (^ 3.1415926 0.5))"
std_norm_distr = "(/ (- {x} {mean}) (^ (* {variance} 2.0) 0.5))"

# variables
var = """
(declare-fun x_a () Real)
(declare-fun x_b () Real)
(declare-fun P () Real)
"""

# formula
formula = """
(assert (and 
    (= x_a {x_a})
    (= x_b {x_b})
    (>= P 0.0)
    (>= 1.0 P)
    (= P (- {F_b} {F_a}))
))
"""

F_a = "(/ (+ 1 " + erf.format(z = std_norm_distr.format(x = "x_a", mean = mean, variance = variance).strip()).strip() + ") 2)"
F_b = "(/ (+ 1 " + erf.format(z = std_norm_distr.format(x = "x_b", mean = mean, variance = variance).strip()).strip() + ") 2)"

filename = "norm_distr_erf.smt2"
fo = open(filename, "w")
fo.write("(set-logic QF_NRA_ODE)\n")
fo.write(var + "\n")
fo.write(formula.format(x_a = x_a, x_b = x_b, F_a = F_a, F_b = F_b).strip() + "\n\n")
fo.write("(check-sat)\n(exit)")
fo.close()
