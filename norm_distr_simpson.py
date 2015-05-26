#!/usr/bin/python

import sys
import os

# constants
mean = 0.0
variance = 10.0
x_a = 0.9
x_b = 1.1

# functions
norm_distr = "(/ (exp (/ (^ (- {x} {mean}) 2) (* {variance} -2.0))) (^ (* {variance} (* 3.1415926 2.0)) 0.5))"

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
    (= P (* (/ (- {x_b} {x_a}) 6) (+ (+ {f_1} (* 4 {f_2})) {f_3})))
))
"""

f_1 = norm_distr.format(x = "x_a", mean = mean, variance = variance).strip()
f_2 = norm_distr.format(x = "(/ (+ x_a x_b) 2)", mean = mean, variance = variance).strip()
f_3 = norm_distr.format(x = "x_b", mean = mean, variance = variance).strip()

filename = "norm_distr_simpson.smt2"
fo = open(filename, "w")
fo.write("(set-logic QF_NRA_ODE)\n")
fo.write(var + "\n")
fo.write(formula.format(x_a = x_a, x_b = x_b, f_1 = f_1, f_2 = f_2, f_3 = f_3).strip() + "\n\n")
fo.write("(check-sat)\n(exit)")
fo.close()

