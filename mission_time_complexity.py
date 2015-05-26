#!/usr/bin/python

import sys
import os
import time

# constants
# pi = 3.141592653589793
# e = 2.718281828459045
timeout = 50
time_step = 1
speed = 300.0
small_speed = 0.01
drop_off = 2000.0
satu_radius = 100.0
goal_tol = 500.0

# calibrated velocity
cal_vel_mean = (300.0, 300.0)
cal_vel_var = (0.0, 0.0, 0.0, 0.0)
cal_vel = (cal_vel_mean, cal_vel_var)

# translational uncertainty
tran_unc_mean = (-5.1435, 2.223)
tran_unc_var = (8.228, 0.0, 0.0, 862.855)
tran_unc = (tran_unc_mean, tran_unc_var)

# initial position distribution
pos_0_mean = (5500.0, 5000.0)
pos_0_var = (500.0, 0.0, 0.0, 500.0)
pos_0 = (pos_0_mean, pos_0_var)

# goal position (18000.0, 5000.0)
# pos_goal = (17500.0, 5000.0)
pos_goal = (7500.0, 5000.0)
prob_range = 150.0
prob_threshold = 0.8

# functions
norm_dist = "(/ (exp (/ (^ (- {x} {mu}) 2) (* {sigma} -2))) (sqrt (* {sigma} (* 3.1415926 2))))"

# flow variables
flow_var = """
(declare-fun pos_{0}_mean_x () Real)
(declare-fun pos_{0}_mean_y () Real)
(declare-fun pos_{0}_var_xx () Real)
(declare-fun pos_{0}_var_xy () Real)
(declare-fun pos_{0}_var_yx () Real)
(declare-fun pos_{0}_var_yy () Real)
(declare-fun speed_{0} () Real)
(declare-fun prob_{0} () Real)
"""

# Initial conditions
init_cond = """
(assert (= pos_0_mean_x {pos_0_mean_x}))
(assert (= pos_0_mean_y {pos_0_mean_y}))
(assert (= pos_0_var_xx {pos_0_var_xx}))
(assert (= pos_0_var_xy {pos_0_var_xy}))
(assert (= pos_0_var_yx {pos_0_var_yx}))
(assert (= pos_0_var_yy {pos_0_var_yy}))
(assert (ite (> (sqrt (+ (^ (- pos_0_mean_x {pos_goal_x}) 2) (^ (- pos_0_mean_y {pos_goal_y}) 2))) {drop_off}) (= speed_0 {speed}) (ite (< (sqrt (+ (^ (- pos_0_mean_x {pos_goal_x}) 2) (^ (- pos_0_mean_y {pos_goal_y}) 2))) {satu_radius}) (= speed_0 {small_speed}) (= speed_0 (/ (* {speed} (+ (sqrt (+ (^ (- pos_0_mean_x {pos_goal_x}) 2) (^ (- pos_0_mean_y {pos_goal_y}) 2))) {goal_tol})) (+ {drop_off} {goal_tol}))))))
"""

prob_a_x = norm_dist.format(x = "(- {pos_goal_x} {prob_range})", mu = "pos_0_mean_x", sigma = "pos_0_var_xx").strip()
prob_b_x = norm_dist.format(x = "(+ {pos_goal_x} {prob_range})", mu = "pos_0_mean_x", sigma = "pos_0_var_xx").strip()
prob_c_x = norm_dist.format(x = "{pos_goal_x}", mu = "pos_0_mean_x", sigma = "pos_0_var_xx").strip()
prob_a_y = norm_dist.format(x = "(- {pos_goal_y} {prob_range})", mu = "pos_0_mean_y", sigma = "pos_0_var_yy").strip()
prob_b_y = norm_dist.format(x = "(+ {pos_goal_y} {prob_range})", mu = "pos_0_mean_y", sigma = "pos_0_var_yy").strip()
prob_c_y = norm_dist.format(x = "{pos_goal_y}", mu = "pos_0_mean_y", sigma = "pos_0_var_yy").strip()

prob_init_cond = "(assert (= prob_0 (* (* (+ (/ (+ " + prob_a_x + " " + prob_b_x + ") 2) " + prob_c_x + ") {prob_range}) (* (+ (/ (+ " + prob_a_y + " " + prob_b_y + ") 2) " + prob_c_y + ") {prob_range}))))"

flow_cond = """
(assert (= pos_{1}_mean_x (+ (+ pos_{0}_mean_x (* speed_{0} (/ (- {pos_goal_x} pos_{0}_mean_x) (sqrt (+ (^ (- pos_{0}_mean_x {pos_goal_x}) 2) (^ (- pos_{0}_mean_y {pos_goal_y}) 2)))))) (* {tran_unc_mean_x} (/ speed_{0} {cal_vel_mean_x})))))
(assert (= pos_{1}_mean_y (+ (+ pos_{0}_mean_y (* speed_{0} (/ (- {pos_goal_y} pos_{0}_mean_y) (sqrt (+ (^ (- pos_{0}_mean_x {pos_goal_x}) 2) (^ (- pos_{0}_mean_y {pos_goal_y}) 2)))))) (* {tran_unc_mean_y} (/ speed_{0} {cal_vel_mean_y})))))
(assert (= pos_{1}_var_xx (+ pos_{0}_var_xx {tran_unc_var_xx})))
(assert (= pos_{1}_var_xy (+ pos_{0}_var_xy {tran_unc_var_xy})))
(assert (= pos_{1}_var_yx (+ pos_{0}_var_yx {tran_unc_var_yx})))
(assert (= pos_{1}_var_yy (+ pos_{0}_var_yy {tran_unc_var_yy})))
(assert (ite (> (sqrt (+ (^ (- pos_{1}_mean_x {pos_goal_x}) 2) (^ (- pos_{1}_mean_y {pos_goal_y}) 2))) {drop_off}) (= speed_{1} {speed}) (ite (< (sqrt (+ (^ (- pos_{1}_mean_x {pos_goal_x}) 2) (^ (- pos_{1}_mean_y {pos_goal_y}) 2))) {satu_radius}) (= speed_{1} {small_speed}) (= speed_{1} (/ (* {speed} (+ (sqrt (+ (^ (- pos_{1}_mean_x {pos_goal_x}) 2) (^ (- pos_{1}_mean_y {pos_goal_y}) 2))) {goal_tol})) (+ {drop_off} {goal_tol}))))))
"""

prob_a_x_flow = norm_dist.format(x = "(- {pos_goal_x} {prob_range})", mu = "pos_{1}_mean_x", sigma = "pos_{1}_var_xx").strip()
prob_b_x_flow = norm_dist.format(x = "(+ {pos_goal_x} {prob_range})", mu = "pos_{1}_mean_x", sigma = "pos_{1}_var_xx").strip()
prob_c_x_flow = norm_dist.format(x = "{pos_goal_x}", mu = "pos_{1}_mean_x", sigma = "pos_{1}_var_xx").strip()
prob_a_y_flow = norm_dist.format(x = "(- {pos_goal_y} {prob_range})", mu = "pos_{1}_mean_y", sigma = "pos_{1}_var_yy").strip()
prob_b_y_flow = norm_dist.format(x = "(+ {pos_goal_y} {prob_range})", mu = "pos_{1}_mean_y", sigma = "pos_{1}_var_yy").strip()
prob_c_y_flow = norm_dist.format(x = "{pos_goal_y}", mu = "pos_{1}_mean_y", sigma = "pos_{1}_var_yy").strip()

prob_flow_cond = "(assert (= prob_{1} (+ prob_{0} (* (* {prob_range} (+ " + prob_c_x_flow + " (/ (+ " + prob_a_x_flow + " " + prob_b_x_flow + ") 2))) (* {prob_range} (+ " + prob_c_y_flow + " (/ (+ " + prob_a_y_flow + " " + prob_b_y_flow + ") 2)))))))"

# Goal conditions
goal_cond = "(assert (>= prob_{0} {prob_threshold}))"

filename = "success1_{0}.smt2"
for mytime in range(timeout + 1):
    start = time.time()
    fo = open("mission_time_complexity.smt2", "w")
    fo.write("(set-logic QF_NRA)\n\n")
    fo.write("(set-info :precision 0.001)\n\n")
    
    for i in range(mytime + 1):
        fo.write(flow_var.format(i).strip() + "\n\n")
    
    fo.write(init_cond.format(pos_0_mean_x = pos_0_mean[0], pos_0_mean_y = pos_0_mean[1], pos_0_var_xx = pos_0_var[0], pos_0_var_xy = pos_0_var[1], pos_0_var_yx = pos_0_var[2], pos_0_var_yy = pos_0_var[3], pos_goal_x = pos_goal[0], pos_goal_y = pos_goal[1], drop_off = drop_off, speed = speed, satu_radius = satu_radius, small_speed = small_speed, goal_tol = goal_tol, tran_unc_mean_x = tran_unc_mean[0], tran_unc_mean_y = tran_unc_mean[1], cal_vel_mean_x = cal_vel_mean[0], cal_vel_mean_y = cal_vel_mean[1]).strip() + "\n\n")
    fo.write(prob_init_cond.format(pos_goal_x = pos_goal[0], pos_goal_y = pos_goal[1], prob_range = prob_range).strip() + "\n\n")
    
    for i in range(mytime):
        fo.write(flow_cond.format(i, i+1, pos_goal_x = pos_goal[0], pos_goal_y = pos_goal[1], drop_off = drop_off, speed = speed, satu_radius = satu_radius, small_speed = small_speed, goal_tol = goal_tol, tran_unc_mean_x = tran_unc_mean[0], tran_unc_mean_y = tran_unc_mean[1], cal_vel_mean_x = cal_vel_mean[0], cal_vel_mean_y = cal_vel_mean[1], tran_unc_var_xx = tran_unc_var[0], tran_unc_var_xy = tran_unc_var[1], tran_unc_var_yx = tran_unc_var[2], tran_unc_var_yy = tran_unc_var[3]).strip() + "\n\n")
        fo.write(prob_flow_cond.format(i, i+1, pos_goal_x = pos_goal[0], pos_goal_y = pos_goal[1], prob_range = prob_range).strip() + "\n\n")
            
    fo.write(goal_cond.format(mytime, prob_threshold = prob_threshold).strip() + "\n\n")
    
    fo.write("(check-sat)\n(exit)")
    
    fo.close()
    
    #results = os.popen('./dReal --verbose ' + fo.name).readlines()
    results = os.popen('./dReal ' + fo.name).readlines()
    print ("Time " + str(mytime) + ": " + results[0].strip("\n"))
    if results[0] == "sat\n":
        os.system('cp ' + fo.name + ' ' + filename.format(mytime))
        end = time.time()
        print end - start
        break
        
    end = time.time()
    print end - start
    
    
    