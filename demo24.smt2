;upper_bound
(declare-fun smt_upper_bound () Int)
(assert (= smt_upper_bound 5))
;gaps
(declare-fun gap_1 (Int Int) Int)
(declare-fun gap_2 (Int Int) Int)
(declare-fun gap_3 (Int Int) Int)
(assert (forall ((x Int) (y Int)) (=> (and (and (> x 0) (<= x smt_upper_bound)) (and (>= y 1) (<= y 3))) (>= (gap_1 x y) 0))))
(assert (forall ((x Int) (y Int)) (=> (and (and (> x 0) (<= x smt_upper_bound)) (and (>= y 1) (<= y 3))) (>= (gap_2 x y) 0))))
(assert (forall ((x Int) (y Int)) (=> (and (and (> x 0) (<= x smt_upper_bound)) (and (>= y 1) (<= y 3))) (>= (gap_3 x y) 0))))
;clock
(declare-fun clock (Int) Int) 
(assert (= (clock 1) 1))
(assert (forall ((x Int)) (=> (and (> x 0)  (<= x smt_upper_bound)) (= (clock (+ x 1)) (+ (clock x) 1)))))
;sat point
(declare-fun sat_point_x () Int)
(declare-fun sat_point_y () Int)
(assert (and (> sat_point_x 0) (<= sat_point_x smt_upper_bound)))
(assert (and (>= sat_point_y 1) (<= sat_point_y 3)))
;initial state
(assert (= (gap_1 (clock 1) 1) 4))
(assert (= (gap_2 (clock 1) 1) 5))
(assert (= (gap_3 (clock 1) 1) 4))
;total robot&Node count
(declare-fun node_count () Int)
(declare-fun gap_node_count () Int)
(assert (>= node_count 10))
(assert (= gap_node_count (- node_count 3)))
(assert (forall ((x Int) (y Int)) (=> (and (and (> x 0) (<= x smt_upper_bound)) (and (>= y 1) (<= y 3))) (= gap_node_count (+ (gap_1 (clock x) y) (+ (gap_2 (clock x) y) (gap_3 (clock x) y)))))))
;trans-situation
(assert (forall ((x Int)) (=> (and (> x 0) (<= x smt_upper_bound)) (and (and (= (gap_1 (clock x) 2) (gap_2 (clock x) 1)) (and (= (gap_2 (clock x) 2) (gap_3 (clock x) 1)) (= (gap_3 (clock x) 2) (gap_1 (clock x) 1)))) (and (and (= (gap_1 (clock x) 3) (gap_3 (clock x) 1)) (and (= (gap_2 (clock x) 3) (gap_1 (clock x) 1)) (= (gap_3 (clock x) 3) (gap_2 (clock x) 1)))))))))
;RC1
(assert 
   (
     forall ((x Int) (y Int))
      (=> 
        (and 
         (and (and (> x 0) (<= x smt_upper_bound)) (and (>= y 1) (<= y 3))) 
         (and (>= (gap_1 (clock x) y) 4) 
              (and (= (gap_2 (clock x) y) 0) 
                   (> (gap_3 (clock x) y) (gap_1 (clock x) y))
              )
         )
        )
        (and (= (gap_1 (clock (+ x 1)) 1) (- (gap_1 (clock x) y) 1))
             (and (= (gap_2 (clock (+ x 1)) 1) (gap_2 (clock x) y))
                  (= (gap_3 (clock (+ x 1)) 1) (+ (gap_3 (clock x) y) 1))
             )
        )
      )
    )
)

 ;RC2
(assert (forall ((x Int) (y Int)) 
           (=> (and (and (and (> x 0) (<= x smt_upper_bound)) (and (>= y 1) (<= y 3)))
                    (and (and (> (gap_1 (clock x) y) 0)
                           (distinct (gap_1 (clock x) y) (gap_2 (clock x) y))
                         )
                         (= (gap_1 (clock x) y) (gap_3 (clock x) y))
                    )
               )
               (xor (and (= (gap_1 (clock (+ x 1)) 1) (- (gap_1 (clock x) y) 1)) 
                         (and (= (gap_3 (clock (+ x 1)) 1) (+ (gap_3 (clock x) y) 1)) 
                              (= (gap_2 (clock (+ x 1)) 1) (gap_2 (clock x) y))
                         )
                    )
                    (and (= (gap_1 (clock (+ x 1)) 1) (+ (gap_1 (clock x) y) 1)) 
                         (and (= (gap_3 (clock (+ x 1)) 1) (- (gap_3 (clock x) y) 1)) 
                              (= (gap_2 (clock (+ x 1)) 1) (gap_2 (clock x) y))
                         )
                    )                                               
               )           
           )
        )
)



;test
(declare-fun l () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun l1 () Int)
(declare-fun m1 () Int)
(declare-fun n1 () Int)
(assert (= (gap_1 (clock sat_point_x) sat_point_y) 3))
(assert (= (gap_2 (clock sat_point_x) sat_point_y) 5))
(assert (= (gap_3 (clock sat_point_x) sat_point_y) 5))
(check-sat)
(get-value (sat_point_x))
(get-value (sat_point_y))
(get-value ((gap_1 (clock sat_point_x) sat_point_y)))
(get-value ((gap_2 (clock sat_point_x) sat_point_y)))
(get-value ((gap_3 (clock sat_point_x) sat_point_y)))
(get-value ((gap_1 (clock sat_point_x) 1)))
(get-value ((gap_2 (clock sat_point_x) 1)))
(get-value ((gap_3 (clock sat_point_x) 1)))


(get-model)