(declare-fun clock (Int) Int)
(declare-fun gap_1 (Int) Int)
(declare-fun gap_2 (Int) Int)
(declare-fun gap_3 (Int) Int)
(declare-fun l () Int)
(declare-fun k () Int)
(declare-fun t () Int)
(declare-fun m () Int)
(assert (<= k 50))
(assert (>= m 0))

(assert (forall ((x Int)) (=> (and (> x 0)  (<= x k)) (= (clock (+ x 1)) (+ (clock x) 1)))))
(assert (forall ((x Int)) (=> (and (> x 0)  (<= x k)) (>= (gap_1 x) 0))))
(assert (forall ((x Int)) (=> (and (> x 0)  (<= x k)) (>= (gap_2 x) 0))))
(assert (forall ((x Int)) (=> (and (> x 0)  (<= x k)) (>= (gap_3 x) 0))))

(assert (and (> l 0) (<= l k)))
(assert (= (clock 1) 1))

(assert (= (gap_1 (clock 1)) 4))
(assert (= (gap_2 (clock 1)) 0))
(assert (= (gap_3 (clock 1)) 5))

(assert (forall ((x Int)) (=> (and (> x 0)  (<= x k)) (= t (+ (gap_1 (clock x)) (+ (gap_2 (clock x)) (gap_3 (clock x))))))))

(assert 
   (
     forall ((x Int))
      (=> 
        (and 
         (and (> x 0) (<= x k)) 
         (and (>= (gap_1 (clock x)) 4) 
              (and (= (gap_2 (clock x)) 0) 
                   (> (gap_3 (clock x)) (gap_1 (clock x)))
              )
         )
        )
        (and (= (gap_1 (clock (+ x 1))) (- (gap_1 (clock x)) 1))
             (and (= (gap_2 (clock (+ x 1))) (gap_2 (clock x)))
                  (= (gap_3 (clock (+ x 1))) (+ (gap_3 (clock x)) 1))
             )
        )
      )
   )
 )

(assert (= (gap_1 l) 3))
(assert (= (gap_2 l) 0))
(assert (= (gap_3 l) m))

(check-sat)
(get-value (l))
(get-value (k))
(get-value (t))
(get-model)