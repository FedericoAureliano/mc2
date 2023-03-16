(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((MyList 0)) (((Nil) (Cons (Head Real) (Tail MyList)))))



(declare-const real_test Real)
(declare-const bool_test Bool)

(assert (= green blue))

(check-sat)