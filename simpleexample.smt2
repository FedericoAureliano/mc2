
(declare-datatypes (( Color 0)) (((red) (green) (blue))))
(declare-datatypes ((MyList 0)) (((Nil) (Cons (Head Real) (Tail MyList)))))

(declare-const real_test Real)
(declare-const bool_test Bool)
(declare-const rational_test Rational)

;(declare-const list_test List)
;(declare-const array_test Array)




(declare-const x MyList)

(assert (= green blue))

;(assert (is_green green))
;(assert (is_blue green))
;(assert (is_green blue))
;(assert (is_blue blue))
;(assert (is_red blue))


;(assert (is_Nil Nil))
;(assert (is_Cons (Cons 1 Nil)))

(assert (= 7 (Head (Tail (Cons 1 Nil)))))
(assert (= (Tail (Cons 2 Nil)) Nil))
(assert (= Nil (Tail Nil)))
(assert (= 7 (Head (Tail (Tail (Cons 1 Nil))))))
(assert (not (= 7 (Head (Tail (Tail (Tail (Cons 1 Nil))))))))


(declare-sort silly_sort 0)
(declare-const billy silly_sort)
(declare-const hilly silly_sort)

(declare-sort another_sort 0)
(declare-const thing_one another_sort)
(declare-const thing_two another_sort)


;(assert (= 1 (Head (Cons 1 Nil))))

;(assert (= (Cons 1 Nil) (Cons 2 Nil)))

;(assert (= 1 1))


(check-sat)