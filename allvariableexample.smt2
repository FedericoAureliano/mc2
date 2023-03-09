(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((MyList 0)) (((Nil) (Cons (Head Color) (Tail MyList)))))

(declare-const r Color)
(declare-const g Color)
(declare-const b Color)
(assert (= r red))
(assert (= g green))
(assert (= b blue))


(declare-const x MyList)
(declare-const y MyList)

(assert (and (is_Cons (Cons red Nil)) (is_Nil (Cons red Nil))))

; testing Axiom 1, i.e. that exactly one tester is true for each ADT

;(assert (not (is_Cons x)))
;(assert (and (is_Nil x) (is_Cons x)))


;testing Axiom 2 i.e. that testers and constructors play nicely(assuming Axiom 1)

;(assert (= x Nil))
;(assert (is_Cons x))

(assert (= y (Cons r Nil)))
;(assert (is_Nil y))


(check-sat)

;(assert (not (= y (Cons contrived_variable_8 contrived_variable_9))))
;(assert (not (= y (Cons contrived_variable_10 contrived_variable_11))))
;(assert (not (= y (Cons contrived_variable_12 contrived_variable_13))))
;(assert (not (= y (Cons contrived_variable_14 contrived_variable_15))))

;(check-sat)
