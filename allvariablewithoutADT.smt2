(declare-sort MyList 0)
(declare-sort Element 0)

(declare-fun Nil () MyList)
(declare-fun Cons (Element MyList) MyList)
(declare-fun head (MyList) Element)
(declare-fun tail (MyList) MyList)
(declare-fun is_Nil (MyList) Bool)
(declare-fun is_Cons (MyList) Bool)

(declare-fun One () Element)
(declare-fun Two () Element)
(declare-fun Three () Element)

(declare-fun x () MyList)
(declare-fun y () MyList)
(declare-fun z () MyList)

(declare-fun a () Element)

(assert (or (and (is_Cons x) (not (is_Nil x))) (and (is_Nil x) (not (is_Cons x)))))
(assert (or (and (is_Cons y) (not (is_Nil x))) (and (is_Nil y) (not (is_Cons y)))))
(assert (or (and (is_Cons z) (not (is_Nil x))) (and (is_Nil z) (not (is_Cons z)))))

(declare-fun contrived_variable_1 () Element)
(declare-fun contrived_variable_2 () MyList)
(declare-fun contrived_variable_3 () MyList)

(assert (= (is_Cons x) (= (Cons contrived_variable_1 contrived_variable_2) x)))
(assert (= (is_Nil x) (= Nil x)))

;(assert (= x (Cons a Nil)))
(assert (= x (Cons a y)))
(assert (is_Nil y))


(check-sat)