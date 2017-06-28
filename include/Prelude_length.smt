; define 'Prelude.length' by axiomatization of rules:
(declare-fun Prelude_length ((List TVar)) Int)

(assert
  (= (Prelude_length nil)
     0))
(assert (forall ((x TVar) (xs (List TVar)))
  (= (Prelude_length (insert x xs))
     (+ 1 (Prelude_length xs)))))

