
; define 'Prelude.take' by axiomatization of rules:
(declare-fun Prelude_take (Int (List TVar)) (List TVar))

(assert (forall ((xs (List TVar)))
  (= (Prelude_take 0 xs) nil)))
(assert (forall ((n Int) (x TVar) (xs (List TVar)))
  (=> (> n 0)
      (= (Prelude_take n (insert x xs))
         (insert x (Prelude_take (- n 1) xs))))))

