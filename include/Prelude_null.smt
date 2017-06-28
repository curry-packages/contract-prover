; define 'Prelude.null' by axiomatization of rules:
(declare-fun Prelude_null ((List TVar)) Bool)

(assert (= (Prelude_null nil)  true))
(assert (forall ((x TVar) (xs (List TVar)))
  (= (Prelude_null (insert x xs)) false)))


