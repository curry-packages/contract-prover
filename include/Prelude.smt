; disable model-based quantifier instantiation (avoid loops)
(set-option :smt.mbqi false)

; For polymorphic types:
(declare-sort TVar 0)

; For functional types:
(declare-datatypes (T1 T2) ((Func (mk-func (argument T1) (result T2)))))

