; Choice type to represent a "choice plan"
(declare-datatypes ()
   ((Choice (ChoiceLeaf (leaf-choose Bool))
            (ChoicePlan (plan-choose Bool) (plan-l Choice) (plan-r Choice)))))

; return the main choice of the plan:
(define-fun choose ((x Choice)) Bool
   (ite (is-ChoiceLeaf x)
        (leaf-choose x)
        (plan-choose x)))

; return the left choice plan of the plan:
(define-fun lchoice ((x Choice)) Choice
   (ite (is-ChoiceLeaf x) x (plan-l x)))

; return the right choice plan of the plan:
(define-fun rchoice ((x Choice)) Choice
   (ite (is-ChoiceLeaf x) x (plan-r x)))

