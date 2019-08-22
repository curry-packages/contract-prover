
-- This program contains an example of a non-deterministic contract.
-- It also discussed options to model non-deterministic operations in SMT.

-- Consider the classical choice operation of Curry:
choice :: a -> a -> a
choice x _ = x
choice _ y = y

-- A non-deterministic precondition is satisfied if each non-deterministic
-- choice is satisfied, i.e., the precondition cannot reduce to `False`.
-- Hence, this precondition is not satisfied for `(f'pre 3 3)`!
f'pre :: Int -> Int -> Bool
f'pre x y = x > choice 2 4 || choice 2 4 > y

f :: Int -> Int -> Int
f x y = x + y

-- Due to this semantics, the precondition in this call cannot be eliminated.
h :: Int
h = f 3 3

{-

In a previous version of this tool, a non-deterministic operation
was modelled as a function in SMT with the axiomatization
that each of the different results could occur.
However, this translation is only valid if a choice occurs at most one.
In this example, the choice operation was translated into the following
(type-spezialized) definition:

    (declare-fun choice_Int (Int Int) Int)
    
    ; Axiomatization of function 'choice_Int'
    (assert
     (forall
      ((x1 Int) (x2 Int))
      (or (= (choice_Int x1 x2) x1) (= (choice_Int x1 x2) x2))))

Then the following assertions are unsatisfiable:

    ; Free variables:
    (declare-const x2 Int)
    (declare-const x1 Int)
    
    ; Bindings of implication:
    (assert (and (= x1 3) (= x2 3)))
    
    ; Assert negated implication:
    (assert (not (or (> x1 (choice_Int 2 4)) (> (choice_Int 2 4) x2))))

For both occurrences of choice_Int, either the left or the right
argument is returned. Thus, the precondition might be classified
as correct.

For a correct modelling, non-deterministically defined operations
are translated into deterministic ones by adding an additional
"choice plan" argument which determines the possible branches
to be taken. This approach is described in

    S. Antoy, M. Hanus, and S. Libby:
    _Proving non-deterministic computations in Agda_.
    In Proc. of the 24th International Workshop on Functional and
    (Constraint) Logic Programming (WFLP 2016),
    volume 234 of Electronic Proceedings in Theoretical Computer Science,
    pages 180--195. Open Publishing Association, 2017

and implemented in the module `FlatCurry.Typed.NonDet2Det`.
With this approach, the choice operation is translated into

    (declare-fun choice_Int (Choice Int Int) Int)
    
    ; Axiomatization of non-deterministic function 'choice_Int'
    (assert
     (forall
      ((c Choice) (x1 Int) (x2 Int))
      (= (choice_Int c x1 x2)
         (ite (choose c) x1 x2))))
      
and the proof obligation as follows (note that each call to
`choice_Int` has its own choice plan):

    ; Free variables:
    (declare-const ch1 Choice)
    (declare-const ch2 Choice)
    (declare-const x2 Int)
    (declare-const x1 Int)
    
    ; Bindings of implication:
    (assert (and (= x1 3) (= x2 3)))
    
    ; Assert negated implication:
    (assert
     (not (or (> x1 (choice_Int ch1 2 4))
              (> (choice_Int ch2 2 4) x2))))

Now, unsatisfiability means that there do not exist choice plans
for both choices. This is not provable so that the precondition
is not eliminated.

-}
