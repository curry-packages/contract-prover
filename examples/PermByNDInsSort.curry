{-# OPTIONS_CYMAKE -Wno-overlapping #-}

-- Contract verification requires option "-s"

--- Non-deterministic list insertion
ins :: a -> [a] -> [a]
ins x ys     = x : ys
ins x (y:ys) = y : ins x ys

-- Postcondition on the length of the list.
ins'post :: a -> [a] -> [a] -> Bool
ins'post _ xs ys = length xs + 1 == length ys

--- Insertion sort with a non-deterministic insert operator.
--- This computes all permutations of the input list, see also
--- Christiansen, J. and Danilenko, N. and Dylus, S.:
--- All sorts of permutations (functional pearl), ICFP 2016,
--- DOI: 10.1145/2951913.2951949
insertionSort  :: [a] -> [a]
insertionSort []     = []
insertionSort (x:xs) = ins x (insertionSort xs)

-- Postcondition: input and output lists have same length.
insertionSort'post ::[a] -> [a] -> Bool
insertionSort'post xs ys = length xs == length ys

-- Compute all permutations of the list [1,2,3]:
main :: [Int]
main = insertionSort [1,2,3]
