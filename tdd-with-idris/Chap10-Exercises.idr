import Data.List.Views
import Data.Vect
import Data.Vect.Views
import Data.Nat.Views

-- Exercises for 10.2.4
--- 1
equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys = helper xs ys []
  where helper : Eq a => List a -> List a -> List a -> List a
        helper input1 input2 result with (snocList input1)
          helper [] input2 result | Empty = result
          helper (xs ++ [x]) input2 result | (Snoc rec1) with (snocList input2)
            helper (xs ++ [x]) [] result | (Snoc rec1) | Empty = result
            helper (xs ++ [x]) (ys ++ [y]) result | (Snoc rec1) | (Snoc rec2)
              = if x == y then helper xs ys (x :: result) | rec1 | rec2
                          else result

--- 2
mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec)
    = (mergeSort ys | lrec) ++ (mergeSort zs | rrec)

--- 3
toBinary : Nat -> String
toBinary Z = "0"
toBinary n = helper n
  where helper : Nat -> String
        helper k with (halfRec k)
          helper Z | HalfRecZ = ""
          helper (x + x) | (HalfRecEven rec) = (helper x | rec) ++ "0"
          helper (S (x + x)) | (HalfRecOdd rec) = (helper x | rec) ++ "1"

--- 4
palindrome : Eq a => List a -> Bool
palindrome xs with (vList xs)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (ys ++ [y])) | (VCons rec)
    = if x == y then palindrome ys | rec
                else False

