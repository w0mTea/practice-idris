import Data.Vect

data SplitList : List a -> Type where
     SplitNil : SplitList []
     SplitOne : SplitList [x]
     SplitPair : (left : List a) -> (right : List a) -> SplitList (left ++ right)

total
splitList : (input : List a) -> SplitList input
splitList input = splitHelper input input
  where splitHelper : List a -> (input : List a) -> SplitList input
        splitHelper _ [] = SplitNil
        splitHelper _ [x] = SplitOne
        splitHelper (_ :: _ :: counter) (item :: items)
          = case splitHelper counter items of
                 SplitNil => SplitOne
                 SplitOne {x} => SplitPair [item] [x]
                 (SplitPair left right) => SplitPair (item :: left) right
        splitHelper _ input = SplitPair [] input

total
splitList1 : (input : List a) -> SplitList input
splitList1 input = splitHelper input input
  where splitHelper : List a -> (input : List a) -> SplitList input
        splitHelper _ [] = SplitNil
        splitHelper _ [x] = SplitOne
        splitHelper (_ :: _ :: counter) (item :: items)
          = case splitHelper counter items of
                 SplitNil => SplitOne
                 SplitOne {x} => SplitPair [item] [x]
                 (SplitPair left right) => SplitPair (item :: left) right
        splitHelper (_ :: counter) (item :: items) = SplitPair [item] items
        splitHelper _ input = SplitPair [] input

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (left ++ right) | (SplitPair left right) =
    let sLeft = mergeSort left
        sRight = mergeSort right
     in merge sLeft sRight 

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

total
takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = Exact []
takeN (S k) [] = Fewer
takeN (S k) (x :: xs) = case takeN k xs of
                             Fewer => Fewer
                             (Exact n_xs) => Exact (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs)
    = case rest of
           [] => [n_xs]
           _ => n_xs :: groupByN n rest

data SnocList : List a -> Type where
  Empty : SnocList []
  Snoc : (rec : SnocList xs) -> SnocList (xs ++ [x])

snocList : (xs : List a) -> SnocList xs
snocList xs = helper Empty xs
  where helper : {input : List a} -> (snoc : SnocList input) -> (rest : List a) ->
                 SnocList (input ++ rest)
        helper {input = input} snoc []
          = rewrite appendNilRightNeutral input in snoc
        helper {input = input} snoc (x :: ys)
          = rewrite appendAssociative input [x] ys in
            helper (Snoc snoc {x}) ys

myReverse : List a -> List a
myReverse xs = helper xs (snocList xs)
  where helper : (input : List a) -> (SnocList input) -> List a
        helper [] Empty = xs
        helper (ys ++ [x]) (Snoc rec) = x :: helper ys rec 

myReverse1 : List a -> List a
myReverse1 xs with (snocList xs)
  myReverse1 [] | Empty = []
  myReverse1 (ys ++ [x]) | (Snoc rec) = x :: myReverse1 ys | rec

isSuffix : Eq a => List a -> List a -> Bool
isSuffix input1 input2 with (snocList input1)
  isSuffix [] input2 | Empty = True
  isSuffix (xs ++ [x]) input2 | (Snoc rec1) with (snocList input2)
    isSuffix (xs ++ [x]) [] | (Snoc rec1) | Empty = False
    isSuffix (xs ++ [x]) (ys ++ [y]) | (Snoc rec1) | (Snoc rec2)
      = case x == y of
             False => False
             True => isSuffix xs ys | rec1 | rec2


