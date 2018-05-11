module DataStructure.FingerTree

import Data.Vect
import Proofs.Nat
import DataStructure.Measured

%default total
%access export


public export
data Node v a = Node2 v a a | Node3 v a a a


(Measured a v) => Measured (Node v a) v where
  measure (Node2 v _ _) = v
  measure (Node3 v _ _ _) = v


||| Calculate measurement and create a Node2 node
node2 : (Measured a v) => a -> a -> Node v a
node2 x y = Node2 (measure x <+> measure y) x y


||| Calculate measurement and create a Node3 node
node3 : (Measured a v) => a -> a -> a -> Node v a
node3 x y z = Node3 (measure x <+> measure y <+> measure z) x y z


public export
data Digit a = One a | Two a a | Three a a a | Four a a a a


(Measured a v) => Measured (Digit a) v where
  measure (One x) = measure x
  measure (Two x y) = measure x <+> measure y
  measure (Three x y z) = measure x <+> measure y <+> measure z
  measure (Four x y z w) = measure x <+> measure y <+> measure z <+> measure w


||| Satisfiable if the digit is not full
public export
data DigitIsNotFull : Digit a -> Type where
  IsOne : DigitIsNotFull (One _)
  IsTwo : DigitIsNotFull (Two _ _)
  IsThree : DigitIsNotFull (Three _ _ _)


Uninhabited (DigitIsNotFull (Four _ _ _ _)) where
  uninhabited IsOne impossible
  uninhabited IsTwo impossible
  uninhabited IsThree impossible


public export
data FingerTree v a = Empty
                    | Single a
                    | Deep v (Digit a) (FingerTree v (Node v a)) (Digit a)


(Measured a v) => Measured (FingerTree v a) v where
  measure Empty = neutral
  measure (Single x) = measure x
  measure (Deep v ld subtree rd) = v


||| Calculate measurement and create a deep finger tree
deep : (Measured a v) => Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
deep ld subtree rd = Deep (measure ld <+> measure subtree <+> measure rd) ld subtree rd


||| Satisfiable if the finger tree is non-empty
public export
data FingerTreeIsNonEmpty : FingerTree v a -> Type where
     IsSingle : FingerTreeIsNonEmpty (Single x)
     IsDeep : FingerTreeIsNonEmpty (Deep v ld subtree rd)


Uninhabited (FingerTreeIsNonEmpty Empty) where
  uninhabited IsSingle impossible
  uninhabited IsDeep impossible


namespace Digit
  ||| Convert a digit into a finger tree
  toTree : (Measured a v) => Digit a -> FingerTree v a
  toTree (One x) = Single x
  toTree (Two x y) = Deep (measure x <+> measure y) (One x) Empty (One y)
  toTree (Three x y z) = Deep (measure x <+> measure y <+> measure z) (Two x y) Empty (One z)
  toTree (Four x y z w) = Deep (measure x <+> measure y <+> measure z <+> measure w) (Two x y) Empty (Two z w)


  ||| Convert a digit into a list
  toList : Digit a -> List a
  toList (One x) = [x]
  toList (Two x y) = [x, y]
  toList (Three x y z) = [x, y, z]
  toList (Four x y z w) = [x, y, z, w]


  ||| Count of elements in a digit
  length : Digit a -> Nat
  length (One _) = 1
  length (Two _ _) = 2
  length (Three _ _ _) = 3
  length (Four _ _ _ _) = 4


  ||| Convert a digit into a Vect
  toVect : (d : Digit a) -> Vect (length d) a
  toVect (One x) = [x]
  toVect (Two x y) = [x, y]
  toVect (Three x y z) = [x, y, z]
  toVect (Four x y z w) = [x, y, z, w]


  ||| Proof that a digit contains at least one element
  public export
  digitHasAtLeastOneElem : (d : Digit a) -> ((S Z) `LTE` length d)
  digitHasAtLeastOneElem (One x) = LTESucc LTEZero
  digitHasAtLeastOneElem (Two x y) = LTESucc LTEZero
  digitHasAtLeastOneElem (Three x y z) = LTESucc LTEZero
  digitHasAtLeastOneElem (Four x y z w) = LTESucc LTEZero


  ||| Get the first element of the digit
  head : Digit a -> a
  head (One x) = x
  head (Two x y) = x
  head (Three x y z) = x
  head (Four x y z w) = x


  ||| Get the last elemment of the digit
  last : Digit a -> a
  last (One x) = x
  last (Two x y) = y
  last (Three x y z) = z
  last (Four x y z w) = w


  ||| Append an element into a digit
  ||| @ prf proof that the digit is not full
  append : (d : Digit a) -> a -> {auto prf : DigitIsNotFull d} -> Digit a
  append (One y) x {prf = IsOne} = Two y x
  append (Two y z) x {prf = IsTwo} = Three y z x
  append (Three y z w) x {prf = IsThree} = Four y z w x


  ||| Add an element into the front of digit
  ||| @ prf proof that the digit is not full
  cons : (x : a) -> (d : Digit a) -> {auto prf : DigitIsNotFull d} -> Digit a
  cons x (One y) {prf = IsOne} = Two x y
  cons x (Two y z) {prf = IsTwo} = Three x y z
  cons x (Three y z w) {prf = IsThree} = Four x y z w


namespace Node
  ||| Convert a node into a digit
  toDigit : Node v a -> Digit a
  toDigit (Node2 _ x y) = Two x y
  toDigit (Node3 _ x y z) = Three x y z


  ||| Convert a node into a list
  toList : Node v a -> List a
  toList (Node2 _ x y) = [x, y]
  toList (Node3 _ x y z) = [x, y, z]


  ||| Get the first element of the node
  head : Node v a -> a
  head (Node2 _ x y) = x
  head (Node3 _ x y z) = x


  ||| Get the last element of the node
  last : Node v a -> a
  last (Node2 _ x y) = y
  last (Node3 _ x y z) = z


infixr 5 <|
||| Push an element into the front of a finger tree
(<|) : (Measured a v) => a -> FingerTree v a -> FingerTree v a
(<|) x Empty = Single x
(<|) x (Single y) = deep (One x) Empty (One y)
(<|) x (Deep _ (Four y z w s) subtree digit) = deep (Two x y) ((node3 z w s) <| subtree) digit
(<|) x (Deep _ ld@(One _) subtree digit) = deep (cons x ld) subtree digit
(<|) x (Deep _ ld@(Two _ _) subtree digit) = deep (cons x ld) subtree digit
(<|) x (Deep _ ld@(Three _ _ _) subtree digit) = deep (cons x ld) subtree digit


infixl 5 |>
||| Push an element into the back of a finger tree
(|>) : (Measured a v) => FingerTree v a -> a -> FingerTree v a
(|>) Empty x = Single x
(|>) (Single y) x = deep (One y) Empty (One x)
(|>) (Deep _ digit subtree rd@(One _)) x = deep digit subtree (append rd x)
(|>) (Deep _ digit subtree rd@(Two _ _)) x = deep digit subtree (append rd x)
(|>) (Deep _ digit subtree rd@(Three _ _ _)) x = deep digit subtree (append rd x)
(|>) (Deep _ digit subtree (Four y z w s)) x = deep digit (subtree |> (node3 y z w)) (Two s x)


||| Convert a list into a finger tree
fromList : (Measured a v) => List a -> FingerTree v a
fromList = foldl (|>) Empty


||| Convert a finger tree into a list
toList : FingerTree v a -> List a
toList Empty = []
toList (Single x) = [x]
toList (Deep _ ldigit subtree rdigit) =
  let lList = toList ldigit
      rList = toList rdigit
      mList = do node <- toList subtree
                 pure $ toList node
  in  lList ++ join mList ++ rList


namespace ViewL
  ||| View to iterate a finger tree from left to right
  public export
  data ViewL : (treeTy : Type -> Type) ->
               (elemTy : Type) ->
               Type where
       Nil : ViewL treeTy elemTy
       (::) : elemTy -> Lazy (treeTy elemTy) -> ViewL treeTy elemTy


  mutual
    ||| Remove the first element of the leftmost digit
    private
    deepL : (Measured a v) => Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
    deepL (One _) subtree rdigit = case viewL subtree of
                                        [] => toTree rdigit
                                        (node :: subtree') => deep (toDigit node) subtree' rdigit
    deepL (Two _ y) subtree rdigit = deep (One y) subtree rdigit
    deepL (Three _ y z) subtree rdigit = deep (Two y z) subtree rdigit
    deepL (Four _ y z w) subtree rdigit = deep (Three y z w) subtree rdigit


    ||| Create a view to iterate a finger tree from left to right
    viewL : (Measured a v) => FingerTree v a -> ViewL (FingerTree v) a
    viewL Empty = []
    viewL (Single x) = x :: Empty
    viewL (Deep _ ldigit subtree rdigit) = head ldigit :: deepL ldigit subtree rdigit


namespace ViewR
  ||| View to iterate a finger tree from right to left
  public export
  data ViewR : (treeTy : Type -> Type) ->
               (elemTy : Type) ->
               Type where
       Nil : ViewR treeTy elemTy
       (::) : elemTy -> Lazy (treeTy elemTy) -> ViewR treeTy elemTy


  mutual
    ||| Remove the first element of the rightmost digit
    private
    deepR : (Measured a v) => Digit a -> FingerTree v (Node v a) -> Digit a -> FingerTree v a
    deepR ldigit subtree (One _) = case viewR subtree of
                                        [] => toTree ldigit
                                        (node :: subtree') => deep ldigit subtree' (toDigit node)
    deepR ldigit subtree (Two x _) = deep ldigit subtree (One x)
    deepR ldigit subtree (Three x y _) = deep ldigit subtree (Two x y)
    deepR ldigit subtree (Four x y z _) = deep ldigit subtree (Three x y z)


    ||| Create a view to iterate a finger tree from right to left
    viewR : (Measured a v) => FingerTree v a -> ViewR (FingerTree v) a
    viewR Empty = []
    viewR (Single x) = x :: Empty
    viewR (Deep _ ldigit subtree rdigit) = last rdigit :: deepR ldigit subtree rdigit


||| Get the first element of a non-empty finger tree
||| @ prf proof that the finger tree in non-empty
head : (tree : FingerTree v a) -> {auto prf : FingerTreeIsNonEmpty tree} -> a
head Empty {prf} impossible
head (Single x) {prf = IsSingle} = x
head (Deep _ ld subtree rd) {prf = IsDeep} = head ld


||| Get the tail of a non-empty finger tree
||| @ prf proof that the finger tree in non-empty
tail : (Measured a v) => (tree : FingerTree v a) -> {auto prf : FingerTreeIsNonEmpty tree} -> FingerTree v a
tail Empty {prf} impossible
tail (Single x) {prf = IsSingle} = Empty
tail (Deep _ ld subtree rd) {prf = IsDeep} = deepL ld subtree rd


||| Get the last element of a non-empty finger tree
||| @ prf proof that the finger tree in non-empty
last : (tree : FingerTree v a) -> {auto prf : FingerTreeIsNonEmpty tree} -> a
last Empty {prf} impossible
last (Single x) {prf = IsSingle} = x
last (Deep _ ld subtree rd) {prf = IsDeep} = last rd


||| Return all but the last element of a non-empty finger tree
||| @ prf proof that the finger tree is non-empty
init : (Measured a v) => (tree : FingerTree v a) -> {auto prf : FingerTreeIsNonEmpty tree} -> FingerTree v a
init Empty {prf} impossible
init (Single x) {prf = IsSingle} = Empty
init (Deep _ ld subtree rd) {prf = IsDeep} = deepR ld subtree rd


||| Split a vect of elements into a list of nodes
||| @prf proof that the vector has at least 2 elements
private
nodes : (Measured a v) => Vect n a -> {auto prf : n `GTE` 2} -> List (Node v a)
nodes [_] {prf = (LTESucc LTEZero)} impossible
nodes [_] {prf = (LTESucc (LTESucc _))} impossible
nodes [x, y] {prf = (LTESucc (LTESucc LTEZero))} = [node2 x y]
nodes [x, y, z] {prf = (LTESucc (LTESucc LTEZero))} = [node3 x y z]
nodes [x, y, z, w] {prf = (LTESucc (LTESucc LTEZero))} = [node2 x y, node2 z w]
nodes (x :: (y :: (z :: (w :: (s :: xs))))) {prf = (LTESucc (LTESucc LTEZero))} =
  node3 x y z :: nodes (w :: (s :: xs))


||| Prove that the concatenated vect has at least two elements
private
lengthIsGTE2 : (rd0, ld1 : Digit a) -> (vect : Vect len a) ->
               (length rd0 + (len + length ld1) `GTE` 2)
lengthIsGTE2 {len} rd0 ld1 vect =
  let p0 = digitHasAtLeastOneElem rd0
      p1 = digitHasAtLeastOneElem ld1
      p2 = the (Z `LTE` len) LTEZero
      p21 = ltePlusNatRight p2 p1
  in  ltePlusNatRight p0 p21


||| Combine two finger tree and a list of elements into a new finger tree
private
conc : (Measured a v) => FingerTree v a -> List a -> FingerTree v a -> FingerTree v a
conc Empty elems tree1 = foldr (<|) tree1 elems
conc (Single x) elems tree1 = x <| (foldr (<|) tree1 elems)
conc tree0 elems Empty = foldl (|>) tree0 elems
conc tree0 elems (Single x) = (foldl (|>) tree0 elems) |> x
conc (Deep _ ld0 st0 rd0) elems (Deep _ ld1 st1 rd1) =
  let list0 = toVect rd0
      list1 = toVect ld1
      listE = Data.Vect.fromList elems
      l = list0 ++ listE ++ list1
      prf = lengthIsGTE2 rd0 ld1 listE
  in  deep ld0 (conc st0 (nodes l) st1) rd1


||| Concatenate two finger trees
(++) : (Measured a v) => FingerTree v a -> FingerTree v a -> FingerTree v a
(++) x y = conc x [] y
