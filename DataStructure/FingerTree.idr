module FingerTree

%default total

data Node a = Node2 a a | Node3 a a a


data Digit a = One a | Two a a | Three a a a | Four a a a a


data FingerTree a = Empty
                  | Single a
                  | Deep (Digit a) (FingerTree (Node a)) (Digit a)


namespace Digit
  toTree : Digit a -> FingerTree a
  toTree (One x) = Single x
  toTree (Two x y) = Deep (One x) Empty (One y)
  toTree (Three x y z) = Deep (Two x y) Empty (One z)
  toTree (Four x y z w) = Deep (Two x y) Empty (Two z w)


  toList : Digit a -> List a
  toList (One x) = [x]
  toList (Two x y) = [x, y]
  toList (Three x y z) = [x, y, z]
  toList (Four x y z w) = [x, y, z, w]


  head : Digit a -> a
  head (One x) = x
  head (Two x y) = x
  head (Three x y z) = x
  head (Four x y z w) = x


  tail : Digit a -> a
  tail (One x) = x
  tail (Two x y) = y
  tail (Three x y z) = z
  tail (Four x y z w) = w


namespace Node
  toDigit : Node a -> Digit a
  toDigit (Node2 x y) = Two x y
  toDigit (Node3 x y z) = Three x y z


  toList : Node a -> List a
  toList (Node2 x y) = [x, y]
  toList (Node3 x y z) = [x, y, z]


  head : Node a -> a
  head (Node2 x y) = x
  head (Node3 x y z) = x


  tail : Node a -> a
  tail (Node2 x y) = y
  tail (Node3 x y z) = z



infixr 5 <|
(<|) : a -> FingerTree a -> FingerTree a
(<|) x Empty = Single x
(<|) x (Single y) = Deep (One x) Empty (One y)
(<|) x (Deep (One y) subtree digit) = Deep (Two x y) subtree digit
(<|) x (Deep (Two y z) subtree digit) = Deep (Three x y z) subtree digit
(<|) x (Deep (Three y z w) subtree digit) = Deep (Four x y z w) subtree digit
(<|) x (Deep (Four y z w s) subtree digit) = Deep (Two x y) ((Node3 y w s) <| subtree) digit


infixl 5 |>
(|>) : FingerTree a -> a -> FingerTree a
(|>) Empty x = Single x
(|>) (Single y) x = Deep (One y) Empty (One x)
(|>) (Deep digit subtree (One y)) x = Deep digit subtree (Two y x)
(|>) (Deep digit subtree (Two y z)) x = Deep digit subtree (Three y z x)
(|>) (Deep digit subtree (Three y z w)) x = Deep digit subtree (Four y z w x)
(|>) (Deep digit subtree (Four y z w s)) x = Deep digit (subtree |> (Node3 y z w)) (Two s x)


fromList : List a -> FingerTree a
fromList = foldl (|>) Empty


toList : FingerTree a -> List a
toList Empty = []
toList (Single x) = [x]
toList (Deep ldigit subtree rdigit) =
  let lList = toList ldigit
      rList = toList rdigit
      mList = do node <- toList subtree
                 pure $ toList node
  in  lList ++ join mList ++ rList


namespace ViewL
  data ViewL : (treeTy : Type -> Type) ->
               (elemTy : Type) ->
               Type where
       Nil : ViewL treeTy elemTy
       (::) : elemTy -> Lazy (treeTy elemTy) -> ViewL treeTy elemTy


  mutual
    deepL : Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
    deepL (One _) subtree rdigit = case viewL subtree of
                                        [] => toTree rdigit
                                        (node :: subtree') => Deep (toDigit node) subtree' rdigit
    deepL (Two _ y) subtree rdigit = Deep (One y) subtree rdigit
    deepL (Three _ y z) subtree rdigit = Deep (Two y z) subtree rdigit
    deepL (Four _ y z w) subtree rdigit = Deep (Three y z w) subtree rdigit

    viewL : FingerTree a -> ViewL FingerTree a
    viewL Empty = []
    viewL (Single x) = x :: Empty
    viewL (Deep ldigit subtree rdigit) = head ldigit :: deepL ldigit subtree rdigit


  partial
  headL : FingerTree a -> a
  headL tree = case viewL tree of
                    (x :: _) => x


  partial
  tailL : FingerTree a -> FingerTree a
  tailL tree = case viewL tree of
                    (_ :: tree') => tree'


namespace ViewR
  data ViewR : (treeTy : Type -> Type) ->
               (elemTy : Type) ->
               Type where
       Nil : ViewR treeTy elemTy
       (::) : elemTy -> Lazy (treeTy elemTy) -> ViewR treeTy elemTy


  mutual
    deepR : Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
    deepR ldigit subtree (One _) = case viewR subtree of
                                        [] => toTree ldigit
                                        (node :: subtree') => Deep ldigit subtree' (toDigit node)
    deepR ldigit subtree (Two x _) = Deep ldigit subtree (One x)
    deepR ldigit subtree (Three x y _) = Deep ldigit subtree (Two x y)
    deepR ldigit subtree (Four x y z _) = Deep ldigit subtree (Three x y z)


    viewR : FingerTree a -> ViewR FingerTree a
    viewR Empty = []
    viewR (Single x) = x :: Empty
    viewR (Deep ldigit subtree rdigit) = tail rdigit :: deepR ldigit subtree rdigit

  partial
  headR : FingerTree a -> a
  headR tree = case viewR tree of
                 (x :: _) => x


  partial
  tailR : FingerTree a -> FingerTree a
  tailR tree = case viewR tree of
                 (_ :: tree') => tree'
