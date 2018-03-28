module FingerTree

%default total

data Node a = Node2 a a | Node3 a a a


data Digit a = One a | Two a a | Three a a a | Four a a a a


data FingerTree a = Empty
                  | Single a
                  | Deep (Digit a) (FingerTree (Node a)) (Digit a)


infixr 5 <|
(<|) : a -> FingerTree a -> FingerTree a
(<|) x Empty = Single x
(<|) x (Single y) = Deep (One x) Empty (One y)
(<|) x (Deep (One y) subtree digit) = Deep (Two x y) subtree digit
(<|) x (Deep (Two y z) subtree digit) = Deep (Three x y z) subtree digit
(<|) x (Deep (Three y z w) subtree digit) = Deep (Four x y z w) subtree digit
(<|) x (Deep (Four y z w s) subtree digit) = Deep (Two x y) ((Node3 z w s) <| subtree) digit


infixl 5 |>
(|>) : FingerTree a -> a -> FingerTree a
(|>) Empty x = Single x
(|>) (Single y) x = Deep (One y) Empty (One x)
(|>) (Deep digit subtree (One y)) x = Deep digit subtree (Two y x)
(|>) (Deep digit subtree (Two y z)) x = Deep digit subtree (Three y z x)
(|>) (Deep digit subtree (Three y z w)) x = Deep digit subtree (Four y z w x)
(|>) (Deep digit subtree (Four y z w s)) x = Deep digit (subtree |> (Node3 y z w)) (Two s x)

