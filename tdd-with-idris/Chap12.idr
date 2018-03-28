import Control.Monad.State

data Tree a = Empty
            | Node (Tree a) a (Tree a)

flatten : Tree a -> List a
flatten Empty = []
flatten (Node lchild e rchild) = flatten lchild ++ [e] ++ flatten rchild

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) 
                      "Fred"
                      (Node Empty "Sheila" Empty))
                "Alice"
                (Node Empty
                      "Bob"
                      (Node Empty "Eve" Empty))

treeLabelHelper : Stream Integer -> Tree a -> (Stream Integer, Tree (Integer, a))
treeLabelHelper label Empty= (label, Empty)
treeLabelHelper label (Node lchild e rchild) = 
  let (l :: l1, lchild') = treeLabelHelper label lchild
      e' = (l, e)
      (l2, rchild') = treeLabelHelper l1 rchild
  in  (l2, Node lchild' e' rchild')

treeLabel : Tree a -> Tree (Integer, a)
treeLabel tree = snd $ treeLabelHelper [1..] tree

treeLabelWith : Tree a -> State (Stream labelType) (Tree (labelType, a))
treeLabelWith Empty = pure Empty
treeLabelWith (Node lchild elem rchild) =
  do lchild' <- treeLabelWith lchild
     (label :: l) <- get
     put l
     rchild' <- treeLabelWith rchild
     pure $ Node lchild' (label, elem) rchild'

treeLabel' : Tree a -> Tree (Integer, a)
treeLabel' tree = evalState (treeLabelWith tree) [1..]
