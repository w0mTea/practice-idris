import Data.Vect

data Matrix : (rows : Nat) -> (cols : Nat) -> (elem : Type) -> Type where
     MkMatrix : Num elem => Vect rows (Vect cols elem) -> Matrix rows cols elem

||| Add two matrices
add : Matrix a b elem -> Matrix a b elem -> Matrix a b elem
add {a = Z} (MkMatrix []) (MkMatrix []) = MkMatrix []
add {a = (S k)} (MkMatrix (x :: xs)) (MkMatrix (y :: ys)) =
    case add (MkMatrix xs) (MkMatrix ys) of
         (MkMatrix xs') => MkMatrix (zipWith (+) x y :: xs')

||| Helper function to generate a new row during multiplying matrices.
||| @inputRow A row from the first matrix to be multiplied
||| @matrix The second metrix to be multiplied
genNewRow : Num numType =>
            (inputRow : Vect b numType) ->
            (matrix : Vect b (Vect c numType)) ->
            Vect c numType
genNewRow [] [] = replicate _ 0
genNewRow (elem :: elems) (row :: rows) = let tmpRow = map (elem *) row
                                              otherRow = genNewRow elems rows in
                                          zipWith (+) tmpRow otherRow

||| Multiply two matrices
mult : Matrix a b elem -> Matrix b c elem -> Matrix a c elem
mult {a = Z} (MkMatrix []) ys = MkMatrix []
mult {a = (S k)} (MkMatrix (x :: xs)) mat@(MkMatrix ys) =
    case mult (MkMatrix xs) mat of
         (MkMatrix xs') => MkMatrix (genNewRow x ys :: xs')

internalTranspose : Num numType =>
                    Vect a (Vect b numType) ->
                    Vect b (Vect a numType)
internalTranspose [] = replicate _ []
internalTranspose (x :: xs) = let xsTrans = internalTranspose xs in
                              zipWith (::) x xsTrans
||| Transpose a matrix
transpose : Matrix a b elem -> Matrix b a elem
transpose {a = Z} (MkMatrix []) = MkMatrix (replicate _ [])
transpose {a = (S k)} (MkMatrix (x :: xs)) =
    case transpose (MkMatrix xs) of
         (MkMatrix xsTrans) => MkMatrix (zipWith (::) x xsTrans)
-- transpose (MkMatrix xs) = MkMatrix (internalTranspose xs)

||| Get rows of a matrix
rows : Matrix a b elem -> Vect a (Vect b elem)
rows (MkMatrix xs) = xs

||| Get columns of a matrix
cols : Matrix a b elem -> Vect b (Vect a elem)
cols mat = case transpose mat of
                (MkMatrix xs) => xs
