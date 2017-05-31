import Data.Vect

||| Add two matrices
addMatrix : Num numType =>
            Vect a (Vect b numType) ->
            Vect a (Vect b numType) ->
            Vect a (Vect b numType)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) = zipWith (+) x y :: addMatrix xs ys

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
multMatrix : Num numType =>
             Vect a (Vect b numType) ->
             Vect b (Vect c numType) ->
             Vect a (Vect c numType)
multMatrix [] _ = []
multMatrix (x :: xs) ys = genNewRow x ys :: multMatrix xs ys

||| Transpose a matrix
transposeMatrix : Num numType =>
                  Vect a (Vect b numType) ->
                  Vect b (Vect a numType)
transposeMatrix [] = replicate _ []
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                            zipWith (::) x xsTrans
