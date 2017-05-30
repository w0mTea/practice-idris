import Data.Vect

addMatrix : Num numType =>
            Vect a (Vect b numType) ->
            Vect a (Vect b numType) ->
            Vect a (Vect b numType)

multMatrix : Num numType =>
             Vect a (Vect b numType) ->
             Vect b (Vect c numType) ->
             Vect a (Vect c numType)

transposeMatrix : Num numType =>
                  Vect a (Vect b numType) ->
                  Vect b (Vect a numType)
transposeMatrix [] = replicate _ []
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                            transposeHelper x xsTrans
    where transposeHelper = zipWith (::)
