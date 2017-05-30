import Data.Vect

addMatrix : Num numType =>
            Vect a (Vect b numType) ->
            Vect a (Vect b numType) ->
            Vect a (Vect b numType)

multMatrix : Num numType =>
             Vect a (Vect b numType) ->
             Vect b (Vect c numType) ->
             Vect a (Vect c numType)

createEmtpies : Num numType => Vect b (Vect 0 numType)
createEmtpies = replicate _ []

transposeHelper : Num numType => (x : Vect b numType) -> (xsTrans : Vect b (Vect len numType)) -> Vect b (Vect (S len) numType)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

transposeMatrix : Num numType =>
                  Vect a (Vect b numType) ->
                  Vect b (Vect a numType)
transposeMatrix [] = createEmtpies
transposeMatrix (x :: xs) = let xsTrans = transposeMatrix xs in
                            transposeHelper x xsTrans
