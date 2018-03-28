import Data.Primitives.Views

labelWith : Stream labelType -> List a -> List (labelType, a)
labelWith xs [] = []
labelWith (value :: xs) (x :: ys) = (value, x) :: (labelWith xs ys)

label : List a -> List (Integer, a)
label = labelWith [0..]

bound : Int -> Int
bound x with (divides x 12)
  bound ((12 * div) + rem) | (DivBy prf) = rem

every_other : Stream a -> Stream a
every_other (x0 :: x1 :: xs) = x1 :: every_other xs

data InfList : Type -> Type where
  (::) : (elem : ty) -> Inf (InfList ty) -> InfList ty

Functor InfList where  
  map func (elem :: infList) = func elem :: map func infList

-- 11.2 InfIO
data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO
  
loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg)
                   (\_ => loopPrint msg)

data Fuel = Dry | More (Lazy Fuel)

forever : Fuel
forever = More forever

run : Fuel -> InfIO -> IO ()
run Dry infIO = putStrLn "No more fuel"
run (More fuel) (Do x f) = do a <- x
                              run fuel $ f a

(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

total
totalRepl : (promt : String) -> (onInput : String -> String) -> InfIO
totalRepl promt onInput = do putStr promt
                             str <- getLine
                             putStrLn $ onInput str
                             totalRepl promt onInput

-- 11.3 Improve InfIO with termination
-- See RunIO.idr
