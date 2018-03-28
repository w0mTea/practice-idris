module StackIO

import Stack
import Data.Vect

%default total

public export
data StackIO : Type -> Nat -> Type where
 (>>=) : StackOp ty height1 height2 elemType -> 
         (ty -> Inf (StackIO elemType height2)) -> StackIO elemType height1

export
data Fuel = Dry | More (Lazy Fuel)

export
partial
forever : Fuel
forever = More forever

runStackIO : Fuel ->
             (stack : Vect height elemType) ->
             (stackIO : StackIO elemType height) ->
             IO ()
runStackIO Dry stack stackIO = do putStr "No fuel"
runStackIO (More x) stack (stackOp >>= f)
  = do (res, newStack) <- runStack stack stackOp
       runStackIO x newStack (f res)

