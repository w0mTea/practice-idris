import Data.Vect

data StackOp : (resultType : Type) ->
               (beforeHeight : Nat) ->
               (afterHeight : Nat) ->
               (elemType : Type) ->
               Type where
  Push : elemType -> StackOp () height (S height) elemType
  Pop : StackOp elemType (S height) height elemType
  Top : StackOp elemType (S height) (S height) elemType
  
  Pure : elemType -> StackOp elemType height height elemType
  (>>=) : StackOp a height1 height2 elemType ->
          (a -> StackOp b height2 height3 elemType) ->
          StackOp b height1 height3 elemType

runStack : (stack : Vect inHeight elemType) ->
           (op : StackOp ty inHeight outHeight elemType) ->
           (ty, Vect outHeight elemType)
runStack stack (Push x) = ((), x :: stack)
runStack (x :: xs) Pop = (x, xs)
runStack stack@(x :: _) Top = (x, stack)
runStack stack (Pure x) = (x, stack)
runStack stack (op >>= f) = let (res, newStack) = runStack stack op
                            in  runStack newStack $ f res
