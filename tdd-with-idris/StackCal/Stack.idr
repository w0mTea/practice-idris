module StackOp

import Data.Vect

%default total


public export
data StackOp : (resultType : Type) ->
               (beforeHeight : Nat) ->
               (afterHeight : Nat) ->
               (elemType : Type) ->
               Type where
  Push : elemType -> StackOp () height (S height) elemType
  Pop : StackOp elemType (S height) height elemType
  Top : StackOp elemType (S height) (S height) elemType
  
  GetLine : StackOp String height height elemType
  PutStr : String -> StackOp () height height elemType
  
  Pure : elemType -> StackOp elemType height height elemType
  (>>=) : StackOp a height1 height2 elemType ->
          (a -> StackOp b height2 height3 elemType) ->
          StackOp b height1 height3 elemType

export
runStack : (stack : Vect inHeight elemType) ->
           (op : StackOp ty inHeight outHeight elemType) ->
           IO (ty, Vect outHeight elemType)
runStack stack (Push x) = pure ((), x :: stack)
runStack (x :: xs) Pop = pure (x, xs)
runStack stack@(x :: _) Top = pure (x, stack)
runStack stack GetLine = do str <- getLine
                            pure (str, stack)
runStack stack (PutStr x) = do putStr x
                               pure ((), stack)
runStack stack (Pure x) = pure (x, stack)
runStack stack (op >>= next) = do (res, newStack) <- runStack stack op
                                  runStack newStack (next res)
