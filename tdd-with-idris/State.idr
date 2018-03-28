-- 12.2 Implementation of State

data State : (stateType : Type) -> Type -> Type where
  Get : State stateType stateType
  Put : (newState : stateType) -> State stateType ()
  
  Pure : ty -> State stateType ty
  Bind : State stateType a -> (a -> State stateType b) -> State stateType b

namespace noMonad  
  (>>=) : State stateType a -> (a -> State stateType b) -> State stateType b
  (>>=) = Bind

  count : List a -> State Integer (List a)
  count [] = Pure []
  count lst@(x :: xs) = do _ <- count xs
                           c <- Get
                           Put $ c + 1
                           Pure lst


Functor (State stateType) where
  map func state = Bind state (Pure . func)

Applicative (State stateType) where
  pure = Pure
  (<*>) f x = Bind f (\f' => map f' x)

Monad (State stateType) where
  (>>=) = Bind

runState : State stateType ty -> (initState : stateType) -> (ty, stateType)
runState Get initState = (initState, initState)
runState (Put newState) initState = ((), newState)
runState (Pure x) initState = (x, initState)
runState (Bind s f) initState = let (x, nextState) = runState s initState
                                    nextS = f x
                                in  runState nextS nextState


addIfPositive : Integer -> State Integer Bool
addIfPositive x = do when (x > 0) $
                          do current <- Get
                             Put $ current + x
                     pure (x > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do bools <- traverse addIfPositive xs
                     pure $ length $ filter id bools
