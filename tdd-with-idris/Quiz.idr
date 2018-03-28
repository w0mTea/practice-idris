-- 12.3.1 Arithmetic quiz
%default total

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  
  GetRandom : Command Int
  GetGameState : Command GameState
  SetGameState : GameState -> Command ()
  
  Pure : a -> Command a
  Bind : Command a -> (a -> Command b) -> Command b

mutual  
  Functor Command where
    map func x = do a <- x
                    pure $ func a
  
  Applicative Command where
    pure = Pure
    (<*>) f x = do f' <- f
                   map f' x
  
  Monad Command where
    (>>=) = Bind

runCommand : Command a -> IO a
runCommand (PutStr str) = putStr str
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (Bind x f) = do x' <- runCommand x
                           runCommand $ f x'
runCommand GetRandom = ?runCommand_rhs_1
runCommand GetGameState = ?runCommand_rhs_2
runCommand (SetGameState x) = ?runCommand_rhs_3

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry y = pure Nothing
run (More fuel) (Quit x) = pure $ Just x
run (More fuel) (Do command f) = do res <- runCommand command
                                    run fuel $ f res

