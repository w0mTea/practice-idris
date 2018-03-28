module Command

import QuizState

%default total

public export
data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  
  GetRandom : Command Int
  GetGameState : Command GameState
  SetGameState : GameState -> Command ()

  Pure : a -> Command a
  Bind : Command a -> (a -> Command b) -> Command b

export
Functor Command where
  map func command = Bind command $ Pure . func

export
Applicative Command where
  pure = Pure
  (<*>) f command = Bind f $ flip map command

export
Monad Command where
  (>>=) = Bind


export
runCommand : Command a -> IO a
runCommand (PutStr str) = putStr str
runCommand GetLine = getLine
runCommand GetRandom = ?runCommand_rhs_3
runCommand GetGameState = ?runCommand_rhs_4
runCommand (SetGameState x) = ?runCommand_rhs_5
runCommand (Pure x) = pure x
runCommand (Bind command f) = do res <- runCommand command
                                 runCommand $ f res
