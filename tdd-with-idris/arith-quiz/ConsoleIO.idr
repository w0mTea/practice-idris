module ConsoleIO

import Command

%default total

public export
data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do  : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

export
(>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
(>>=) = Do

export
data RunConsoleIO = Stop | Run (Lazy RunConsoleIO)

export
partial
forever : RunConsoleIO
forever = Run forever

export
n_times : Nat -> RunConsoleIO
n_times Z = Stop
n_times (S k) = Run $ n_times k

export
run : RunConsoleIO -> ConsoleIO a -> IO (Maybe a)
run Stop cIO = pure $ Nothing
run (Run runCIO) (Quit x) = pure $ Just x
run (Run runCIO) (Do command f) = do res <- runCommand command
                                     run runCIO $ f res
