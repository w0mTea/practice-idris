import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

data Process : Type -> Type where
  Action : IO a -> Process a
  Spawn : Process () -> Process (Maybe PID)
  Request : PID -> Message -> Process (Maybe Nat)
  Respond : (Message -> Process Nat) -> Process (Maybe Message)
  
  Loop : Inf (Process a) -> Process a

  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b


run : Process a -> IO a
run (Action x) = x
run (Spawn x) = spawn $ run x
run (Request pid message) =
  do Just chan <- connect pid
          | Nothing => pure Nothing
     ok <- unsafeSend chan message
     if ok then do Just num <- unsafeRecv Nat chan
                        | Nothing => pure Nothing
                   pure $ Just num
           else pure Nothing
run (Respond f) = 
  do Just chan <- listen 1
          | Nothing => pure Nothing
     Just message <- unsafeRecv Message chan
          | Nothing => pure Nothing
     res <- run $ f message
     unsafeSend chan res
     pure $ Just message
run (Loop (Delay proc)) = ?run_rhs
run (Pure x) = pure x
run (process >>= next) = do res <- run process
                            run $ next res

procAdder : Process ()
procAdder = do Respond (\msg => (case msg of
                                      (Add x y) => Pure $ x + y))
               Loop procAdder

procMain : Process ()
procMain = do Just pid <- Spawn procAdder
                   | Nothing => Action (putStrLn "Failed to spawn a process")
              Just answer <- Request pid (Add 2 3)
                   | Nothing => Action (putStrLn "Failed to request")
              Action $ printLn answer
