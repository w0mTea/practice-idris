import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

data ServiceState = NotRequest | Sent | Complete

namespace NS
  data Service : Type -> 
                 (beforeState : ServiceState) ->
                 (afterState : ServiceState) ->
                 Type where
    Respond : (Message -> Service Nat NotRequest NotRequest) ->
              Service (Maybe Message) state Sent
    Loop : Inf (Service a NotRequest Complete) -> Service a Sent Complete

    Pure : a -> Service a state state
    (>>=) : Service a state1 state2 ->
            (a -> Service b state2 state3) ->
            Service b state1 state3

namespace NC
  data Client : Type -> Type where
    Action : IO a -> Client a
    Spawn : Service a NotRequest Complete -> Client (Maybe PID)
    Request : PID -> Message -> Client (Maybe Nat)

    Pure : a -> Client a
    (>>=) : Client a -> (a -> Client b) -> Client b

data Fuel = Dry | More (Lazy Fuel)

runService : Fuel -> Service a state1 state2 -> IO (Maybe a)
runService Dry _ = pure Nothing
runService fuel (Respond f) =
  do Just chan <- listen 1
          | Nothing => pure (Just Nothing)
     Just message <- unsafeRecv Message chan
          | Nothing => pure (Just Nothing)
     Just answer <- runService fuel $ f message
          | Nothing => pure (Just Nothing)
     unsafeSend chan answer
     pure $ Just $ Just message
runService (More fuel) (Loop service) = runService fuel service
runService _ (Pure x) = pure $ Just x
runService fuel (service >>= next) = 
  do Just a <- runService fuel service
          | Nothing => pure Nothing
     runService fuel $ next a

runClient : Fuel -> Client a -> IO a
runClient _ (Action x) = x
runClient fuel (Spawn service) =
  do let service = runService fuel service
     spawn (do service; pure ())
runClient _ (Request pid message) =
  do Just chan <- connect pid
          | Nothing => pure Nothing
     ok <- unsafeSend chan message
     if ok then do Just answer <- unsafeRecv Nat chan
                        | Nothing => pure Nothing
                   pure $ Just answer
           else pure Nothing
runClient _ (Pure x) = pure x
runClient fuel (client >>= next) =
  do a <- runClient fuel client
     runClient fuel $ next a

partial
forever : Fuel
forever = More forever

testService : Service Nat NotRequest Complete
testService = do Respond (\message => (case message of
                                            (Add x y) => Pure (x + y)))
                 Loop testService

testClient : Client ()
testClient = do Just pid <- Spawn testService
                     | Nothing => do Action $ putStrLn "Failed to create process"
                                     Pure ()
                Just answer <- Request pid (Add 2 3)
                     | Nothing => do Action $ putStrLn "Failed to request"
                                     Pure ()
                Action $ printLn answer
                Pure ()

partial
testRun : IO ()
testRun = runClient forever testClient

badService : Service Nat NotRequest Complete
badService = do Respond (\message => (case message of
                                            (Add x y) => Pure (x + y)))
