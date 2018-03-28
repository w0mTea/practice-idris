import System.Concurrency.Channels

%default total

data Message = Add Nat Nat

AdderType : Message -> Type
AdderType (Add k j) = Nat

NoRecv : Void -> Type
NoRecv = const Void

data ProcState = NotRequest | Sent | Complete

data ProcPID : (iface : reqType -> Type) -> Type where
  MkPID : PID -> ProcPID iface

data Service : (iface : reqType -> Type) ->
               Type ->
               (inState : ProcState) ->
               (outState : ProcState) ->
               Type where
  Respond : ((message : reqType) -> iface reqType) ->
            Service iface (iface message) state sent
  Loop : Inf (Service iface ty NotRequest Complete) ->
         Service iface ty Sent Complete

  Pure : a -> Service iface a state state
  (>>=) : Service iface a state1 state2 ->
          (a -> Service iface b state2 state3) ->
          Service iface b state1 state3

data Client : (iface : reqType -> Type) ->
              Type ->
              Type where
  Action : IO a -> Client iface a
  Spawn : Service iface a NotRequest Complete ->
          Client iface (Maybe (ProcPID iface))
  Request : (ProcPID iface) -> (message : reqType) ->
            Client iface (Maybe (iface message))
