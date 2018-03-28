
namespace Door
  data DoorState = DoorClosed | DoorOpen
  
  data DoorCmd : Type ->      -- return type of the command
                 DoorState -> -- state before the command
                 DoorState -> -- state after the command
                 Type where
    Open : DoorCmd () DoorClosed DoorOpen
    Close : DoorCmd () DoorOpen DoorClosed
    RingBell : DoorCmd () state state
    
    Pure : a -> DoorCmd a state state
    (>>=) : DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) -> DoorCmd b state1 state3
  
  testDoor : DoorCmd () DoorClosed DoorClosed
  testDoor = do Open
                RingBell
                Close
                RingBell

-- 13.1.3 Vend Machine

VendState : Type
VendState = (Nat, Nat)

data Input = COIN       -- Insert a coin
           | VEND       -- Get a chocolate
           | CHANGE     -- Get change
           | REFILL Nat -- Add chocolate into the machine

data MachineCmd : Type ->
                  VendState ->
                  VendState ->
                  Type where
  InsertCoin : MachineCmd () (pounds, chocs) (S pounds, chocs)
  Vend : MachineCmd () (S pounds, S chocs) (pounds, chocs)
  ReturnCoins : MachineCmd () (pounds, chocs) (Z, chocs)
  Refill : (n : Nat) -> MachineCmd () (Z, chocs) (Z, chocs + n)

  Display : String -> MachineCmd () state state
  GetInput : MachineCmd (Maybe Input) state state
  
  Pure : a -> MachineCmd a state state
  (>>=) : MachineCmd a state1 state2 ->
          (a -> MachineCmd b state2 state3) ->
          MachineCmd b state1 state3

data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1

namespace MachineDo
  (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
  (>>=) = Do

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = S p} {chocs = S c} = do Vend
                                         Display "Enjoy!"
                                         machineLoop
  vend {pounds = Z} = do Display "No enough pounds inserted"
                         machineLoop
  vend {chocs = Z} = do Display "Out of stock"
                        machineLoop

  refill : Nat -> MachineIO (pounds, chocs)
  refill {pounds = Z} num = do Refill num
                               machineLoop
  refill _ = do Display "Coins in the machine!"
                machineLoop
  
  machineLoop : MachineIO (pounds, chocs)
  machineLoop = 
    do Just x <- GetInput
            | Nothing => do Display "Invalid input"
                            machineLoop
       case x of
            COIN => do InsertCoin
                       machineLoop
            VEND => vend
            CHANGE => do ReturnCoins
                         Display "Change Returned"
                         machineLoop
            (REFILL k) => refill k
