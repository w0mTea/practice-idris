import Data.Vect

namespace Door
  data DoorResult = OK | Jammed

  data DoorState = DoorOpen | DoorClosed

  data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
    Open : DoorCmd DoorResult DoorClosed (\res => case res of
                                                       OK => DoorOpen
                                                       Jammed => DoorClosed)
    Close : DoorCmd DoorResult DoorOpen (\res => case res of
                                                      OK => DoorClosed
                                                      Jammed => DoorOpen)

    Pure : (res : ty) -> DoorCmd ty (state_fn res) state_fn
    (>>=) : DoorCmd a state1 state2_fn ->
            ((res : a) -> DoorCmd b (state2_fn res) state3_fn) ->
            DoorCmd b state1 state3_fn

-- ATM
PIN : Type
PIN = Vect 4 Char

data ATMState = Ready | CardInserted | Session

data PINCheck = CorrectPIN | IncorrectPIN

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard : ATMCmd () Ready (const CardInserted)
  EjectCard : ATMCmd () state (const Ready)
  GetPin : ATMCmd PIN CardInserted (const CardInserted)
  CheckPin : PIN -> ATMCmd PINCheck CardInserted
                                    (\checkResult => case checkResult of
                                                          CorrectPIN => Session
                                                          IncorrectPIN => CardInserted)
  Dispense : Nat -> ATMCmd () Session (const Session)
  GetAmount : ATMCmd Nat Session (const Session)
  Message : String -> ATMCmd () state (const state)

  Pure : (res : ty) -> ATMCmd ty (state_fn res) state_fn
  (>>=) : ATMCmd a state1 state2_fn ->
          ((res : a) -> ATMCmd b (state2_fn res) state3_fn) ->
          ATMCmd b state1 state3_fn

atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPin
         pinOK <- CheckPin pin
         case pinOK of
              CorrectPIN => ?atm_rhs_1
              IncorrectPIN => ?atm_rhs_2

checkResult : PINCheck -> Bool
checkResult x = ?checkResult_rhs
