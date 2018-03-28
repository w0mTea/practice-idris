module QuizState

%default total

public export
record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

public export
record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

export
initState : GameState
initState = MkGameState (MkScore 0 0) 10

export
Show Score where
  show (MkScore correct attempted) = show correct ++ "/" ++ show attempted

export
Show GameState where
  show (MkGameState score difficulty) = show score ++ "\nDifficulty: " ++ show difficulty

