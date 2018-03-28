import Data.Vect

data WordState : (guess_remaining : Nat) -> (letters : Nat) -> Type where
     MkWordState : (word : String) ->
                   (missing : Vect letters Char) ->
                   WordState guess_remaining letters

data Finished : Type where
     Lost : (game : WordState 0 (S letters)) -> Finished
     Won : (game : WordState (S guesses) 0) -> Finished

game : WordState (S guesses) (S letters) -> IO Finished
game x = ?game_rhs

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]
     
isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = ?isValidString_rhs

readGuess : IO (x ** ValidInput x)
readGuess = do
  putStr "Guess: "
  str <- getLine
  case isValidString str of
    (Yes prf) => pure (_ ** prf)
    (No contra) => do
      putStr "Invalid guess, please retry."
      readGuess

processGuess : (letter : Char) -> WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) =
  case isElem letter missing of
       (Yes prf) => Right ?processGuess_rhs_2
       (No contra) => Left ?processGuess_rhs_3
