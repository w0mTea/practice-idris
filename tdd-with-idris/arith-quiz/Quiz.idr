module Main

import Data.String

import QuizState
import Command
import ConsoleIO

%default total

data Input = QuitCmd | Answer Int

parseInput : String -> Maybe Input
parseInput = parse . toLower
  where parse : String -> Maybe Input
        parse "quit" = Just QuitCmd
        parse str = map (Answer . fromInteger) $ parseInteger str


data Forever = More (Lazy Forever)

readInput' : Forever -> String -> Command Input
readInput' (More x) prompt = do PutStr prompt
                                line <- GetLine
                                case parseInput line of
                                     Nothing => readInput' x prompt
                                     (Just x) => pure x

partial
tryForever : Forever
tryForever = More tryForever

readInput : String -> Command Input
readInput prompt = readInput' tryForever prompt

addCorrect : GameState -> GameState
addCorrect = record {score->correct $= S, score->attempted $= S}

addWrong : GameState -> GameState
addWrong = record {score->attempted $= S}


mutual
  correct : ConsoleIO GameState
  correct = do current <- GetGameState
               let next = addCorrect current
               SetGameState next
               quiz
  
  wrong : ConsoleIO GameState
  wrong = ?wrong_rhs
  
  quiz : ConsoleIO GameState
  quiz = do num1 <- GetRandom
            num2 <- GetRandom
            state <- GetGameState
            PutStr $ show state
  
            input <- readInput $ show num1 ++ "*" ++ show num2 ++ "="
            case input of
                 QuitCmd => Quit state
                 (Answer n) => if n == num1 * num2
                               then correct
                               else wrong
  
