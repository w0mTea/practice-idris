module CalculatorInput

import Data.String

%default total

public export
data CalculatorOp = ADD
                  | SUB
                  | MUL
                  | DIV

public export
data CalculatorInput = NumInput Integer
                     | OpInput CalculatorOp

parseOp : String -> Maybe (CalculatorOp)
parseOp str = case toLower str of
                   "add" => pure ADD
                   "sub" => pure SUB
                   "mul" => pure MUL
                   "div" => pure DIV
                   _ => Nothing

parseInput : String -> Maybe (CalculatorInput)
parseInput str = map NumInput (parseInteger str) <|> map OpInput (parseOp str)
