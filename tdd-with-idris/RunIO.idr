%default total

data RunIO : Type -> Type where
  Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b
  Quit : a -> RunIO a

(>>=) : IO a -> (a -> Inf (RunIO b))  -> RunIO b
(>>=) = Do

totalREPL : (promt : String) -> (onInput : String -> Maybe String) -> RunIO ()
totalREPL promt onInput = do putStr promt
                             str <- getLine
                             case onInput str of
                               Nothing => Quit ()
                               (Just s) => do putStrLn s
                                              totalREPL promt onInput
process : String -> Maybe String
process str = case str == "q" of
                   False => Just $ "Hello " ++ str
                   True => Nothing

partial
run : RunIO a -> IO a
run (Do c f) = do r <- c
                  run $ f r
run (Quit x) = pure x
