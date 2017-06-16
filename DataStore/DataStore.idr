module Main

import Data.Vect

infixr 5 .+.
data Schema = SInt
            | SString
            | (.+.) Schema Schema

SchemaType : Schema -> Type
SchemaType SInt = Int
SchemaType SString = String
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

showElem : SchemaType schema -> String
showElem {schema = SInt} elem = show elem
showElem {schema = SString} elem = elem
showElem {schema = (x .+. y)} (a, b) = showElem a ++ " " ++ showElem b

record DataStore where
       constructor MkData
       dsSchema : Schema
       dsSize : Nat
       dsItems : Vect dsSize (SchemaType dsSchema)

addToStore : (store : DataStore) -> (elem : SchemaType (dsSchema store)) -> DataStore
addToStore (MkData dsSchema dsSize dsItems) elem = MkData dsSchema _ (dsItems ++ [elem])

getFromStore : (store : DataStore) -> Fin (dsSize store) -> SchemaType (dsSchema store)
getFromStore store i = index i (dsItems store)

searchInStore : (store : DataStore) ->
                (predict : SchemaType (dsSchema store) -> Bool) ->
                (let ElemType : Type = (Nat, SchemaType (dsSchema store)) in
                    (n ** Vect n ElemType))
searchInStore store predict =
    let elems = dsItems store
        vect = zipWithIndex elems in
        filter (\pair => predict (snd pair)) vect
    where internalZip : Nat -> Vect n ty -> Vect n (Nat, ty)
          internalZip k [] = []
          internalZip k (x :: xs) = (k, x) :: internalZip (S k) xs

          zipWithIndex : Vect n ty -> Vect n (Nat, ty)
          zipWithIndex = internalZip 0

data Command : Schema -> Type where
     CmdAdd : SchemaType schema -> Command schema
     CmdGet : Nat -> Command schema
     CmdSize : Command schema
     CmdSchema : (newSchema : Schema) -> Command schema
     CmdQuit : Command schema

parseBySchema : (schema : Schema) -> (arg : String) -> Maybe (SchemaType schema)
parseBySchema _ "" = Nothing
parseBySchema SInt arg = if all isDigit (unpack arg)
                         then Just (cast arg)
                         else Nothing
parseBySchema SString arg = Just arg
parseBySchema (schema0 .+. schema1) arg =
    let (first, rest) = span (/= ' ') arg in
        do elem0 <- parseBySchema schema0 first
           elem1 <- parseBySchema schema1 (ltrim rest)
           pure (elem0, elem1)

parseBuiltinSchema : String -> Maybe Schema
parseBuiltinSchema "Int" = Just SInt
parseBuiltinSchema "String" = Just SString
parseBuiltinSchema x = Nothing

parseSchema : (args : List String) -> Maybe Schema
parseSchema [] = Nothing
parseSchema (x :: []) = parseBuiltinSchema x
parseSchema (x :: xs) = do s0 <- parseBuiltinSchema x
                           s1 <- parseSchema xs
                           pure (s0 .+. s1)

parseCommand : (schema : Schema) -> (command : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" args = map CmdAdd (parseBySchema schema args)
parseCommand schema "get" args = case all isDigit (unpack args) of
                                     False => Nothing
                                     True => Just (CmdGet (cast args))
parseCommand schema "size" args = Just CmdSize
parseCommand schema "quit" args = Just CmdQuit
parseCommand schema "schema" args = let argList = split (== ' ') args in
                                        map CmdSchema (parseSchema argList)
parseCommand schema cmd args = Nothing

parseInput : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parseInput schema input = let (command, args) = span (/= ' ') input in
                              parseCommand schema command (ltrim args)

processCommand : (store : DataStore) ->
                 (cmd : Command (dsSchema store)) ->
                 Maybe (String, DataStore)
processCommand store (CmdAdd elem) =
    let newStore = addToStore store elem
        index = dsSize store in
        Just ("Add success, index " ++ show index ++ "\n", newStore)
processCommand store (CmdGet elemIndex) =
    case natToFin elemIndex (dsSize store) of
        Nothing =>
            Just ("Index " ++ show elemIndex ++ " is greater equal than store size " ++
                    show (dsSize store) ++ "\n",
                    store)
        Just x => Just (showElem (getFromStore store x) ++ "\n", store)
processCommand store CmdSize = Just (show (dsSize store) ++ "\n", store)
processCommand store (CmdSchema newSchema) =
    if dsSize store == 0
    then Just ("Set schema done\n", MkData newSchema _ [])
    else Just ("Data store not empty, cannot change schema\n", store)
processCommand store CmdQuit = Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
    case parseInput (dsSchema store) input of
        Nothing => Just ("Invalid command\n", store)
        Just cmd => processCommand store cmd

main : IO ()
main = replWith (MkData SString _ []) "Command: " processInput
