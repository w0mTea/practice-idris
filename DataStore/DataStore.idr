module Main

import Data.Vect

data DataStore : Type where
    MkData : (size : Nat) -> (items : Vect size String) -> DataStore

addToStore : (elem : String) -> (store : DataStore) -> DataStore
addToStore elem (MkData size items) = MkData _ (items ++ [elem])

size : DataStore -> Nat
size (MkData size items) = size

items : (store : DataStore) -> Vect (size store) String
items (MkData size items) = items

get : (store : DataStore) -> Fin (size store) -> String
get store elemIndex = index elemIndex (items store)

data Command = CmdAdd String
             | CmdGet Nat
             | CmdQuit

parseCommmand : String -> Maybe Command
parseCommmand input =
    let (command, originArg) = span (/= ' ') input
        arg = ltrim originArg in
        internalParse command arg
    where internalParse : String -> String -> Maybe Command
          internalParse "add" arg = Just (CmdAdd arg)
          internalParse "get" arg = case all isDigit (unpack arg) of
                                         False => Nothing
                                         True => Just (CmdGet (cast arg))
          internalParse "quit" arg = Just CmdQuit
          internalParse cmd arg = Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
    case parseCommmand input of
        Nothing =>
            Just ("Invalid command\n", store)
        Just (CmdAdd elem) =>
            let newStore = addToStore elem store
                index = size store in
                Just ("Add success, index " ++ show index ++ "\n", newStore)
        Just (CmdGet elemIndex) =>
            case natToFin elemIndex (size store) of
                Nothing =>
                    Just ("Index " ++ show elemIndex ++ " is greater equal than store size " ++
                          show (size store) ++ "\n",
                          store)
                Just x =>
                    let elem = get store x in
                        Just (elem ++ "\n", store)
        Just CmdQuit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
