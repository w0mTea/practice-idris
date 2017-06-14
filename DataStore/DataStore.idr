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

search : (store : DataStore) -> (predict : String -> Bool) -> (n ** Vect n String)
search store predict =
    let elems = items store
        vect = zipWithIndex elems in
        case filter (\pair => predict (snd pair)) vect of
            (x ** pf) => (x ** map (\pair => show (fst pair) ++ ": " ++ snd pair) pf)
    where internalZip : Nat -> Vect n ty -> Vect n (Nat, ty)
          internalZip k [] = []
          internalZip k (x :: xs) = (k, x) :: internalZip (S k) xs

          zipWithIndex : Vect n ty -> Vect n (Nat, ty)
          zipWithIndex = internalZip 0

data Command = CmdAdd String
             | CmdGet Nat
             | CmdSize
             | CmdSearch String
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
          internalParse "size" arg = Just CmdSize
          internalParse "search" arg = Just (CmdSearch arg)
          internalParse "quit" arg = Just CmdQuit
          internalParse cmd arg = Nothing

processCommand : (cmd : Command) -> (store : DataStore) -> Maybe (String, DataStore)
processCommand (CmdAdd elem) store =
    let newStore = addToStore elem store
        index = size store in
        Just ("Add success, index " ++ show index ++ "\n", newStore)
processCommand (CmdGet elemIndex) store =
    case natToFin elemIndex (size store) of
        Nothing =>
            Just ("Index " ++ show elemIndex ++ " is greater equal than store size " ++
                    show (size store) ++ "\n",
                    store)
        Just x => Just (get store x ++ "\n", store)
processCommand CmdSize store = Just (show (size store) ++ "\n", store)
processCommand (CmdSearch prefix) store =
    case search store (isPrefixOf prefix) of
         (Z ** []) => Just ("No data found\n", store)
         (n ** vs) => Just ("Get " ++ show n ++ " results:\n" ++ showElems vs, store)
    where showElems : Vect n String -> String
          showElems [] = ""
          showElems (x :: xs) = x ++ "\n" ++ showElems xs
processCommand CmdQuit store = Nothing

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input =
    case parseCommmand input of
        Nothing => Just ("Invalid command\n", store)
        Just cmd => processCommand cmd store

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
