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
     CmdSearch : String -> Command schema
     CmdQuit : Command schema

parseBySchema : (schema : Schema) -> (arg : String) -> Maybe (SchemaType schema)
parseBySchema SInt arg = ?parseBySchema_rhs_1
parseBySchema SString arg = ?parseBySchema_rhs_2
parseBySchema (x .+. y) arg = ?parseBySchema_rhs_3

parseCommand : (schema : Schema) -> (command : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" arg = map CmdAdd (parseBySchema schema arg)
parseCommand schema "get" arg = case all isDigit (unpack arg) of
                                     False => Nothing
                                     True => Just (CmdGet (cast arg))
parseCommand schema "size" arg = Just CmdSize
parseCommand schema "search" arg = Just (CmdSearch arg)
parseCommand schema "quit" arg = Just CmdQuit
parseCommand schema cmd arg = Nothing

parseInput : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parseInput schema input = let (command, args) = span (/= ' ') input in
                              parseCommand schema command args

{-
processCommand : (cmd : Command) -> (store : DataStore) -> Maybe (String, DataStore)
processCommand (CmdAdd elem) store =
    let newStore = addToStore store elem
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
-}