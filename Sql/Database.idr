module Database

import Data.Vect

data StorageDataType = SNull
                     | SInteger
                     | SReal
                     | SText
                     | SBlob

implementation Eq StorageDataType where
    SNull == SNull = True
    SInteger == SInteger = True
    SReal == SReal = True
    SText == SText = True
    SBlob == SBlob = True
    a == b = False

    a /= b = not (a == b)

StorageType : StorageDataType -> Type
StorageType SNull = ()
StorageType SInteger = Integer
StorageType SReal = Double
StorageType SText = String
StorageType SBlob = List Int

record Schema where
    constructor MkSchema
    columnCount : Nat
    columnTypes : Vect cols StorageDataType

SchemaType : Schema -> Type
SchemaType (MkSchema _ dts) = dtsToType dts
    where dtsToType : Vect n StorageDataType -> Type
          dtsToType [] = ()
          dtsToType [x] = StorageType x
          dtsToType (x :: xs) = (StorageType x, dtsToType xs)

record FieldsWithSameType where -- TODO: add constrains to make sure two fields has the same type
    constructor Fst
    fstSchema : Schema
    fstField0 : Fin (columnCount fstSchema)
    fstField1 : Fin (columnCount fstSchema)

data Condition : Schema -> Type where
    CondEq : (schema : Schema) ->
             (fields : FieldsWithSameType) ->
             Condition schema
