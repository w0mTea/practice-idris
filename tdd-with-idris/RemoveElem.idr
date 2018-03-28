import Data.Vect

data MyElem : a -> Vect k a -> Type where
     Here : MyElem x (x :: xs)
     There : (later : MyElem x xs) -> MyElem x (y :: xs)

notInNil : MyElem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (value = x) -> Void) -> (notThere : MyElem value xs -> Void) -> MyElem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

myIsElem : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (MyElem value xs)
myIsElem value [] = No notInNil
myIsElem value (x :: xs) = case decEq value x of
                                (Yes Refl) => Yes Here
                                (No notHere) => (case (myIsElem value xs) of
                                                     (Yes prf) => Yes (There prf)
                                                     (No notThere) => No ((notInTail notHere notThere)))

data MyElemL : a -> List a -> Type where
     HereL : MyElemL x (x :: xs)
     ThereL : (later : MyElemL x xs) -> MyElemL x (y :: xs)
     
notInNilL : MyElemL value [] -> Void
notInNilL HereL impossible
notInNilL (ThereL _) impossible

notInTailL : (notThere : MyElemL value xs -> Void) -> (notHere : (value = x) -> Void) -> MyElemL value (x :: xs) -> Void
notInTailL notThere notHere HereL = notHere Refl
notInTailL notThere notHere (ThereL later) = notThere later

myIsElemL : DecEq ty => (value : ty) -> (xs : List ty) -> Dec (MyElemL value xs)
myIsElemL value [] = No notInNilL
myIsElemL value (x :: xs) = case decEq value x of
                                 (Yes Refl) => Yes HereL
                                 (No notHere) => (case myIsElemL value xs of
                                                       (Yes prf) => Yes (ThereL prf)
                                                       (No notThere) => No (notInTailL notThere notHere))
                                                       
data Last : List ty -> ty -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value
     
notInNil1 : Last [] value -> Void
notInNil1 LastOne impossible
notInNil1 (LastCons _) impossible

notLast : (contra : (value = x) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast contra (LastCons prf) = notInNil1 prf

notLast1 : (contra : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notLast1 contra (LastCons prf) = contra prf

isLast : DecEq ty => (value : ty) -> (xs : List ty) -> Dec (Last xs value)
isLast value [] = No notInNil1
isLast value [x] = case decEq value x of
                        (Yes Refl) => Yes LastOne
                        (No contra) => No (notLast contra)
isLast value (x :: y :: xs) = case (isLast value (y :: xs)) of
                                   (Yes prf) => Yes (LastCons prf)
                                   (No contra) => No (notLast1 contra)
