import Data.Vect

myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs) =
  let result = myReverse xs ++ [x] in
      rewrite plusCommutative 1 k in result

reverseProof : Vect (len + 1) elem -> Vect (S len) elem
reverseProof {len} result = rewrite plusCommutative 1 len in result

myReverse1 : Vect n elem -> Vect n elem
myReverse1 [] = []
myReverse1 (x :: xs) = reverseProof (reverse xs ++ [x])

zeroNotEqSucc : (0 = S k) -> Void
zeroNotEqSucc Refl impossible

succNotEqZero : (S k = 0) -> Void
succNotEqZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat :  (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotEqSucc
checkEqNat (S k) Z = No succNotEqZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              (Yes prf) => Yes (cong prf)
                              (No contra) => No (noRec contra)


