module Proofs.Nat

%access public export
%default total


||| n0 <= n1 -> n0 + c <= n1 + c
plusConstantRightLTE : (p : LTE n0 n1) -> (c : Nat) ->
                       LTE (n0 + c) (n1 + c)
plusConstantRightLTE {n0} {n1} p Z =
  rewrite plusZeroRightNeutral n0 in
  rewrite plusZeroRightNeutral n1 in
  p
plusConstantRightLTE {n0} {n1} p (S k) =
  let hypothesis = plusConstantRightLTE p k in
  rewrite plusLemma1 n0 k in
  rewrite plusLemma1 n1 k in
  LTESucc hypothesis
  where plusLemma1 : (n, k : Nat) -> (n + (S k)) = S (n + k)
        plusLemma1 Z k = Refl
        plusLemma1 (S j) k = let hypothesis = plusLemma1 j k in
                          rewrite hypothesis in
                          Refl
