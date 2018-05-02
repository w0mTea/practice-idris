module Proofs.Nat

%access public export
%default total


||| n0 <= n1 -> n0 + c <= n1 + c
ltePlusConstantRight : (c : Nat) ->
                       (p : LTE n0 n1) ->
                       LTE (n0 + c) (n1 + c)
ltePlusConstantRight {n0} {n1} Z p =
  rewrite plusZeroRightNeutral n0 in
  rewrite plusZeroRightNeutral n1 in
  p
ltePlusConstantRight {n0} {n1} (S k) p =
  let hypothesis = ltePlusConstantRight k p in
  rewrite plusLemma1 n0 k in
  rewrite plusLemma1 n1 k in
  LTESucc hypothesis
  where plusLemma1 : (n, k : Nat) -> (n + (S k)) = S (n + k)
        plusLemma1 Z k = Refl
        plusLemma1 (S j) k = let hypothesis = plusLemma1 j k in
                          rewrite hypothesis in
                          Refl


||| n0 <= n1 -> c + n0 <= c + n1
ltePlusConstantLeft : (c : Nat) ->
                      (p : LTE n0 n1) ->
                      LTE (c + n0) (c + n1)
ltePlusConstantLeft {n0} {n1} c p =
  rewrite plusCommutative c n0 in
  rewrite plusCommutative c n1 in
  ltePlusConstantRight c p


||| n0 <= n1 -> n0 <= n1 + c
lteAddNatRight : (c : Nat) -> (p : LTE n0 n1) ->
                 LTE n0 (n1 + c)
lteAddNatRight {n0} {n1} c p =
  let goal0 = the (LTE n1 (n1 + c)) (lteAddRight n1) in
  lteTransitive p goal0


||| n0 <= n1, k0 <= k1 -> n0 + k0 <= n1 + k1
ltePlusNatRight : (p0 : LTE n0 n1) ->
                  (p1 : LTE k0 k1) ->
                  LTE (n0 + k0) (n1 + k1)
ltePlusNatRight {n0 = n0} {n1 = n1} {k0 = Z} {k1 = k1} p0 p1 =
  rewrite plusZeroRightNeutral n0 in
  lteAddNatRight k1 p0
ltePlusNatRight {n0 = n0} {n1 = n1} {k0 = (S kk0)} {k1 = (S kk1)} p0 (LTESucc p3) =
  let idh = ltePlusNatRight p0 p3 in
  rewrite sym (plusSuccRightSucc n0 kk0) in
  rewrite sym (plusSuccRightSucc n1 kk1) in
  LTESucc idh
