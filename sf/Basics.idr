plus_Z_n : n = Z + n
plus_Z_n = Refl

plus_1_l : (n : Nat) -> 1 + n = S n
plus_1_l n = Refl

mult_0_l : (n : Nat) -> 0 * n = 0
mult_0_l n = Refl

plus_n_Z : n = n + Z
plus_n_Z = ?plus_n_Z_rhs

plus_id_example : (m, n : Nat) -> m = n -> m + m = n + n
plus_id_example m n prf = rewrite prf in Refl

plus_id_exercise : (m, n, o : Nat) -> n = m -> m = o -> n + m = m + o
plus_id_exercise m n o prf prf1 = 
  rewrite prf in
  rewrite prf1 in
  Refl
  
plus_1_neq_0 : (n : Nat) -> Not (n + 1 = 0)
plus_1_neq_0 Z = \Refl impossible
plus_1_neq_0 (S k) = \Refl impossible
