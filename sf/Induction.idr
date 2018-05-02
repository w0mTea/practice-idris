plus_n_Z : (n : Nat) -> n = n + Z
plus_n_Z Z = Refl
plus_n_Z (S k) =
  let inductiveHypothesis = plus_n_Z k in
  rewrite inductiveHypothesis in
  Refl

mult_0_r : (n : Nat) -> n * 0 = 0
mult_0_r Z = Refl
mult_0_r (S k) =
  let inductiveHypothesis = mult_0_r k in
  rewrite inductiveHypothesis in
  Refl
