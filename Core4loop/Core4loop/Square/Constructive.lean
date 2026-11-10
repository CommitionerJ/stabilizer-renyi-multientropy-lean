import Core4loop.Square.Kernel

namespace Core4loop

noncomputable def SquareConstructiveExp (n a b c d : ℕ) [NeZero n] : ℕ :=
  n ^ (b + c + d) + n ^ (a + b + d)
    + Module.finrank F (SquareCombinedKernel n a b c d)

theorem SquareConstructiveExp_add_range {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) :
    SquareConstructiveExp n a b c d
      + Module.finrank F
        (LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)))
      =
      n ^ (b + c + d) + n ^ (a + b + d)
        + n ^ (a + c + d) + n ^ (a + b + c) := by
  unfold SquareConstructiveExp
  have h := finrank_range_SquareCombined_add_kernel
    (n := n) (a := a) (b := b) (c := c) (d := d) ha
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- The exponent contains the same nested-function-space kernel finrank as the card theorem.
theorem DeltaNF_square_constructive_closed {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) :
    DeltaNF .square a b c d n =
      (2 : ℤ) ^ SquareConstructiveExp n a b c d := by
  rw [DeltaNF_square_kernel_count (n := n) (a := a) (b := b) (c := c) (d := d) ha]
  have hcard :
      (Nat.card (SquareCombinedKernel n a b c d) : ℤ) =
        (2 : ℤ) ^ Module.finrank F (SquareCombinedKernel n a b c d) := by
    rw [natCard_SquareCombinedKernel (n := n) (a := a) (b := b) (c := c) (d := d)]
    norm_num
  rw [hcard]
  unfold SquareConstructiveExp
  rw [← pow_add, ← pow_add]
  congr 1
  omega

theorem SquareConstructiveExp_eq_X2Z_of_rank {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a)
    (hrank :
      SquareRankZ a b c d n =
        (Module.finrank F
          (LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ)) :
    (SquareConstructiveExp n a b c d : ℤ) = X2Z a b c d n := by
  let R :=
    LinearMap.range
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))
  have hsumNat := SquareConstructiveExp_add_range
    (n := n) (a := a) (b := b) (c := c) (d := d) ha
  have hsumZ :
      (SquareConstructiveExp n a b c d : ℤ) + (Module.finrank F R : ℤ) =
        Sigma1Z a b c d n := by
    have h := congrArg (fun x : ℕ => (x : ℤ)) hsumNat
    have h' :
        (SquareConstructiveExp n a b c d : ℤ) + (Module.finrank F R : ℤ) =
          nPowZ n (b + c + d) + nPowZ n (a + b + d)
            + nPowZ n (a + c + d) + nPowZ n (a + b + c) := by
      simpa [R, nPowZ] using h
    unfold Sigma1Z
    linarith
  rw [X2Z_eq_Sigma1_sub_SquareRankZ, hrank]
  linarith

theorem DeltaNF_square_closed_of_rank {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a)
    (hrank :
      SquareRankZ a b c d n =
        (Module.finrank F
          (LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ)) :
    DeltaNF .square a b c d n =
      (2 : ℤ) ^ Int.toNat (X2Z a b c d n) := by
  rw [DeltaNF_square_constructive_closed (n := n) (a := a) (b := b) (c := c) (d := d) ha]
  have hExp := SquareConstructiveExp_eq_X2Z_of_rank
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hrank
  rw [← hExp]
  simp

end Core4loop
