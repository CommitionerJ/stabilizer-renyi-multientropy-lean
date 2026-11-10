import Core4loop.Square.Rank.Core
import Core4loop.Square.Constructive

namespace Core4loop

lemma intCast_nat_sub_one_eq_mZ {n : ℕ} [NeZero n] :
    ((n - 1 : ℕ) : ℤ) = mZ n := by
  unfold mZ
  have hn : 1 ≤ n := one_le_of_neZero
  omega

lemma intCast_nat_pow_eq_nPowZ (n e : ℕ) :
    ((n ^ e : ℕ) : ℤ) = nPowZ n e := by
  simp [nPowZ]

theorem SquareRankZ_eq_rank_of_rank_add {rank a b c d n : ℕ} [NeZero n]
    (h :
      rank + (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ c + n ^ d) + (n - 1)
        =
        (n - 1) * (n ^ (c + d) + n ^ (a + d) + n ^ (a + b) + n ^ (b + c))
          + 2 * (n - 1) ^ 3) :
    SquareRankZ a b c d n = (rank : ℤ) := by
  have hInt :
      (rank : ℤ)
        + (((n - 1) ^ 2 * (n ^ a + n ^ b + n ^ c + n ^ d) : ℕ) : ℤ)
        + ((n - 1 : ℕ) : ℤ)
        =
        (((n - 1) *
            (n ^ (c + d) + n ^ (a + d) + n ^ (a + b) + n ^ (b + c))
            + 2 * (n - 1) ^ 3 : ℕ) : ℤ) := by
    exact_mod_cast h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hInt
  rw [intCast_nat_sub_one_eq_mZ (n := n)] at hInt
  unfold mZ at hInt
  unfold SquareRankZ Sigma2_2Z mZ nPowZ
  ring_nf at hInt ⊢
  linarith

theorem SquareRankZ_eq_finrank_range_of_rank_add {a b c d n : ℕ} [NeZero n]
    (h :
      Module.finrank F
          (LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)))
        + (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ c + n ^ d)
        + (n - 1)
      =
        (n - 1) * (n ^ (c + d) + n ^ (a + d) + n ^ (a + b) + n ^ (b + c))
          + 2 * (n - 1) ^ 3) :
    SquareRankZ a b c d n =
      (Module.finrank F
        (LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ) :=
  SquareRankZ_eq_rank_of_rank_add h

theorem DeltaNF_square_closed_of_rank_add {a b c d n : ℕ} [NeZero n]
    (ha : 0 < a)
    (h :
      Module.finrank F
          (LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)))
        + (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ c + n ^ d)
        + (n - 1)
      =
        (n - 1) * (n ^ (c + d) + n ^ (a + d) + n ^ (a + b) + n ^ (b + c))
          + 2 * (n - 1) ^ 3) :
    DeltaNF .square a b c d n =
      (2 : ℤ) ^ Int.toNat (X2Z a b c d n) :=
  DeltaNF_square_closed_of_rank (n := n) (a := a) (b := b) (c := c) (d := d) ha
    (SquareRankZ_eq_finrank_range_of_rank_add
      (n := n) (a := a) (b := b) (c := c) (d := d) h)

end Core4loop
