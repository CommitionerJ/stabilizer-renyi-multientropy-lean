import Core4loop.SquareDiagonal.CorrectedExponent
import Core4loop.SquareDiagonal.CorrectedProvenance.Definitions

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X3FromHalfRankZ_odd_eq_X3PaperOldZ
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    X3FromHalfRankZ a b c d n
        (SquareDiagonal.DirectWitt.diamondOddHalfRank n b c d) =
      X3PaperOldZ a b c d n := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  have hbpow : 1 ≤ n ^ b := Nat.one_le_pow b n hn1
  have hcpow : 1 ≤ n ^ c := Nat.one_le_pow c n hn1
  have hdpow : 1 ≤ n ^ d := Nat.one_le_pow d n hn1
  have habc :
      ¬ TriangleCore.specialBranch a (b + 1) (c + 1) n := by
    intro h
    exact Nat.not_even_iff_odd.mpr hn h.1
  have hacd :
      ¬ TriangleCore.specialBranch a (c + 1) (d + 1) n := by
    intro h
    exact Nat.not_even_iff_odd.mpr hn h.1
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
  rw [TriangleCore.ThetaZ_eq_of_not_special habc,
    TriangleCore.ThetaZ_eq_of_not_special hacd]
  unfold SquareDiagonal.DirectWitt.diamondOddHalfRank
    Sigma2_3Z nPowZ mZ
  simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_sub hn1, Nat.cast_sub hbpow,
    Nat.cast_sub hcpow, Nat.cast_sub hdpow, Nat.cast_one,
    pow_succ]
  simp only [pow_add, pow_succ]
  ring

theorem X3CorrectedZ_eq_old_add_correction_of_odd
    {n a b c d : Nat} [NeZero n]
    (hn : Odd n) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    X3CorrectedZ a b c d n =
      X3PaperOldZ a b c d n +
        DiamondCorrectionZ n a b c d := by
  rw [X3CorrectedZ_of_odd hn]
  rw [X3FromHalfRankZ_odd_eq_X3PaperOldZ hn hb hc hd]
  rw [DiamondCorrectionZ_of_odd hn, add_zero]

end Core4loop
