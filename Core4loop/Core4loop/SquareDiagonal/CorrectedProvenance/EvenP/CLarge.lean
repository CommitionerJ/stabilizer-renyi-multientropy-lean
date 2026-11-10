import Core4loop.SquareDiagonal.CorrectedExponent
import Core4loop.SquareDiagonal.CorrectedProvenance.Definitions
import Core4loop.SquareDiagonal.CorrectedProvenance.CastSafety

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_one_d_one
    {n a c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a) (hc2 : 2 ≤ c) :
    X3FromHalfRankZ a 1 c 1 n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n 1 c 1) =
      X3PaperOldZ a 1 c 1 n +
        DiamondCorrectionZ n a 1 c 1 := by
  obtain ⟨c, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  have hc0 : c ≠ 0 := by omega
  have hcastc : ((n ^ c - 2 : Nat) : Int) = (n : Int) ^ c - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := c + 1) hn2 hc2)
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, hc2, hc0, Nat.succ_eq_add_one, Nat.reduceAdd,
    pow_one, ↓reduceIte, Nat.add_eq_right, add_tsub_cancel_right, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Nat.not_ofNat_le_one, and_false, sub_sub_cancel, mul_one, and_self,
    and_true, or_self, mul_zero, add_zero]
  rw [cast_n_sub_one hn1, hcastc]
  ring

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_one_d_ge_two
    {n a c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    X3FromHalfRankZ a 1 c d n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n 1 c d) =
      X3PaperOldZ a 1 c d n +
        DiamondCorrectionZ n a 1 c d := by
  obtain ⟨c, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  have hc0 : c ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  have hcastc : ((n ^ c - 2 : Nat) : Int) = (n : Int) ^ c - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := c + 1) hn2 hc2)
  have hcastd : ((n ^ d - 2 : Nat) : Int) = (n : Int) ^ d - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := d + 1) hn2 hd2)
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, hc2, hc0, hd2, hd0, Nat.succ_eq_add_one,
    pow_one, ↓reduceIte, Nat.add_eq_right, add_tsub_cancel_right, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Nat.not_ofNat_le_one, false_and, and_false, sub_sub_cancel, mul_one,
    true_and, false_or, Int.reduceNeg, mul_neg]
  rw [cast_n_sub_one hn1, hcastc, hcastd]
  ring

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_one
    {n a b c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    X3FromHalfRankZ a b c 1 n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n b c 1) =
      X3PaperOldZ a b c 1 n +
        DiamondCorrectionZ n a b c 1 := by
  obtain ⟨b, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  obtain ⟨c, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hcastb : ((n ^ b - 2 : Nat) : Int) = (n : Int) ^ b - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := b + 1) hn2 hb2)
  have hcastc : ((n ^ c - 2 : Nat) : Int) = (n : Int) ^ c - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := c + 1) hn2 hc2)
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, hb2, hb0, hc2, hc0, Nat.succ_eq_add_one,
    pow_one, Nat.add_eq_right, ↓reduceIte, add_tsub_cancel_right, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, sub_sub_cancel,
    mul_one, Nat.not_ofNat_le_one, and_false, and_true, or_false,
    Int.reduceNeg, mul_neg]
  rw [cast_n_sub_one hn1, hcastb, hcastc]
  ring

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_ge_two
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    X3FromHalfRankZ a b c d n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n b c d) =
      X3PaperOldZ a b c d n +
        DiamondCorrectionZ n a b c d := by
  obtain ⟨b, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  obtain ⟨c, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hd0 : d ≠ 0 := by omega
  have hcastb : ((n ^ b - 2 : Nat) : Int) = (n : Int) ^ b - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := b + 1) hn2 hb2)
  have hcastc : ((n ^ c - 2 : Nat) : Int) = (n : Int) ^ c - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := c + 1) hn2 hc2)
  have hcastd : ((n ^ d - 2 : Nat) : Int) = (n : Int) ^ d - 2 := by
    simpa using (cast_pow_pred_sub_two (n := n) (r := d + 1) hn2 hd2)
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, hb2, hb0, hc2, hc0, hd2, hd0,
    Nat.succ_eq_add_one, Nat.add_eq_right, add_tsub_cancel_right,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, mul_neg,
    ↓reduceIte, and_self]
  rw [cast_n_sub_one hn1, hcastb, hcastc, hcastd]
  ring

end Core4loop
