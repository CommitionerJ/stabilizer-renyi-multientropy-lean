import Core4loop.SquareDiagonal.CorrectedExponent
import Core4loop.SquareDiagonal.CorrectedProvenance.Definitions
import Core4loop.SquareDiagonal.CorrectedProvenance.CastSafety

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_one_d_one
    {n a : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a) :
    X3FromHalfRankZ a 1 1 1 n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n 1 1 1) =
      X3PaperOldZ a 1 1 1 n +
        DiamondCorrectionZ n a 1 1 1 := by
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, Nat.reduceAdd, pow_one, ↓reduceIte, Nat.cast_mul,
    Nat.cast_pow, Nat.not_ofNat_le_one, and_self, and_false, sub_sub_cancel,
    mul_one, mul_zero, add_zero]
  rw [cast_n_sub_one hn1]
  ring

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_one_d_ge_two
    {n a d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a) (hd2 : 2 ≤ d) :
    X3FromHalfRankZ a 1 1 d n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n 1 1 d) =
      X3PaperOldZ a 1 1 d n +
        DiamondCorrectionZ n a 1 1 d := by
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  have hd1 : d ≠ 1 := by omega
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, hd2, hd1, pow_one, ↓reduceIte, Nat.cast_mul,
    Nat.cast_pow, Nat.reduceAdd, Nat.not_ofNat_le_one, and_self, and_false,
    false_and, sub_sub_cancel, mul_one, mul_zero, add_zero]
  rw [cast_n_sub_one hn1]
  ring

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_ge_two_d_one
    {n a b : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) :
    X3FromHalfRankZ a b 1 1 n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n b 1 1) =
      X3PaperOldZ a b 1 1 n +
        DiamondCorrectionZ n a b 1 1 := by
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  have hb1 : b ≠ 1 := by omega
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, hb2, hb1, pow_one, ↓reduceIte, Nat.cast_mul,
    Nat.cast_pow, Nat.reduceAdd, Nat.not_ofNat_le_one, and_false,
    sub_sub_cancel, mul_one, and_self, mul_zero, add_zero]
  rw [cast_n_sub_one hn1]
  ring

theorem X3FromHalfRankZ_evenP_eq_old_add_correction_of_even_c_one_b_ge_two_d_ge_two
    {n a b d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (ha2 : 2 ≤ a)
    (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    X3FromHalfRankZ a b 1 d n
        (SquareDiagonal.EvenP.diamondEvenPTotalHalfRank n b 1 d) =
      X3PaperOldZ a b 1 d n +
        DiamondCorrectionZ n a b 1 d := by
  have hn1 : 1 ≤ n := by omega
  have ha1 : a ≠ 1 := by omega
  have hb1 : b ≠ 1 := by omega
  have hd1 : d ≠ 1 := by omega
  unfold X3FromHalfRankZ X3PaperOldZ X3Z
    SquareDiagonal.EvenP.diamondEvenPTotalHalfRank
    DiamondCorrectionZ DiamondOverlapKappaZ
  unfold Sigma2_3Z ThetaZ nPowZ mZ
  simp only [hn, ha2, ha1, hb2, hb1, hd2, hd1, ↓reduceIte, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, pow_one, Nat.not_ofNat_le_one, and_self,
    and_false, false_and]
  rw [cast_n_sub_one hn1]
  ring

end Core4loop
