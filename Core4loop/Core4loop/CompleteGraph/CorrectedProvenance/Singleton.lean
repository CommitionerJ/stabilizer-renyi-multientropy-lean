import Core4loop.CompleteGraph.CorrectedProvenance.CorrectionDefinitions
import Core4loop.CompleteGraph.CorrectedProvenance.Definitions

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

open CompleteGraph.SingletonLC

noncomputable section

theorem ThetaZ_swap12_k4_provenance (r s t n : Nat) :
    ThetaZ r s t n = ThetaZ s r t n := by
  unfold ThetaZ
  simp only [and_left_comm]

theorem ThetaZ_swap23_k4_provenance (r s t n : Nat) :
    ThetaZ r s t n = ThetaZ r t s n := by
  unfold ThetaZ
  simp only [and_comm]

theorem X4PaperOldZ_swap12 (a b c d n : Nat) :
    X4PaperOldZ a b c d n = X4PaperOldZ b a c d n := by
  unfold X4PaperOldZ X4Z Sigma1Z Sigma2_4Z
  rw [ThetaZ_swap12_k4_provenance a b c n,
    ThetaZ_swap12_k4_provenance a b d n]
  simp only [nPowZ, pow_add]
  ring

theorem X4PaperOldZ_swap23 (a b c d n : Nat) :
    X4PaperOldZ a b c d n = X4PaperOldZ a c b d n := by
  unfold X4PaperOldZ X4Z Sigma1Z Sigma2_4Z
  rw [ThetaZ_swap23_k4_provenance a b c n]
  rw [ThetaZ_swap12_k4_provenance b c d n]
  simp only [nPowZ, pow_add]
  ring

theorem X4PaperOldZ_swap34 (a b c d n : Nat) :
    X4PaperOldZ a b c d n = X4PaperOldZ a b d c n := by
  unfold X4PaperOldZ X4Z Sigma1Z Sigma2_4Z
  rw [ThetaZ_swap23_k4_provenance a c d n,
    ThetaZ_swap23_k4_provenance b c d n]
  simp only [nPowZ, pow_add]
  ring

theorem k4ThetaCorrectionZ_of_odd
    {n r s t : Nat} (hn : Odd n) :
    k4ThetaCorrectionZ r s t n = 0 := by
  have hnot : ¬ Even n := Nat.not_even_iff_odd.mpr hn
  unfold k4ThetaCorrectionZ k4GenericThetaZ ThetaZ
  simp [hnot]

theorem k4ThetaCorrectionZ_of_even_large
    {n r s t : Nat} (hn : Even n)
    (hr2 : 2 <= r) (hs2 : 2 <= s) (ht2 : 2 <= t) :
    k4ThetaCorrectionZ r s t n =
      -(mZ n * ((n : Int) - 2)) := by
  unfold k4ThetaCorrectionZ k4GenericThetaZ ThetaZ
  simp only [hn, hr2, hs2, ht2, and_self, if_true]
  unfold mZ
  ring

set_option synthInstance.maxHeartbeats 1000000 in
-- The finite function-space instance search needs a bounded local budget increase.
set_option maxHeartbeats 10000000 in
-- The canonical singleton row combines a large finite-space rank identity with integer arithmetic.
private theorem k4StarExpNat_add_theta_defect_eq_X4PaperOldZ_a_one
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (K4StarExpNat n b c d : Int) +
        (ThetaZ b c d n - k4GenericThetaZ n) =
      X4PaperOldZ 1 b c d n := by
  have hk := finrank_ker_K_yzw_add
    (n := n) (a := 1) (b := b) (c := c) (d := d)
    (by omega) hb hc hd
  have hkZ := congrArg (fun q : Nat => (q : Int)) hk
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hkZ
  have hn1 : 1 <= n := one_le_of_neZero (n := n)
  rw [Nat.cast_sub hn1] at hkZ
  have h1bc :
      ¬ (Even n ∧ 2 <= (1 : Nat) ∧ 2 <= b ∧ 2 <= c) := by omega
  have h1bd :
      ¬ (Even n ∧ 2 <= (1 : Nat) ∧ 2 <= b ∧ 2 <= d) := by omega
  have h1cd :
      ¬ (Even n ∧ 2 <= (1 : Nat) ∧ 2 <= c ∧ 2 <= d) := by omega
  unfold K4StarExpNat X4PaperOldZ X4Z Sigma1Z Sigma2_4Z nPowZ ThetaZ
    k4GenericThetaZ mZ
  simp only [h1bc, h1bd, h1cd, if_false]
  simp only [pow_add, pow_one] at hkZ ⊢
  norm_num at hkZ ⊢
  linear_combination hkZ

theorem k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_a_one
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (K4StarExpNat n b c d : Int) =
      X4PaperOldZ 1 b c d n + k4ThetaCorrectionZ b c d n := by
  rw [← k4StarExpNat_add_theta_defect_eq_X4PaperOldZ_a_one hb hc hd]
  unfold k4ThetaCorrectionZ
  ring

theorem k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_b_one
    {n a c d : Nat} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    (K4StarExpNat n a c d : Int) =
      X4PaperOldZ a 1 c d n + k4ThetaCorrectionZ a c d n := by
  rw [X4PaperOldZ_swap12 a 1 c d n]
  exact k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_a_one ha hc hd

theorem k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_c_one
    {n a b d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    (K4StarExpNat n a b d : Int) =
      X4PaperOldZ a b 1 d n + k4ThetaCorrectionZ a b d n := by
  rw [X4PaperOldZ_swap23 a b 1 d n]
  rw [X4PaperOldZ_swap12 a 1 b d n]
  exact k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_a_one ha hb hd

theorem k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_d_one
    {n a b c : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (K4StarExpNat n a b c : Int) =
      X4PaperOldZ a b c 1 n + k4ThetaCorrectionZ a b c n := by
  rw [X4PaperOldZ_swap34 a b c 1 n]
  rw [X4PaperOldZ_swap23 a b 1 c n]
  rw [X4PaperOldZ_swap12 a 1 b c n]
  exact k4StarExpNat_eq_X4PaperOldZ_add_thetaCorrection_a_one ha hb hc

end
end Core4loop
