import Core4loop.TriangleLeaf.AfterWResidual
import Core4loop.TriangleLeaf.ExceptionalResidual
import Core4loop.TriangleLeaf.CorrectedExponent

namespace Core4loop

open TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem correctionZ_regression_four :
    TriangleLeafCorrectionZ 1 2 2 2 4 = 60 := by
  norm_num [TriangleLeafCorrectionZ, TriangleLeafExceptional, mZ, nPowZ]

private theorem X1PaperOldZ_regression_four :
    X1PaperOldZ 1 2 2 2 4 = 5311 := by
  norm_num [X1PaperOldZ, Sigma1Z, Sigma2_1Z, ThetaZ, mZ, nPowZ]

private theorem X1CorrectedZ_regression_four :
    X1CorrectedZ 1 2 2 2 4 = 5251 := by
  norm_num [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, Sigma1Z, Sigma2_1Z, ThetaZ, mZ, nPowZ]

private theorem correctionZ_regression_two :
    TriangleLeafCorrectionZ 1 2 2 2 2 = 0 := by
  norm_num [TriangleLeafCorrectionZ, TriangleLeafExceptional, mZ, nPowZ]

/-- The `a=1` leaf-transfer kernel rank, derived only from the production
rank-nullity identity. -/
theorem exceptional_finrank_ker_KWMap_one
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker
          (KWMap (n := n) (a := 1) (b := b) (c := c) (d := d)))
      =
    n ^ (b + c) := by
  have h :=
    finrank_ker_KWMap_add
      (n := n) (a := 1) (b := b) (c := c) (d := d)
      (by omega) hd
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  have hpow :
      n ^ (1 + b + c) = n * n ^ (b + c) := by
    rw [show 1 + b + c = 1 + (b + c) by omega, pow_add]
    simp
  have hmul :
      n * n ^ (b + c)
        =
      (n - 1) * n ^ (b + c) + n ^ (b + c) := by
    have hn : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    nth_rw 1 [← hn]
    ring
  rw [hpow, hmul] at h
  omega

/-- Level-7 exceptional raw theorem.  The three powers are supplied,
respectively, by root-`A` elimination, the `KWMap` kernel, and the independently
evaluated compatible residual. -/
theorem DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_exceptional
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha : a = 1)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DeltaNF .triangleLeaf a b c d n
      =
    (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
  subst a
  have hd : 0 < d := by omega
  calc
    DeltaNF .triangleLeaf 1 b c d n
        =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := 1) (b := b) (c := c) (d := d))) *
          leafCompatibleResidualSum n 1 b c d) := by
            exact DeltaNF_triangleLeaf_after_WDiff
              (n := n) (a := 1) (b := b) (c := c) (d := d)
    _ =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ (n ^ (b + c)) *
          leafCompatibleResidualSum n 1 b c d) := by
            rw [exceptional_finrank_ker_KWMap_one
              (n := n) (b := b) (c := c) (d := d) hd]
    _ =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ (n ^ (b + c)) *
          (2 : ℤ) ^ TriangleLeafExceptionalResidualExpNat b c d n) := by
            rw [leafCompatibleResidualSum_eq_pow_exceptional_residual
              (n := n) (b := b) (c := c) (d := d)
              hn hb2 hc2 hd2]
            rfl
    _ =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        (2 : ℤ) ^
          (n ^ (b + c) +
            TriangleLeafExceptionalResidualExpNat b c d n) := by
              congr 1
              exact
                (pow_add (2 : ℤ) (n ^ (b + c))
                  (TriangleLeafExceptionalResidualExpNat b c d n)).symm
    _ =
      (2 : ℤ) ^
        (n ^ (b + c + d) +
          (n ^ (b + c) +
            TriangleLeafExceptionalResidualExpNat b c d n)) := by
              exact
                (pow_add (2 : ℤ) (n ^ (b + c + d))
                  (n ^ (b + c) +
                    TriangleLeafExceptionalResidualExpNat b c d n)).symm
    _ =
      (2 : ℤ) ^
        (n ^ (b + c + d) + n ^ (b + c)
          + TriangleLeafExceptionalResidualExpNat b c d n) := by
            congr 1
            exact
              (Nat.add_assoc (n ^ (b + c + d)) (n ^ (b + c))
                (TriangleLeafExceptionalResidualExpNat b c d n)).symm
    _ =
      (2 : ℤ) ^ Int.toNat (X1CorrectedZ 1 b c d n) := by
            congr 1
            have hbridge :=
              exceptional_residual_plus_front_eq_X1CorrectedZ
                (n := n) (b := b) (c := c) (d := d)
                hn hb2 hc2 hd2
            have hnat := congrArg Int.toNat hbridge
            simpa using hnat

private theorem DeltaNF_triangleLeaf_regression_two :
    DeltaNF .triangleLeaf 1 2 2 2 2 = (2 : ℤ) ^ 121 := by
  simpa [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, Sigma1Z, Sigma2_1Z, ThetaZ, nPowZ, mZ] using
    (DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_exceptional
      (n := 2) (a := 1) (b := 2) (c := 2) (d := 2)
      (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num))

set_option exponentiation.threshold 6000 in
private theorem DeltaNF_triangleLeaf_regression_four :
    DeltaNF .triangleLeaf 1 2 2 2 4 = (2 : ℤ) ^ 5251 := by
  have hxnat :
      Int.toNat (X1CorrectedZ 1 2 2 2 4) = 5251 := by
    have hxnonneg : 0 ≤ X1CorrectedZ 1 2 2 2 4 := by
      rw [X1CorrectedZ_regression_four]
      norm_num
    have hxcast :
        ((Int.toNat (X1CorrectedZ 1 2 2 2 4) : ℕ) : ℤ) = 5251 := by
      rw [Int.toNat_of_nonneg hxnonneg]
      exact X1CorrectedZ_regression_four
    exact_mod_cast hxcast
  rw [← hxnat]
  exact
    DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_exceptional
      (n := 4) (a := 1) (b := 2) (c := 2) (d := 2)
      (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num)

end

end Core4loop
