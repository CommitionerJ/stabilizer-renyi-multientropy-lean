import Core4loop.TriangleLeaf.AfterWResidual
import Core4loop.TriangleLeaf.E6ResidualFinal
import Core4loop.TriangleLeaf.CorrectedExponent

namespace Core4loop
namespace TriangleLeaf

noncomputable section

set_option synthInstance.maxHeartbeats 100000 in
-- Nested kernel finrank inference needs more than the project default.
/-- Logical level 7: raw TriangleLeaf Delta for the even all-large branch. -/
theorem DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_even_large
    {n a b c d : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
  have ha : 0 < a := by omega
  have hd : 0 < d := by omega
  have hnot : ¬ TriangleLeafExceptional n a b c d := by
    intro hex
    unfold TriangleLeafExceptional at hex
    omega
  have hcorrected :
      X1CorrectedZ a b c d n = X1Z a b c d n := by
    unfold X1CorrectedZ
    rw [X1PaperOldZ_eq_current_X1Z]
    rw [correctionZ_nonexceptional hnot, sub_zero]
  let totalExp : ℕ :=
    n ^ (b + c + d)
      + Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (triangleLeafE5LB n a b c d)
  have htotalCast :
      (totalExp : ℤ) = X1CorrectedZ a b c d n := by
    rw [hcorrected]
    unfold totalExp
    rw [Nat.cast_add, Nat.cast_add]
    rw [intCast_finrank_ker_KWMap_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
    rw [finrank_triangleLeafE5LB_eq_CompatibleResidualSplitZ_even_large
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2 hb2 hc2 hd]
    change
      nPowZ n (b + c + d)
          + TriangleLeafAfterWKernelExpZ a b c d n
          + CompatibleResidualSplitZ a b c d n =
        X1Z a b c d n
    rw [CompatibleResidualSplitZ_eq_CompatibleResidualExpZ
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
    rw [← X1Z_eq_afterW_plus_compatible
      (n := n) (a := a) (b := b) (c := c) (d := d)]
  have htotalNat :
      totalExp = Int.toNat (X1CorrectedZ a b c d n) := by
    have h := congrArg Int.toNat htotalCast
    simpa using h
  calc
    DeltaNF .triangleLeaf a b c d n =
        (2 : ℤ) ^ (n ^ (b + c + d)) *
          ((2 : ℤ) ^ Module.finrank F
            (LinearMap.ker
              (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) *
            leafCompatibleResidualSum n a b c d) :=
      DeltaNF_triangleLeaf_after_WDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)
    _ =
        (2 : ℤ) ^ (n ^ (b + c + d)) *
          ((2 : ℤ) ^ Module.finrank F
            (LinearMap.ker
              (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) *
            (2 : ℤ) ^ Module.finrank F
              (triangleLeafE5LB n a b c d)) := by
      rw [leafCompatibleResidualSum_even_large_eq_pow_finrank
        hn2 hn ha2 hb2 hc2 hd2]
    _ = (2 : ℤ) ^ totalExp := by
      unfold totalExp
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ = (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
      rw [htotalNat]

end

end TriangleLeaf
end Core4loop
