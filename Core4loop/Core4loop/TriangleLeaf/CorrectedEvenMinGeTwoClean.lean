import Core4loop.TriangleLeaf.E5Swap
import Core4loop.TriangleLeaf.AfterWResidual
import Core4loop.TriangleLeaf.CorrectedExponent

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private theorem leafCompatibleResidualSum_closed_triangleLeafE5_clean
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n a b c d =
      (2 : ℤ) ^
        Int.toNat (CompatibleResidualSplitZ a b c d n) := by
  rcases hdeg with hb1 | hc1
  · subst b
    exact leafCompatibleResidualSum_b_eq_one hn ha2 hc hd2
  · subst c
    calc
      leafCompatibleResidualSum n a b 1 d =
          leafCompatibleResidualSum n a 1 b d :=
        leafCompatibleResidualSum_swap
      _ =
          (2 : ℤ) ^
            Int.toNat (CompatibleResidualSplitZ a 1 b d n) :=
        leafCompatibleResidualSum_b_eq_one hn ha2 hb hd2
      _ =
          (2 : ℤ) ^
            Int.toNat (CompatibleResidualSplitZ a b 1 d n) := by
        rw [CompatibleResidualSplitZ_swap a b 1 d n]

set_option synthInstance.maxHeartbeats 100000 in
-- Nested kernel finrank inference needs more than the project default.
/-- Logical level 7: corrected raw TriangleLeaf Delta for the even E5 branch. -/
theorem DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_triangleLeafE5
    {n a b c d : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hdeg : b = 1 ∨ c = 1) (hd2 : 2 ≤ d) :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
  letI : NeZero n := ⟨by omega⟩
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
  have hresNonneg :
      0 ≤ CompatibleResidualSplitZ a b c d n := by
    rcases hdeg with hb1 | hc1
    · subst b
      calc
        (0 : ℤ) ≤
            (Module.finrank F
              (triangleLeafE5LB n a 1 c d) : ℤ) := by positivity
        _ = CompatibleResidualSplitZ a 1 c d n :=
          finrank_triangleLeafE5LB_eq_CompatibleResidualSplitZ
            hn ha2 hc hd
    · subst c
      rw [CompatibleResidualSplitZ_swap a b 1 d n]
      calc
        (0 : ℤ) ≤
            (Module.finrank F
              (triangleLeafE5LB n a 1 b d) : ℤ) := by positivity
        _ = CompatibleResidualSplitZ a 1 b d n :=
          finrank_triangleLeafE5LB_eq_CompatibleResidualSplitZ
            hn ha2 hb hd
  let totalExp : ℕ :=
    n ^ (b + c + d)
      + Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Int.toNat (CompatibleResidualSplitZ a b c d n)
  have htotalCast :
      (totalExp : ℤ) = X1CorrectedZ a b c d n := by
    rw [hcorrected]
    unfold totalExp
    rw [Nat.cast_add, Nat.cast_add]
    rw [Int.toNat_of_nonneg hresNonneg]
    rw [intCast_finrank_ker_KWMap_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
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
            (2 : ℤ) ^
              Int.toNat (CompatibleResidualSplitZ a b c d n)) := by
      rw [leafCompatibleResidualSum_closed_triangleLeafE5_clean
        hn ha2 hb hc hdeg hd2]
    _ = (2 : ℤ) ^ totalExp := by
      unfold totalExp
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    _ =
        (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c d n) := by
      rw [htotalNat]

end

end TriangleLeaf
end Core4loop
