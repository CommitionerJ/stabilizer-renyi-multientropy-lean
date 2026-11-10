import Core4loop.TriangleLeaf.CompatibleResidualKCvCard
import Core4loop.TriangleLeaf.TotalQCvCoeffApply

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

theorem leafCompatibleResidualSum_eq_after_kCv_totalCvCoeffCondition_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            if TotalCdCoeffCondition
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd
                  H (kBv, kBd) then
              (2 : ℤ) ^ (n ^ (a + b) * (n - 1)) *
                (if TotalCvCoeffCondition
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) then
                  (2 : ℤ) ^
                    (((n ^ (a - 1) - 1) * n) * n ^ b * (n ^ d - (n - 1))) *
                    bitSign
                      (qLeafProfileKernelTotalCvConst
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd
                        H (kBv, kBd))
                else 0)
            else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_kCv_totalCoeffCondition_closedCard
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  by_cases hCd :
      TotalCdCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H (kBv, kBd)
  · simp only [hCd, if_true]
    let L :=
      qLeafProfileKernelTotalCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H (kBv, kBd)
    let P :=
      TotalCvCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H (kBv, kBd)
    have hiff : L = 0 ↔ P := by
      simpa [L, P] using
        qLeafProfileKernelTotalCvLinearMap_eq_zero_iff_coeffCondition
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H (kBv, kBd)
    by_cases hP : P
    · rw [if_pos ((hiff).2 hP), if_pos hP]
    · have hL : L ≠ 0 := by
        intro h
        exact hP ((hiff).1 h)
      rw [if_neg hL, if_neg hP]
  · simp [hCd]

end

end TriangleLeaf
end Core4loop
