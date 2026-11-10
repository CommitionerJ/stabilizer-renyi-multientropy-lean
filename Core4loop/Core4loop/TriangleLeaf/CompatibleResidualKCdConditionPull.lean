import Core4loop.TriangleLeaf.CompatibleResidualKCdCoeffCondition

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

theorem leafCompatibleResidualSum_eq_after_kCd_totalCoeffCondition_kCvSum
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
                (∑ kCv : PassiveVisibleIndex n d hd →
                    YVec n b → I n → LeafScalarProfileKernel n a,
                  bitSign
                    (qLeafProfileKernelTotalIndexDiff
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) (kCv, 0)))
            else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_kCd_totalCoeffCondition_closedCard
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  by_cases hC :
      TotalCdCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  · simp only [hC, if_true]
    rw [Finset.mul_sum]
  · simp [hC]

end

end TriangleLeaf
end Core4loop
