import Core4loop.TriangleLeaf.CompatibleResidualKCdSum
import Core4loop.TriangleLeaf.TotalQCdCoeffReadZero

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

def TotalCdCoeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : Prop :=
  ∀ i : LeafCdFamilyIndex n b, ∀ p : PVec n a, ∀ s : NonzeroI n,
    qLeafProfileKernelTotalCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
        i p s.1
      =
    qLeafProfileKernelTotalCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
        i p 0

theorem qLeafProfileKernelTotalCdCoeffRead_eq_zero_iff_condition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      TotalCdCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB := by
  simpa [TotalCdCoeffCondition] using
    qLeafProfileKernelTotalCdCoeffRead_eq_zero_iff_forall_coeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB

theorem leafCompatibleResidualSum_eq_after_kCd_totalCoeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              if TotalCdCoeffCondition
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) then
                (Fintype.card
                  (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ) *
                  bitSign
                    (qLeafProfileKernelTotalIndexDiff
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) (kCv, 0))
              else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_kCd_coeffRead
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  let C :=
    qLeafProfileKernelTotalCdCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  let P :=
    TotalCdCoeffCondition
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  have hiff : C = 0 ↔ P := by
    simpa [C, P] using
      qLeafProfileKernelTotalCdCoeffRead_eq_zero_iff_condition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  by_cases hP : P
  · rw [if_pos ((hiff).2 hP), if_pos hP]
  · have hC : C ≠ 0 := by
      intro h
      exact hP ((hiff).1 h)
    rw [if_neg hC, if_neg hP]

theorem leafCompatibleResidualSum_eq_after_kCd_totalCoeffCondition_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              if TotalCdCoeffCondition
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) then
                (2 : ℤ) ^ (n ^ (a + b) * (n - 1)) *
                  bitSign
                    (qLeafProfileKernelTotalIndexDiff
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) (kCv, 0))
              else 0 := by
  rw [leafCompatibleResidualSum_eq_after_kCd_totalCoeffCondition
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  by_cases hC :
      TotalCdCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  · rw [if_pos hC, if_pos hC]
    rw [intCast_card_kCdFamily (n := n) (a := a) (b := b) ha]
  · rw [if_neg hC, if_neg hC]

end

end TriangleLeaf
end Core4loop
