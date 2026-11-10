import Core4loop.TriangleLeaf.TotalQCdLinear
import Core4loop.TriangleLeaf.TotalQCdCoeffApply
import Core4loop.TriangleLeaf.KCdCard

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafCompatibleResidualSum_eq_after_kCd_linearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              if qLeafProfileKernelTotalCdExplicitLinearMap
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) = 0 then
                (Fintype.card
                  (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ) *
                  bitSign
                    (qLeafProfileKernelTotalIndexDiff
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) (kCv, 0))
              else 0 := by
  rw [leafCompatibleResidualSum_eq_canonicalIndexDiffTotalQComponentSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  exact sum_kCd_bitSign_qLeafProfileKernelTotalIndexDiff_eq_if_linearMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd) kCv

theorem leafCompatibleResidualSum_eq_after_kCd_linearMap_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              if qLeafProfileKernelTotalCdExplicitLinearMap
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) = 0 then
                (2 : ℤ) ^ (n ^ (a + b) * (n - 1)) *
                  bitSign
                    (qLeafProfileKernelTotalIndexDiff
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) (kCv, 0))
              else 0 := by
  rw [leafCompatibleResidualSum_eq_after_kCd_linearMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  by_cases hL :
      qLeafProfileKernelTotalCdExplicitLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd) = 0
  · rw [if_pos hL, if_pos hL]
    rw [intCast_card_kCdFamily (n := n) (a := a) (b := b) ha]
  · rw [if_neg hL, if_neg hL]

theorem leafCompatibleResidualSum_eq_after_kCd_coeffRead
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              if qLeafProfileKernelTotalCdCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) = 0 then
                (Fintype.card
                  (YVec n b → I n → LeafDiffProfileCoord n a) : ℤ) *
                  bitSign
                    (qLeafProfileKernelTotalIndexDiff
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) (kCv, 0))
              else 0 := by
  rw [leafCompatibleResidualSum_eq_after_kCd_linearMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  let L :=
    qLeafProfileKernelTotalCdExplicitLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  let C :=
    qLeafProfileKernelTotalCdCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  have hiff : L = 0 ↔ C = 0 := by
    simpa [L, C] using
      qLeafProfileKernelTotalCdExplicitLinearMap_eq_zero_iff_coeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  by_cases hC : C = 0
  · rw [if_pos ((hiff).2 hC), if_pos hC]
  · have hL : L ≠ 0 := by
      intro h
      exact hC ((hiff).1 h)
    rw [if_neg hL, if_neg hC]

theorem leafCompatibleResidualSum_eq_after_kCd_coeffRead_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              if qLeafProfileKernelTotalCdCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) = 0 then
                (2 : ℤ) ^ (n ^ (a + b) * (n - 1)) *
                  bitSign
                    (qLeafProfileKernelTotalIndexDiff
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) (kCv, 0))
              else 0 := by
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
  by_cases hC :
      qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd) = 0
  · rw [if_pos hC, if_pos hC]
    rw [intCast_card_kCdFamily (n := n) (a := a) (b := b) ha]
  · rw [if_neg hC, if_neg hC]

end

end TriangleLeaf
end Core4loop
