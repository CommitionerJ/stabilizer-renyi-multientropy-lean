import Core4loop.TriangleLeaf.TotalQBAffine

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

theorem leafCompatibleResidualSum_eq_after_XB_BCoeffRead_eq_const_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          if qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                (0 : LeafVisibleKernel n b c d) XB
              =
              qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
            (2 : ℤ) ^ kCdCvElimExpNat n a b d *
              bitSign
                (qLeafProfileKernelTotalCvConst
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
          else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_XB_totalCoeffCondition_closedCard
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro XB _
  rw [TotalBCoeffCondition_iff_zeroH_read_eq_const
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  by_cases h :
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        =
        qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0
  · simp [h]
  · simp [h]

theorem leafCompatibleResidualSum_eq_after_XB_BCoeffRead_eq_const_affineCv
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          if qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                (0 : LeafVisibleKernel n b c d) XB
              =
              qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
            (2 : ℤ) ^ kCdCvElimExpNat n a b d *
              bitSign
                (qLeafProfileKernelTotalCvConstLinearMap
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                  +
                  qLeafProfileKernelTotalCvVisibleConst
                    (n := n) (b := b) (c := c) (d := d) hd H)
          else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_XB_BCoeffRead_eq_const_closedCard
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro XB _
  rw [qLeafProfileKernelTotalCvConst_eq_linear_add_visibleConst
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]

end

end TriangleLeaf
end Core4loop
