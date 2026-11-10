import Core4loop.TriangleLeaf.TotalQBConstLinear

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafVisibleKernelEquivCoord_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafVisibleKernelEquivCoord (n := n) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d)
      =
      0 := by
  funext ω
  apply Subtype.ext
  apply Prod.ext
  · funext sy z
    simp [leafVisibleKernelEquivCoord, leafVisiblePairEquivCoord]
  · funext y sz
    simp [leafVisibleKernelEquivCoord, leafVisiblePairEquivCoord]

theorem qLeafProfileKernelTotalCdCoeff_affine_split
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      qLeafProfileKernelTotalCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        +
      qLeafProfileKernelTotalCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  funext i p s
  unfold qLeafProfileKernelTotalCdCoeff qLeafProfileKernelRemainderCdCoeff
    qLeafScalarCanonicalProfileBlockCdCoeff
  simp [Pi.add_apply, hzero]

theorem qLeafProfileKernelTotalCdCoeffRead_affine_split
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      qLeafProfileKernelTotalCdCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        +
      qLeafProfileKernelTotalCdCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
  unfold qLeafProfileKernelTotalCdCoeffRead
  rw [qLeafProfileKernelTotalCdCoeff_affine_split
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  rw [leafDiffFamilyCoeffRead_add]

theorem qLeafProfileKernelTotalCvCoeff_affine_split
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      qLeafProfileKernelTotalCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        +
      qLeafProfileKernelTotalCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  funext i p
  unfold qLeafProfileKernelTotalCvCoeff qLeafProfileKernelRemainderCvCoeff
    qLeafProfileKernelRemainderCvCoeffLeft qLeafProfileKernelRemainderCvCoeffRight
    qLeafProfileKernelProfileCvCoeff qLeafProfileKernelProfileCvCoeffLeft
    qLeafProfileKernelProfileCvCoeffRight
    qLeafProfileKernelVisibleScalarCvCoeff qLeafProfileKernelVisibleScalarCvCoeffLeft
    qLeafProfileKernelVisibleScalarCvCoeffRight
  simp [Pi.add_apply, hzero]

theorem qLeafProfileKernelTotalCvCoeffRead_affine_split
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      qLeafProfileKernelTotalCvCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        +
      qLeafProfileKernelTotalCvCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
  unfold qLeafProfileKernelTotalCvCoeffRead
  rw [qLeafProfileKernelTotalCvCoeff_affine_split
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  rw [leafScalarFamilyCoeffRead_add]

theorem qLeafProfileKernelTotalBCoeffRead_affine_split
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalBCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        +
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
  apply Prod.ext
  · exact qLeafProfileKernelTotalCdCoeffRead_affine_split
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  · exact qLeafProfileKernelTotalCvCoeffRead_affine_split
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB

theorem qLeafProfileKernelTotalBCoeffRead_eq_zero_iff_zeroH_eq_const
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalBCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        =
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
  rw [qLeafProfileKernelTotalBCoeffRead_affine_split
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  exact add_eq_zero_iff_eq_of_F_module _ _

theorem TotalBCoeffCondition_iff_zeroH_read_eq_const
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    TotalBCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      ↔
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) XB
        =
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 := by
  rw [← qLeafProfileKernelTotalBCoeffRead_eq_zero_iff_condition
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  exact qLeafProfileKernelTotalBCoeffRead_eq_zero_iff_zeroH_eq_const
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB

end

end TriangleLeaf
end Core4loop
