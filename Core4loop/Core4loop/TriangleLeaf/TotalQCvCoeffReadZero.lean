import Core4loop.TriangleLeaf.TotalQCvCoeffApply

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def qLeafProfileKernelTotalCvCoeffRead
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    LeafCvFamilyIndex n b d hd
      × {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F :=
  leafScalarFamilyCoeffRead
    (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
    (qLeafProfileKernelTotalCvCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)

theorem qLeafProfileKernelTotalCvCoeffRead_eq_zero_iff_condition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      TotalCvCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB := by
  simpa [qLeafProfileKernelTotalCvCoeffRead, TotalCvCoeffCondition] using
    leafScalarFamilyCoeffRead_eq_zero_iff_condition
      (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
      (qLeafProfileKernelTotalCvCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)

end

end TriangleLeaf
end Core4loop
