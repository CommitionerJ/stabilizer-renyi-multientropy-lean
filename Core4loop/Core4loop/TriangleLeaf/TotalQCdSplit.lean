import Core4loop.TriangleLeaf.CompatibleResidualTotalQSplit

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafCDiffCanonicalScalarIndexDiff
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a)
    (ω : PassiveVisibleIndex n d hd) : Core3loop.ScalarCCoef b n :=
  fun y sz => (kCd y sz (zeroVec : PVec n a)).1 (vecSum ω.1)

def qLeafProfileKernelTotalCdPart
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) : F :=
  qLeafProfileKernelTotalIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      H XB (kCv, kCd)
    +
  qLeafProfileKernelTotalIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      H XB (kCv, 0)

theorem qLeafProfileKernelTotalCdPart_zero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a) :
    qLeafProfileKernelTotalCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H XB kCv 0 = 0 := by
  unfold qLeafProfileKernelTotalCdPart
  exact F_add_self _

theorem qLeafProfileKernelTotalIndexDiff_eq_cdPart_add_cdZero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    qLeafProfileKernelTotalIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H XB (kCv, kCd)
      =
      qLeafProfileKernelTotalCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd
      +
      qLeafProfileKernelTotalIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H XB (kCv, 0) := by
  unfold qLeafProfileKernelTotalCdPart
  rw [add_assoc, F_add_self, add_zero]

theorem bitSign_qLeafProfileKernelTotalIndexDiff_eq_cdPart_mul_cdZero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, kCd))
      =
      bitSign
        (qLeafProfileKernelTotalCdPart
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd)
      *
      bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, 0)) := by
  rw [qLeafProfileKernelTotalIndexDiff_eq_cdPart_add_cdZero
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd]
  rw [bitSign_add]

theorem sum_kCd_bitSign_qLeafProfileKernelTotalIndexDiff_eq_cdPart_sum_mul_cdZero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : PassiveVisibleIndex n d hd →
      YVec n b → I n → LeafScalarProfileKernel n a) :
    (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
      bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, kCd)))
      =
      (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
        bitSign
          (qLeafProfileKernelTotalCdPart
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd))
      *
      bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, 0)) := by
  calc
    (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
      bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, kCd)))
        =
        ∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
          bitSign
            (qLeafProfileKernelTotalCdPart
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd)
          *
          bitSign
            (qLeafProfileKernelTotalIndexDiff
              (n := n) (a := a) (b := b) (c := c) (d := d) hd
              H XB (kCv, 0)) := by
          refine Finset.sum_congr rfl ?_
          intro kCd _
          rw [bitSign_qLeafProfileKernelTotalIndexDiff_eq_cdPart_mul_cdZero
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd]
    _ =
      (∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
        bitSign
          (qLeafProfileKernelTotalCdPart
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv kCd))
      *
      bitSign
        (qLeafProfileKernelTotalIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H XB (kCv, 0)) := by
        rw [Finset.sum_mul]

end

end TriangleLeaf
end Core4loop
