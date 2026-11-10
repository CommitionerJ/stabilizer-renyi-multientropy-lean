import Core4loop.TriangleLeaf.CompatibleResidualVisibleRemainderSplit
import Core4loop.TriangleLeaf.CanonicalVisibleBaseSign

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafScalarCanonicalProfileBlockSign
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd)
    (ω : PassiveVisibleIndex n d hd) : ℤ :=
  bitSign
    (Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
      (leafScalarBProfileKernelCoordEquivCore3BWodd
        (n := n) (a := a) (c := c) (XB.1 ω)).1
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b) (XC.1 ω)).1)
  *
  bitSign
    (Core3loop.qScalar (b := b) (c := c) (n := n)
      (leafBKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (c := c) (d := d) hd XB ω)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)
  *
  bitSign
    (Core3loop.qScalar (b := b) (c := c) (n := n)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
      (leafCKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd XC ω))
  *
  bitSign
    (Core3loop.qScalar (b := b) (c := c) (n := n)
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
      ((leafVisibleKernelEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)

theorem prod_leafScalarCanonicalProfileBlockSign_eq_products
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    (∏ ω : PassiveVisibleIndex n d hd,
      leafScalarCanonicalProfileBlockSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω)
      =
      (∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
            (leafScalarBProfileKernelCoordEquivCore3BWodd
              (n := n) (a := a) (c := c) (XB.1 ω)).1
            (leafScalarCProfileKernelCoordEquivCore3CWodd
              (n := n) (a := a) (b := b) (XC.1 ω)).1))
      *
      (∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            (leafBKernelCanonicalScalarIndexDiff
              (n := n) (a := a) (c := c) (d := d) hd XB ω)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2))
      *
      (∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
            (leafCKernelCanonicalScalarIndexDiff
              (n := n) (a := a) (b := b) (d := d) hd XC ω)))
      *
      (∏ ω : PassiveVisibleIndex n d hd,
        bitSign
          (Core3loop.qScalar (b := b) (c := c) (n := n)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)) := by
  unfold leafScalarCanonicalProfileBlockSign
  simp_rw [Finset.prod_mul_distrib]

theorem leafCompatibleResidualSum_eq_canonicalIndexDiffProfileBlockComponentSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              ∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
                bitSign
                  (qLeafProfileKernelRemainderIndexDiff
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    (kBv, kBd) (kCv, kCd))
                *
                (∏ ω : PassiveVisibleIndex n d hd,
                  leafScalarCanonicalProfileBlockSign
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) (kCv, kCd) ω) := by
  rw [leafCompatibleResidualSum_eq_canonicalIndexDiffVisibleRemainderComponentSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro kBv _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro kBd _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro kCv _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro kCd _
  rw [leafVisibleCanonicalBaseSign_eq_product_bitSign_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  rw [prod_leafScalarCanonicalProfileBlockSign_eq_products
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    (kBv, kBd) (kCv, kCd)]
  ring

end

end TriangleLeaf
end Core4loop
