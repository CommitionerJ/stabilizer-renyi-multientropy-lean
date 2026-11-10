import Core4loop.TriangleLeaf.CompatibleResidualScalarProductSplit
import Core4loop.TriangleLeaf.ProfileKernelIndexDiffVisibleSign

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafCompatibleResidualSum_eq_canonicalIndexDiffVisibleRemainderComponentSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        (∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              ∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
                ((∏ ω : PassiveVisibleIndex n d hd,
                  bitSign
                    (Core3loop.qProfileABC
                      (a := a) (b := b) (c := c) (n := n)
                      (leafScalarBProfileKernelCoordEquivCore3BWodd
                        (n := n) (a := a) (c := c) (kBv ω)).1
                      (leafScalarCProfileKernelCoordEquivCore3CWodd
                        (n := n) (a := a) (b := b) (kCv ω)).1))
                *
                bitSign
                  (qLeafProfileKernelRemainderIndexDiff
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    (kBv, kBd) (kCv, kCd)))
                *
                (∏ ω : PassiveVisibleIndex n d hd,
                  bitSign
                    (Core3loop.qScalar (b := b) (c := c) (n := n)
                      (leafBKernelCanonicalScalarIndexDiff
                        (n := n) (a := a) (c := c) (d := d) hd
                        (kBv, kBd) ω)
                      ((leafVisibleKernelEquivCoord
                        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2))
                *
                (∏ ω : PassiveVisibleIndex n d hd,
                  bitSign
                    (Core3loop.qScalar (b := b) (c := c) (n := n)
                      ((leafVisibleKernelEquivCoord
                        (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
                      (leafCKernelCanonicalScalarIndexDiff
                        (n := n) (a := a) (b := b) (d := d) hd
                        (kCv, kCd) ω))))
          *
          leafVisibleCanonicalBaseSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  rw [leafCompatibleResidualSum_eq_canonicalIndexDiffScalarProductComponentSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine congrArg (fun x : ℤ => x *
    leafVisibleCanonicalBaseSign
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H) ?_
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  refine Finset.sum_congr rfl ?_
  intro kCd _
  rw [bitSign_qLeafProfileKernelIndexDiff_eq_visibleProd_mul_remainder
    (n := n) (a := a) (b := b) (c := c) (d := d) hd
    (kBv, kBd) (kCv, kCd)]

end

end TriangleLeaf
end Core4loop
