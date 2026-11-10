import Core4loop.TriangleLeaf.ProfileKernelIndexDiffCrossQ

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafCompatibleResidualSum_eq_canonicalIndexDiffSplitComponentSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        (∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            ∑ kCv : PassiveVisibleIndex n d hd →
                YVec n b → I n → LeafScalarProfileKernel n a,
              ∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
                bitSign
                  (qLeafProfileKernelIndexDiff
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    (kBv, kBd) (kCv, kCd))
                * bitSign
                  (qLeafProfileKernelCanonicalIndexDiff
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                    (kBv, kBd))
                * bitSign
                  (qLeafProfileCanonicalKernelIndexDiff
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                    (kCv, kCd)))
          *
          leafVisibleCanonicalBaseSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  rw [leafCompatibleResidualSum_eq_canonicalBaseWeightedInteractionSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  rw [leafVisibleCanonicalProfileKernelInteractionSum_eq_indexDiffSplitComponentSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]

end

end TriangleLeaf
end Core4loop
