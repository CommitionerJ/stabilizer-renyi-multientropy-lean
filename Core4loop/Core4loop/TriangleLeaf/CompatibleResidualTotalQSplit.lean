import Core4loop.TriangleLeaf.ProfileBlockSignQ

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def qLeafProfileKernelTotalIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  qLeafProfileKernelRemainderIndexDiff
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC
  +
  ∑ ω : PassiveVisibleIndex n d hd,
    qLeafScalarCanonicalProfileBlock
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω

theorem leafCompatibleResidualSum_eq_canonicalIndexDiffTotalQComponentSum
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
                  (qLeafProfileKernelTotalIndexDiff
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd) (kCv, kCd)) := by
  rw [leafCompatibleResidualSum_eq_canonicalIndexDiffProfileBlockComponentSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  refine Finset.sum_congr rfl ?_
  intro kCv _
  refine Finset.sum_congr rfl ?_
  intro kCd _
  rw [prod_leafScalarCanonicalProfileBlockSign_eq_bitSign_sum_qBlock
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    (kBv, kBd) (kCv, kCd)]
  unfold qLeafProfileKernelTotalIndexDiff
  rw [bitSign_add]

end

end TriangleLeaf
end Core4loop
