import Core4loop.TriangleLeaf.ProfileKernelIndexDiffFun
import Core4loop.TriangleLeaf.CanonicalProfileKernelInteraction

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafVisibleCanonicalProfileKernelIndexDiffInteractionSign
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : ℤ :=
  leafVisibleCanonicalProfileKernelInteractionSign
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    ((leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd).symm XB)
    ((leafCProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (b := b) (d := d) hd).symm XC)

theorem leafVisibleCanonicalProfileKernelInteractionSum_eq_indexDiffSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafVisibleCanonicalProfileKernelInteractionSum n a b c d hd H =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        ∑ XC : LeafCProfileKernelIndexDiffCoord n a b d hd,
          leafVisibleCanonicalProfileKernelIndexDiffInteractionSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC := by
  classical
  let eB :=
    (leafBProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd).toEquiv
  let eC :=
    (leafCProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (b := b) (d := d) hd).toEquiv
  unfold leafVisibleCanonicalProfileKernelInteractionSum
  calc
    (∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
      ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
        leafVisibleCanonicalProfileKernelInteractionSign
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC)
      =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
          leafVisibleCanonicalProfileKernelInteractionSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H
            (eB.symm XB) kC := by
        simpa [eB] using
          (Equiv.sum_comp eB
            (fun XB : LeafBProfileKernelIndexDiffCoord n a c d hd =>
              ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
                leafVisibleCanonicalProfileKernelInteractionSign
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                  (eB.symm XB) kC))
    _ =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        ∑ XC : LeafCProfileKernelIndexDiffCoord n a b d hd,
          leafVisibleCanonicalProfileKernelInteractionSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H
            (eB.symm XB) (eC.symm XC) := by
        refine Finset.sum_congr rfl ?_
        intro XB _
        simpa [eC] using
          (Equiv.sum_comp eC
            (fun XC : LeafCProfileKernelIndexDiffCoord n a b d hd =>
              leafVisibleCanonicalProfileKernelInteractionSign
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                (eB.symm XB) (eC.symm XC)))
    _ =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        ∑ XC : LeafCProfileKernelIndexDiffCoord n a b d hd,
          leafVisibleCanonicalProfileKernelIndexDiffInteractionSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC := by
        rfl

theorem leafVisibleCanonicalProfileKernelInteractionSum_eq_indexDiffComponentSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafVisibleCanonicalProfileKernelInteractionSum n a b c d hd H =
      ∑ kBv : PassiveVisibleIndex n d hd →
          I n → ZVec n c → LeafScalarProfileKernel n a,
        ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
          ∑ kCv : PassiveVisibleIndex n d hd →
              YVec n b → I n → LeafScalarProfileKernel n a,
            ∑ kCd : YVec n b → I n → LeafDiffProfileCoord n a,
              leafVisibleCanonicalProfileKernelIndexDiffInteractionSign
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                (kBv, kBd) (kCv, kCd) := by
  classical
  rw [leafVisibleCanonicalProfileKernelInteractionSum_eq_indexDiffSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  unfold LeafBProfileKernelIndexDiffCoord
    LeafCProfileKernelIndexDiffCoord
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  rw [Fintype.sum_prod_type]

end

end TriangleLeaf
end Core4loop
