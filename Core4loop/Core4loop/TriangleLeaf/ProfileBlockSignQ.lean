import Core4loop.TriangleLeaf.CompatibleResidualProfileBlockSplit

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private lemma prod_bitSign_eq_bitSign_sum {α : Type*} (s : Finset α)
    (f : α → F) :
    s.prod (fun a => bitSign (f a)) = bitSign (s.sum f) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [bitSign_zero]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, bitSign_add, ih]

def qLeafScalarCanonicalProfileBlock
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd)
    (ω : PassiveVisibleIndex n d hd) : F :=
  Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
    (leafScalarBProfileKernelCoordEquivCore3BWodd
      (n := n) (a := a) (c := c) (XB.1 ω)).1
    (leafScalarCProfileKernelCoordEquivCore3CWodd
      (n := n) (a := a) (b := b) (XC.1 ω)).1
  +
  Core3loop.qScalar (b := b) (c := c) (n := n)
    (leafBKernelCanonicalScalarIndexDiff
      (n := n) (a := a) (c := c) (d := d) hd XB ω)
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2
  +
  Core3loop.qScalar (b := b) (c := c) (n := n)
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
    (leafCKernelCanonicalScalarIndexDiff
      (n := n) (a := a) (b := b) (d := d) hd XC ω)
  +
  Core3loop.qScalar (b := b) (c := c) (n := n)
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
    ((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2

theorem leafScalarCanonicalProfileBlockSign_eq_bitSign_qBlock
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafScalarCanonicalProfileBlockSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω
      =
      bitSign
        (qLeafScalarCanonicalProfileBlock
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω) := by
  unfold leafScalarCanonicalProfileBlockSign qLeafScalarCanonicalProfileBlock
  repeat rw [bitSign_add]

theorem prod_leafScalarCanonicalProfileBlockSign_eq_bitSign_sum_qBlock
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    (∏ ω : PassiveVisibleIndex n d hd,
      leafScalarCanonicalProfileBlockSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω)
      =
      bitSign
        (∑ ω : PassiveVisibleIndex n d hd,
          qLeafScalarCanonicalProfileBlock
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω) := by
  rw [← prod_bitSign_eq_bitSign_sum
    (s := (Finset.univ : Finset (PassiveVisibleIndex n d hd)))
    (f := fun ω =>
      qLeafScalarCanonicalProfileBlock
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω)]
  refine Finset.prod_congr rfl ?_
  intro ω _
  rw [leafScalarCanonicalProfileBlockSign_eq_bitSign_qBlock
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB XC ω]

end

end TriangleLeaf
end Core4loop
