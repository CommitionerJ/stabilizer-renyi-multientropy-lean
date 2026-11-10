import Core4loop.TriangleLeaf.PassiveDotIndex
import Core4loop.TriangleLeaf.LeafProfileKernelDecomposition
import Core4loop.TriangleLeaf.LeafProfileKernelFullCoordinates

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafDotProfile_visibleDiff_symm_apply_index
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafVisibleProfileCoord n a d hd × LeafDiffProfileCoord n a) :
    leafDotProfile
        ((leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm X)
        ((leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm Y)
      =
      ∑ p : PVec n a,
        ((∑ ω : PassiveVisibleIndex n d hd,
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (X.1 p) ω *
            passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (Y.1 p) ω)
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (X.1 p) ω *
            (Y.2 p).1 (vecSum ω.1))
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.2 p).1 (vecSum ω.1) *
            passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (Y.1 p) ω)
          +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n, (X.2 p).1 s * (Y.2 p).1 s) := by
  rw [leafDotProfile_eq_sum_passiveDot]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [leafProfileEquivVisibleDiff_symm_apply
    (n := n) (a := a) (d := d) hd X p]
  rw [leafProfileEquivVisibleDiff_symm_apply
    (n := n) (a := a) (d := d) hd Y p]
  exact passiveDot_visibleDiff_symm_apply_index
    (n := n) (d := d) hd (X.1 p, X.2 p) (Y.1 p, Y.2 p)

theorem leafDotProfile_kernel_visibleDiff_symm_apply_index
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafVisibleProfileKernel n a d hd × LeafDiffProfileCoord n a) :
    leafDotProfile
        (((leafProfileKernelEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm X).1)
        (((leafProfileKernelEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm Y).1)
      =
      ∑ p : PVec n a,
        ((∑ ω : PassiveVisibleIndex n d hd,
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (X.1.1 p) ω *
            passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (Y.1.1 p) ω)
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (X.1.1 p) ω *
            (Y.2 p).1 (vecSum ω.1))
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.2 p).1 (vecSum ω.1) *
            passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (Y.1.1 p) ω)
          +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n, (X.2 p).1 s * (Y.2 p).1 s) := by
  change
    leafDotProfile
        ((leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm (X.1.1, X.2))
        ((leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm (Y.1.1, Y.2))
      =
      ∑ p : PVec n a,
        ((∑ ω : PassiveVisibleIndex n d hd,
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (X.1.1 p) ω *
            passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (Y.1.1 p) ω)
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (X.1.1 p) ω *
            (Y.2 p).1 (vecSum ω.1))
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.2 p).1 (vecSum ω.1) *
            passiveVisibleSpaceEquivIndex (n := n) (d := d) hd (Y.1.1 p) ω)
          +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n, (X.2 p).1 s * (Y.2 p).1 s)
  exact leafDotProfile_visibleDiff_symm_apply_index
    (n := n) (a := a) (d := d) hd (X.1.1, X.2) (Y.1.1, Y.2)

theorem passiveVisible_index_leafVisibleProfileKernelEquivIndex_symm
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (G : PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
    (p : PVec n a) (ω : PassiveVisibleIndex n d hd) :
    passiveVisibleSpaceEquivIndex (n := n) (d := d) hd
        (((leafVisibleProfileKernelEquivIndex
          (n := n) (a := a) (d := d) hd).symm G).1 p) ω
      =
      (G ω).1 p := by
  let V :=
    (leafVisibleProfileKernelEquivIndex
      (n := n) (a := a) (d := d) hd).symm G
  have hV :
      leafVisibleProfileKernelEquivIndex
          (n := n) (a := a) (d := d) hd V = G :=
    (leafVisibleProfileKernelEquivIndex
      (n := n) (a := a) (d := d) hd).right_inv G
  have hω := congrFun hV ω
  have hval := congrArg Subtype.val hω
  change
    (leafVisibleProfileCoordEquivIndex
      (n := n) (a := a) (d := d) hd V.1) ω p =
      (G ω).1 p
  exact congrFun hval p

theorem leafDotProfile_kernel_indexDiff_symm_apply_index
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y :
      (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        × LeafDiffProfileCoord n a) :
    leafDotProfile
        (((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).symm X).1)
        (((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).symm Y).1)
      =
      ∑ p : PVec n a,
        ((∑ ω : PassiveVisibleIndex n d hd,
          (X.1 ω).1 p * (Y.1 ω).1 p)
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.1 ω).1 p * (Y.2 p).1 (vecSum ω.1))
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.2 p).1 (vecSum ω.1) * (Y.1 ω).1 p)
          +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n, (X.2 p).1 s * (Y.2 p).1 s) := by
  change
    leafDotProfile
        (((leafProfileKernelEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm
          (((leafVisibleProfileKernelEquivIndex
            (n := n) (a := a) (d := d) hd).symm X.1), X.2)).1)
        (((leafProfileKernelEquivVisibleDiff
          (n := n) (a := a) (d := d) hd).symm
          (((leafVisibleProfileKernelEquivIndex
            (n := n) (a := a) (d := d) hd).symm Y.1), Y.2)).1)
      =
      ∑ p : PVec n a,
        ((∑ ω : PassiveVisibleIndex n d hd,
          (X.1 ω).1 p * (Y.1 ω).1 p)
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.1 ω).1 p * (Y.2 p).1 (vecSum ω.1))
          +
        (∑ ω : PassiveVisibleIndex n d hd,
          (X.2 p).1 (vecSum ω.1) * (Y.1 ω).1 p)
          +
        (Fintype.card (Vec n (d - 1)) : F) *
          ∑ s : I n, (X.2 p).1 s * (Y.2 p).1 s)
  rw [leafDotProfile_kernel_visibleDiff_symm_apply_index
    (n := n) (a := a) (d := d) hd
    (((leafVisibleProfileKernelEquivIndex
      (n := n) (a := a) (d := d) hd).symm X.1), X.2)
    (((leafVisibleProfileKernelEquivIndex
      (n := n) (a := a) (d := d) hd).symm Y.1), Y.2)]
  simp_rw [passiveVisible_index_leafVisibleProfileKernelEquivIndex_symm
    (n := n) (a := a) (d := d) hd]

end

end TriangleLeaf
end Core4loop
