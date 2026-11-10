import Core4loop.TriangleLeaf.LeafProfileKernelSplitDims

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def leafProfileKernelEquivIndexDiff
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafProfileKernel n a d ≃ₗ[F]
      (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        × LeafDiffProfileCoord n a :=
  (leafProfileKernelEquivVisibleDiff (n := n) (a := a) (d := d) hd).trans
    (LinearEquiv.prodCongr
      (leafVisibleProfileKernelEquivIndex (n := n) (a := a) (d := d) hd)
      (LinearEquiv.refl F (LeafDiffProfileCoord n a)))

theorem leafProfileKernelEquivIndexDiff_apply_fst
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (K : LeafProfileKernel n a d) :
    (leafProfileKernelEquivIndexDiff (n := n) (a := a) (d := d) hd K).1 =
      leafVisibleProfileKernelEquivIndex (n := n) (a := a) (d := d) hd
        ((leafProfileKernelEquivVisibleDiff
          (n := n) (a := a) (d := d) hd K).1) := rfl

theorem leafProfileKernelEquivIndexDiff_apply_snd
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (K : LeafProfileKernel n a d) :
    (leafProfileKernelEquivIndexDiff (n := n) (a := a) (d := d) hd K).2 =
      (leafProfileKernelEquivVisibleDiff
        (n := n) (a := a) (d := d) hd K).2 := rfl

theorem leafProfileKernelEquivIndexDiff_apply_fst_value
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (K : LeafProfileKernel n a d) (ω : PassiveVisibleIndex n d hd) :
    ((leafProfileKernelEquivIndexDiff
      (n := n) (a := a) (d := d) hd K).1 ω : LeafScalarProfile n a)
      =
      (leafVisibleProfileCoordEquivIndex
        (n := n) (a := a) (d := d) hd
        ((leafProfileEquivVisibleDiff
          (n := n) (a := a) (d := d) hd K.1).1)) ω := by
  rfl

theorem finrank_LeafProfileKernel_index_diff
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (LeafProfileKernel n a d) =
      Module.finrank F
          (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        + Module.finrank F (LeafDiffProfileCoord n a) := by
  calc
    Module.finrank F (LeafProfileKernel n a d)
        =
        Module.finrank F
          ((PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
            × LeafDiffProfileCoord n a) := by
          exact LinearEquiv.finrank_eq
            (leafProfileKernelEquivIndexDiff
              (n := n) (a := a) (d := d) hd)
    _ =
        Module.finrank F
          (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
          + Module.finrank F (LeafDiffProfileCoord n a) := by
          simp

theorem card_LeafProfileKernel_index_diff
    {n a d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (LeafProfileKernel n a d) =
      Fintype.card (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        * Fintype.card (LeafDiffProfileCoord n a) := by
  classical
  rw [Fintype.card_congr
    (leafProfileKernelEquivIndexDiff
      (n := n) (a := a) (d := d) hd).toEquiv]
  rw [Fintype.card_prod]

end

end TriangleLeaf
end Core4loop
