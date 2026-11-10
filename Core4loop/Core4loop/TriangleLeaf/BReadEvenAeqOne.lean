import Core4loop.TriangleLeaf.BReadEvenClosed

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

theorem fintype_card_PVec_one {n : ℕ} [NeZero n] :
    Fintype.card (PVec n 1) = 1 := by
  simpa [PVec] using (card_vec n 0)

theorem PVec_one_subsingleton {n : ℕ} [NeZero n] :
    Subsingleton (PVec n 1) := by
  change Subsingleton (Fin 0 → I n)
  infer_instance

private theorem leafScalarProfileSum_PVec_one_eq
    {n : ℕ} [NeZero n] (C : LeafScalarProfile n 1) :
    leafScalarProfileSum (n := n) (a := 1) C =
      C (zeroVec : PVec n 1) := by
  classical
  haveI := PVec_one_subsingleton (n := n)
  change (∑ p : PVec n 1, C p) = C (zeroVec : PVec n 1)
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    exact (hp (Subsingleton.elim p (zeroVec : PVec n 1))).elim
  · simp

theorem leafScalarProfileKernel_one_subsingleton
    {n : ℕ} [NeZero n] :
    Subsingleton (LeafScalarProfileKernel n 1) := by
  classical
  haveI := PVec_one_subsingleton (n := n)
  refine ⟨?_⟩
  intro X Y
  apply Subtype.ext
  funext p
  have hp : p = (zeroVec : PVec n 1) :=
    Subsingleton.elim p (zeroVec : PVec n 1)
  have hXsum := LinearMap.mem_ker.mp X.2
  have hYsum := LinearMap.mem_ker.mp Y.2
  rw [leafScalarProfileSum_PVec_one_eq (n := n) X.1] at hXsum
  rw [leafScalarProfileSum_PVec_one_eq (n := n) Y.1] at hYsum
  rw [hp, hXsum, hYsum]

theorem leafScalarProfileKernel_one_eq_zero
    {n : ℕ} [NeZero n] (X : LeafScalarProfileKernel n 1) :
    X = 0 := by
  haveI := leafScalarProfileKernel_one_subsingleton (n := n)
  exact Subsingleton.elim X 0

theorem leafScalarProfileKernel_one_apply
    {n : ℕ} [NeZero n] (X : LeafScalarProfileKernel n 1)
    (p : PVec n 1) :
    X.1 p = 0 := by
  rw [leafScalarProfileKernel_one_eq_zero (n := n) X]
  rfl

theorem isEmpty_LeafBReadCvTargetIndex_one
    {n b d : ℕ} [NeZero n] (hd : 0 < d) :
    IsEmpty (LeafBReadCvTargetIndex n 1 b d hd) := by
  classical
  haveI := PVec_one_subsingleton (n := n)
  refine ⟨?_⟩
  intro i
  exact i.2.2 (Subsingleton.elim i.2.1 (zeroVec : PVec n 1))

theorem leafBReadTarget_one_cv_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n 1 b c d hd) :
    U.2 = 0 := by
  classical
  have hEmpty := isEmpty_LeafBReadCvTargetIndex_one
    (n := n) (b := b) (d := d) hd
  funext i
  exact (hEmpty.false i).elim

noncomputable def leafBReadTargetOneEquivCd
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafBReadTarget n 1 b c d hd ≃
      (LeafBReadCdTargetIndex n 1 b → F) where
  toFun U := U.1
  invFun Ucd := (Ucd, 0)
  left_inv U := by
    apply Prod.ext
    · rfl
    · exact (leafBReadTarget_one_cv_eq_zero
        (n := n) (b := b) (c := c) (d := d) hd U
      ).symm
  right_inv Ucd := rfl

noncomputable def leafBReadCdTargetIndexOneEquiv
    {n b : ℕ} [NeZero n] :
    LeafBReadCdTargetIndex n 1 b ≃ LeafCdFamilyIndex n b × NonzeroI n where
  toFun i := (i.1, i.2.2)
  invFun i := (i.1, ((zeroVec : PVec n 1), i.2))
  left_inv i := by
    classical
    haveI := PVec_one_subsingleton (n := n)
    rcases i with ⟨j, p, s⟩
    simp [Subsingleton.elim p (zeroVec : PVec n 1)]
  right_inv i := by
    rcases i with ⟨j, s⟩
    rfl

theorem card_LeafBReadCdTargetIndex_one
    {n b : ℕ} [NeZero n] :
    Fintype.card (LeafBReadCdTargetIndex n 1 b) =
      n ^ (b + 1) * (n - 1) := by
  classical
  rw [Fintype.card_congr
    (leafBReadCdTargetIndexOneEquiv (n := n) (b := b))]
  unfold LeafCdFamilyIndex
  rw [Fintype.card_prod, Fintype.card_prod, card_vec, card_NonzeroI]
  simp [I, ZMod.card]
  rw [pow_succ]
  exact Or.inl rfl

theorem card_LeafBReadTarget_one
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (LeafBReadTarget n 1 b c d hd) =
      2 ^ (n ^ (b + 1) * (n - 1)) := by
  classical
  letI : Fintype (LeafBReadCdTargetIndex n 1 b) :=
    instFintypeLeafBReadCdTargetIndex (n := n) (a := 1) (b := b)
  rw [Fintype.card_congr
    (leafBReadTargetOneEquivCd
      (n := n) (b := b) (c := c) (d := d) hd)]
  rw [Fintype.card_fun, card_LeafBReadCdTargetIndex_one]
  simp [F]

theorem leafBReadTargetDot_one_eq_cd
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U V : LeafBReadTarget n 1 b c d hd) :
    leafBReadTargetDot hd U V = coeffApply U.1 V.1 := by
  rw [leafBReadTargetDot]
  rw [leafBReadTarget_one_cv_eq_zero
    (n := n) (b := b) (c := c) (d := d) hd U]
  rw [leafBReadTarget_one_cv_eq_zero
    (n := n) (b := b) (c := c) (d := d) hd V]
  have hcv :
      coeffApply
          (0 : LeafBReadCvTargetIndex n 1 b d hd → F)
          (0 : LeafBReadCvTargetIndex n 1 b d hd → F) = 0 := by
    unfold coeffApply
    refine Finset.sum_eq_zero ?_
    intro i _
    exact ((isEmpty_LeafBReadCvTargetIndex_one
      (n := n) (b := b) (d := d) hd).false i).elim
  rw [hcv, add_zero]

theorem leafBReadFourierTailPhase_one_eq_cd
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n 1 b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd) :
    leafBReadFourierTailPhase
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd U XB
      =
    coeffApply U.1
      (((leafBReadTailReadMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd) XB).1) := by
  rw [leafBReadFourierTailPhase_eq_dot_tailRead]
  exact leafBReadTargetDot_one_eq_cd
    (n := n) (b := b) (c := c) (d := d) hd U
    ((leafBReadTailReadMap
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd) XB)

theorem leafBReadTailReadMap_one_cv_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd) :
    ((leafBReadTailReadMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd) XB).2 = 0 := by
  exact leafBReadTarget_one_cv_eq_zero
    (n := n) (b := b) (c := c) (d := d) hd
    ((leafBReadTailReadMap
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd) XB)

theorem leafBReadVisibleBAdjoint_one_cv_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (leafBReadVisibleBAdjoint
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd H).2 = 0 := by
  exact leafBReadTarget_one_cv_eq_zero
    (n := n) (b := b) (c := c) (d := d) hd
    (leafBReadVisibleBAdjoint
      (n := n) (a := 1) (b := b) (c := c) (d := d) hd H)

theorem leafBReadKernelScalarBTrace_one_apply
    {n c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n 1 c d hd)
    (ω : PassiveVisibleIndex n d hd) (sy : I n) (z : ZVec n c) :
    leafBReadKernelScalarBTrace
        (n := n) (a := 1) (c := c) (d := d) hd XB ω sy z
      =
    (XB.2 sy z (zeroVec : PVec n 1)).1 (vecSum ω.1) := by
  unfold leafBReadKernelScalarBTrace leafBKernelCanonicalScalarIndexDiff
  rw [leafScalarProfileKernel_one_apply
    (n := n) (X := XB.1 ω sy z) (p := zeroVec)]
  simp

theorem leafBReadCvDualScalarCTrace_one_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n 1 b c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafBReadCvDualScalarCTrace
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd U ω
      =
    0 := by
  ext y sz
  unfold leafBReadCvDualScalarCTrace
  refine Finset.sum_eq_zero ?_
  intro p _
  exact ((isEmpty_LeafBReadCvTargetIndex_one
    (n := n) (b := b) (d := d) hd).false ((ω, (y, sz)), p)).elim

theorem leafBReadDualScalarCTrace_one_eq_cd
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n 1 b c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafBReadDualScalarCTrace
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd U ω
      =
    leafBReadCdDualScalarCTrace
        (n := n) (a := 1) (b := b) (c := c) (d := d) hd U ω := by
  unfold leafBReadDualScalarCTrace
  rw [leafBReadCvDualScalarCTrace_one_eq_zero
    (n := n) (b := b) (c := c) (d := d) hd U ω]
  simp

noncomputable def leafBProfileKernelIndexDiffCoordOneEquivDiff
    {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafBProfileKernelIndexDiffCoord n 1 c d hd ≃
      (I n → ZVec n c → LeafDiffProfileCoord n 1) where
  toFun XB := XB.2
  invFun X := (0, X)
  left_inv XB := by
    apply Prod.ext
    · funext ω sy z
      exact (leafScalarProfileKernel_one_eq_zero (n := n) (XB.1 ω sy z)).symm
    · rfl
  right_inv X := rfl

theorem card_leafDiffProfileCoord_one
    {n : ℕ} [NeZero n] :
    Fintype.card (LeafDiffProfileCoord n 1) = 2 ^ (n - 1) := by
  classical
  rw [Fintype.card_congr
    (leafDiffProfileCoordEquivNonzero (n := n) (a := 1))]
  rw [Fintype.card_fun, Fintype.card_prod]
  rw [fintype_card_PVec_one, card_NonzeroI]
  simp [F]

theorem card_LeafBProfileKernelIndexDiffCoord_one
    {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (LeafBProfileKernelIndexDiffCoord n 1 c d hd) =
      ((2 ^ (n - 1)) ^ (n ^ c)) ^ n := by
  classical
  rw [Fintype.card_congr
    (leafBProfileKernelIndexDiffCoordOneEquivDiff
      (n := n) (c := c) (d := d) hd)]
  rw [Fintype.card_fun, Fintype.card_fun, card_vec]
  rw [card_leafDiffProfileCoord_one]
  simp [I, ZMod.card]

end

end TriangleLeaf
end Core4loop
