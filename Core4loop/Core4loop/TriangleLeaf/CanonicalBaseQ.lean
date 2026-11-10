import Core4loop.TriangleLeaf.CanonicalProfileKernelInteraction
import Core4loop.TriangleLeaf.PassiveDot
import Core4loop.TriangleLeaf.ScalarBlocks

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private lemma sum_yzω_comm
    {Y Z Ω : Type*} [Fintype Y] [Fintype Z] [Fintype Ω]
    (f : Y → Z → Ω → F) :
    (∑ y : Y, ∑ z : Z, ∑ ω : Ω, f y z ω)
      =
      ∑ ω : Ω, ∑ y : Y, ∑ z : Z, f y z ω := by
  calc
    (∑ y : Y, ∑ z : Z, ∑ ω : Ω, f y z ω)
        = ∑ y : Y, ∑ ω : Ω, ∑ z : Z, f y z ω := by
            refine Finset.sum_congr rfl ?_
            intro y _
            rw [Finset.sum_comm]
    _ = ∑ ω : Ω, ∑ y : Y, ∑ z : Z, f y z ω := by
            rw [Finset.sum_comm]

theorem passiveDot_visibleSpace_eq_index_sum
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (f g : PassiveVisibleSpace n d hd) :
    passiveDot (n := n) (d := d) f.1 g.1 =
      ∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd g ω := by
  classical
  let s : Finset (WVec n d) :=
    (Finset.univ : Finset (WVec n d)).filter
      (fun w => ¬ passiveExcludedPred (n := n) (d := d) hd w)
  have hfilter :
      (∑ w : WVec n d, f.1 w * g.1 w)
        =
      s.sum (fun w => f.1 w * g.1 w) := by
    subst s
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro w _
    by_cases hw : passiveExcludedPred (n := n) (d := d) hd w
    · rcases hw with ⟨s, hs, rfl⟩
      simp [passiveExcludedPred, f.2 s hs]
    · simp [hw]
  unfold passiveDot
  rw [hfilter]
  calc
    s.sum (fun w => f.1 w * g.1 w)
      =
      ∑ w : {w : WVec n d //
          ¬ passiveExcludedPred (n := n) (d := d) hd w},
        f.1 w.1 * g.1 w.1 := by
        subst s
        simpa using
          (Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset (WVec n d)))
            (p := fun w => ¬ passiveExcludedPred (n := n) (d := d) hd w)
            (f := fun w => f.1 w * g.1 w)).symm
    _ =
      ∑ ω : PassiveVisibleIndex n d hd,
        f.1 ω.1 * g.1 ω.1 := by
        let e := passiveVisibleIndexEquivComplement (n := n) (d := d) hd
        simpa [e] using
          (Equiv.sum_comp e
            (fun w : {w : WVec n d //
                ¬ passiveExcludedPred (n := n) (d := d) hd w} =>
              f.1 w.1 * g.1 w.1)).symm
    _ =
      ∑ ω : PassiveVisibleIndex n d hd,
        passiveVisibleSpaceEquivIndex (n := n) (d := d) hd f ω *
          passiveVisibleSpaceEquivIndex (n := n) (d := d) hd g ω := by
        rfl

theorem leafDotProfile_canonicalBase_eq_passiveDot
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (VB : LeafBVisible n c d) (VC : LeafCVisible n b d)
    (sy : I n) (z : ZVec n c) (y : YVec n b) (sz : I n) :
    leafDotProfile
        (leafBProfile
          (leafBVisCanonicalBase
            (n := n) (a := a) (c := c) (d := d) hd VB) sy z)
        (leafCProfile
          (leafCVisCanonicalBase
            (n := n) (a := a) (b := b) (d := d) hd VC) y sz)
      =
      passiveDot (n := n) (d := d)
        (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (VB sy z)).1
        (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (VC y sz)).1 := by
  unfold leafDotProfile passiveDot
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · simp [leafBProfile, leafCProfile, leafBVisCanonicalBase, leafCVisCanonicalBase]
  · intro p _ hp
    simp [leafBProfile, leafCProfile, leafBVisCanonicalBase,
      leafCVisCanonicalBase, hp]
  · simp

theorem leafDotProfile_canonicalBase_eq_index_sum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (VB : LeafBVisible n c d) (VC : LeafCVisible n b d)
    (sy : I n) (z : ZVec n c) (y : YVec n b) (sz : I n) :
    leafDotProfile
        (leafBProfile
          (leafBVisCanonicalBase
            (n := n) (a := a) (c := c) (d := d) hd VB) sy z)
        (leafCProfile
          (leafCVisCanonicalBase
            (n := n) (a := a) (b := b) (d := d) hd VC) y sz)
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VB sy z) ω *
          passiveQuotEquivVisibleIndex (n := n) (d := d) hd (VC y sz) ω := by
  rw [leafDotProfile_canonicalBase_eq_passiveDot
    (n := n) (a := a) (b := b) (c := c) (d := d) hd VB VC sy z y sz]
  rw [passiveDot_visibleSpace_eq_index_sum
    (n := n) (d := d) hd
    (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (VB sy z))
    (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (VC y sz))]
  rfl

theorem qLeafLeft_canonicalBase_eq_sum_qLeftScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    qLeafLeft
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qLeftScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2 := by
  unfold qLeafLeft
  simp_rw [leafDotProfile_canonicalBase_eq_index_sum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H.1.1 H.1.2]
  rw [sum_yzω_comm]
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [Core3loop.qLeftScalar_eq_sum_yz]
  rfl

theorem qLeafRight_canonicalBase_eq_sum_qRightScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    qLeafRight
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qRightScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2 := by
  unfold qLeafRight
  simp_rw [leafDotProfile_canonicalBase_eq_index_sum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H.1.1 H.1.2]
  rw [sum_yzω_comm]
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [Core3loop.qRightScalar_eq_sum_yz]
  rfl

theorem qLeafProfile_canonicalBase_eq_sum_qScalar
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    qLeafProfile
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2 := by
  unfold qLeafProfile
  rw [qLeafLeft_canonicalBase_eq_sum_qLeftScalar
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H,
    qLeafRight_canonicalBase_eq_sum_qRightScalar
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ω _
  rfl

end

end TriangleLeaf
end Core4loop
