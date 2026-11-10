import Core4loop.TriangleLeaf.PassiveSpace

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def passiveExcludedPred {n d : ℕ} [NeZero n] (hd : 0 < d) (w : WVec n d) : Prop :=
  ∃ s : I n, s ≠ 0 ∧ w = vecSumRep (n := n) (k := d) hd s

abbrev PassiveExcludedIndex (n d : ℕ) [NeZero n] (hd : 0 < d) :=
  {w : WVec n d // passiveExcludedPred (n := n) (d := d) hd w}

abbrev PassiveVisibleIndex (n d : ℕ) [NeZero n] (hd : 0 < d) :=
  {w : WVec n d //
    ∀ s : I n, s ≠ 0 → w ≠ vecSumRep (n := n) (k := d) hd s}

noncomputable instance instFintypePassiveExcludedIndex {n d : ℕ} [NeZero n]
    (hd : 0 < d) :
    Fintype (PassiveExcludedIndex n d hd) := by
  classical
  letI : Finite (PassiveExcludedIndex n d hd) :=
    Finite.of_injective
      (fun w : PassiveExcludedIndex n d hd => (w.1 : WVec n d))
      (fun _ _ h => Subtype.ext h)
  exact Fintype.ofFinite (PassiveExcludedIndex n d hd)

noncomputable instance instFintypePassiveVisibleIndex {n d : ℕ} [NeZero n]
    (hd : 0 < d) :
    Fintype (PassiveVisibleIndex n d hd) := by
  classical
  letI : Finite (PassiveVisibleIndex n d hd) :=
    Finite.of_injective
      (fun w : PassiveVisibleIndex n d hd => (w.1 : WVec n d))
      (fun _ _ h => Subtype.ext h)
  exact Fintype.ofFinite (PassiveVisibleIndex n d hd)

def nonzeroToPassiveExcluded {n d : ℕ} [NeZero n] (hd : 0 < d) :
    NonzeroI n → PassiveExcludedIndex n d hd :=
  fun s =>
    ⟨vecSumRep (n := n) (k := d) hd s.1,
      ⟨s.1, s.2, rfl⟩⟩

theorem nonzeroToPassiveExcluded_injective {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Injective (nonzeroToPassiveExcluded (n := n) (d := d) hd) := by
  intro s t h
  apply Subtype.ext
  have hval := congrArg Subtype.val h
  have hsum := congrArg (vecSum (n := n) (k := d)) hval
  change
    vecSum (vecSumRep (n := n) (k := d) hd s.1)
      =
    vecSum (vecSumRep (n := n) (k := d) hd t.1) at hsum
  simpa [vecSum_vecSumRep (n := n) (k := d) hd] using hsum

theorem nonzeroToPassiveExcluded_surjective {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Surjective (nonzeroToPassiveExcluded (n := n) (d := d) hd) := by
  intro w
  rcases w.2 with ⟨s, hs, hw⟩
  refine ⟨⟨s, hs⟩, ?_⟩
  apply Subtype.ext
  exact hw.symm

def passiveExcludedEquivNonzero {n d : ℕ} [NeZero n] (hd : 0 < d) :
    NonzeroI n ≃ PassiveExcludedIndex n d hd :=
  Equiv.ofBijective (nonzeroToPassiveExcluded (n := n) (d := d) hd)
    ⟨nonzeroToPassiveExcluded_injective (n := n) (d := d) hd,
      nonzeroToPassiveExcluded_surjective (n := n) (d := d) hd⟩

theorem card_PassiveExcludedIndex {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (PassiveExcludedIndex n d hd) = n - 1 := by
  rw [← card_NonzeroI (n := n)]
  exact (Fintype.card_congr
    (passiveExcludedEquivNonzero (n := n) (d := d) hd)).symm

def passiveVisibleIndexEquivComplement {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveVisibleIndex n d hd ≃
      {w : WVec n d // ¬ passiveExcludedPred (n := n) (d := d) hd w} where
  toFun w :=
    ⟨w.1, by
      intro hw
      rcases hw with ⟨s, hs, hrep⟩
      exact w.2 s hs hrep⟩
  invFun w :=
    ⟨w.1, by
      intro s hs hrep
      exact w.2 ⟨s, hs, hrep⟩⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

theorem card_PassiveVisibleIndex {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (PassiveVisibleIndex n d hd) = n ^ d - (n - 1) := by
  classical
  calc
    Fintype.card (PassiveVisibleIndex n d hd)
        =
        Fintype.card {w : WVec n d //
          ¬ passiveExcludedPred (n := n) (d := d) hd w} := by
            exact Fintype.card_congr
              (passiveVisibleIndexEquivComplement (n := n) (d := d) hd)
    _ =
        Fintype.card (WVec n d)
          - Fintype.card (PassiveExcludedIndex n d hd) := by
            simp [PassiveExcludedIndex,
              Fintype.card_subtype_compl
                (passiveExcludedPred (n := n) (d := d) hd)]
    _ = n ^ d - (n - 1) := by
            rw [card_vec, card_PassiveExcludedIndex (n := n) (d := d) hd]

noncomputable def passiveRepProfileMap {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveRaw n d →ₗ[F] ZeroSumProfile n where
  toFun f :=
    pullProfile (n := n)
      (fun s : NonzeroI n => f (vecSumRep (n := n) (k := d) hd s.1))
  map_add' f g := by
    apply Subtype.ext
    funext s
    unfold pullProfile pullProfileVal
    by_cases hs : s = 0
    · simp [hs, Finset.sum_add_distrib]
    · simp [hs]
  map_smul' r f := by
    apply Subtype.ext
    funext s
    unfold pullProfile pullProfileVal
    by_cases hs : s = 0
    · simp [hs, Finset.mul_sum]
    · simp [hs]

noncomputable def passiveDiffPart {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveRaw n d →ₗ[F] PassiveRaw n d :=
  (PassiveDiffEmbed (n := n) (d := d)).comp
    (passiveRepProfileMap (n := n) (d := d) hd)

noncomputable def passiveVisiblePart {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveRaw n d →ₗ[F] PassiveRaw n d :=
  LinearMap.id + passiveDiffPart (n := n) (d := d) hd

noncomputable def PassiveVisibleSpace (n d : ℕ) [NeZero n] (hd : 0 < d) :
    Submodule F (PassiveRaw n d) where
  carrier := {f | ∀ s : I n, s ≠ 0 → f (vecSumRep (n := n) (k := d) hd s) = 0}
  zero_mem' := by
    intro s hs
    rfl
  add_mem' hf hg := by
    intro s hs
    simp [hf s hs, hg s hs]
  smul_mem' r f hf := by
    intro s hs
    simp [hf s hs]

theorem passiveVisiblePart_rep_nonzero {n d : ℕ} [NeZero n] (hd : 0 < d)
    (f : PassiveRaw n d) (s : I n) (hs : s ≠ 0) :
    passiveVisiblePart (n := n) (d := d) hd f
        (vecSumRep (n := n) (k := d) hd s) = 0 := by
  simp [passiveVisiblePart, passiveDiffPart, passiveRepProfileMap,
    PassiveDiffEmbed, pullProfile, pullProfileVal, hs,
    vecSum_vecSumRep (n := n) (k := d) hd, F_add_self]

theorem passiveVisiblePart_mem_visibleSpace {n d : ℕ} [NeZero n] (hd : 0 < d)
    (f : PassiveRaw n d) :
    passiveVisiblePart (n := n) (d := d) hd f ∈ PassiveVisibleSpace n d hd := by
  intro s hs
  exact passiveVisiblePart_rep_nonzero (n := n) (d := d) hd f s hs

noncomputable def passiveVisibleSpaceEquivIndex {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveVisibleSpace n d hd ≃ₗ[F] (PassiveVisibleIndex n d hd → F) where
  toFun f := fun w => f.1 w.1
  invFun g :=
    ⟨fun w =>
      if h : ∀ s : I n, s ≠ 0 → w ≠ vecSumRep (n := n) (k := d) hd s
      then g ⟨w, h⟩
      else 0,
      by
        intro s hs
        have hnot :
            ¬ (∀ t : I n,
              t ≠ 0 → vecSumRep (n := n) (k := d) hd s ≠
                vecSumRep (n := n) (k := d) hd t) := by
          intro h
          exact h s hs rfl
        simp [hnot]⟩
  left_inv f := by
    apply Subtype.ext
    funext w
    by_cases h :
        ∀ s : I n, s ≠ 0 → w ≠ vecSumRep (n := n) (k := d) hd s
    · change
        (if h' : ∀ s : I n,
          s ≠ 0 → w ≠ vecSumRep (n := n) (k := d) hd s
        then f.1 w
        else 0) = f.1 w
      rw [dif_pos h]
    · change
        (if h' : ∀ s : I n,
          s ≠ 0 → w ≠ vecSumRep (n := n) (k := d) hd s
        then f.1 w
        else 0) = f.1 w
      rw [dif_neg h]
      simp only [not_forall, Classical.not_not] at h
      rcases h with ⟨s, hs, hw⟩
      rw [hw]
      exact (f.2 s hs).symm
  right_inv g := by
    funext w
    change
      (if h : ∀ s : I n,
        s ≠ 0 → w.1 ≠ vecSumRep (n := n) (k := d) hd s
      then g (⟨w.1, h⟩ : PassiveVisibleIndex n d hd)
      else 0) = g w
    rw [dif_pos w.2]
  map_add' f g := by
    rfl
  map_smul' r f := by
    rfl

theorem finrank_PassiveVisibleSpace {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (PassiveVisibleSpace n d hd) = n ^ d - (n - 1) := by
  calc
    Module.finrank F (PassiveVisibleSpace n d hd)
        = Module.finrank F (PassiveVisibleIndex n d hd → F) := by
            exact LinearEquiv.finrank_eq
              (passiveVisibleSpaceEquivIndex (n := n) (d := d) hd)
    _ = Fintype.card (PassiveVisibleIndex n d hd) := by
            rw [← Module.finrank_fintype_fun_eq_card
              (R := F) (η := PassiveVisibleIndex n d hd)]
    _ = n ^ d - (n - 1) := card_PassiveVisibleIndex (n := n) (d := d) hd

theorem passiveRepProfileMap_PassiveDiffEmbed {n d : ℕ} [NeZero n] (hd : 0 < d)
    (R : ZeroSumProfile n) :
    passiveRepProfileMap (n := n) (d := d) hd
        (PassiveDiffEmbed (n := n) (d := d) R) = R := by
  apply Subtype.ext
  funext s
  change
    (pullProfile (n := n)
      (fun u : NonzeroI n =>
        (PassiveDiffEmbed (n := n) (d := d) R)
          (vecSumRep (n := n) (k := d) hd u.1))).1 s = R.1 s
  have hread :
      (fun u : NonzeroI n =>
        (PassiveDiffEmbed (n := n) (d := d) R)
          (vecSumRep (n := n) (k := d) hd u.1))
        =
      readProfile (n := n) R := by
    funext u
    simp [PassiveDiffEmbed, readProfile,
      vecSum_vecSumRep (n := n) (k := d) hd]
  rw [hread]
  exact congrFun (congrArg Subtype.val (pullProfile_readProfile (n := n) R)) s

theorem passiveVisiblePart_eq_zero_iff_mem_PassiveDiffSpace
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : PassiveRaw n d) :
    passiveVisiblePart (n := n) (d := d) hd f = 0
      ↔ f ∈ PassiveDiffSpace n d := by
  constructor
  · intro hzero
    refine ⟨passiveRepProfileMap (n := n) (d := d) hd f, ?_⟩
    funext w
    have hw := congrFun hzero w
    calc
      (PassiveDiffEmbed (n := n) (d := d)
          (passiveRepProfileMap (n := n) (d := d) hd f)) w
          = passiveDiffPart (n := n) (d := d) hd f w := rfl
      _ = f w := by
          simp only [passiveVisiblePart, LinearMap.add_apply, LinearMap.id_coe,
            id_eq, Pi.add_apply, Pi.zero_apply] at hw
          calc
            passiveDiffPart (n := n) (d := d) hd f w
                = passiveDiffPart (n := n) (d := d) hd f w + 0 := by simp
            _ = passiveDiffPart (n := n) (d := d) hd f w
                  + (f w + passiveDiffPart (n := n) (d := d) hd f w) := by rw [hw]
            _ = f w + (passiveDiffPart (n := n) (d := d) hd f w
                  + passiveDiffPart (n := n) (d := d) hd f w) := by ring
            _ = f w := by rw [F_add_self]; simp
  · intro hf
    rcases hf with ⟨R, rfl⟩
    funext w
    simp [passiveVisiblePart, passiveDiffPart,
      passiveRepProfileMap_PassiveDiffEmbed (n := n) (d := d) hd R,
      F_add_self]

noncomputable def passiveVisiblePartToSpace {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveRaw n d →ₗ[F] PassiveVisibleSpace n d hd :=
  (passiveVisiblePart (n := n) (d := d) hd).codRestrict
    (PassiveVisibleSpace n d hd)
    (passiveVisiblePart_mem_visibleSpace (n := n) (d := d) hd)

theorem passiveVisiblePartToSpace_apply {n d : ℕ} [NeZero n] (hd : 0 < d)
    (f : PassiveRaw n d) :
    (passiveVisiblePartToSpace (n := n) (d := d) hd f : PassiveRaw n d) =
      passiveVisiblePart (n := n) (d := d) hd f := rfl

theorem ker_passiveVisiblePartToSpace {n d : ℕ} [NeZero n] (hd : 0 < d) :
    LinearMap.ker (passiveVisiblePartToSpace (n := n) (d := d) hd)
      =
    PassiveDiffSpace n d := by
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro hf
    have hval := congrArg Subtype.val hf
    exact
      (passiveVisiblePart_eq_zero_iff_mem_PassiveDiffSpace
        (n := n) (d := d) hd f).1 hval
  · intro hf
    apply Subtype.ext
    exact
      (passiveVisiblePart_eq_zero_iff_mem_PassiveDiffSpace
        (n := n) (d := d) hd f).2 hf

theorem passiveRepProfileMap_eq_zero_of_mem_visibleSpace
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : PassiveVisibleSpace n d hd) :
    passiveRepProfileMap (n := n) (d := d) hd f.1 = 0 := by
  apply Subtype.ext
  funext s
  unfold passiveRepProfileMap pullProfile pullProfileVal
  by_cases hs : s = 0
  · subst hs
    simp
    refine Finset.sum_eq_zero ?_
    intro u _
    exact f.2 u.1 u.2
  · simp [hs, f.2 s hs]

theorem passiveVisiblePart_fixed_of_mem_visibleSpace
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : PassiveVisibleSpace n d hd) :
    passiveVisiblePart (n := n) (d := d) hd f.1 = f.1 := by
  funext w
  simp [passiveVisiblePart, passiveDiffPart,
    passiveRepProfileMap_eq_zero_of_mem_visibleSpace (n := n) (d := d) hd f]

theorem passiveVisiblePartToSpace_surjective
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Surjective (passiveVisiblePartToSpace (n := n) (d := d) hd) := by
  intro f
  refine ⟨f.1, ?_⟩
  apply Subtype.ext
  exact passiveVisiblePart_fixed_of_mem_visibleSpace (n := n) (d := d) hd f

noncomputable def passiveQuotEquivVisibleSpace {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveQuot n d ≃ₗ[F] PassiveVisibleSpace n d hd :=
  let L := passiveVisiblePartToSpace (n := n) (d := d) hd
  let hker : LinearMap.ker L = PassiveDiffSpace n d :=
    ker_passiveVisiblePartToSpace (n := n) (d := d) hd
  (Submodule.quotEquivOfEq (PassiveDiffSpace n d) (LinearMap.ker L) hker.symm).trans
    (L.quotKerEquivOfSurjective
      (passiveVisiblePartToSpace_surjective (n := n) (d := d) hd))

noncomputable def passiveQuotEquivVisibleIndex {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveQuot n d ≃ₗ[F] (PassiveVisibleIndex n d hd → F) :=
  (passiveQuotEquivVisibleSpace (n := n) (d := d) hd).trans
    (passiveVisibleSpaceEquivIndex (n := n) (d := d) hd)

end

end TriangleLeaf
end Core4loop
