import Core4loop.CyclicDifference

open scoped BigOperators

namespace Core4loop

abbrev NonzeroI (n : ℕ) := {s : I n // s ≠ 0}

noncomputable def sigmaMap {n : ℕ} [NeZero n] : Profile n →ₗ[F] F where
  toFun u := ∑ s : I n, u s
  map_add' u v := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r u := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

noncomputable def ZeroSumProfile (n : ℕ) [NeZero n] : Submodule F (Profile n) :=
  LinearMap.ker (sigmaMap (n := n))

lemma card_NonzeroI {n : ℕ} [NeZero n] :
    Fintype.card (NonzeroI n) = n - 1 := by
  classical
  calc
    Fintype.card (NonzeroI n)
        = Fintype.card (I n) - Fintype.card {s : I n // s = 0} := by
            simp [NonzeroI,
              (Fintype.card_subtype_compl (fun s : I n => s = 0))
            ]
    _ = n - 1 := by
            rw [Fintype.card_subtype_eq (0 : I n)]
            simp [I, ZMod.card]

lemma sum_I_eq_value_zero_add_sum_nonzero {n : ℕ} [NeZero n]
    (f : I n → F) :
    (∑ s : I n, f s) = f 0 + ∑ s : NonzeroI n, f s.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (I n))) (p := fun s : I n => s = 0) f).symm
  calc
    (∑ s : I n, f s)
        = (∑ s ∈ (Finset.univ : Finset (I n)) with s = 0, f s)
            + (∑ s ∈ (Finset.univ : Finset (I n)) with ¬s = 0, f s) := by
              simpa using hpart
    _ = f 0 + (∑ s ∈ (Finset.univ : Finset (I n)) with ¬s = 0, f s) := by
              congr 1
              · rw [Finset.sum_eq_single (0 : I n)]
                · intro s hmem hs
                  have hs0 : s = 0 := by
                    simpa using (Finset.mem_filter.mp hmem).2
                  exact False.elim (hs hs0)
                · intro hnot
                  simp at hnot
    _ = f 0 + ∑ s : NonzeroI n, f s.1 := by
              congr 1
              simpa using
                (Finset.sum_subtype_eq_sum_filter
                  (s := (Finset.univ : Finset (I n))) (p := fun s : I n => s ≠ 0)
                  (f := f)).symm

noncomputable def pullProfileVal {n : ℕ} [NeZero n]
    (g : NonzeroI n → F) : Profile n :=
  fun s => if h : s = 0 then ∑ u : NonzeroI n, g u else g ⟨s, h⟩

lemma pullProfileVal_zero_sum {n : ℕ} [NeZero n]
    (g : NonzeroI n → F) :
    (∑ s : I n, pullProfileVal g s) = 0 := by
  classical
  let S : F := ∑ u : NonzeroI n, g u
  calc
    (∑ s : I n, pullProfileVal g s)
        = pullProfileVal g 0 + ∑ s : NonzeroI n, pullProfileVal g s.1 := by
            rw [sum_I_eq_value_zero_add_sum_nonzero]
    _ = S + S := by
            congr 1
            · simp [pullProfileVal, S]
            · refine Finset.sum_congr rfl ?_
              intro s _
              simp [pullProfileVal, s.2]
    _ = 0 := F_add_self S

lemma value_zero_eq_sum_nonzero_of_sum_zero {n : ℕ} [NeZero n]
    {f : I n → F} (hf : (∑ s : I n, f s) = 0) :
    f 0 = ∑ s : NonzeroI n, f s.1 := by
  rw [sum_I_eq_value_zero_add_sum_nonzero] at hf
  let S : F := ∑ s : NonzeroI n, f s.1
  calc
    f 0 = f 0 + 0 := by simp
    _ = f 0 + (S + S) := by rw [F_add_self S]
    _ = (f 0 + S) + S := by abel
    _ = S := by
      rw [hf]
      simp [S]

noncomputable def pullProfile {n : ℕ} [NeZero n] :
    (NonzeroI n → F) →ₗ[F] ZeroSumProfile n where
  toFun g :=
    ⟨pullProfileVal g, LinearMap.mem_ker.mpr (pullProfileVal_zero_sum g)⟩
  map_add' g h := by
    apply Subtype.ext
    funext s
    unfold pullProfileVal
    by_cases hs : s = 0
    · simp [hs, Finset.sum_add_distrib]
    · simp [hs]
  map_smul' r g := by
    apply Subtype.ext
    funext s
    unfold pullProfileVal
    by_cases hs : s = 0
    · simp [hs, Finset.mul_sum]
    · simp [hs]

noncomputable def readProfile {n : ℕ} [NeZero n] :
    ZeroSumProfile n →ₗ[F] (NonzeroI n → F) where
  toFun u := fun s => u.1 s.1
  map_add' u v := by
    funext s
    rfl
  map_smul' r u := by
    funext s
    rfl

lemma readProfile_pullProfile {n : ℕ} [NeZero n]
    (g : NonzeroI n → F) :
    readProfile (pullProfile (n := n) g) = g := by
  funext s
  simp [readProfile, pullProfile, pullProfileVal, s.2]

lemma pullProfile_readProfile {n : ℕ} [NeZero n]
    (u : ZeroSumProfile n) :
    pullProfile (n := n) (readProfile u) = u := by
  apply Subtype.ext
  funext s
  by_cases hs : s = 0
  · subst hs
    have hz : (∑ s : I n, u.1 s) = 0 :=
      LinearMap.mem_ker.mp u.2
    have h0 := value_zero_eq_sum_nonzero_of_sum_zero hz
    simp [pullProfile, pullProfileVal, readProfile, h0]
  · simp [pullProfile, pullProfileVal, readProfile, hs]

noncomputable def zeroSumProfileEquivNonzero {n : ℕ} [NeZero n] :
    ZeroSumProfile n ≃ₗ[F] (NonzeroI n → F) where
  toFun := readProfile
  invFun := pullProfile
  left_inv := pullProfile_readProfile
  right_inv := readProfile_pullProfile
  map_add' := by
    intro u v
    rfl
  map_smul' := by
    intro r u
    rfl

lemma finrank_ZeroSumProfile {n : ℕ} [NeZero n] :
    Module.finrank F (ZeroSumProfile n) = n - 1 := by
  calc
    Module.finrank F (ZeroSumProfile n)
        = Module.finrank F (NonzeroI n → F) := by
            exact LinearEquiv.finrank_eq (zeroSumProfileEquivNonzero (n := n))
    _ = ∑ _ : NonzeroI n, Module.finrank F F := by
            simp [Module.finrank_pi_fintype (R := F) (M := fun _ : NonzeroI n => F)]
    _ = Fintype.card (NonzeroI n) := by
            simp
    _ = n - 1 := card_NonzeroI

lemma cycDiff_mem_ZeroSumProfile {n : ℕ} [NeZero n] (u : Profile n) :
    cycDiff (n := n) F u ∈ ZeroSumProfile n := by
  apply LinearMap.mem_ker.mpr
  have hshift : (∑ s : I n, u (s + 1)) = ∑ s : I n, u s := by
    simpa using ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n)) u)
  calc
    (∑ s : I n, cycDiff (n := n) F u s)
        = (∑ s : I n, u s) + ∑ s : I n, u (s + 1) := by
            simp [cycDiff, Finset.sum_add_distrib]
    _ = (∑ s : I n, u s) + ∑ s : I n, u s := by
            rw [hshift]
    _ = 0 := F_add_self _

theorem range_cycDiff_eq_ZeroSumProfile {n : ℕ} [NeZero n] :
    LinearMap.range (cycDiff (n := n) F) = ZeroSumProfile n := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro u hu
    rcases hu with ⟨v, rfl⟩
    exact cycDiff_mem_ZeroSumProfile v
  · rw [finrank_range_cycDiff_profile, finrank_ZeroSumProfile]

lemma F_module_add_self {M : Type*} [AddCommMonoid M] [Module F M] (x : M) :
    x + x = 0 := by
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + (1 : F)) • x := by rw [add_smul]
    _ = 0 := by simp [F_add_self (1 : F)]

lemma sum_I_eq_value_zero_add_sum_nonzeroM {n : ℕ} [NeZero n]
    {M : Type*} [AddCommMonoid M] (f : I n → M) :
    (∑ s : I n, f s) = f 0 + ∑ s : NonzeroI n, f s.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (I n))) (p := fun s : I n => s = 0) f).symm
  calc
    (∑ s : I n, f s)
        = (∑ s ∈ (Finset.univ : Finset (I n)) with s = 0, f s)
            + (∑ s ∈ (Finset.univ : Finset (I n)) with ¬s = 0, f s) := by
              simpa using hpart
    _ = f 0 + (∑ s ∈ (Finset.univ : Finset (I n)) with ¬s = 0, f s) := by
              congr 1
              · rw [Finset.sum_eq_single (0 : I n)]
                · intro s hmem hs
                  have hs0 : s = 0 := by
                    simpa using (Finset.mem_filter.mp hmem).2
                  exact False.elim (hs hs0)
                · intro hnot
                  simp at hnot
    _ = f 0 + ∑ s : NonzeroI n, f s.1 := by
              congr 1
              simpa using
                (Finset.sum_subtype_eq_sum_filter
                  (s := (Finset.univ : Finset (I n))) (p := fun s : I n => s ≠ 0)
                  (f := f)).symm

noncomputable def sigmaMapM {n : ℕ} [NeZero n]
    (M : Type*) [AddCommMonoid M] [Module F M] :
    (I n → M) →ₗ[F] M where
  toFun u := ∑ s : I n, u s
  map_add' u v := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r u := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]

noncomputable def ZeroSumProfileM (n : ℕ) [NeZero n]
    (M : Type*) [AddCommMonoid M] [Module F M] : Submodule F (I n → M) :=
  LinearMap.ker (sigmaMapM (n := n) M)

lemma cycDiff_mem_ZeroSumProfileM {n : ℕ} [NeZero n]
    {M : Type*} [AddCommGroup M] [Module F M] (u : I n → M) :
    cycDiff (n := n) M u ∈ ZeroSumProfileM n M := by
  apply LinearMap.mem_ker.mpr
  have hshift : (∑ s : I n, u (s + 1)) = ∑ s : I n, u s := by
    simpa using ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n)) u)
  calc
    (∑ s : I n, cycDiff (n := n) M u s)
        = (∑ s : I n, u s) + ∑ s : I n, u (s + 1) := by
            simp [cycDiff, Finset.sum_add_distrib]
    _ = (∑ s : I n, u s) + ∑ s : I n, u s := by
            rw [hshift]
    _ = 0 := F_module_add_self _

noncomputable def pullProfileValM {n : ℕ} [NeZero n]
    {M : Type*} [AddCommMonoid M] [Module F M]
    (g : NonzeroI n → M) : I n → M :=
  fun s => if h : s = 0 then ∑ u : NonzeroI n, g u else g ⟨s, h⟩

lemma pullProfileValM_zero_sum {n : ℕ} [NeZero n]
    {M : Type*} [AddCommMonoid M] [Module F M]
    (g : NonzeroI n → M) :
    (∑ s : I n, pullProfileValM g s) = 0 := by
  classical
  let S : M := ∑ u : NonzeroI n, g u
  calc
    (∑ s : I n, pullProfileValM g s)
        = pullProfileValM g 0 + ∑ s : NonzeroI n, pullProfileValM g s.1 := by
            rw [sum_I_eq_value_zero_add_sum_nonzeroM]
    _ = S + S := by
            congr 1
            · simp [pullProfileValM, S]
            · refine Finset.sum_congr rfl ?_
              intro s _
              simp [pullProfileValM, s.2]
    _ = 0 := F_module_add_self S

lemma value_zero_eq_sum_nonzero_of_sum_zeroM {n : ℕ} [NeZero n]
    {M : Type*} [AddCommMonoid M] [Module F M]
    {f : I n → M} (hf : (∑ s : I n, f s) = 0) :
    f 0 = ∑ s : NonzeroI n, f s.1 := by
  rw [sum_I_eq_value_zero_add_sum_nonzeroM] at hf
  let S : M := ∑ s : NonzeroI n, f s.1
  calc
    f 0 = f 0 + 0 := by simp
    _ = f 0 + (S + S) := by rw [F_module_add_self S]
    _ = (f 0 + S) + S := by simp [add_assoc]
    _ = S := by
      rw [hf]
      simp [S]

noncomputable def pullProfileM {n : ℕ} [NeZero n]
    (M : Type*) [AddCommMonoid M] [Module F M] :
    (NonzeroI n → M) →ₗ[F] ZeroSumProfileM n M where
  toFun g :=
    ⟨pullProfileValM g, LinearMap.mem_ker.mpr (pullProfileValM_zero_sum g)⟩
  map_add' g h := by
    apply Subtype.ext
    funext s
    unfold pullProfileValM
    by_cases hs : s = 0
    · simp [hs, Finset.sum_add_distrib]
    · simp [hs]
  map_smul' r g := by
    apply Subtype.ext
    funext s
    unfold pullProfileValM
    by_cases hs : s = 0
    · simp [hs, Finset.smul_sum]
    · simp [hs]

noncomputable def readProfileM {n : ℕ} [NeZero n]
    (M : Type*) [AddCommMonoid M] [Module F M] :
    ZeroSumProfileM n M →ₗ[F] (NonzeroI n → M) where
  toFun u := fun s => u.1 s.1
  map_add' u v := by
    funext s
    rfl
  map_smul' r u := by
    funext s
    rfl

lemma readProfileM_pullProfileM {n : ℕ} [NeZero n]
    {M : Type*} [AddCommMonoid M] [Module F M]
    (g : NonzeroI n → M) :
    readProfileM (n := n) M (pullProfileM (n := n) M g) = g := by
  funext s
  simp [readProfileM, pullProfileM, pullProfileValM, s.2]

lemma pullProfileM_readProfileM {n : ℕ} [NeZero n]
    {M : Type*} [AddCommMonoid M] [Module F M]
    (u : ZeroSumProfileM n M) :
    pullProfileM (n := n) M (readProfileM (n := n) M u) = u := by
  apply Subtype.ext
  funext s
  by_cases hs : s = 0
  · subst hs
    have hz : (∑ s : I n, u.1 s) = 0 :=
      LinearMap.mem_ker.mp u.2
    have h0 := value_zero_eq_sum_nonzero_of_sum_zeroM hz
    simp [pullProfileM, pullProfileValM, readProfileM, h0]
  · simp [pullProfileM, pullProfileValM, readProfileM, hs]

noncomputable def zeroSumProfileMEquivNonzero {n : ℕ} [NeZero n]
    (M : Type*) [AddCommMonoid M] [Module F M] :
    ZeroSumProfileM n M ≃ₗ[F] (NonzeroI n → M) where
  toFun := readProfileM (n := n) M
  invFun := pullProfileM (n := n) M
  left_inv := pullProfileM_readProfileM
  right_inv := readProfileM_pullProfileM
  map_add' := by
    intro u v
    rfl
  map_smul' := by
    intro r u
    rfl

lemma finrank_ZeroSumProfileM {n : ℕ} [NeZero n]
    {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M] :
    Module.finrank F (ZeroSumProfileM n M) = (n - 1) * Module.finrank F M := by
  calc
    Module.finrank F (ZeroSumProfileM n M)
        = Module.finrank F (NonzeroI n → M) := by
            exact LinearEquiv.finrank_eq (zeroSumProfileMEquivNonzero (n := n) M)
    _ = ∑ _ : NonzeroI n, Module.finrank F M := by
            simp [Module.finrank_pi_fintype
              (R := F) (M := fun _ : NonzeroI n => M)]
    _ = Fintype.card (NonzeroI n) * Module.finrank F M := by
            simp
    _ = (n - 1) * Module.finrank F M := by
            rw [card_NonzeroI]

end Core4loop
