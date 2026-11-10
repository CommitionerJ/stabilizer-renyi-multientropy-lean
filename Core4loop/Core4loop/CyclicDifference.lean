import Core4loop.PhaseAfterA

namespace Core4loop

abbrev Profile (n : ℕ) := I n → F

private theorem add_self_eq_zero_of_module_F {M : Type*}
    [AddCommGroup M] [Module F M] (x : M) :
    x + x = 0 := by
  have htwo : (1 : F) + (1 : F) = 0 := by decide
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + (1 : F)) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

private theorem neg_eq_self_of_module_F {M : Type*}
    [AddCommGroup M] [Module F M] (x : M) :
    -x = x := by
  have hxx : x + x = 0 := add_self_eq_zero_of_module_F x
  calc
    -x = -x + 0 := by simp
    _ = -x + (x + x) := by rw [hxx]
    _ = x := by abel

noncomputable def cycDiff {n : ℕ} [NeZero n] (M : Type*)
    [AddCommGroup M] [Module F M] :
    (I n → M) →ₗ[F] (I n → M) where
  toFun f := fun s => f s + f (s + 1)
  map_add' f g := by
    funext s
    simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
  map_smul' c f := by
    funext s
    simp [Pi.smul_apply, smul_add]

@[simp] theorem cycDiff_apply {n : ℕ} [NeZero n] {M : Type*}
    [AddCommGroup M] [Module F M] (f : I n → M) (s : I n) :
    cycDiff (n := n) M f s = f s + f (s + 1) := rfl

noncomputable def constantFunctionLinear (n : ℕ) [NeZero n] (M : Type*)
    [AddCommGroup M] [Module F M] :
    M →ₗ[F] (I n → M) where
  toFun m := fun _ => m
  map_add' x y := by
    funext s
    simp
  map_smul' c x := by
    funext s
    simp

theorem cycDiff_constant {n : ℕ} [NeZero n] (M : Type*)
    [AddCommGroup M] [Module F M] (m : M) :
    cycDiff (n := n) M (constantFunctionLinear n M m) = 0 := by
  funext s
  exact add_self_eq_zero_of_module_F m

theorem cycDiff_eq_zero_iff_exists_constant {n : ℕ} [NeZero n]
    (M : Type*) [AddCommGroup M] [Module F M] (f : I n → M) :
    cycDiff (n := n) M f = 0 ↔ ∃ m : M, f = constantFunctionLinear n M m := by
  constructor
  · intro hzero
    have hstep : ∀ s : I n, f (s + 1) = f s := by
      intro s
      have hs : f s + f (s + 1) = 0 := by
        simpa using congrFun hzero s
      calc
        f (s + 1) = 0 + f (s + 1) := by simp
        _ = (-f s + f s) + f (s + 1) := by simp
        _ = -f s + (f s + f (s + 1)) := by abel
        _ = -f s := by rw [hs]; simp
        _ = f s := neg_eq_self_of_module_F (f s)
    refine ⟨f 0, ?_⟩
    funext s
    exact zmod_step_const f hstep s
  · rintro ⟨m, rfl⟩
    exact cycDiff_constant M m

theorem cycDiff_eq_zero_iff_constant_apply {n : ℕ} [NeZero n]
    (M : Type*) [AddCommGroup M] [Module F M] (f : I n → M) :
    cycDiff (n := n) M f = 0 ↔ ∀ s : I n, f s = f 0 := by
  constructor
  · intro hzero s
    rcases (cycDiff_eq_zero_iff_exists_constant M f).1 hzero with ⟨m, hm⟩
    rw [hm]
    rfl
  · intro hconst
    apply (cycDiff_eq_zero_iff_exists_constant M f).2
    refine ⟨f 0, ?_⟩
    funext s
    exact hconst s

noncomputable def cycDiffKerEquiv {n : ℕ} [NeZero n] (M : Type*)
    [AddCommGroup M] [Module F M] :
    LinearMap.ker (cycDiff (n := n) M) ≃ₗ[F] M where
  toFun u := u.1 0
  invFun m :=
    ⟨constantFunctionLinear n M m,
      LinearMap.mem_ker.mpr (cycDiff_constant M m)⟩
  map_add' u v := rfl
  map_smul' c u := rfl
  left_inv u := by
    apply Subtype.ext
    funext s
    have hzero : cycDiff (n := n) M u.1 = 0 := LinearMap.mem_ker.mp u.2
    exact ((cycDiff_eq_zero_iff_constant_apply M u.1).1 hzero s).symm
  right_inv m := rfl

theorem finrank_ker_cycDiff {n : ℕ} [NeZero n] (M : Type*)
    [AddCommGroup M] [Module F M] :
    Module.finrank F (LinearMap.ker (cycDiff (n := n) M)) =
      Module.finrank F M :=
  LinearEquiv.finrank_eq (cycDiffKerEquiv M)

theorem finrank_profile {n : ℕ} [NeZero n] :
    Module.finrank F (Profile n) = n := by
  calc
    Module.finrank F (Profile n) = ∑ _ : I n, Module.finrank F F := by
      simp [Profile, Module.finrank_pi_fintype (R := F) (M := fun _ : I n => F)]
    _ = n := by
      simp [I, ZMod.card]

theorem finrank_ker_cycDiff_profile {n : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.ker (cycDiff (n := n) F)) = 1 := by
  simpa using finrank_ker_cycDiff (n := n) F

theorem finrank_range_cycDiff_profile {n : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.range (cycDiff (n := n) F)) = n - 1 := by
  let r := Module.finrank F (LinearMap.range (cycDiff (n := n) F))
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker (cycDiff (n := n) F)
  have hsum : r + 1 = n := by
    simpa [r, finrank_profile, finrank_ker_cycDiff_profile] using hrank
  have hnpos : 0 < n := NeZero.pos n
  omega

end Core4loop
