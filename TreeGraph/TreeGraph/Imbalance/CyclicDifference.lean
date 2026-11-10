import TreeGraph.Imbalance.CharacterSum

namespace TreeGraph
namespace Imbalance

noncomputable def cycDiff (n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    (Rep n → M) →ₗ[F2] (Rep n → M) where
  toFun f := fun t => f t + f (t + 1)
  map_add' f g := by
    ext t
    simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
  map_smul' c f := by
    ext t
    simp [Pi.smul_apply, smul_add]

@[simp] theorem cycDiff_apply {n : Nat} [NeZero n] {M : Type}
    [AddCommGroup M] [Module F2 M] (f : Rep n → M) (t : Rep n) :
    cycDiff n M f t = f t + f (t + 1) := rfl

private theorem add_self_eq_zero_of_module_F2 {M : Type}
    [AddCommGroup M] [Module F2 M] (x : M) :
    x + x = 0 := by
  have htwo : (1 : F2) + (1 : F2) = 0 := by decide
  calc
    x + x = (1 : F2) • x + (1 : F2) • x := by simp
    _ = ((1 : F2) + (1 : F2)) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

private theorem neg_eq_self_of_module_F2 {M : Type}
    [AddCommGroup M] [Module F2 M] (x : M) :
    -x = x := by
  have hxx : x + x = 0 := add_self_eq_zero_of_module_F2 x
  calc
    -x = -x + 0 := by simp
    _ = -x + (x + x) := by rw [hxx]
    _ = x := by abel

noncomputable def constantFunctionLinear (n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    M →ₗ[F2] (Rep n → M) where
  toFun m := fun _ => m
  map_add' x y := by
    ext t
    simp
  map_smul' c x := by
    ext t
    simp

theorem cycDiff_constant {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] (m : M) :
    cycDiff n M (constantFunctionLinear n M m) = 0 := by
  ext t
  exact add_self_eq_zero_of_module_F2 m

theorem cycDiff_eq_zero_iff_exists_constant {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (f : Rep n → M) :
    cycDiff n M f = 0 ↔ ∃ m : M, f = constantFunctionLinear n M m := by
  constructor
  · intro hzero
    have hstep : ∀ t : Rep n, f (t + 1) = f t := by
      intro t
      have ht : f t + f (t + 1) = 0 := by
        simpa using congrArg (fun g : Rep n → M => g t) hzero
      calc
        f (t + 1) = 0 + f (t + 1) := by simp
        _ = (-f t + f t) + f (t + 1) := by simp
        _ = -f t + (f t + f (t + 1)) := by abel
        _ = -f t := by rw [ht]; simp
        _ = f t := neg_eq_self_of_module_F2 (f t)
    refine ⟨f 0, ?_⟩
    ext t
    have hnat : ∀ k : Nat, f ((k : Nat) : Rep n) = f 0 := by
      intro k
      induction k with
      | zero =>
          simp
      | succ k ih =>
          calc
            f ((Nat.succ k : Nat) : Rep n)
                = f ((k : Rep n) + 1) := by simp [Nat.cast_succ]
            _ = f (k : Rep n) := hstep (k : Rep n)
            _ = f 0 := ih
    rw [← ZMod.natCast_zmod_val t]
    exact hnat t.val
  · rintro ⟨m, rfl⟩
    exact cycDiff_constant M m

theorem cycDiff_eq_zero_iff_constant_apply {n : Nat} [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M] (f : Rep n → M) :
    cycDiff n M f = 0 ↔ ∀ t : Rep n, f t = f 0 := by
  constructor
  · intro hzero t
    rcases (cycDiff_eq_zero_iff_exists_constant M f).1 hzero with ⟨m, hm⟩
    rw [hm]
    rfl
  · intro hconst
    apply (cycDiff_eq_zero_iff_exists_constant M f).2
    refine ⟨f 0, ?_⟩
    ext t
    exact hconst t

noncomputable def cycDiffKerEquiv {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    LinearMap.ker (cycDiff n M) ≃ₗ[F2] M where
  toFun u := u.1 0
  invFun m :=
    ⟨constantFunctionLinear n M m,
      LinearMap.mem_ker.mpr (cycDiff_constant M m)⟩
  map_add' u v := rfl
  map_smul' c u := rfl
  left_inv u := by
    apply Subtype.ext
    funext t
    have hzero : cycDiff n M u.1 = 0 := LinearMap.mem_ker.mp u.2
    exact ((cycDiff_eq_zero_iff_constant_apply M u.1).1 hzero t).symm
  right_inv m := rfl

theorem finrank_ker_cycDiff {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    Module.finrank F2 (LinearMap.ker (cycDiff n M)) =
      Module.finrank F2 M :=
  LinearEquiv.finrank_eq (cycDiffKerEquiv M)

theorem finrank_range_cycDiff {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.range (cycDiff n M)) =
      (n - 1) * Module.finrank F2 M := by
  classical
  let d := Module.finrank F2 M
  let r := Module.finrank F2 (LinearMap.range (cycDiff n M))
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker (cycDiff n M)
  have hker :
      Module.finrank F2 (LinearMap.ker (cycDiff n M)) = d := by
    simpa [d] using finrank_ker_cycDiff (n := n) M
  have hdomain :
      Module.finrank F2 (Rep n → M) = n * d := by
    calc
      Module.finrank F2 (Rep n → M)
          = ∑ _ : Rep n, d := by
              simpa [Rep, d] using
                (Module.finrank_pi_fintype
                  (R := F2) (M := fun _ : Rep n => M))
      _ = n * d := by
              simp [Rep, ZMod.card, Finset.card_univ]
  have hsum : r + d = n * d := by
    simpa [r, hker, hdomain] using hrank
  have hn : n = (n - 1) + 1 := by
    have hnpos : 0 < n := NeZero.pos n
    omega
  have hmul : n * d = (n - 1) * d + d := by
    calc
      n * d = ((n - 1) + 1) * d := by rw [← hn]
      _ = (n - 1) * d + d := by rw [Nat.add_mul, one_mul]
  have hcancel : r = (n - 1) * d := by
    have hadd : r + d = (n - 1) * d + d := by
      rw [hsum, hmul]
    exact Nat.add_right_cancel hadd
  simpa [r, d] using hcancel

end Imbalance
end TreeGraph
