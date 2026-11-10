import TreeGraph.Imbalance.Transport

namespace TreeGraph
namespace Imbalance

noncomputable def familyCycDiff (n : Nat) [NeZero n]
    (E M : Type) [AddCommGroup M] [Module F2 M] :
    (E × Rep n → M) →ₗ[F2] (E × Rep n → M) where
  toFun f := fun et => f (et.1, et.2) + f (et.1, et.2 + 1)
  map_add' f g := by
    ext et
    simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
  map_smul' r f := by
    ext et
    simp [Pi.smul_apply, smul_add]

@[simp] theorem familyCycDiff_apply (n : Nat) [NeZero n]
    (E M : Type) [AddCommGroup M] [Module F2 M]
    (f : E × Rep n → M) (et : E × Rep n) :
    familyCycDiff n E M f et =
      f (et.1, et.2) + f (et.1, et.2 + 1) := rfl

noncomputable def constantFamilyLinear (n : Nat) [NeZero n]
    (E M : Type) [AddCommGroup M] [Module F2 M] :
    (E → M) →ₗ[F2] (E × Rep n → M) where
  toFun c := fun et => c et.1
  map_add' c d := by
    ext et
    simp
  map_smul' r c := by
    ext et
    simp

theorem familyCycDiff_constant (n : Nat) [NeZero n]
    (E M : Type) [AddCommGroup M] [Module F2 M] (c : E → M) :
    familyCycDiff n E M (constantFamilyLinear n E M c) = 0 := by
  ext et
  have h := congrFun (cycDiff_constant (n := n) M (c et.1)) et.2
  simpa [constantFunctionLinear] using h

theorem familyCycDiff_eq_zero_iff_exists_constant
    (n : Nat) [NeZero n]
    (E M : Type) [AddCommGroup M] [Module F2 M]
    (f : E × Rep n → M) :
    familyCycDiff n E M f = 0 ↔
      ∃ c : E → M, f = constantFamilyLinear n E M c := by
  constructor
  · intro hzero
    have hslice :
        ∀ e : E, ∃ m : M,
          (fun t : Rep n => f (e, t)) =
            constantFunctionLinear n M m := by
      intro e
      apply (cycDiff_eq_zero_iff_exists_constant M
        (fun t : Rep n => f (e, t))).1
      ext t
      exact congrFun hzero (e, t)
    choose c hc using hslice
    refine ⟨c, ?_⟩
    ext et
    have hce := congrFun (hc et.1) et.2
    simpa [constantFamilyLinear, constantFunctionLinear] using hce
  · rintro ⟨c, rfl⟩
    exact familyCycDiff_constant n E M c

theorem familyCycDiff_eq_zero_iff_constant_apply
    (n : Nat) [NeZero n]
    (E M : Type) [AddCommGroup M] [Module F2 M]
    (f : E × Rep n → M) :
    familyCycDiff n E M f = 0 ↔
      ∀ et : E × Rep n, f et = f (et.1, 0) := by
  constructor
  · intro hzero et
    have hslice :
        cycDiff n M (fun t : Rep n => f (et.1, t)) = 0 := by
      ext t
      exact congrFun hzero (et.1, t)
    exact (cycDiff_eq_zero_iff_constant_apply M
      (fun t : Rep n => f (et.1, t))).1 hslice et.2
  · intro hconst
    apply (familyCycDiff_eq_zero_iff_exists_constant n E M f).2
    refine ⟨fun e => f (e, 0), ?_⟩
    ext et
    exact hconst et

noncomputable def familyCycDiffKerEquiv (n : Nat) [NeZero n]
    (E M : Type) [AddCommGroup M] [Module F2 M] :
    LinearMap.ker (familyCycDiff n E M) ≃ₗ[F2] (E → M) where
  toFun u := fun e => u.1 (e, 0)
  invFun c :=
    ⟨constantFamilyLinear n E M c,
      LinearMap.mem_ker.mpr (familyCycDiff_constant n E M c)⟩
  map_add' u v := rfl
  map_smul' r u := rfl
  left_inv u := by
    apply Subtype.ext
    funext et
    have hzero : familyCycDiff n E M u.1 = 0 :=
      LinearMap.mem_ker.mp u.2
    exact ((familyCycDiff_eq_zero_iff_constant_apply n E M u.1).1
      hzero et).symm
  right_inv c := rfl

theorem finrank_ker_familyCycDiff (n : Nat) [NeZero n]
    (E M : Type) [Fintype E]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.ker (familyCycDiff n E M)) =
      Fintype.card E * Module.finrank F2 M := by
  classical
  calc
    Module.finrank F2 (LinearMap.ker (familyCycDiff n E M)) =
        Module.finrank F2 (E → M) :=
      LinearEquiv.finrank_eq (familyCycDiffKerEquiv n E M)
    _ = ∑ _ : E, Module.finrank F2 M := by
      simpa using
        (Module.finrank_pi_fintype
          (R := F2) (M := fun _ : E => M))
    _ = Fintype.card E * Module.finrank F2 M := by
      simp [Finset.card_univ]

theorem finrank_range_familyCycDiff (n : Nat) [NeZero n]
    (E M : Type) [Fintype E]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.range (familyCycDiff n E M)) =
      Fintype.card E * (n - 1) * Module.finrank F2 M := by
  classical
  let cE := Fintype.card E
  let d := Module.finrank F2 M
  let r := Module.finrank F2 (LinearMap.range (familyCycDiff n E M))
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker (familyCycDiff n E M)
  have hker :
      Module.finrank F2 (LinearMap.ker (familyCycDiff n E M)) =
        cE * d := by
    simpa [cE, d] using finrank_ker_familyCycDiff n E M
  have hdomain :
      Module.finrank F2 (E × Rep n → M) = (cE * n) * d := by
    calc
      Module.finrank F2 (E × Rep n → M)
          = ∑ _ : E × Rep n, d := by
              simpa [d] using
                (Module.finrank_pi_fintype
                  (R := F2) (M := fun _ : E × Rep n => M))
      _ = (cE * n) * d := by
          simp [cE, Rep, ZMod.card, Fintype.card_prod]
  have hsum : r + cE * d = (cE * n) * d := by
    simpa [r, hker, hdomain] using hrank
  have hn : n = (n - 1) + 1 := by
    have hnpos : 0 < n := NeZero.pos n
    omega
  have hmul :
      (cE * n) * d = cE * (n - 1) * d + cE * d := by
    calc
      (cE * n) * d = (cE * ((n - 1) + 1)) * d := by
        rw [← hn]
      _ = (cE * (n - 1) + cE) * d := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = cE * (n - 1) * d + cE * d := by
        rw [Nat.add_mul, Nat.mul_assoc]
  have hcancel : r = cE * (n - 1) * d := by
    have hadd : r + cE * d = cE * (n - 1) * d + cE * d := by
      rw [hsum, hmul]
    exact Nat.add_right_cancel hadd
  simpa [r, cE, d] using hcancel

end Imbalance
end TreeGraph
