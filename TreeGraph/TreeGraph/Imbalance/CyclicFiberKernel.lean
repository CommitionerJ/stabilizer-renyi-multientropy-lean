import TreeGraph.Imbalance.FiberSum

namespace TreeGraph
namespace Imbalance

theorem range_comp_eq_range_of_surjective_for_cyc
    {P Q R : Type} [AddCommGroup P] [Module F2 P]
    [AddCommGroup Q] [Module F2 Q] [AddCommGroup R] [Module F2 R]
    (L : Q →ₗ[F2] R) (π : P →ₗ[F2] Q)
    (hπ : Function.Surjective π) :
    LinearMap.range (L.comp π) = LinearMap.range L := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨π p, rfl⟩
  · rintro ⟨q, rfl⟩
    rcases hπ q with ⟨p, hp⟩
    exact ⟨p, by simp [LinearMap.comp_apply, hp]⟩

theorem finrank_blockFunctionSpace
    (n a : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (Block n a → M) =
      n ^ a * Module.finrank F2 M := by
  classical
  let d := Module.finrank F2 M
  calc
    Module.finrank F2 (Block n a → M) = ∑ _ : Block n a, d := by
      simpa [d] using
        (Module.finrank_pi_fintype
          (R := F2) (M := fun _ : Block n a => M))
    _ = Fintype.card (Block n a) * d := by
      simp
    _ = n ^ a * d := by
      rw [card_Block]

noncomputable def cycDiffAfterFiberSum
    (n : Nat) {a : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] :
    (Block n a → M) →ₗ[F2] (Rep n → M) :=
  (cycDiff n M).comp (fiberSum n ha M)

theorem range_cycDiffAfterFiberSum_eq_range_cycDiff
    (n : Nat) {a : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] :
    LinearMap.range (cycDiffAfterFiberSum n ha M) =
      LinearMap.range (cycDiff n M) := by
  exact range_comp_eq_range_of_surjective_for_cyc (cycDiff n M) (fiberSum n ha M)
    (fiberSum_surjective n ha M)

theorem finrank_range_cycDiffAfterFiberSum
    (n : Nat) {a : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.range (cycDiffAfterFiberSum n ha M)) =
      (n - 1) * Module.finrank F2 M := by
  rw [range_cycDiffAfterFiberSum_eq_range_cycDiff n ha M]
  exact finrank_range_cycDiff M

theorem finrank_ker_cycDiffAfterFiberSum
    (n : Nat) {a : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.ker (cycDiffAfterFiberSum n ha M)) =
      n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M := by
  classical
  let L := cycDiffAfterFiberSum n ha M
  let d := Module.finrank F2 M
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdomain :
      Module.finrank F2 (Block n a → M) = n ^ a * d := by
    simpa [d] using finrank_blockFunctionSpace n a M
  have hrange :
      Module.finrank F2 (LinearMap.range L) = (n - 1) * d := by
    simpa [L, d] using finrank_range_cycDiffAfterFiberSum n ha M
  rw [hdomain, hrange] at hsum
  let K := Module.finrank F2 (LinearMap.ker L)
  let R := (n - 1) * d
  let D := n ^ a * d
  have hK : K = D - R := by
    omega
  simpa [L, K, R, D, d] using hK

theorem card_ker_cycDiffAfterFiberSum
    (n : Nat) {a : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card (↥(LinearMap.ker (cycDiffAfterFiberSum n ha M))) =
      2 ^ (n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (cycDiffAfterFiberSum n ha M))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker (cycDiffAfterFiberSum n ha M)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.ker (cycDiffAfterFiberSum n ha M))
    _ = 2 ^ (n ^ a * Module.finrank F2 M -
        (n - 1) * Module.finrank F2 M) := by
      rw [finrank_ker_cycDiffAfterFiberSum n ha M]
      simp [F2]

noncomputable def contextSumLinear
    (C : Type) [Fintype C] (M : Type)
    [AddCommMonoid M] [Module F2 M] :
    (C → M) →ₗ[F2] M where
  toFun f := ∑ c : C, f c
  map_add' f g := by
    simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    rw [Finset.smul_sum]
    rfl

@[simp] theorem contextSumLinear_apply
    (C : Type) [Fintype C]
    {M : Type} [AddCommMonoid M] [Module F2 M] (f : C → M) :
    contextSumLinear C M f = ∑ c : C, f c := rfl

theorem contextSumLinear_surjective
    (C : Type) [Fintype C] [Nonempty C]
    (M : Type) [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (contextSumLinear C M) := by
  classical
  intro m
  let c0 : C := Classical.choice (inferInstance : Nonempty C)
  refine ⟨fun c => if c = c0 then m else 0, ?_⟩
  rw [contextSumLinear_apply]
  rw [Fintype.sum_eq_single c0]
  · simp
  · intro c hc
    simp [hc]

noncomputable def contextSummedCycDiff
    (C : Type) [Fintype C] (n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    (C → Rep n → M) →ₗ[F2] (Rep n → M) :=
  (cycDiff n M).comp (contextSumLinear C (Rep n → M))

@[simp] theorem contextSummedCycDiff_apply
    (C : Type) [Fintype C] {n : Nat} [NeZero n] {M : Type}
    [AddCommGroup M] [Module F2 M] (f : C → Rep n → M)
    (t : Rep n) :
    contextSummedCycDiff C n M f t =
      (∑ c : C, f c t) + ∑ c : C, f c (t + 1) := by
  simp [contextSummedCycDiff, contextSumLinear, Finset.sum_apply]

theorem range_contextSummedCycDiff_eq_range_cycDiff
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    LinearMap.range (contextSummedCycDiff C n M) =
      LinearMap.range (cycDiff n M) := by
  rw [contextSummedCycDiff]
  exact range_comp_eq_range_of_surjective_for_cyc (cycDiff n M)
    (contextSumLinear C (Rep n → M))
    (contextSumLinear_surjective C (Rep n → M))

theorem finrank_contextRepFunctionSpace
    (C : Type) [Fintype C] {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (C → Rep n → M) =
      Fintype.card C * (n * Module.finrank F2 M) := by
  classical
  let d := Module.finrank F2 M
  have hz : Module.finrank F2 (Rep n → M) = n * d := by
    calc
      Module.finrank F2 (Rep n → M) = ∑ _ : Rep n, d := by
        simpa [Rep, d] using
          (Module.finrank_pi_fintype
            (R := F2) (M := fun _ : Rep n => M))
      _ = n * d := by
        simp [Rep, ZMod.card, Finset.card_univ]
  calc
    Module.finrank F2 (C → Rep n → M) =
        ∑ _ : C, Module.finrank F2 (Rep n → M) := by
      simpa using
        (Module.finrank_pi_fintype
          (R := F2) (M := fun _ : C => Rep n → M))
    _ = Fintype.card C * (n * d) := by
      simp [hz]

theorem finrank_range_contextSummedCycDiff
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.range (contextSummedCycDiff C n M)) =
      (n - 1) * Module.finrank F2 M := by
  rw [range_contextSummedCycDiff_eq_range_cycDiff C M]
  exact finrank_range_cycDiff M

theorem finrank_ker_contextSummedCycDiff
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Module.finrank F2 (LinearMap.ker (contextSummedCycDiff C n M)) =
      Fintype.card C * (n * Module.finrank F2 M) -
        (n - 1) * Module.finrank F2 M := by
  classical
  let L := contextSummedCycDiff C n M
  let d := Module.finrank F2 M
  let D := Fintype.card C * (n * d)
  let R := (n - 1) * d
  let K := Module.finrank F2 (LinearMap.ker L)
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hdomain : Module.finrank F2 (C → Rep n → M) = D := by
    simpa [D, d] using finrank_contextRepFunctionSpace C M
  have hrange : Module.finrank F2 (LinearMap.range L) = R := by
    simpa [L, R, d] using finrank_range_contextSummedCycDiff C M
  rw [hdomain, hrange] at hsum
  have hK : K = D - R := by
    omega
  simpa [L, K, D, R, d] using hK

theorem card_ker_contextSummedCycDiff
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    Nat.card (↥(LinearMap.ker (contextSummedCycDiff C n M))) =
      2 ^ (Fintype.card C * (n * Module.finrank F2 M) -
        (n - 1) * Module.finrank F2 M) := by
  classical
  calc
    Nat.card (↥(LinearMap.ker (contextSummedCycDiff C n M))) =
        Nat.card F2 ^ Module.finrank F2
          (LinearMap.ker (contextSummedCycDiff C n M)) :=
      Module.natCard_eq_pow_finrank
        (K := F2) (V := LinearMap.ker (contextSummedCycDiff C n M))
    _ = 2 ^ (Fintype.card C * (n * Module.finrank F2 M) -
        (n - 1) * Module.finrank F2 M) := by
      rw [finrank_ker_contextSummedCycDiff C M]
      simp [F2]

theorem card_ker_contextSummedCycDiff_F2
    (C : Type) [Fintype C] [Nonempty C]
    {n : Nat} [NeZero n] :
    Nat.card (↥(LinearMap.ker (contextSummedCycDiff C n F2))) =
      2 ^ (Fintype.card C * n - (n - 1)) := by
  simpa [F2, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    card_ker_contextSummedCycDiff C (n := n) F2

end Imbalance
end TreeGraph
