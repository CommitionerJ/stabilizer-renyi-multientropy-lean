import TreeGraph.Imbalance.Multiplicity

namespace TreeGraph
namespace Imbalance

noncomputable def sliceLinearMap
    {E P G : Type} [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid G] [Module F2 G]
    (R : P →ₗ[F2] G) :
    (E → P) →ₗ[F2] (E → G) where
  toFun h := fun e => R (h e)
  map_add' h k := by
    ext e
    simp [Pi.add_apply]
  map_smul' r h := by
    ext e
    simp [Pi.smul_apply]

@[simp] theorem sliceLinearMap_apply
    {E P G : Type} [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid G] [Module F2 G]
    (R : P →ₗ[F2] G) (h : E → P) (e : E) :
    sliceLinearMap R h e = R (h e) := rfl

theorem sliceLinearMap_surjective
    {E P G : Type} [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid G] [Module F2 G]
    (R : P →ₗ[F2] G) (hR : Function.Surjective R) :
    Function.Surjective (sliceLinearMap (E := E) R) := by
  classical
  intro g
  choose h hh using fun e : E => hR (g e)
  refine ⟨h, ?_⟩
  ext e
  exact hh e

noncomputable def RtildeAbstract (n : Nat) [NeZero n]
    (E P M : Type) [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M)) :
    (E → P) →ₗ[F2] (E × Rep n → Module.Dual F2 M) where
  toFun h := fun et => R (h et.1) et.2
  map_add' h k := by
    ext et m
    simp [Pi.add_apply]
  map_smul' r h := by
    ext et m
    simp [Pi.smul_apply]

@[simp] theorem RtildeAbstract_apply (n : Nat) [NeZero n]
    (E P M : Type) [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (h : E → P) (et : E × Rep n) :
    RtildeAbstract n E P M R h et = R (h et.1) et.2 := rfl

theorem RtildeAbstract_surjective (n : Nat) [NeZero n]
    (E P M : Type) [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    Function.Surjective (RtildeAbstract n E P M R) := by
  classical
  intro g
  have hslice :
      ∀ e : E, ∃ p : P, R p = fun t : Rep n => g (e, t) := by
    intro e
    exact hR (fun t : Rep n => g (e, t))
  choose h hh using hslice
  refine ⟨h, ?_⟩
  ext et m
  have heq := congrFun (hh et.1) et.2
  exact congrArg (fun ell : Module.Dual F2 M => ell m) heq

theorem Rtilde_surjective (n : Nat) [NeZero n]
    (E P M : Type) [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    Function.Surjective (RtildeAbstract n E P M R) := by
  exact RtildeAbstract_surjective n E P M R hR

private theorem range_comp_eq_range_of_surjective'
    {P Q S : Type}
    [AddCommMonoid P] [Module F2 P]
    [AddCommMonoid Q] [Module F2 Q]
    [AddCommMonoid S] [Module F2 S]
    (L : P →ₗ[F2] Q) (R : Q →ₗ[F2] S)
    (hL : Function.Surjective L) :
    LinearMap.range (R.comp L) = LinearMap.range R := by
  ext s
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨L p, hp⟩
  · rintro ⟨q, hq⟩
    rcases hL q with ⟨p, hp⟩
    exact ⟨p, by simp [hp, hq]⟩

noncomputable def oneSliceCyclicKernel (n : Nat) [NeZero n]
    (P M : Type) [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M)) :
    Submodule F2 P :=
  LinearMap.ker ((cycDiff n (Module.Dual F2 M)).comp R)

theorem finrank_oneSliceCyclicKernel (n : Nat) [NeZero n]
    (P M : Type) [AddCommGroup P] [Module F2 P]
    [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    Module.finrank F2 (oneSliceCyclicKernel n P M R) =
      Module.finrank F2 P - (n - 1) * Module.finrank F2 M := by
  classical
  let L : P →ₗ[F2] (Rep n → Module.Dual F2 M) :=
    (cycDiff n (Module.Dual F2 M)).comp R
  have hrange_eq :
      LinearMap.range L =
        LinearMap.range (cycDiff n (Module.Dual F2 M)) := by
    exact range_comp_eq_range_of_surjective' R
      (cycDiff n (Module.Dual F2 M)) hR
  have hrange :
      Module.finrank F2 (LinearMap.range L) =
        (n - 1) * Module.finrank F2 M := by
    rw [hrange_eq]
    rw [finrank_range_cycDiff]
    rw [Subspace.dual_finrank_eq]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hsum :
      (n - 1) * Module.finrank F2 M +
        Module.finrank F2 (oneSliceCyclicKernel n P M R) =
        Module.finrank F2 P := by
    simpa [L, oneSliceCyclicKernel, hrange] using hrank
  omega

theorem oneSliceCyclicRank_le_of_surjective (n : Nat) [NeZero n]
    (P M : Type) [AddCommGroup P] [Module F2 P]
    [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    (n - 1) * Module.finrank F2 M ≤ Module.finrank F2 P := by
  classical
  let L : P →ₗ[F2] (Rep n → Module.Dual F2 M) :=
    (cycDiff n (Module.Dual F2 M)).comp R
  have hrange_eq :
      LinearMap.range L =
        LinearMap.range (cycDiff n (Module.Dual F2 M)) := by
    exact range_comp_eq_range_of_surjective' R
      (cycDiff n (Module.Dual F2 M)) hR
  have hrange :
      Module.finrank F2 (LinearMap.range L) =
        (n - 1) * Module.finrank F2 M := by
    rw [hrange_eq]
    rw [finrank_range_cycDiff]
    rw [Subspace.dual_finrank_eq]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hsum :
      (n - 1) * Module.finrank F2 M +
        Module.finrank F2 (LinearMap.ker L) =
        Module.finrank F2 P := by
    simpa [L, hrange] using hrank
  omega

end Imbalance
end TreeGraph
