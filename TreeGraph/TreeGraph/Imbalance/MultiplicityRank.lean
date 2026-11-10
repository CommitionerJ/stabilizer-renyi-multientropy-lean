import TreeGraph.Imbalance.CyclicFamily

namespace TreeGraph
namespace Imbalance

theorem range_comp_eq_range_of_surjective
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

theorem visibleRank_not_multiplied (n : Nat) [NeZero n]
    (E P M : Type) [Fintype E]
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    [FiniteDimensional F2 (Module.Dual F2 M)]
    (R : P →ₗ[F2] (E × Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    Module.finrank F2
      (LinearMap.range
        ((familyCycDiff n E (Module.Dual F2 M)).comp R)) =
      Fintype.card E * (n - 1) *
        Module.finrank F2 (Module.Dual F2 M) := by
  rw [range_comp_eq_range_of_surjective R
    (familyCycDiff n E (Module.Dual F2 M)) hR]
  exact finrank_range_familyCycDiff n E (Module.Dual F2 M)

noncomputable def rtildeVisibleKernel (n : Nat) [NeZero n]
    (E P M : Type) [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M)) :
    Submodule F2 (E → P) :=
  LinearMap.ker
    ((familyCycDiff n E (Module.Dual F2 M)).comp
      (RtildeAbstract n E P M R))

noncomputable instance rtildeVisibleKernelFintype (n : Nat) [NeZero n]
    (E P M : Type) [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P] [Fintype P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M)) :
    Fintype (rtildeVisibleKernel n E P M R) := by
  exact Fintype.ofFinite (rtildeVisibleKernel n E P M R)

theorem finrank_rtildeVisibleKernel (n : Nat) [NeZero n]
    (E P M : Type) [Fintype E]
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    Module.finrank F2 (rtildeVisibleKernel n E P M R) =
      Fintype.card E * Module.finrank F2 P -
        Fintype.card E * (n - 1) * Module.finrank F2 M := by
  classical
  let L : (E → P) →ₗ[F2] (E × Rep n → Module.Dual F2 M) :=
    (familyCycDiff n E (Module.Dual F2 M)).comp
      (RtildeAbstract n E P M R)
  have hRtilde : Function.Surjective (RtildeAbstract n E P M R) :=
    RtildeAbstract_surjective n E P M R hR
  have hrange_eq :
      LinearMap.range L =
        LinearMap.range (familyCycDiff n E (Module.Dual F2 M)) := by
    exact range_comp_eq_range_of_surjective
      (RtildeAbstract n E P M R)
      (familyCycDiff n E (Module.Dual F2 M)) hRtilde
  have hrange :
      Module.finrank F2 (LinearMap.range L) =
        Fintype.card E * (n - 1) * Module.finrank F2 M := by
    rw [hrange_eq]
    rw [finrank_range_familyCycDiff]
    rw [Subspace.dual_finrank_eq]
  have hdomain :
      Module.finrank F2 (E → P) =
        Fintype.card E * Module.finrank F2 P := by
    calc
      Module.finrank F2 (E → P) =
          ∑ _ : E, Module.finrank F2 P := by
        simpa using
          (Module.finrank_pi_fintype
            (R := F2) (M := fun _ : E => P))
      _ = Fintype.card E * Module.finrank F2 P := by
        simp [Finset.card_univ]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hsum :
      Fintype.card E * (n - 1) * Module.finrank F2 M +
        Module.finrank F2 (rtildeVisibleKernel n E P M R) =
        Fintype.card E * Module.finrank F2 P := by
    simpa [L, rtildeVisibleKernel, hrange, hdomain] using hrank
  omega

theorem Ktilde_dim (n : Nat) [NeZero n]
    (E P M : Type) [Fintype E]
    [AddCommGroup P] [Module F2 P] [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    Module.finrank F2 (rtildeVisibleKernel n E P M R) =
      Fintype.card E * Module.finrank F2 P -
        Fintype.card E * (n - 1) * Module.finrank F2 M := by
  exact finrank_rtildeVisibleKernel n E P M R hR

theorem card_rtildeVisibleKernel (n : Nat) [NeZero n]
    (E P M : Type) [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P] [Fintype P]
    [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    Fintype.card (rtildeVisibleKernel n E P M R) =
      2 ^ (Fintype.card E * Module.finrank F2 P -
        Fintype.card E * (n - 1) * Module.finrank F2 M) := by
  rw [submodule_card_eq_pow_finrank]
  rw [finrank_rtildeVisibleKernel n E P M R hR]

end Imbalance
end TreeGraph
