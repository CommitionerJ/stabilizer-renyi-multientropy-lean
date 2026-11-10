import TreeGraph.Imbalance.IncidenceShear

namespace TreeGraph
namespace Imbalance

noncomputable def multiplicitySum (n : Nat) [NeZero n]
    (Q E M : Type) [Fintype Q]
    [AddCommMonoid M] [Module F2 M] :
    (Q × E × Rep n → M) →ₗ[F2] (E × Rep n → M) where
  toFun μ := fun et => ∑ q : Q, μ (q, et.1, et.2)
  map_add' μ ν := by
    classical
    ext et
    change
      (Finset.univ.sum
        (fun q : Q => μ (q, et.1, et.2) + ν (q, et.1, et.2))) =
        (Finset.univ.sum (fun q : Q => μ (q, et.1, et.2))) +
          Finset.univ.sum (fun q : Q => ν (q, et.1, et.2))
    rw [← Finset.sum_add_distrib]
  map_smul' r μ := by
    classical
    ext et
    change
      (Finset.univ.sum (fun q : Q => r • μ (q, et.1, et.2))) =
        r • Finset.univ.sum (fun q : Q => μ (q, et.1, et.2))
    rw [Finset.smul_sum]

@[simp] theorem multiplicitySum_apply (n : Nat) [NeZero n]
    (Q E M : Type) [Fintype Q]
    [AddCommMonoid M] [Module F2 M]
    (μ : Q × E × Rep n → M) (et : E × Rep n) :
    multiplicitySum n Q E M μ et =
      ∑ q : Q, μ (q, et.1, et.2) := rfl

theorem multiplicitySum_surjective (n : Nat) [NeZero n]
    (Q E M : Type) [Fintype Q] [Nonempty Q]
    [AddCommMonoid M] [Module F2 M] :
    Function.Surjective (multiplicitySum n Q E M) := by
  classical
  intro g
  let q0 : Q := Classical.choice ‹Nonempty Q›
  let μ : Q × E × Rep n → M := fun p =>
    if p.1 = q0 then g (p.2.1, p.2.2) else 0
  refine ⟨μ, ?_⟩
  ext et
  rw [multiplicitySum_apply]
  rw [Fintype.sum_eq_single q0]
  · simp [μ]
  · intro q hq
    simp [μ, hq]

noncomputable def multiplicityExponent (n : Nat) [NeZero n]
    {Q E M : Type} [Fintype Q] [Fintype E]
    [AddCommMonoid M] [Module F2 M]
    (coeff : E × Rep n → Module.Dual F2 M) :
    (Q × E × Rep n → M) →ₗ[F2] F2 where
  toFun μ := ∑ et : E × Rep n,
    coeff et (multiplicitySum n Q E M μ et)
  map_add' μ ν := by
    classical
    change
      (∑ et : E × Rep n,
        coeff et (multiplicitySum n Q E M (μ + ν) et)) =
        (∑ et : E × Rep n,
          coeff et (multiplicitySum n Q E M μ et)) +
          ∑ et : E × Rep n,
            coeff et (multiplicitySum n Q E M ν et)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro et _
    rw [map_add]
    change
      coeff et
        (multiplicitySum n Q E M μ et + multiplicitySum n Q E M ν et) =
        coeff et (multiplicitySum n Q E M μ et) +
          coeff et (multiplicitySum n Q E M ν et)
    rw [map_add]
  map_smul' r μ := by
    classical
    change
      (∑ et : E × Rep n,
        coeff et (multiplicitySum n Q E M (r • μ) et)) =
        r • ∑ et : E × Rep n,
          coeff et (multiplicitySum n Q E M μ et)
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro et _
    rw [map_smul]
    change
      coeff et (r • multiplicitySum n Q E M μ et) =
        r • coeff et (multiplicitySum n Q E M μ et)
    rw [map_smul]

@[simp] theorem multiplicityExponent_apply (n : Nat) [NeZero n]
    {Q E M : Type} [Fintype Q] [Fintype E]
    [AddCommMonoid M] [Module F2 M]
    (coeff : E × Rep n → Module.Dual F2 M)
    (μ : Q × E × Rep n → M) :
    multiplicityExponent n coeff μ =
      ∑ et : E × Rep n,
        coeff et (multiplicitySum n Q E M μ et) := rfl

set_option linter.unusedDecidableInType false in
theorem multiplicityExponent_eq_zero_iff (n : Nat) [NeZero n]
    {Q E M : Type} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommMonoid M] [Module F2 M]
    (coeff : E × Rep n → Module.Dual F2 M) :
    multiplicityExponent n (Q := Q) coeff = 0 ↔ coeff = 0 := by
  classical
  constructor
  · intro h
    ext et m
    let q0 : Q := Classical.choice ‹Nonempty Q›
    let p0 : Q × E × Rep n := (q0, et.1, et.2)
    have hp0 :
        multiplicityExponent n (Q := Q) coeff
          (Pi.single (M := fun _ : Q × E × Rep n => M) p0 m) = 0 := by
      simpa using
        congrArg
          (fun ell : (Q × E × Rep n → M) →ₗ[F2] F2 =>
            ell (Pi.single (M := fun _ : Q × E × Rep n => M) p0 m))
          h
    have hsumq_same :
        (∑ q : Q,
          Pi.single (M := fun _ : Q × E × Rep n => M) p0 m
            (q, et.1, et.2)) = m := by
      rw [Fintype.sum_eq_single q0]
      · simp [p0]
      · intro q hq
        simp [p0, hq]
    have hsumq_other :
        ∀ et' : E × Rep n, et' ≠ et →
          (∑ q : Q,
            Pi.single (M := fun _ : Q × E × Rep n => M) p0 m
              (q, et'.1, et'.2)) = 0 := by
      intro et' het'
      rw [Fintype.sum_eq_zero]
      intro q
      have hp_ne : (q, et'.1, et'.2) ≠ p0 := by
        intro hp
        apply het'
        have htail : (et'.1, et'.2) = (et.1, et.2) := by
          simpa [p0] using congrArg Prod.snd hp
        simpa [Prod.eta] using htail
      simp [Pi.single_eq_of_ne, hp_ne]
    have hsum :
        (∑ et' : E × Rep n,
          coeff et'
            (multiplicitySum n Q E M
              (Pi.single (M := fun _ : Q × E × Rep n => M) p0 m)
              et')) = coeff et m := by
      rw [Fintype.sum_eq_single et]
      · rw [multiplicitySum_apply, hsumq_same]
      · intro et' het'
        rw [multiplicitySum_apply, hsumq_other et' het']
        simp
    have hsingleExp :
        multiplicityExponent n (Q := Q) coeff
          (Pi.single (M := fun _ : Q × E × Rep n => M) p0 m) =
            coeff et m := by
      rw [multiplicityExponent_apply, hsum]
    simpa [hsingleExp] using hp0
  · intro h
    subst coeff
    ext μ
    simp [multiplicityExponent]

theorem multiplicity_char_sum_card (n : Nat) [NeZero n]
    {Q E M : Type} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    (coeff : E × Rep n → Module.Dual F2 M) :
    (∑ μ : Q × E × Rep n → M,
      chi (multiplicityExponent n (Q := Q) coeff μ)) =
      if coeff = 0 then
        (Fintype.card (Q × E × Rep n → M) : ℤ)
      else
        0 := by
  by_cases hcoeff : coeff = 0
  · have hL :
        multiplicityExponent n (Q := Q) coeff = 0 :=
      (multiplicityExponent_eq_zero_iff n (Q := Q) coeff).2 hcoeff
    calc
      (∑ μ : Q × E × Rep n → M,
        chi (multiplicityExponent n (Q := Q) coeff μ)) =
          (Fintype.card (Q × E × Rep n → M) : ℤ) :=
        char_sum_linear_zero
          (multiplicityExponent n (Q := Q) coeff) hL
      _ =
          if coeff = 0 then
            (Fintype.card (Q × E × Rep n → M) : ℤ)
          else 0 := by
        simp [hcoeff]
  · have hL :
        multiplicityExponent n (Q := Q) coeff ≠ 0 := by
      intro hzero
      exact hcoeff
        ((multiplicityExponent_eq_zero_iff n (Q := Q) coeff).1 hzero)
    calc
      (∑ μ : Q × E × Rep n → M,
        chi (multiplicityExponent n (Q := Q) coeff μ)) = 0 :=
        char_sum_linear_nonzero
          (multiplicityExponent n (Q := Q) coeff) hL
      _ =
          if coeff = 0 then
            (Fintype.card (Q × E × Rep n → M) : ℤ)
          else 0 := by
        simp [hcoeff]

theorem multiplicity_char_sum (n : Nat) [NeZero n]
    {Q E M : Type} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (coeff : E × Rep n → Module.Dual F2 M) :
    (∑ μ : Q × E × Rep n → M,
      chi (multiplicityExponent n (Q := Q) coeff μ)) =
      if coeff = 0 then
        (2 : ℤ) ^
          (Fintype.card Q * Fintype.card E * n *
            Module.finrank F2 M)
      else
        0 := by
  rw [multiplicity_char_sum_card n coeff]
  by_cases hcoeff : coeff = 0
  · have hcardM :
        Fintype.card M = 2 ^ Module.finrank F2 M := by
      calc
        Fintype.card M = Nat.card M := Fintype.card_eq_nat_card
        _ = Nat.card F2 ^ Module.finrank F2 M :=
            Module.natCard_eq_pow_finrank (K := F2) (V := M)
        _ = 2 ^ Module.finrank F2 M := by
            simp [F2]
    have hcardIndex :
        Fintype.card (Q × E × Rep n) =
          Fintype.card Q * Fintype.card E * n := by
      simp [Rep, ZMod.card, Fintype.card_prod, Nat.mul_assoc]
    have hcard :
        Fintype.card (Q × E × Rep n → M) =
          2 ^ (Fintype.card Q * Fintype.card E * n *
            Module.finrank F2 M) := by
      calc
        Fintype.card (Q × E × Rep n → M) =
            Fintype.card M ^ Fintype.card (Q × E × Rep n) := by
          simp
        _ = (2 ^ Module.finrank F2 M) ^
            Fintype.card (Q × E × Rep n) := by
          rw [hcardM]
        _ = 2 ^ (Module.finrank F2 M *
            Fintype.card (Q × E × Rep n)) := by
          rw [Nat.pow_mul]
        _ = 2 ^ (Module.finrank F2 M *
            (Fintype.card Q * Fintype.card E * n)) := by
          rw [hcardIndex]
        _ = 2 ^ (Fintype.card Q * Fintype.card E * n *
            Module.finrank F2 M) := by
          congr 1
          ring
    simp [hcoeff, hcard]
  · simp [hcoeff]

theorem multiplicity_cyclic_family_sum (n : Nat) [NeZero n]
    {Q E M : Type} [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (coeff : E × Rep n → Module.Dual F2 M) :
    (∑ μ : Q × E × Rep n → M,
      chi (multiplicityExponent n (Q := Q) coeff μ)) =
      if coeff = 0 then
        (2 : ℤ) ^
          (Fintype.card Q * Fintype.card E * n *
            Module.finrank F2 M)
      else
        0 := by
  exact multiplicity_char_sum n coeff

end Imbalance
end TreeGraph
