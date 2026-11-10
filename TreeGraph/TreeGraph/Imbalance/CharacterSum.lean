import TreeGraph.Imbalance.Basic
import TreeGraph.AlgebraLemmas

namespace TreeGraph
namespace Imbalance

theorem char_sum_linear_card
    {W : Type} [AddCommGroup W] [Module F2 W] [Fintype W]
    (ell : W →ₗ[F2] F2) :
    (∑ w : W, chi (ell w)) =
      if ell = 0 then (Fintype.card W : ℤ) else 0 := by
  simpa [chi] using TreeGraph.sum_bitSign_linear ell

lemma char_sum_linear_zero
    {W : Type} [AddCommGroup W] [Module F2 W] [Fintype W]
    (ell : W →ₗ[F2] F2) (h : ell = 0) :
    (∑ w : W, chi (ell w)) = (Fintype.card W : ℤ) := by
  rw [char_sum_linear_card, if_pos h]

lemma char_sum_linear_nonzero
    {W : Type} [AddCommGroup W] [Module F2 W] [Fintype W]
    (ell : W →ₗ[F2] F2) (h : ell ≠ 0) :
    (∑ w : W, chi (ell w)) = 0 := by
  rw [char_sum_linear_card, if_neg h]

theorem char_sum_linear
    {W : Type} [AddCommGroup W] [Module F2 W] [Fintype W]
    [FiniteDimensional F2 W]
    (ell : W →ₗ[F2] F2) :
    (∑ w : W, chi (ell w)) =
      if ell = 0 then (2 : ℤ) ^ Module.finrank F2 W else 0 := by
  rw [char_sum_linear_card ell]
  by_cases h : ell = 0
  · have hcard :
        (Fintype.card W : ℤ) =
          (2 : ℤ) ^ Module.finrank F2 W := by
      have hnat :
          Fintype.card W = 2 ^ Module.finrank F2 W := by
        calc
          Fintype.card W = Nat.card W := Fintype.card_eq_nat_card
          _ = Nat.card F2 ^ Module.finrank F2 W :=
              Module.natCard_eq_pow_finrank (K := F2) (V := W)
          _ = 2 ^ Module.finrank F2 W := by
              simp [F2]
      exact_mod_cast hnat
    simp [h, hcard]
  · simp [h]

noncomputable def familyExponent
    {I M : Type} [Fintype I]
    [AddCommGroup M] [Module F2 M]
    (coeff : I → Module.Dual F2 M) :
    (I → M) →ₗ[F2] F2 where
  toFun μ := ∑ i : I, coeff i (μ i)
  map_add' μ ν := by
    simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r μ := by
    simpa [Pi.smul_apply] using
      (Finset.smul_sum
        (s := Finset.univ)
        (f := fun i : I => coeff i (μ i))
        (r := r)).symm

@[simp] theorem familyExponent_apply
    {I M : Type} [Fintype I]
    [AddCommGroup M] [Module F2 M]
    (coeff : I → Module.Dual F2 M) (μ : I → M) :
    familyExponent coeff μ = ∑ i : I, coeff i (μ i) := rfl

set_option linter.unusedDecidableInType false in
theorem familyExponent_eq_zero_iff
    {I M : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module F2 M]
    (coeff : I → Module.Dual F2 M) :
    familyExponent coeff = 0 ↔ coeff = 0 := by
  classical
  constructor
  · intro h
    ext i m
    have hi : familyExponent coeff (Pi.single i m) = 0 := by
      simpa using
      congrArg
        (fun ell : (I → M) →ₗ[F2] F2 =>
          ell (Pi.single (M := fun _ : I => M) i m))
        h
    have hsum :
        (∑ j : I,
          coeff j (Pi.single (M := fun _ : I => M) i m j)) =
            coeff i m := by
      rw [Fintype.sum_eq_single i]
      · simp
      · intro j hj
        simp [Pi.single_eq_of_ne, hj]
    simpa [familyExponent, hsum] using hi
  · intro h
    subst coeff
    ext μ
    simp [familyExponent]

theorem family_char_sum_card
    {I M : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    (coeff : I → Module.Dual F2 M) :
    (∑ μ : I → M, chi (familyExponent coeff μ)) =
      if coeff = 0 then (Fintype.card (I → M) : ℤ) else 0 := by
  by_cases h : coeff = 0
  · have hL : familyExponent coeff = 0 :=
      (familyExponent_eq_zero_iff coeff).2 h
    calc
      (∑ μ : I → M, chi (familyExponent coeff μ)) =
          (Fintype.card (I → M) : ℤ) :=
        char_sum_linear_zero (familyExponent coeff) hL
      _ = if coeff = 0 then (Fintype.card (I → M) : ℤ) else 0 := by
        simp [h]
  · have hL : familyExponent coeff ≠ 0 := by
      intro hzero
      exact h ((familyExponent_eq_zero_iff coeff).1 hzero)
    calc
      (∑ μ : I → M, chi (familyExponent coeff μ)) = 0 :=
        char_sum_linear_nonzero (familyExponent coeff) hL
      _ = if coeff = 0 then (Fintype.card (I → M) : ℤ) else 0 := by
        simp [h]

theorem family_char_sum
    {I M : Type} [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (coeff : I → Module.Dual F2 M) :
    (∑ μ : I → M, chi (familyExponent coeff μ)) =
      if coeff = 0 then
        (2 : ℤ) ^ (Fintype.card I * Module.finrank F2 M)
      else
        0 := by
  rw [family_char_sum_card coeff]
  by_cases h : coeff = 0
  · have hcardM :
        Fintype.card M = 2 ^ Module.finrank F2 M := by
      calc
        Fintype.card M = Nat.card M := Fintype.card_eq_nat_card
        _ = Nat.card F2 ^ Module.finrank F2 M :=
            Module.natCard_eq_pow_finrank (K := F2) (V := M)
        _ = 2 ^ Module.finrank F2 M := by
            simp [F2]
    have hcard :
        Fintype.card (I → M) =
          2 ^ (Fintype.card I * Module.finrank F2 M) := by
      calc
        Fintype.card (I → M) = Fintype.card M ^ Fintype.card I := by
          simp
        _ = (2 ^ Module.finrank F2 M) ^ Fintype.card I := by
          rw [hcardM]
        _ = 2 ^ (Module.finrank F2 M * Fintype.card I) := by
          rw [Nat.pow_mul]
        _ = 2 ^ (Fintype.card I * Module.finrank F2 M) := by
          rw [Nat.mul_comm (Module.finrank F2 M) (Fintype.card I)]
    simp [h, hcard]
  · simp [h]

end Imbalance
end TreeGraph
