import Core4loop.LinearSignSum

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

theorem sum_bitSign_bilinear_eq_ker_mul
    {U V : Type*}
    [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (L : U →ₗ[F] Module.Dual F V) :
    (∑ z : U × V, bitSign (L z.1 z.2)) =
      (Nat.card (LinearMap.ker L) : Int) * Fintype.card V := by
  classical
  letI : Fintype (LinearMap.ker L) :=
    Fintype.ofInjective
      (fun x : LinearMap.ker L => x.1)
      Subtype.val_injective
  rw [Fintype.sum_prod_type]
  have hinner (u : U) :
      (∑ v : V, bitSign (L u v)) =
        if L u = 0 then (Fintype.card V : Int) else 0 :=
    sum_bitSign_linearMap (L u)
  simp_rw [hinner]
  let c : Int := Fintype.card V
  have hindicator :
      (∑ u : U, if L u = 0 then c else 0) =
        ∑ u : LinearMap.ker L, c := by
    calc
      (∑ u : U, if L u = 0 then c else 0) =
          ∑ u ∈ (Finset.univ.filter fun u : U => L u = 0), c := by
            exact
              (Finset.sum_filter (fun u : U => L u = 0)
                (fun _u : U => c)).symm
      _ = ∑ u ∈ (Finset.univ.subtype fun u : U => L u = 0), c := by
            exact
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset U))
                (f := fun _u : U => c)
                (p := fun u : U => L u = 0)).symm
      _ = ∑ _u : LinearMap.ker L, c := by
            apply Finset.sum_congr
            · ext u
              constructor
              · intro _
                exact @Finset.mem_univ (LinearMap.ker L) _ u
              · intro _
                exact (Finset.mem_subtype).2 (Finset.mem_univ u.1)
            · intro _ _
              rfl
  rw [hindicator]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show Fintype.card (LinearMap.ker L) =
      Nat.card (LinearMap.ker L) by
    exact Nat.card_eq_fintype_card.symm]

theorem sum_bitSign_bilinear_eq_pow
    {U V : Type*}
    [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (L : U →ₗ[F] Module.Dual F V) :
    (∑ z : U × V, bitSign (L z.1 z.2)) =
      (2 : Int) ^
        (Module.finrank F (LinearMap.ker L) +
          Module.finrank F V) := by
  rw [sum_bitSign_bilinear_eq_ker_mul]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  rw [← Nat.card_eq_fintype_card]
  have hV :
      Nat.card V = 2 ^ Module.finrank F V :=
    by
      simpa [F] using
        (Module.natCard_eq_pow_finrank (K := F) (V := V))
  rw [hV]
  norm_num [F, pow_add]

end

end Core4loop.SquareDiagonal.DirectWitt
