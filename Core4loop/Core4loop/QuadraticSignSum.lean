import Core4loop.LinearSignSum

open scoped BigOperators

namespace Core4loop

noncomputable section

private theorem add_self_eq_zero_of_F_module
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 := by
  have htwo : (1 : F) + 1 = 0 := by decide
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + 1) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

private noncomputable def quadraticAddRightF2Equiv
    {V : Type*} [AddCommGroup V] [Module F V] (x0 : V) : V ≃ V where
  toFun x := x + x0
  invFun x := x + x0
  left_inv x := by
    change (x + x0) + x0 = x
    rw [add_assoc, add_self_eq_zero_of_F_module x0, add_zero]
  right_inv x := by
    change (x + x0) + x0 = x
    rw [add_assoc, add_self_eq_zero_of_F_module x0, add_zero]

/-- Minimal metabolic evaluator over `F = ZMod 2`.

If `L` is a self-dual isotropic submodule for the polar form of `q`, then the
quadratic sign sum is the cardinality of `L`.
-/
theorem sum_bitSign_eq_card_of_selfDual_isotropic
    {V : Type*}
    [AddCommGroup V] [Module F V] [Fintype V]
    (q : V → F)
    (polar : V →ₗ[F] V →ₗ[F] F)
    (hq_add : ∀ x y : V,
      q (x + y) = q x + q y + polar x y)
    (L : Submodule F V) [Fintype L]
    (hq_zero : ∀ x : L, q x.1 = 0)
    (hself : ∀ x : V,
      ((polar x).comp L.subtype = 0 ↔ x ∈ L)) :
    (∑ x : V, bitSign (q x)) = (Fintype.card L : ℤ) := by
  classical
  let c : ℤ := Fintype.card L
  let G : ℤ := ∑ x : V, bitSign (q x)
  have hcard_pos : 0 < Fintype.card L :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hcard_ne : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (ne_of_gt hcard_pos)
  have htranslate (l : L) :
      G = ∑ x : V, bitSign (q (x + l.1)) := by
    dsimp [G]
    simpa [quadraticAddRightF2Equiv] using
      (((quadraticAddRightF2Equiv (V := V) l.1).sum_comp
        (fun x : V => bitSign (q x))).symm)
  have hmul_translate :
      c * G = ∑ x : V, ∑ l : L, bitSign (q (x + l.1)) := by
    calc
      c * G = ∑ l : L, G := by
        simp [c, Finset.sum_const, nsmul_eq_mul]
      _ = ∑ l : L, ∑ x : V, bitSign (q (x + l.1)) := by
        refine Finset.sum_congr rfl ?_
        intro l _
        exact htranslate l
      _ = ∑ x : V, ∑ l : L, bitSign (q (x + l.1)) := by
        rw [Finset.sum_comm]
  have hinner (x : V) :
      (∑ l : L, bitSign (q (x + l.1))) =
        if x ∈ L then c else 0 := by
    have hfactor :
        (∑ l : L, bitSign (q (x + l.1))) =
          bitSign (q x) *
            ∑ l : L, bitSign (((polar x).comp L.subtype) l) := by
      calc
        (∑ l : L, bitSign (q (x + l.1)))
            =
            ∑ l : L, bitSign (q x) *
              bitSign (((polar x).comp L.subtype) l) := by
              refine Finset.sum_congr rfl ?_
              intro l _
              rw [hq_add, hq_zero l]
              simp [bitSign_add, mul_assoc]
        _ =
            bitSign (q x) *
              ∑ l : L, bitSign (((polar x).comp L.subtype) l) := by
              rw [Finset.mul_sum]
    rw [hfactor]
    have hlin := sum_bitSign_linearMap ((polar x).comp L.subtype)
    by_cases hx : x ∈ L
    · have hzeroMap : (polar x).comp L.subtype = 0 := (hself x).mpr hx
      have hqx : q x = 0 := hq_zero ⟨x, hx⟩
      rw [hlin]
      rw [if_pos hzeroMap]
      rw [hqx, bitSign_zero]
      simp [c, hx]
    · have hnonzeroMap : (polar x).comp L.subtype ≠ 0 := by
        intro hzeroMap
        exact hx ((hself x).mp hzeroMap)
      rw [hlin]
      rw [if_neg hnonzeroMap]
      simp [hx]
  have hindicator :
      (∑ x : V, (if x ∈ L then c else 0)) = c * c := by
    calc
      (∑ x : V, (if x ∈ L then c else 0))
          =
          ∑ x ∈ (Finset.univ.filter fun x : V => x ∈ L), c := by
            exact (Finset.sum_filter (fun x : V => x ∈ L)
              (fun _x : V => c)).symm
      _ =
          ∑ x ∈ (Finset.univ.subtype fun x : V => x ∈ L), c := by
            exact (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset V))
              (f := fun _x : V => c)
              (p := fun x : V => x ∈ L)).symm
      _ = ∑ x : L, c := by
            apply Finset.sum_congr
            · ext x
              constructor
              · intro _
                exact @Finset.mem_univ L _ x
              · intro _
                exact (Finset.mem_subtype).2 (Finset.mem_univ x.1)
            · intro _ _
              rfl
      _ = c * c := by
            simp [c, Finset.sum_const, nsmul_eq_mul]
  have hmul : c * G = c * c := by
    calc
      c * G = ∑ x : V, ∑ l : L, bitSign (q (x + l.1)) := hmul_translate
      _ = ∑ x : V, (if x ∈ L then c else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            exact hinner x
      _ = c * c := hindicator
  exact mul_left_cancel₀ hcard_ne hmul

theorem sum_bitSign_eq_pow_finrank_of_selfDual_isotropic
    {V : Type*}
    [AddCommGroup V] [Module F V] [Fintype V]
    (q : V → F)
    (polar : V →ₗ[F] V →ₗ[F] F)
    (hq_add : ∀ x y : V,
      q (x + y) = q x + q y + polar x y)
    (L : Submodule F V) [Fintype L]
    (hq_zero : ∀ x : L, q x.1 = 0)
    (hself : ∀ x : V,
      ((polar x).comp L.subtype = 0 ↔ x ∈ L)) :
    (∑ x : V, bitSign (q x)) =
      (2 : ℤ) ^ Module.finrank F L := by
  rw [sum_bitSign_eq_card_of_selfDual_isotropic q polar hq_add L hq_zero hself]
  calc
    (Fintype.card L : ℤ) = (Nat.card L : ℤ) := by
      rw [Nat.card_eq_fintype_card]
    _ = ((2 ^ Module.finrank F L : ℕ) : ℤ) := by
      rw [Module.natCard_eq_pow_finrank (K := F)]
      simp [F]
    _ = (2 : ℤ) ^ Module.finrank F L := by
      norm_num

end

end Core4loop
