import Core4loop.ZeroSumSpaces.Profile

open scoped BigOperators

namespace Core4loop

theorem range_cycDiff_eq_ZeroSumProfileM {n : ℕ} [NeZero n]
    (M : Type*) [AddCommGroup M] [Module F M] [FiniteDimensional F M] :
    LinearMap.range (cycDiff (n := n) M) = ZeroSumProfileM n M := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro u hu
    rcases hu with ⟨v, rfl⟩
    exact cycDiff_mem_ZeroSumProfileM v
  · let r := Module.finrank F (LinearMap.range (cycDiff (n := n) M))
    let m := Module.finrank F M
    have hdom : Module.finrank F (I n → M) = n * m := by
      calc
        Module.finrank F (I n → M)
            = ∑ _ : I n, Module.finrank F M := by
                simp [Module.finrank_pi_fintype (R := F) (M := fun _ : I n => M)]
        _ = Fintype.card (I n) * m := by
                simp [m]
        _ = n * m := by
                simp [I, ZMod.card]
    have hnull :=
      LinearMap.finrank_range_add_finrank_ker (cycDiff (n := n) M)
    have hsum : r + m = n * m := by
      simpa [r, m, hdom, finrank_ker_cycDiff (n := n) M] using hnull
    have hsplit : n * m = (n - 1) * m + m := by
      have hnpos : 0 < n := NeZero.pos n
      have hn : n = n - 1 + 1 := by omega
      calc
        n * m = ((n - 1) + 1) * m := congrArg (fun q => q * m) hn
        _ = (n - 1) * m + 1 * m := by rw [Nat.add_mul]
        _ = (n - 1) * m + m := by simp
    have hr : r = (n - 1) * m := by
      rw [hsplit] at hsum
      exact Nat.add_right_cancel hsum
    rw [finrank_ZeroSumProfileM]
    exact hr

noncomputable def cycDiffToZeroSumM {n : ℕ} [NeZero n]
    (M : Type*) [AddCommGroup M] [Module F M] :
    (I n → M) →ₗ[F] ZeroSumProfileM n M where
  toFun f := ⟨cycDiff (n := n) M f, cycDiff_mem_ZeroSumProfileM f⟩
  map_add' f g := by
    apply Subtype.ext
    exact (cycDiff (n := n) M).map_add f g
  map_smul' r f := by
    apply Subtype.ext
    exact (cycDiff (n := n) M).map_smul r f

theorem cycDiffToZeroSumM_surjective {n : ℕ} [NeZero n]
    (M : Type*) [AddCommGroup M] [Module F M] [FiniteDimensional F M] :
    Function.Surjective (cycDiffToZeroSumM (n := n) M) := by
  intro u
  have hu : u.1 ∈ LinearMap.range (cycDiff (n := n) M) := by
    rw [range_cycDiff_eq_ZeroSumProfileM (n := n) M]
    exact u.2
  rcases hu with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  apply Subtype.ext
  exact hf

noncomputable def cycPrimitiveM {n : ℕ} [NeZero n]
    (M : Type*) [AddCommGroup M] [Module F M] [FiniteDimensional F M] :
    ZeroSumProfileM n M →ₗ[F] (I n → M) :=
  Classical.choose
    ((cycDiffToZeroSumM (n := n) M).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (cycDiffToZeroSumM_surjective (n := n) M)))

theorem cycDiff_cycPrimitiveM {n : ℕ} [NeZero n]
    (M : Type*) [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (u : ZeroSumProfileM n M) :
    cycDiffToZeroSumM (n := n) M (cycPrimitiveM (n := n) M u) = u := by
  unfold cycPrimitiveM
  let e :=
    (cycDiffToZeroSumM (n := n) M).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (cycDiffToZeroSumM_surjective (n := n) M))
  change ((cycDiffToZeroSumM (n := n) M).comp (Classical.choose e)) u = u
  have hright := Classical.choose_spec e
  rw [hright]
  rfl

end Core4loop
