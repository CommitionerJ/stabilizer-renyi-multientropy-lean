import Core4loop.SquareDiagonal.DirectWitt.BilinearSignSum

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

noncomputable def diamondOddFamilyCross
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    (T → U) →ₗ[F] Module.Dual F (T → V) where
  toFun u :=
    { toFun := fun v => ∑ t, L (u t) (v t)
      map_add' := by
        intro v w
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r v
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply,
          Finset.smul_sum] }
  map_add' := by
    intro u u'
    apply LinearMap.ext
    intro v
    change
      (∑ t, L (u t + u' t) (v t)) =
        (∑ t, L (u t) (v t)) + ∑ t, L (u' t) (v t)
    simp only [map_add, LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' := by
    intro r u
    apply LinearMap.ext
    intro v
    change
      (∑ t, L (r • u t) (v t)) =
        r • ∑ t, L (u t) (v t)
    simp only [map_smul, LinearMap.smul_apply,
      Finset.smul_sum]

@[simp] theorem diamondOddFamilyCross_apply
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V)
    (u : T → U) (v : T → V) :
    diamondOddFamilyCross L u v =
      ∑ t, L (u t) (v t) :=
  rfl

theorem diamondOddFamilyCross_mem_ker_iff
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V)
    (u : T → U) :
    u ∈ LinearMap.ker
        (diamondOddFamilyCross (T := T) L) ↔
      ∀ t, u t ∈ LinearMap.ker L := by
  classical
  rw [LinearMap.mem_ker]
  constructor
  · intro hu t
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro v
    have hpoint :=
      LinearMap.congr_fun hu (Pi.single t v)
    simp only [diamondOddFamilyCross_apply,
      LinearMap.zero_apply] at hpoint
    rw [Finset.sum_eq_single t] at hpoint
    · simpa using hpoint
    · intro s _ hst
      rw [Pi.single_eq_of_ne hst]
      simp
    · simp
  · intro hu
    apply LinearMap.ext
    intro v
    simp only [diamondOddFamilyCross_apply,
      LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro t _
    exact LinearMap.congr_fun
      (LinearMap.mem_ker.mp (hu t)) (v t)

private noncomputable def diamondOddFamilyCrossKerEquiv
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    LinearMap.ker
        (diamondOddFamilyCross (T := T) L) ≃ₗ[F]
      (T → LinearMap.ker L) where
  toFun u := fun t => ⟨u.1 t,
    (diamondOddFamilyCross_mem_ker_iff
      (T := T) (U := U) (V := V) L u.1).mp u.2 t⟩
  invFun u := ⟨fun t => (u t).1,
    (diamondOddFamilyCross_mem_ker_iff
      (T := T) (U := U) (V := V) L
      (fun t => (u t).1)).mpr
      (fun t => (u t).2)⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv u := by
    funext t
    rfl
  map_add' u v := rfl
  map_smul' r u := rfl

private theorem finrank_ker_diamondOddFamilyCross
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F
        (LinearMap.ker
          (diamondOddFamilyCross (T := T) L)) =
      Fintype.card T *
        Module.finrank F (LinearMap.ker L) := by
  rw [LinearEquiv.finrank_eq
    (diamondOddFamilyCrossKerEquiv
      (T := T) (U := U) (V := V) L)]
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul]

theorem finrank_range_diamondOddFamilyCross
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F
        (LinearMap.range
          (diamondOddFamilyCross (T := T) L)) =
      Fintype.card T *
        Module.finrank F (LinearMap.range L) := by
  have hfamily :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondOddFamilyCross (T := T) L)
  have hbase :=
    LinearMap.finrank_range_add_finrank_ker L
  rw [finrank_ker_diamondOddFamilyCross
      (T := T) (U := U) (V := V),
    Module.finrank_pi_fintype] at hfamily
  simp only [Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul] at hfamily
  have hscaled :
      Fintype.card T *
          Module.finrank F (LinearMap.range L) +
        Fintype.card T *
          Module.finrank F (LinearMap.ker L) =
        Fintype.card T * Module.finrank F U := by
    rw [← Nat.mul_add, hbase]
  exact Nat.add_right_cancel
    (hfamily.trans hscaled.symm)

end

end Core4loop.SquareDiagonal.DirectWitt
