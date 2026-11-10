import Core4loop.CompleteGraph.Odd.LeftKernelQZero

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.Odd

open Core4loop

noncomputable section

attribute [local instance] Fintype.ofFinite

/-- The family of cyclic profiles indexed by the invariant pair
`(y, x + z)`. -/
abbrev K4DiagonalOrbitFamily (n : Nat) :=
  (I n × I n) → Profile n

/-- Diagonal-orbit coordinates for a cyclic cube.  The orbit index is
`(y, x + z)` and the cyclic coordinate is `z`. -/
noncomputable def k4DiagonalOrbitEquiv
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] K4DiagonalOrbitFamily n where
  toFun f q t := f (q.2 - t) q.1 t
  invFun g x y z := g (y, x + z) z
  left_inv f := by
    funext x y z
    change f (x + z - z) y z = f x y z
    rw [add_sub_cancel_right]
  right_inv g := by
    funext q t
    change g (q.1, q.2 - t + t) t = g q t
    congr 2
    exact sub_add_cancel q.2 t
  map_add' f g := by
    rfl
  map_smul' r f := by
    rfl

/-- The literal diagonal difference `1 + T_x⁻¹ T_z`. -/
noncomputable def k4DiagonalDiff
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n where
  toFun f := fun x y z => f x y z + f (x - 1) y (z + 1)
  map_add' f g := by
    funext x y z
    simp only [Pi.add_apply]
    abel
  map_smul' r f := by
    funext x y z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private theorem k4DiagonalOrbitEquiv_diff
    {n : Nat} [NeZero n] (f : CyclicCube n)
    (q : I n × I n) (t : I n) :
    k4DiagonalOrbitEquiv (k4DiagonalDiff f) q t =
      cycDiff (n := n) F (k4DiagonalOrbitEquiv f q) t := by
  change
    f (q.2 - t) q.1 t +
        f ((q.2 - t) - 1) q.1 (t + 1) =
      f (q.2 - t) q.1 t +
        f (q.2 - (t + 1)) q.1 (t + 1)
  congr 2
  abel

/-- Cubes which are constant on every diagonal orbit. -/
noncomputable def K4DiagonalOrbitConst
    (n : Nat) [NeZero n] :
    Submodule F (CyclicCube n) where
  carrier := {f | ∀ q t,
    k4DiagonalOrbitEquiv f q t =
      k4DiagonalOrbitEquiv f q 0}
  zero_mem' := by
    intro q t
    rfl
  add_mem' := by
    intro f g hf hg q t
    change
      k4DiagonalOrbitEquiv f q t +
          k4DiagonalOrbitEquiv g q t =
        k4DiagonalOrbitEquiv f q 0 +
          k4DiagonalOrbitEquiv g q 0
    rw [hf q t, hg q t]
  smul_mem' := by
    intro r f hf q t
    change
      r * k4DiagonalOrbitEquiv f q t =
        r * k4DiagonalOrbitEquiv f q 0
    rw [hf q t]

/-- Cubes whose sum on each diagonal orbit is zero. -/
noncomputable def K4DiagonalOrbitZero
    (n : Nat) [NeZero n] :
    Submodule F (CyclicCube n) where
  carrier := {f | ∀ q,
    ∑ t : I n, k4DiagonalOrbitEquiv f q t = 0}
  zero_mem' := by
    intro q
    simp
  add_mem' := by
    intro f g hf hg q
    change
      (∑ t : I n,
        (k4DiagonalOrbitEquiv f q t +
          k4DiagonalOrbitEquiv g q t)) = 0
    rw [Finset.sum_add_distrib, hf q, hg q, add_zero]
  smul_mem' := by
    intro r f hf q
    change
      (∑ t : I n, r * k4DiagonalOrbitEquiv f q t) = 0
    rw [← Finset.mul_sum, hf q, mul_zero]

theorem ker_k4DiagonalDiff_eq_orbitConst
    {n : Nat} [NeZero n] :
    LinearMap.ker (k4DiagonalDiff (n := n)) =
      K4DiagonalOrbitConst n := by
  ext f
  constructor
  · intro hf
    rw [LinearMap.mem_ker] at hf
    change ∀ q t,
      k4DiagonalOrbitEquiv f q t =
        k4DiagonalOrbitEquiv f q 0
    intro q
    apply (cycDiff_eq_zero_iff_constant_apply F
      (k4DiagonalOrbitEquiv f q)).mp
    funext t
    rw [← k4DiagonalOrbitEquiv_diff f q t, hf]
    rfl
  · intro hf
    rw [LinearMap.mem_ker]
    change ∀ q t,
      k4DiagonalOrbitEquiv f q t =
        k4DiagonalOrbitEquiv f q 0 at hf
    apply k4DiagonalOrbitEquiv.injective
    funext q t
    rw [LinearEquiv.map_zero, k4DiagonalOrbitEquiv_diff]
    have hz :
        cycDiff (n := n) F
          (k4DiagonalOrbitEquiv f q) = 0 :=
      (cycDiff_eq_zero_iff_constant_apply F
        (k4DiagonalOrbitEquiv f q)).mpr (hf q)
    exact congrFun hz t

theorem range_k4DiagonalDiff_eq_orbitZero
    {n : Nat} [NeZero n] :
    LinearMap.range (k4DiagonalDiff (n := n)) =
      K4DiagonalOrbitZero n := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    change ∀ q,
      ∑ t : I n,
        k4DiagonalOrbitEquiv (k4DiagonalDiff f) q t = 0
    intro q
    have hz :=
      cycDiff_mem_ZeroSumProfile (k4DiagonalOrbitEquiv f q)
    have hz' :
        (∑ t : I n,
          cycDiff (n := n) F
            (k4DiagonalOrbitEquiv f q) t) = 0 := hz
    simpa only [k4DiagonalOrbitEquiv_diff] using hz'
  · intro hg
    change ∀ q,
      ∑ t : I n, k4DiagonalOrbitEquiv g q t = 0 at hg
    let u : (q : I n × I n) → ZeroSumProfile n :=
      fun q => ⟨k4DiagonalOrbitEquiv g q, hg q⟩
    let f : CyclicCube n :=
      k4DiagonalOrbitEquiv.symm
        (fun q => explicitCyclicPrimitive n (u q))
    refine ⟨f, ?_⟩
    apply k4DiagonalOrbitEquiv.injective
    funext q t
    rw [k4DiagonalOrbitEquiv_diff]
    change
      cycDiff (n := n) F
          (k4DiagonalOrbitEquiv
            (k4DiagonalOrbitEquiv.symm
              (fun q => explicitCyclicPrimitive n (u q))) q) t =
        k4DiagonalOrbitEquiv g q t
    rw [k4DiagonalOrbitEquiv.apply_symm_apply]
    exact congrFun (cycDiff_explicitCyclicPrimitive (u q)) t

private noncomputable def k4DiagonalOrbitZeroEquiv
    {n : Nat} [NeZero n] :
    K4DiagonalOrbitZero n ≃ₗ[F]
      ((I n × I n) → ZeroSumProfile n) where
  toFun f q := ⟨k4DiagonalOrbitEquiv f.1 q, f.2 q⟩
  invFun u := ⟨k4DiagonalOrbitEquiv.symm
      (fun q => (u q).1), by
    intro q
    change
      ∑ t : I n,
        k4DiagonalOrbitEquiv
          (k4DiagonalOrbitEquiv.symm
            (fun q => (u q).1)) q t = 0
    rw [k4DiagonalOrbitEquiv.apply_symm_apply]
    exact u q |>.2⟩
  left_inv f := by
    apply Subtype.ext
    exact k4DiagonalOrbitEquiv.symm_apply_apply f.1
  right_inv u := by
    funext q
    apply Subtype.ext
    exact congrFun
      (k4DiagonalOrbitEquiv.apply_symm_apply
        (fun q => (u q).1)) q
  map_add' f g := by
    rfl
  map_smul' r f := by
    rfl

theorem finrank_range_k4DiagonalDiff
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (k4DiagonalDiff (n := n))) =
      n ^ 2 * (n - 1) := by
  rw [range_k4DiagonalDiff_eq_orbitZero]
  calc
    Module.finrank F (K4DiagonalOrbitZero n) =
        Module.finrank F
          ((I n × I n) → ZeroSumProfile n) :=
      LinearEquiv.finrank_eq k4DiagonalOrbitZeroEquiv
    _ = Fintype.card (I n × I n) *
          Module.finrank F (ZeroSumProfile n) := by
      rw [Module.finrank_pi_fintype]
      simp
    _ = n ^ 2 * (n - 1) := by
      rw [finrank_ZeroSumProfile, Fintype.card_prod]
      simp [ZMod.card, pow_two]

end

end Core4loop.CompleteGraph.Odd
