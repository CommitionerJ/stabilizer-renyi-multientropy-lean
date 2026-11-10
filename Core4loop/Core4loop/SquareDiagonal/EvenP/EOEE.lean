import Core4loop.SquareDiagonal.EvenP.CubeOrbit

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

abbrev DiamondEOEELeftAmbient (n : Nat) :=
  ((CyclicCube n × CyclicCube n) × (CyclicCube n × CyclicCube n)) ×
    (CyclicCube n × CyclicCube n)

abbrev DiamondEOEERightAmbient (n : Nat) :=
  (CyclicCube n × CyclicCube n) × (CyclicCube n × CyclicCube n)

noncomputable def diamondEOEELeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEOEELeftAmbient n →ₗ[F] (CyclicCube n × CyclicCube n) where
  toFun l :=
    (cubeDiffP l.1.1.1,
      cubeDiffP l.1.1.2 + cubeDiffR l.2.1)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable abbrev DiamondEOEELeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEOEELeftConstraintMap (n := n))

noncomputable def diamondEOEECoeffMap
    {n : Nat} [NeZero n] :
    DiamondEOEELeftAmbient n →ₗ[F] DiamondEOEERightAmbient n where
  toFun l :=
    ((cubeDiffI (l.1.1.1 + l.1.1.2 + l.1.2.1 + l.1.2.2) +
        cubeDiffK (l.2.1 + l.2.2),
      cubeDiffI (l.1.1.1 + l.1.2.1)),
     (cubeDiffI (l.1.1.1 + l.1.1.2) + cubeDiffK l.2.1,
      cubeDiffI l.1.1.1))
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp <;> ring

noncomputable def DiamondEOEERightSource
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEOEERightAmbient n) where
  carrier := { A |
    cubeDiffJInv A.1.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
    cubeDiffJInv A.1.2 ∈
      LinearMap.range (LinearMap.coprod
        (cubeDiffP (n := n)) (cubeDiffR (n := n))) }
  zero_mem' := by
    constructor <;> simp
  add_mem' := by
    intro A A' hA hA'
    constructor
    · simpa using
        (LinearMap.range (cubeDiffP (n := n))).add_mem hA.1 hA'.1
    · simpa using
        (LinearMap.range
          (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))).add_mem
            hA.2 hA'.2
  smul_mem' := by
    intro r A hA
    constructor
    · simpa using
        (LinearMap.range (cubeDiffP (n := n))).smul_mem r hA.1
    · simpa using
        (LinearMap.range
          (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))).smul_mem
            r hA.2

private theorem cubeDot_smul_left
    {n : Nat} [NeZero n] (r : F) (x y : CyclicCube n) :
    cubeDot (r • x) y = r • cubeDot x y := by
  simp only [cubeDot, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ q : I n × I n × I n,
        r * x q.1 q.2.1 q.2.2 * y q.1 q.2.1 q.2.2) =
      ∑ q : I n × I n × I n,
        r * (x q.1 q.2.1 q.2.2 * y q.1 q.2.1 q.2.2) := by
          apply Finset.sum_congr rfl
          intro q _
          ring
    _ = r * ∑ q : I n × I n × I n,
        x q.1 q.2.1 q.2.2 * y q.1 q.2.1 q.2.2 :=
      (Finset.mul_sum _ _ _).symm

private theorem cubeDot_smul_right
    {n : Nat} [NeZero n] (r : F) (x y : CyclicCube n) :
    cubeDot x (r • y) = r • cubeDot x y := by
  simp only [cubeDot, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ q : I n × I n × I n,
        x q.1 q.2.1 q.2.2 * (r * y q.1 q.2.1 q.2.2)) =
      ∑ q : I n × I n × I n,
        r * (x q.1 q.2.1 q.2.2 * y q.1 q.2.1 q.2.2) := by
          apply Finset.sum_congr rfl
          intro q _
          ring
    _ = r * ∑ q : I n × I n × I n,
        x q.1 q.2.1 q.2.2 * y q.1 q.2.1 q.2.2 :=
      (Finset.mul_sum _ _ _).symm

private noncomputable def cubeDotDual
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) where
  toFun c :=
    { toFun := fun f => cubeDot c f
      map_add' := by
        intro f g
        simp only [cubeDot, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := by
        intro r f
        exact cubeDot_smul_right r c f }
  map_add' c d := by
    apply LinearMap.ext
    intro f
    change cubeDot (c + d) f = cubeDot c f + cubeDot d f
    simp only [cubeDot, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]
  map_smul' r c := by
    apply LinearMap.ext
    intro f
    change cubeDot (r • c) f = r • cubeDot c f
    exact cubeDot_smul_left r c f

private theorem cubeDotDual_injective
    {n : Nat} [NeZero n] :
    Function.Injective (cubeDotDual (n := n)) := by
  intro x y h
  funext i j k
  let q0 : I n × I n × I n := (i, j, k)
  let e : CyclicCube n := fun i' j' k' =>
    if (i', j', k') = q0 then 1 else 0
  have he := LinearMap.congr_fun h e
  change cubeDot x e = cubeDot y e at he
  classical
  have hx : cubeDot x e = x i j k := by
    rw [cubeDot]
    rw [Finset.sum_eq_single q0]
    · simp [e, q0]
    · intro q _ hq
      simp [e, hq]
    · simp
  have hy : cubeDot y e = y i j k := by
    rw [cubeDot]
    rw [Finset.sum_eq_single q0]
    · simp [e, q0]
    · intro q _ hq
      simp [e, hq]
    · simp
  simpa [hx, hy] using he

private noncomputable def cubeDotEquiv
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] Module.Dual F (CyclicCube n) :=
  LinearEquiv.ofBijective cubeDotDual
    ⟨cubeDotDual_injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        Subspace.dual_finrank_eq.symm).mp cubeDotDual_injective⟩

private noncomputable def diamondEOEERightPairing
    {n : Nat} [NeZero n] :
    DiamondEOEERightAmbient n →ₗ[F]
      Module.Dual F (DiamondEOEERightAmbient n) where
  toFun R :=
    { toFun := fun A =>
        cubeDot R.1.1 A.1.1 +
        cubeDot R.1.2 A.1.2 +
        cubeDot R.2.1 A.2.1 +
        cubeDot R.2.2 A.2.2
      map_add' := by
        intro A A'
        change
          cubeDot R.1.1 (A.1.1 + A'.1.1) +
              cubeDot R.1.2 (A.1.2 + A'.1.2) +
              cubeDot R.2.1 (A.2.1 + A'.2.1) +
              cubeDot R.2.2 (A.2.2 + A'.2.2) =
            (cubeDot R.1.1 A.1.1 + cubeDot R.1.2 A.1.2 +
              cubeDot R.2.1 A.2.1 + cubeDot R.2.2 A.2.2) +
            (cubeDot R.1.1 A'.1.1 + cubeDot R.1.2 A'.1.2 +
              cubeDot R.2.1 A'.2.1 + cubeDot R.2.2 A'.2.2)
        simp only [cubeDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro r A
        change
          cubeDot R.1.1 (r • A.1.1) + cubeDot R.1.2 (r • A.1.2) +
              cubeDot R.2.1 (r • A.2.1) + cubeDot R.2.2 (r • A.2.2) =
            r • (cubeDot R.1.1 A.1.1 + cubeDot R.1.2 A.1.2 +
              cubeDot R.2.1 A.2.1 + cubeDot R.2.2 A.2.2)
        rw [cubeDot_smul_right, cubeDot_smul_right,
          cubeDot_smul_right, cubeDot_smul_right]
        simp only [smul_eq_mul]
        ring }
  map_add' R R' := by
    apply LinearMap.ext
    intro A
    change
      cubeDot (R.1.1 + R'.1.1) A.1.1 +
          cubeDot (R.1.2 + R'.1.2) A.1.2 +
          cubeDot (R.2.1 + R'.2.1) A.2.1 +
          cubeDot (R.2.2 + R'.2.2) A.2.2 =
        (cubeDot R.1.1 A.1.1 + cubeDot R.1.2 A.1.2 +
          cubeDot R.2.1 A.2.1 + cubeDot R.2.2 A.2.2) +
        (cubeDot R'.1.1 A.1.1 + cubeDot R'.1.2 A.1.2 +
          cubeDot R'.2.1 A.2.1 + cubeDot R'.2.2 A.2.2)
    simp only [cubeDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' r R := by
    apply LinearMap.ext
    intro A
    change
      cubeDot (r • R.1.1) A.1.1 + cubeDot (r • R.1.2) A.1.2 +
          cubeDot (r • R.2.1) A.2.1 + cubeDot (r • R.2.2) A.2.2 =
        r • (cubeDot R.1.1 A.1.1 + cubeDot R.1.2 A.1.2 +
          cubeDot R.2.1 A.2.1 + cubeDot R.2.2 A.2.2)
    rw [cubeDot_smul_left, cubeDot_smul_left,
      cubeDot_smul_left, cubeDot_smul_left]
    simp only [smul_eq_mul]
    ring

private noncomputable def diamondEOEERestrictRightDual
    {n : Nat} [NeZero n] :
    Module.Dual F (DiamondEOEERightAmbient n) →ₗ[F]
      Module.Dual F (DiamondEOEERightSource n) where
  toFun phi := phi.comp (DiamondEOEERightSource n).subtype
  map_add' phi psi := by
    ext A
    rfl
  map_smul' r phi := by
    ext A
    rfl

noncomputable def diamondEOEECross
    {n : Nat} [NeZero n] :
    DiamondEOEELeftSource n →ₗ[F] Module.Dual F (DiamondEOEERightSource n) :=
  diamondEOEERestrictRightDual.comp
    (diamondEOEERightPairing.comp
      (diamondEOEECoeffMap.comp (DiamondEOEELeftSource n).subtype))

noncomputable abbrev DiamondEOEELeftKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEOEECross (n := n))

abbrev DiamondEOEEMultiplierAmbient
    (n : Nat) [NeZero n] :=
  DiamondEOEELeftSource n × (CyclicCube n × CyclicCube n)

noncomputable def diamondEOEEMultiplierConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEOEEMultiplierAmbient n →ₗ[F]
      (((CyclicCube n × CyclicCube n) × (CyclicCube n × CyclicCube n)) ×
        ((CyclicCube n × CyclicCube n) × CyclicCube n)) where
  toFun z :=
    let R := diamondEOEECoeffMap z.1.1
    let lambda0 := z.2.1
    let lambda1 := z.2.2
    (((R.2.2, R.2.1),
      (R.1.2 + cubeDiffJStar lambda1, cubeDiffPStar lambda1)),
     ((cubeDiffRStar lambda1, R.1.1 + cubeDiffJStar lambda0),
      cubeDiffPStar lambda0))
  map_add' x y := by
    ext <;> simp [diamondEOEECoeffMap] <;> abel
  map_smul' r x := by
    ext <;> simp [diamondEOEECoeffMap, mul_add]

noncomputable def DiamondEOEEMultiplierSolution
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEOEEMultiplierAmbient n) :=
  LinearMap.ker (diamondEOEEMultiplierConstraintMap (n := n))

noncomputable def diamondEOEEProjection
    {n : Nat} [NeZero n] :
    DiamondEOEEMultiplierSolution n →ₗ[F] DiamondEOEELeftSource n :=
  (LinearMap.fst F (DiamondEOEELeftSource n)
    (CyclicCube n × CyclicCube n)).comp
      (DiamondEOEEMultiplierSolution n).subtype

noncomputable def DiamondEOEEMultiplierGauge
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEOEEMultiplierSolution n) :=
  LinearMap.ker (diamondEOEEProjection (n := n))

private theorem cubeDot_add_right
    {n : Nat} [NeZero n] (x y z : CyclicCube n) :
    cubeDot x (y + z) = cubeDot x y + cubeDot x z := by
  simp only [cubeDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem cubeDot_left_ext
    {n : Nat} [NeZero n] (x y : CyclicCube n)
    (h : ∀ z : CyclicCube n, cubeDot x z = cubeDot y z) :
    x = y := by
  apply cubeDotDual_injective
  apply LinearMap.ext
  exact h

private theorem dual_exists_cubeDot
    {n : Nat} [NeZero n] (phi : Module.Dual F (CyclicCube n)) :
    ∃ lambda : CyclicCube n,
      ∀ x : CyclicCube n, phi x = cubeDot lambda x := by
  let lambda := (cubeDotEquiv (n := n)).symm phi
  refine ⟨lambda, fun x => ?_⟩
  have h := LinearMap.congr_fun
    ((cubeDotEquiv (n := n)).apply_symm_apply phi) x
  exact h.symm

private theorem dual_factor_of_vanishes_on_comap_range
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (d : V →ₗ[F] V) (p : U →ₗ[F] V)
    (phi : Module.Dual F V)
    (hphi : ∀ x : V, d x ∈ LinearMap.range p → phi x = 0) :
    ∃ psi : Module.Dual F V,
      phi = psi.comp d ∧ ∀ u : U, psi (p u) = 0 := by
  let S : Submodule F V := LinearMap.range p
  let f : V →ₗ[F] V ⧸ S := S.mkQ.comp d
  have hmem : phi ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    apply hphi x
    have hzero : S.mkQ (d x) = 0 := by
      simpa [f, LinearMap.mem_ker] using hx
    exact (Submodule.Quotient.mk_eq_zero S).mp hzero
  have hrange : phi ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact hmem
  rcases hrange with ⟨eta, heta⟩
  refine ⟨eta.comp S.mkQ, ?_, ?_⟩
  · symm
    simpa [f] using heta
  · intro u
    change eta (S.mkQ (p u)) = 0
    rw [Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).mpr
        (LinearMap.mem_range_self p u), map_zero]

private theorem A00_dual_factor
    {n : Nat} [NeZero n] (phi : Module.Dual F (CyclicCube n))
    (hphi : ∀ A : CyclicCube n,
      cubeDiffJInv A ∈ LinearMap.range (cubeDiffP (n := n)) →
      phi A = 0) :
    ∃ psi : Module.Dual F (CyclicCube n),
      phi = psi.comp cubeDiffJInv ∧
      ∀ X : CyclicCube n, psi (cubeDiffP X) = 0 :=
  dual_factor_of_vanishes_on_comap_range cubeDiffJInv cubeDiffP phi hphi

private theorem A01_dual_factor
    {n : Nat} [NeZero n] (phi : Module.Dual F (CyclicCube n))
    (hphi : ∀ A : CyclicCube n,
      cubeDiffJInv A ∈ LinearMap.range
        (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n))) →
      phi A = 0) :
    ∃ psi : Module.Dual F (CyclicCube n),
      phi = psi.comp cubeDiffJInv ∧
      ∀ q : CyclicCube n × CyclicCube n,
        psi (cubeDiffP q.1 + cubeDiffR q.2) = 0 :=
  dual_factor_of_vanishes_on_comap_range cubeDiffJInv
    (LinearMap.coprod cubeDiffP cubeDiffR) phi hphi

private theorem A00_pairing_zero
    {n : Nat} [NeZero n]
    (R lambda A X : CyclicCube n)
    (hR : R = cubeDiffJStar lambda)
    (hp : cubeDiffPStar lambda = 0)
    (hA : cubeDiffJInv A = cubeDiffP X) :
    cubeDot R A = 0 := by
  rw [hR, cubeDiffJ_pairing_adjoint, hA,
    ← cubeDiffP_pairing_adjoint, hp]
  simp [cubeDot]

private theorem A01_pairing_zero
    {n : Nat} [NeZero n]
    (R lambda A X Y : CyclicCube n)
    (hR : R = cubeDiffJStar lambda)
    (hp : cubeDiffPStar lambda = 0)
    (hr : cubeDiffRStar lambda = 0)
    (hA : cubeDiffJInv A = cubeDiffP X + cubeDiffR Y) :
    cubeDot R A = 0 := by
  rw [hR, cubeDiffJ_pairing_adjoint, hA, cubeDot_add_right,
    ← cubeDiffP_pairing_adjoint, ← cubeDiffR_pairing_adjoint, hp, hr]
  simp [cubeDot]

private theorem projection_forward_pairing_zero
    {n : Nat} [NeZero n]
    (R00 R01 R10 R11 lambda0 lambda1
      A00 A01 A10 A11 X0 X1 Y1 : CyclicCube n)
    (hR11 : R11 = 0) (hR10 : R10 = 0)
    (hR01 : R01 = cubeDiffJStar lambda1)
    (hp1 : cubeDiffPStar lambda1 = 0)
    (hr1 : cubeDiffRStar lambda1 = 0)
    (hR00 : R00 = cubeDiffJStar lambda0)
    (hp0 : cubeDiffPStar lambda0 = 0)
    (hA00 : cubeDiffJInv A00 = cubeDiffP X0)
    (hA01 : cubeDiffJInv A01 = cubeDiffP X1 + cubeDiffR Y1) :
    cubeDot R00 A00 + cubeDot R01 A01 +
      cubeDot R10 A10 + cubeDot R11 A11 = 0 := by
  rw [A00_pairing_zero R00 lambda0 A00 X0 hR00 hp0 hA00,
    A01_pairing_zero R01 lambda1 A01 X1 Y1 hR01 hp1 hr1 hA01,
    hR10, hR11]
  simp [cubeDot]

private theorem cube_add_self
    {n : Nat} [NeZero n] (x : CyclicCube n) : x + x = 0 := by
  funext i j k
  exact F_add_self _

set_option maxHeartbeats 800000 in
theorem range_EOEE_projection_eq_leftKernel
    {n : Nat} [NeZero n] :
    LinearMap.range (diamondEOEEProjection (n := n)) =
      DiamondEOEELeftKernel n := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    let R := diamondEOEECoeffMap z.1.1.1
    let lambda0 := z.1.2.1
    let lambda1 := z.1.2.2
    have hcon := LinearMap.mem_ker.mp z.2
    have hR11 : R.2.2 = 0 :=
      congrArg (fun t => t.1.1.1) hcon
    have hR10 : R.2.1 = 0 :=
      congrArg (fun t => t.1.1.2) hcon
    have hR01add : R.1.2 + cubeDiffJStar lambda1 = 0 :=
      congrArg (fun t => t.1.2.1) hcon
    have hp1 : cubeDiffPStar lambda1 = 0 :=
      congrArg (fun t => t.1.2.2) hcon
    have hr1 : cubeDiffRStar lambda1 = 0 :=
      congrArg (fun t => t.2.1.1) hcon
    have hR00add : R.1.1 + cubeDiffJStar lambda0 = 0 :=
      congrArg (fun t => t.2.1.2) hcon
    have hp0 : cubeDiffPStar lambda0 = 0 :=
      congrArg (fun t => t.2.2) hcon
    have hR01 : R.1.2 = cubeDiffJStar lambda1 := by
      rw [← cube_add_self (cubeDiffJStar lambda1)] at hR01add
      exact add_right_cancel hR01add
    have hR00 : R.1.1 = cubeDiffJStar lambda0 := by
      rw [← cube_add_self (cubeDiffJStar lambda0)] at hR00add
      exact add_right_cancel hR00add
    rcases A.2.1 with ⟨X0, hX0⟩
    rcases A.2.2 with ⟨q, hq⟩
    have hpair := projection_forward_pairing_zero
      R.1.1 R.1.2 R.2.1 R.2.2 lambda0 lambda1
      A.1.1.1 A.1.1.2 A.1.2.1 A.1.2.2 X0 q.1 q.2
      hR11 hR10 hR01 hp1 hr1 hR00 hp0 hX0.symm hq.symm
    simpa [diamondEOEECross, diamondEOEERestrictRightDual,
      diamondEOEERightPairing, R] using hpair
  · intro l hl
    let R := diamondEOEECoeffMap l.1
    have hcross (A : DiamondEOEERightSource n) :
        cubeDot R.1.1 A.1.1.1 + cubeDot R.1.2 A.1.1.2 +
          cubeDot R.2.1 A.1.2.1 + cubeDot R.2.2 A.1.2.2 = 0 := by
      have hA := LinearMap.congr_fun (LinearMap.mem_ker.mp hl) A
      simpa [diamondEOEECross, diamondEOEERestrictRightDual,
        diamondEOEERightPairing, R] using hA
    have hR10 : R.2.1 = 0 := by
      apply cubeDot_left_ext R.2.1 0
      intro A10
      let A : DiamondEOEERightSource n :=
        ⟨((0, 0), (A10, 0)), by constructor <;> simp⟩
      simpa [A, cubeDot] using hcross A
    have hR11 : R.2.2 = 0 := by
      apply cubeDot_left_ext R.2.2 0
      intro A11
      let A : DiamondEOEERightSource n :=
        ⟨((0, 0), (0, A11)), by constructor <;> simp⟩
      simpa [A, cubeDot] using hcross A
    have hvanish00 (A00 : CyclicCube n)
        (hA00 : cubeDiffJInv A00 ∈
          LinearMap.range (cubeDiffP (n := n))) :
        cubeDotDual R.1.1 A00 = 0 := by
      let A : DiamondEOEERightSource n :=
        ⟨((A00, 0), (0, 0)), by constructor; exact hA00; simp⟩
      simpa [A, hR10, hR11, cubeDotDual, cubeDot] using hcross A
    rcases A00_dual_factor (cubeDotDual R.1.1) hvanish00 with
      ⟨psi0, hfactor0, hann0⟩
    rcases dual_exists_cubeDot psi0 with ⟨lambda0, hpsi0⟩
    have hR00 : R.1.1 = cubeDiffJStar lambda0 := by
      apply cubeDot_left_ext
      intro A00
      calc
        cubeDot R.1.1 A00 = psi0 (cubeDiffJInv A00) :=
          LinearMap.congr_fun hfactor0 A00
        _ = cubeDot lambda0 (cubeDiffJInv A00) := hpsi0 _
        _ = cubeDot (cubeDiffJStar lambda0) A00 :=
          (cubeDiffJ_pairing_adjoint lambda0 A00).symm
    have hp0 : cubeDiffPStar lambda0 = 0 := by
      apply cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffPStar lambda0) X =
            cubeDot lambda0 (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda0 X
        _ = psi0 (cubeDiffP X) := (hpsi0 _).symm
        _ = 0 := hann0 X
        _ = cubeDot 0 X := by simp [cubeDot]
    have hvanish01 (A01 : CyclicCube n)
        (hA01 : cubeDiffJInv A01 ∈ LinearMap.range
          (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))) :
        cubeDotDual R.1.2 A01 = 0 := by
      let A : DiamondEOEERightSource n :=
        ⟨((0, A01), (0, 0)), by constructor; simp; exact hA01⟩
      simpa [A, hR10, hR11, cubeDotDual, cubeDot] using hcross A
    rcases A01_dual_factor (cubeDotDual R.1.2) hvanish01 with
      ⟨psi1, hfactor1, hann1⟩
    rcases dual_exists_cubeDot psi1 with ⟨lambda1, hpsi1⟩
    have hR01 : R.1.2 = cubeDiffJStar lambda1 := by
      apply cubeDot_left_ext
      intro A01
      calc
        cubeDot R.1.2 A01 = psi1 (cubeDiffJInv A01) :=
          LinearMap.congr_fun hfactor1 A01
        _ = cubeDot lambda1 (cubeDiffJInv A01) := hpsi1 _
        _ = cubeDot (cubeDiffJStar lambda1) A01 :=
          (cubeDiffJ_pairing_adjoint lambda1 A01).symm
    have hp1 : cubeDiffPStar lambda1 = 0 := by
      apply cubeDot_left_ext
      intro X
      have hpsi : psi1 (cubeDiffP X) = 0 := by
        simpa using hann1 (X, 0)
      calc
        cubeDot (cubeDiffPStar lambda1) X =
            cubeDot lambda1 (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda1 X
        _ = psi1 (cubeDiffP X) := (hpsi1 _).symm
        _ = 0 := hpsi
        _ = cubeDot 0 X := by simp [cubeDot]
    have hr1 : cubeDiffRStar lambda1 = 0 := by
      apply cubeDot_left_ext
      intro Y
      have hpsi : psi1 (cubeDiffR Y) = 0 := by
        simpa using hann1 (0, Y)
      calc
        cubeDot (cubeDiffRStar lambda1) Y =
            cubeDot lambda1 (cubeDiffR Y) :=
          cubeDiffR_pairing_adjoint lambda1 Y
        _ = psi1 (cubeDiffR Y) := (hpsi1 _).symm
        _ = 0 := hpsi
        _ = cubeDot 0 Y := by simp [cubeDot]
    let z0 : DiamondEOEEMultiplierAmbient n := (l, (lambda0, lambda1))
    have hz0 : diamondEOEEMultiplierConstraintMap z0 = 0 := by
      change (((R.2.2, R.2.1),
        (R.1.2 + cubeDiffJStar lambda1, cubeDiffPStar lambda1)),
        ((cubeDiffRStar lambda1, R.1.1 + cubeDiffJStar lambda0),
          cubeDiffPStar lambda0)) = 0
      rw [hR11, hR10, hR01, hp1, hr1, hR00, hp0,
        cube_add_self, cube_add_self]
      rfl
    exact ⟨⟨z0, hz0⟩, rfl⟩

private noncomputable def eoeePRShear
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i s k => f i (s - i - k) k
  invFun g := fun i j k => g i (i + j + k) k
  left_inv f := by
    funext i j k
    simp only
    rw [show i + j + k - i - k = j by abel]
  right_inv g := by
    funext i s k
    simp only
    rw [show i + (s - i - k) + k = s by abel]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem eoeePRShear_p
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    eoeePRShear (cubeDiffP f) = cubeDiffI (eoeePRShear f) := by
  funext i s k
  change
    f i (s - i - k) k +
        f (i + 1) ((s - i - k) + (-1)) (k + 0) =
      f i (s - i - k) k +
        f (i + 1) (s - (i + 1) - k) k
  congr 2
  · abel
  · simp

private theorem eoee_cubeDiffK_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  change f i j k + f (i + 0) (j + 0) (k + 1) = _
  simp

private theorem eoeePRShear_r
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    eoeePRShear (cubeDiffR f) = cubeDiffK (eoeePRShear f) := by
  funext i s k
  have hk :
      cubeDiffK (eoeePRShear f) i s k =
        f i (s - i - k) k +
          f i (s - i - (k + 1)) (k + 1) := by
    rw [eoee_cubeDiffK_apply]
    rfl
  rw [hk]
  change
    f i (s - i - k) k +
        f (i + 0) ((s - i - k) + (-1)) (k + 1) =
      f i (s - i - k) k +
        f i (s - i - (k + 1)) (k + 1)
  congr 2
  · simp
  · abel

private noncomputable def eoeePKerEquivIKer
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffP (n := n)) ≃ₗ[F]
      LinearMap.ker (cubeDiffI (n := n)) where
  toFun z := ⟨eoeePRShear z.1, by
    apply LinearMap.mem_ker.mpr
    rw [← eoeePRShear_p]
    rw [LinearMap.mem_ker.mp z.2, map_zero]⟩
  invFun z := ⟨(eoeePRShear (n := n)).symm z.1, by
    apply LinearMap.mem_ker.mpr
    apply (eoeePRShear (n := n)).injective
    rw [map_zero, eoeePRShear_p, LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_ker.mp z.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (eoeePRShear (n := n)).symm_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact (eoeePRShear (n := n)).apply_symm_apply z.1
  map_add' z w := by
    apply Subtype.ext
    exact map_add eoeePRShear z.1 w.1
  map_smul' r z := by
    apply Subtype.ext
    exact map_smul eoeePRShear r z.1

private noncomputable def eoeePRSourceMap
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F] CyclicCube n :=
  LinearMap.coprod cubeDiffP cubeDiffR

private noncomputable def EOEEPRSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (eoeePRSourceMap (n := n))

private noncomputable def eoeePRSourceEquivStar
    {n : Nat} [NeZero n] :
    EOEEPRSource n ≃ₗ[F] LinearMap.ker (cubeStarIK (n := n)) where
  toFun z := ⟨(eoeePRShear z.1.1, eoeePRShear z.1.2), by
    apply LinearMap.mem_ker.mpr
    change cubeDiffI (eoeePRShear z.1.1) +
      cubeDiffK (eoeePRShear z.1.2) = 0
    rw [← eoeePRShear_p, ← eoeePRShear_r, ← map_add]
    have hz := LinearMap.mem_ker.mp z.2
    change cubeDiffP z.1.1 + cubeDiffR z.1.2 = 0 at hz
    rw [hz, map_zero]⟩
  invFun z := ⟨((eoeePRShear (n := n)).symm z.1.1,
      (eoeePRShear (n := n)).symm z.1.2), by
    apply LinearMap.mem_ker.mpr
    apply (eoeePRShear (n := n)).injective
    change
      eoeePRShear
        (cubeDiffP ((eoeePRShear (n := n)).symm z.1.1) +
          cubeDiffR ((eoeePRShear (n := n)).symm z.1.2)) = 0
    rw [map_add, eoeePRShear_p, eoeePRShear_r]
    simp only [LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_ker.mp z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;>
      exact (eoeePRShear (n := n)).symm_apply_apply _
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;>
      exact (eoeePRShear (n := n)).apply_symm_apply _
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext <;> exact map_add eoeePRShear _ _
  map_smul' r z := by
    apply Subtype.ext
    apply Prod.ext <;> exact map_smul eoeePRShear r _

private noncomputable def eoeeLeftSourceEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEELeftSource n ≃ₗ[F]
      (LinearMap.ker (cubeDiffP (n := n)) × EOEEPRSource n) ×
        ((CyclicCube n × CyclicCube n) × CyclicCube n) where
  toFun l := by
    have h := LinearMap.mem_ker.mp l.2
    exact ((⟨l.1.1.1.1, congrArg Prod.fst h⟩,
      ⟨(l.1.1.1.2, l.1.2.1), congrArg Prod.snd h⟩),
      ((l.1.1.2.1, l.1.1.2.2), l.1.2.2))
  invFun q := ⟨(((q.1.1.1, q.1.2.1.1), q.2.1),
      (q.1.2.1.2, q.2.2)), by
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · exact LinearMap.mem_ker.mp q.1.1.2
    · exact LinearMap.mem_ker.mp q.1.2.2⟩
  left_inv l := by rfl
  right_inv q := by rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private theorem finrank_EOEE_leftSource
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEOEELeftSource n) =
      4 * n ^ 3 + n ^ 2 + n := by
  rw [LinearEquiv.finrank_eq (eoeeLeftSourceEquiv (n := n))]
  have hP :
      Module.finrank F (LinearMap.ker (cubeDiffP (n := n))) =
        Module.finrank F (CubeOrbitConst n) :=
    (LinearEquiv.finrank_eq (eoeePKerEquivIKer (n := n))).trans
      (LinearEquiv.finrank_eq
        (cubeDiff_ker_equiv_orbitConst (n := n)))
  have hPR :
      Module.finrank F (EOEEPRSource n) = n ^ 3 + n :=
    (LinearEquiv.finrank_eq
      (eoeePRSourceEquivStar (n := n))).trans
        finrank_ker_cubeStarIK
  have hC :
      Module.finrank F (CubeOrbitConst n) = n ^ 2 := by
    simp [CubeOrbitConst, MatrixProfile, Module.finrank_pi_fintype,
      I, ZMod.card, pow_two]
  have hCube :
      Module.finrank F (CyclicCube n) = n ^ 3 := by
    simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
      pow_succ, mul_assoc]
  simp only [Module.finrank_prod, hP, hPR, hC, hCube]
  ring

end

end Core4loop.SquareDiagonal.EvenP

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

private theorem module_add_self
    {X : Type*} [AddCommGroup X] [Module F X] (x : X) :
    x + x = 0 := by
  have htwo : (1 : F) + 1 = 0 := by decide
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + 1) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

/- Exact four factor spaces. -/

private noncomputable def factorIMap
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n × CyclicCube n :=
  LinearMap.prod cubeDiffP cubeDiffI

private noncomputable def FactorI
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (factorIMap (n := n))

private abbrev FactorII
    (n : Nat) [NeZero n] :=
  CubePairPRDISolution n

private noncomputable def factorIIIMap
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F]
      ((CyclicCube n × CyclicCube n) × CyclicCube n) :=
  LinearMap.prod
    (LinearMap.prod
      (cubeDiffPStar.comp
        (LinearMap.snd F (CyclicCube n) (CyclicCube n)))
      (cubeDiffRStar.comp
        (LinearMap.snd F (CyclicCube n) (CyclicCube n))))
    (LinearMap.coprod cubeDiffI cubeDiffJStar)

private noncomputable def FactorIII
    (n : Nat) [NeZero n] :
    Submodule F (CyclicCube n × CyclicCube n) :=
  LinearMap.ker (factorIIIMap (n := n))

private noncomputable def factorIVMap
    {n : Nat} [NeZero n] :
    ((CyclicCube n × CyclicCube n) × CyclicCube n) →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  LinearMap.prod cubeStarMultiplierMap
    (cubeDiffPStar.comp
      (LinearMap.snd F (CyclicCube n × CyclicCube n) (CyclicCube n)))

private noncomputable def FactorIV
    (n : Nat) [NeZero n] :
    Submodule F ((CyclicCube n × CyclicCube n) × CyclicCube n) :=
  LinearMap.ker (factorIVMap (n := n))

private abbrev FourFactors
    (n : Nat) [NeZero n] :=
  ((FactorI n × FactorII n) × FactorIII n) × FactorIV n

/- The exact multiplier solution splits into I/II/III/IV.
The fourth coordinate uses U = B10+B11 and reconstructs B11 = U+B10. -/

private noncomputable def multiplierToFactors
    {n : Nat} [NeZero n] :
    DiamondEOEEMultiplierSolution n →ₗ[F] FourFactors n where
  toFun z := by
    let l := z.1.1.1
    let R := diamondEOEECoeffMap l
    let B00 := l.1.1.1
    let B01 := l.1.1.2
    let B10 := l.1.2.1
    let B11 := l.1.2.2
    let W0 := l.2.1
    let W1 := l.2.2
    let lambda0 := z.1.2.1
    let lambda1 := z.1.2.2
    have hm := LinearMap.mem_ker.mp z.2
    have hleft := LinearMap.mem_ker.mp z.1.1.2
    have hLP : cubeDiffP B00 = 0 := by
      have h := congrArg Prod.fst hleft
      change cubeDiffP B00 = 0 at h
      exact h
    have hLPR : cubeDiffP B01 + cubeDiffR W0 = 0 := by
      have h := congrArg Prod.snd hleft
      change cubeDiffP B01 + cubeDiffR W0 = 0 at h
      exact h
    have hR11 : R.2.2 = 0 := by
      have h := congrArg (fun x => x.1.1.1) hm
      change R.2.2 = 0 at h
      exact h
    have hR10 : R.2.1 = 0 := by
      have h := congrArg (fun x => x.1.1.2) hm
      change R.2.1 = 0 at h
      exact h
    have hR01 : R.1.2 + cubeDiffJStar lambda1 = 0 := by
      have h := congrArg (fun x => x.1.2.1) hm
      change R.1.2 + cubeDiffJStar lambda1 = 0 at h
      exact h
    have hp1 : cubeDiffPStar lambda1 = 0 := by
      have h := congrArg (fun x => x.1.2.2) hm
      change cubeDiffPStar lambda1 = 0 at h
      exact h
    have hr1 : cubeDiffRStar lambda1 = 0 := by
      have h := congrArg (fun x => x.2.1.1) hm
      change cubeDiffRStar lambda1 = 0 at h
      exact h
    have hR00 : R.1.1 + cubeDiffJStar lambda0 = 0 := by
      have h := congrArg (fun x => x.2.1.2) hm
      change R.1.1 + cubeDiffJStar lambda0 = 0 at h
      exact h
    have hp0 : cubeDiffPStar lambda0 = 0 := by
      have h := congrArg (fun x => x.2.2) hm
      change cubeDiffPStar lambda0 = 0 at h
      exact h
    have hI : cubeDiffI B00 = 0 := by
      simpa [R, diamondEOEECoeffMap, l, B00] using hR11
    have hII : cubeDiffI B01 + cubeDiffK W0 = 0 := by
      change
        cubeDiffI (B00 + B01) + cubeDiffK W0 = 0 at hR10
      rw [map_add, hI, zero_add] at hR10
      exact hR10
    have hIII :
        cubeDiffI B10 + cubeDiffJStar lambda1 = 0 := by
      change
        cubeDiffI (B00 + B10) +
          cubeDiffJStar lambda1 = 0 at hR01
      rw [map_add, hI, zero_add] at hR01
      exact hR01
    refine (((⟨B00, ?_⟩, ⟨(B01, W0), ?_⟩),
      ⟨(B10, lambda1), ?_⟩),
      ⟨((B10 + B11, W1), lambda0), ?_⟩)
    · apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact hLP
      · exact hI
    · apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact hLPR
      · exact hII
    · apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · apply Prod.ext
        · exact hp1
        · exact hr1
      · exact hIII
    · apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · change cubeStarIK (B10 + B11, W1) +
          cubeDiffJStar lambda0 = 0
        change
          cubeDiffI (B10 + B11) + cubeDiffK W1 +
            cubeDiffJStar lambda0 = 0
        have hcoeff :
            R.1.1 =
              cubeDiffI B00 + cubeDiffI B01 +
              (cubeDiffI (B10 + B11) + cubeDiffK W1) +
              cubeDiffK W0 := by
          simp [R, diamondEOEECoeffMap]
          abel
        have hsum :
            (cubeDiffI B01 + cubeDiffK W0) +
                (cubeDiffI (B10 + B11) + cubeDiffK W1 +
                  cubeDiffJStar lambda0) = 0 := by
          calc
            _ = R.1.1 + cubeDiffJStar lambda0 := by
              rw [hcoeff, hI]
              abel
            _ = 0 := hR00
        rw [hII, zero_add] at hsum
        exact hsum
      · exact hp0
  map_add' z w := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> apply Subtype.ext
        · rfl
        · rfl
      · apply Subtype.ext
        rfl
    · apply Subtype.ext
      ext <;> simp
      all_goals abel
  map_smul' r z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> apply Subtype.ext
        · rfl
        · rfl
      · apply Subtype.ext
        rfl
    · apply Subtype.ext
      ext <;> simp [smul_eq_mul]

private noncomputable def factorsToMultiplier
    {n : Nat} [NeZero n] :
    FourFactors n →ₗ[F] DiamondEOEEMultiplierSolution n where
  toFun q := by
    let B00 := q.1.1.1.1
    let B01 := q.1.1.2.1.1
    let W0 := q.1.1.2.1.2
    let B10 := q.1.2.1.1
    let lambda1 := q.1.2.1.2
    let U := q.2.1.1.1
    let W1 := q.2.1.1.2
    let lambda0 := q.2.1.2
    let B11 := U + B10
    let lraw : DiamondEOEELeftAmbient n :=
      (((B00, B01), (B10, B11)), (W0, W1))
    have hI := LinearMap.mem_ker.mp q.1.1.1.2
    have hII := LinearMap.mem_ker.mp q.1.1.2.2
    have hIII := LinearMap.mem_ker.mp q.1.2.2
    have hIV := LinearMap.mem_ker.mp q.2.2
    have hIP : cubeDiffP B00 = 0 := by
      have h := congrArg Prod.fst hI
      change cubeDiffP B00 = 0 at h
      exact h
    have hI0 : cubeDiffI B00 = 0 := by
      have h := congrArg Prod.snd hI
      change cubeDiffI B00 = 0 at h
      exact h
    have hIIPR : cubeDiffP B01 + cubeDiffR W0 = 0 := by
      have h := congrArg Prod.fst hII
      change cubeDiffP B01 + cubeDiffR W0 = 0 at h
      exact h
    have hII0 : cubeDiffI B01 + cubeDiffK W0 = 0 := by
      have h := congrArg Prod.snd hII
      change cubeDiffI B01 + cubeDiffK W0 = 0 at h
      exact h
    have hp1 : cubeDiffPStar lambda1 = 0 := by
      have h := congrArg (fun x => x.1.1) hIII
      change cubeDiffPStar lambda1 = 0 at h
      exact h
    have hr1 : cubeDiffRStar lambda1 = 0 := by
      have h := congrArg (fun x => x.1.2) hIII
      change cubeDiffRStar lambda1 = 0 at h
      exact h
    have hIII0 :
        cubeDiffI B10 + cubeDiffJStar lambda1 = 0 := by
      have h := congrArg Prod.snd hIII
      change cubeDiffI B10 + cubeDiffJStar lambda1 = 0 at h
      exact h
    have hstar :
        cubeDiffI U + cubeDiffK W1 +
          cubeDiffJStar lambda0 = 0 := by
      have h := congrArg Prod.fst hIV
      change
        cubeDiffI U + cubeDiffK W1 +
          cubeDiffJStar lambda0 = 0 at h
      exact h
    have hp0 : cubeDiffPStar lambda0 = 0 := by
      have h := congrArg Prod.snd hIV
      change cubeDiffPStar lambda0 = 0 at h
      exact h
    have hl : lraw ∈ DiamondEOEELeftSource n := by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact hIP
      · exact hIIPR
    let l : DiamondEOEELeftSource n := ⟨lraw, hl⟩
    refine ⟨(l, (lambda0, lambda1)), ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact hI0
        · change
            cubeDiffI (B00 + B01) + cubeDiffK W0 = 0
          rw [map_add, hI0, zero_add]
          exact hII0
      · apply Prod.ext
        · change
            cubeDiffI (B00 + B10) +
              cubeDiffJStar lambda1 = 0
          rw [map_add, hI0, zero_add]
          exact hIII0
        · exact hp1
    · apply Prod.ext
      · apply Prod.ext
        · exact hr1
        · change
            cubeDiffI (B00 + B01 + B10 + B11) +
                cubeDiffK (W0 + W1) +
              cubeDiffJStar lambda0 = 0
          calc
            _ = cubeDiffI B00 +
                (cubeDiffI B01 + cubeDiffK W0) +
                (cubeDiffI U + cubeDiffK W1 +
                  cubeDiffJStar lambda0) := by
                    simp only [map_add, B11]
                    abel_nf
                    simp [two_smul, module_add_self]
            _ = 0 := by
              rw [hI0, hII0, hstar]
              simp
      · change cubeDiffPStar lambda0 = 0
        exact hp0
  map_add' q r := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp
      all_goals abel
    · rfl
  map_smul' r q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp [smul_eq_mul]
    · rfl

private noncomputable def multiplierFourFactorsEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEEMultiplierSolution n ≃ₗ[F] FourFactors n where
  toFun := multiplierToFactors (n := n)
  invFun := factorsToMultiplier (n := n)
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp [multiplierToFactors, factorsToMultiplier]
      all_goals
        abel_nf
        simp [two_smul, module_add_self]
    · rfl
  right_inv q := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext <;> apply Subtype.ext <;> rfl
      · apply Subtype.ext
        rfl
    · apply Subtype.ext
      ext <;> simp [multiplierToFactors, factorsToMultiplier]
      all_goals
        abel_nf
        simp [two_smul, module_add_self]
  map_add' := map_add (multiplierToFactors (n := n))
  map_smul' := map_smul (multiplierToFactors (n := n))

/- Factor IV restriction of the public choice-free star equivalence. -/

private noncomputable def planeSum
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] Profile n where
  toFun f := fun j => ∑ i : I n, ∑ k : I n, f i j k
  map_add' f g := by
    funext j
    simp only [Pi.add_apply]
    simp_rw [Finset.sum_add_distrib]
  map_smul' r f := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← Finset.mul_sum]

private noncomputable def pointDelta
    (n : Nat) [NeZero n] : F →ₗ[F] CyclicCube n where
  toFun a := fun i _ k => if i = 0 ∧ k = 0 then a else 0
  map_add' a b := by
    funext i j k
    by_cases hi : i = 0 <;> by_cases hk : k = 0 <;> simp [hi, hk]
  map_smul' r a := by
    funext i j k
    by_cases hi : i = 0 <;> by_cases hk : k = 0 <;> simp [hi, hk]

private theorem planeSum_pointDelta
    {n : Nat} [NeZero n] (a : F) :
    planeSum (pointDelta n a) = constantFunctionLinear n F a := by
  funext j
  classical
  change
    (∑ i : I n, ∑ k : I n,
      if i = 0 ∧ k = 0 then a else 0) = a
  rw [Finset.sum_eq_single (0 : I n)]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

private theorem pStar_invariant
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffPStar (n := n)))
    (i j k : I n) :
    z.1 i j k = z.1 (i + j) 0 k := by
  let f : Profile n := fun t => z.1 (i + j - t) t k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp z.2) (i + j - t)) t) k
    simp only [Pi.zero_apply] at hz
    change
      z.1 (i + j - t) t k +
        z.1 ((i + j - t) + (-1)) (t + 1) (k + 0) = 0 at hz
    change
      z.1 (i + j - t) t k +
        z.1 (i + j - (t + 1)) (t + 1) k = 0
    rw [show i + j - (t + 1) = (i + j - t) + (-1) by abel]
    simpa only [add_zero] using hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
  simpa [f, show i + j - j = i by abel] using hc

private noncomputable def cubePRStarMap
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n × CyclicCube n :=
  LinearMap.prod cubeDiffPStar cubeDiffRStar

private noncomputable def CubePRStarInvariant
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (cubePRStarMap (n := n))

private theorem factorIII_lambda_mem
    {n : Nat} [NeZero n] (z : FactorIII n) :
    z.1.2 ∈ CubePRStarInvariant n := by
  apply LinearMap.mem_ker.mpr
  have hz := LinearMap.mem_ker.mp z.2
  exact congrArg Prod.fst hz

private theorem cubeDiffJStar_apply_local
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffJStar f i j k = f i j k + f i (j + 1) k := by
  change f i j k + f (i + 0) (j + 1) (k + 0) = _
  simp

private theorem jStar_mem_orbitZero
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffPStar (n := n))) :
    cubeDiffJStar z.1 ∈ CubeOrbitZero n := by
  apply LinearMap.mem_ker.mpr
  change (∑ i : I n, cubeDiffJStar z.1 i) = 0
  funext j k
  simp only [Finset.sum_apply, Pi.zero_apply]
  simp_rw [cubeDiffJStar_apply_local]
  simp_rw [Finset.sum_add_distrib]
  have hpoint (i : I n) :
      z.1 i (j + 1) k = z.1 (i + 1) j k := by
    calc
      z.1 i (j + 1) k = z.1 (i + (j + 1)) 0 k :=
        pStar_invariant z i (j + 1) k
      _ = z.1 ((i + 1) + j) 0 k := by
        rw [show i + (j + 1) = (i + 1) + j by abel]
      _ = z.1 (i + 1) j k :=
        (pStar_invariant z (i + 1) j k).symm
  simp_rw [hpoint]
  have hshift :
      (∑ i : I n, z.1 (i + 1) j k) =
        ∑ i : I n, z.1 i j k := by
    simpa using sum_shift (n := n) (1 : I n)
      (fun i => z.1 i j k)
  rw [hshift, module_add_self]

private theorem prStar_jStar_mem
    {n : Nat} [NeZero n] (z : CubePRStarInvariant n) :
    cubeDiffJStar z.1 ∈ CubeOrbitZero n :=
  jStar_mem_orbitZero
    ⟨z.1, congrArg Prod.fst (LinearMap.mem_ker.mp z.2)⟩

private theorem factorIII_jStar_mem
    {n : Nat} [NeZero n] (z : FactorIII n) :
    cubeDiffJStar z.1.2 ∈ CubeOrbitZero n :=
  prStar_jStar_mem ⟨z.1.2, factorIII_lambda_mem z⟩

private noncomputable def factorIIITo
    {n : Nat} [NeZero n] :
    FactorIII n →ₗ[F]
      (CubePRStarInvariant n ×
        LinearMap.ker (cubeDiffI (n := n))) where
  toFun z := by
    let l : CubePRStarInvariant n := ⟨z.1.2, factorIII_lambda_mem z⟩
    let lp : LinearMap.ker (cubeDiffPStar (n := n)) :=
      ⟨l.1, by
        exact congrArg Prod.fst (LinearMap.mem_ker.mp l.2)⟩
    let X : CubeOrbitZero n :=
      ⟨cubeDiffJStar l.1, jStar_mem_orbitZero lp⟩
    refine (l, ⟨z.1.1 + cubeDiffPrefix X, ?_⟩)
    apply LinearMap.mem_ker.mpr
    rw [map_add]
    have hp := congrArg Subtype.val (cubeDiff_prefix_rightInverse X)
    change cubeDiffI (cubeDiffPrefix X) = X.1 at hp
    rw [hp]
    have hz := LinearMap.mem_ker.mp z.2
    exact congrArg Prod.snd hz
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change
        (z.1.1 + w.1.1) +
            cubeDiffPrefix
              ⟨cubeDiffJStar (z.1.2 + w.1.2), _⟩ =
          (z.1.1 + cubeDiffPrefix
              ⟨cubeDiffJStar z.1.2, _⟩) +
            (w.1.1 + cubeDiffPrefix
              ⟨cubeDiffJStar w.1.2, _⟩)
      have h :
          (⟨cubeDiffJStar (z.1.2 + w.1.2),
              factorIII_jStar_mem (z + w)⟩ :
              CubeOrbitZero n) =
            ⟨cubeDiffJStar z.1.2, factorIII_jStar_mem z⟩ +
              ⟨cubeDiffJStar w.1.2, factorIII_jStar_mem w⟩ := by
        apply Subtype.ext
        exact map_add cubeDiffJStar z.1.2 w.1.2
      rw [h, map_add]
      abel
  map_smul' r z := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change
        r • z.1.1 +
            cubeDiffPrefix
              ⟨cubeDiffJStar (r • z.1.2), _⟩ =
          r •
            (z.1.1 + cubeDiffPrefix
              ⟨cubeDiffJStar z.1.2, _⟩)
      have h :
          (⟨cubeDiffJStar (r • z.1.2),
              factorIII_jStar_mem (r • z)⟩ :
              CubeOrbitZero n) =
            r • ⟨cubeDiffJStar z.1.2, factorIII_jStar_mem z⟩ := by
        apply Subtype.ext
        exact map_smul cubeDiffJStar r z.1.2
      rw [h, map_smul, smul_add]

private noncomputable def factorIIIFrom
    {n : Nat} [NeZero n] :
      (CubePRStarInvariant n ×
        LinearMap.ker (cubeDiffI (n := n))) →ₗ[F]
      FactorIII n where
  toFun p := by
    let lp : LinearMap.ker (cubeDiffPStar (n := n)) :=
      ⟨p.1.1, congrArg Prod.fst (LinearMap.mem_ker.mp p.1.2)⟩
    let X : CubeOrbitZero n :=
      ⟨cubeDiffJStar p.1.1, jStar_mem_orbitZero lp⟩
    refine ⟨(p.2.1 + cubeDiffPrefix X, p.1.1), ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · exact LinearMap.mem_ker.mp p.1.2
    · have hk := LinearMap.mem_ker.mp p.2.2
      have hp := congrArg Subtype.val (cubeDiff_prefix_rightInverse X)
      change cubeDiffI (cubeDiffPrefix X) = X.1 at hp
      change
        cubeDiffI (p.2.1 + cubeDiffPrefix X) +
          cubeDiffJStar p.1.1 = 0
      rw [map_add, hk, hp, zero_add, module_add_self]
  map_add' p q := by
    apply Subtype.ext
    apply Prod.ext
    · change
        (p.2.1 + q.2.1) +
            cubeDiffPrefix
              ⟨cubeDiffJStar (p.1.1 + q.1.1), _⟩ =
          (p.2.1 + cubeDiffPrefix
              ⟨cubeDiffJStar p.1.1, _⟩) +
            (q.2.1 + cubeDiffPrefix
              ⟨cubeDiffJStar q.1.1, _⟩)
      have h :
          (⟨cubeDiffJStar (p.1.1 + q.1.1),
              prStar_jStar_mem (p.1 + q.1)⟩ :
              CubeOrbitZero n) =
            ⟨cubeDiffJStar p.1.1, prStar_jStar_mem p.1⟩ +
              ⟨cubeDiffJStar q.1.1, prStar_jStar_mem q.1⟩ := by
        apply Subtype.ext
        exact map_add cubeDiffJStar p.1.1 q.1.1
      rw [h, map_add]
      abel
    · rfl
  map_smul' r p := by
    apply Subtype.ext
    apply Prod.ext
    · change
        r • p.2.1 +
            cubeDiffPrefix
              ⟨cubeDiffJStar (r • p.1.1), _⟩ =
          r •
            (p.2.1 + cubeDiffPrefix
              ⟨cubeDiffJStar p.1.1, _⟩)
      have h :
          (⟨cubeDiffJStar (r • p.1.1),
              prStar_jStar_mem (r • p.1)⟩ :
              CubeOrbitZero n) =
            r • ⟨cubeDiffJStar p.1.1, prStar_jStar_mem p.1⟩ := by
        apply Subtype.ext
        exact map_smul cubeDiffJStar r p.1.1
      rw [h, map_smul, smul_add]
    · rfl

private noncomputable def factorIIIEquiv
    {n : Nat} [NeZero n] :
    FactorIII n ≃ₗ[F]
      (CubePRStarInvariant n ×
        LinearMap.ker (cubeDiffI (n := n))) where
  toFun := factorIIITo
  invFun := factorIIIFrom
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change
        (z.1.1 + cubeDiffPrefix
            ⟨cubeDiffJStar z.1.2, _⟩) +
          cubeDiffPrefix
            ⟨cubeDiffJStar z.1.2, _⟩ =
          z.1.1
      rw [add_assoc, module_add_self, add_zero]
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change
        (p.2.1 + cubeDiffPrefix
            ⟨cubeDiffJStar p.1.1, _⟩) +
          cubeDiffPrefix
            ⟨cubeDiffJStar p.1.1, _⟩ =
          p.2.1
      rw [add_assoc, module_add_self, add_zero]
  map_add' := map_add factorIIITo
  map_smul' := map_smul factorIIITo

private theorem planeSum_pStar_constant
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffPStar (n := n)))
    (j : I n) :
    planeSum z.1 j = planeSum z.1 0 := by
  change
    (∑ i : I n, ∑ k : I n, z.1 i j k) =
      ∑ i : I n, ∑ k : I n, z.1 i 0 k
  have hpoint (i k : I n) :
      z.1 i j k = z.1 (i + j) 0 k :=
    pStar_invariant z i j k
  simp_rw [hpoint]
  simpa using sum_shift (n := n) j
    (fun i => ∑ k : I n, z.1 i 0 k)

private noncomputable def pStarCoord
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffPStar (n := n)) →ₗ[F]
      (CubePlaneZero n × F) where
  toFun z :=
    let a := planeSum z.1 0
    (⟨z.1 + pointDelta n a, by
      apply LinearMap.mem_ker.mpr
      funext j
      change
        (∑ i : I n, ∑ k : I n,
          (z.1 i j k + pointDelta n a i j k)) = 0
      simp_rw [Finset.sum_add_distrib]
      have hz := planeSum_pStar_constant z j
      change
        (∑ i : I n, ∑ k : I n, z.1 i j k) =
          (∑ i : I n, ∑ k : I n, z.1 i 0 k) at hz
      have hd := congrFun (planeSum_pointDelta (n := n) a) j
      change
        (∑ i : I n, ∑ k : I n, pointDelta n a i j k) = a at hd
      rw [hz, hd]
      change a + a = 0
      exact module_add_self _⟩, a)
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      change
        (z.1 + w.1) +
            pointDelta n (planeSum (z.1 + w.1) 0) =
          (z.1 + pointDelta n (planeSum z.1 0)) +
            (w.1 + pointDelta n (planeSum w.1 0))
      rw [map_add]
      simp only [Pi.add_apply, map_add]
      abel
    · exact congrFun (map_add planeSum z.1 w.1) 0
  map_smul' r z := by
    apply Prod.ext
    · apply Subtype.ext
      change
        r • z.1 + pointDelta n (planeSum (r • z.1) 0) =
          r • (z.1 + pointDelta n (planeSum z.1 0))
      rw [map_smul]
      simp only [Pi.smul_apply, smul_eq_mul, smul_add]
      rw [show pointDelta n (r * planeSum z.1 0) =
          r • pointDelta n (planeSum z.1 0) by
        simpa [smul_eq_mul] using
          map_smul (pointDelta n) r (planeSum z.1 0)]
    · exact congrFun (map_smul planeSum r z.1) 0

private theorem starEquiv_symm_lambda
    {n : Nat} [NeZero n]
    (p : CubePlaneZero n × F)
    (k : LinearMap.ker (cubeStarIK (n := n))) :
    ((cubeStarMultiplier_equiv (n := n)).symm (p, k)).1.2 =
      p.1.1 + pointDelta n p.2 := by
  rfl

private noncomputable def factorIVTo
    {n : Nat} [NeZero n] :
    FactorIV n →ₗ[F]
      (LinearMap.ker (cubeDiffPStar (n := n)) ×
        LinearMap.ker (cubeStarIK (n := n))) where
  toFun z := by
    have hz := LinearMap.mem_ker.mp z.2
    let zs : CubeStarMultiplierSolution n :=
      ⟨z.1, congrArg Prod.fst hz⟩
    exact (⟨z.1.2, congrArg Prod.snd hz⟩,
      (cubeStarMultiplier_equiv zs).2)
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · change
        (cubeStarMultiplier_equiv
          (⟨(z + w).1, congrArg Prod.fst
            (LinearMap.mem_ker.mp (z + w).2)⟩ :
              CubeStarMultiplierSolution n)).2 =
          (cubeStarMultiplier_equiv
            (⟨z.1, congrArg Prod.fst
              (LinearMap.mem_ker.mp z.2)⟩ :
                CubeStarMultiplierSolution n)).2 +
          (cubeStarMultiplier_equiv
            (⟨w.1, congrArg Prod.fst
              (LinearMap.mem_ker.mp w.2)⟩ :
                CubeStarMultiplierSolution n)).2
      exact congrArg Prod.snd
        (map_add (cubeStarMultiplier_equiv (n := n))
          ⟨z.1, congrArg Prod.fst (LinearMap.mem_ker.mp z.2)⟩
          ⟨w.1, congrArg Prod.fst (LinearMap.mem_ker.mp w.2)⟩)
  map_smul' r z := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · change
        (cubeStarMultiplier_equiv
          (⟨(r • z).1, congrArg Prod.fst
            (LinearMap.mem_ker.mp (r • z).2)⟩ :
              CubeStarMultiplierSolution n)).2 =
          r •
            (cubeStarMultiplier_equiv
              (⟨z.1, congrArg Prod.fst
                (LinearMap.mem_ker.mp z.2)⟩ :
                  CubeStarMultiplierSolution n)).2
      exact congrArg Prod.snd
        (map_smul (cubeStarMultiplier_equiv (n := n)) r
          ⟨z.1, congrArg Prod.fst (LinearMap.mem_ker.mp z.2)⟩)

private theorem pStarCoord_reconstruct
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffPStar (n := n))) :
    (pStarCoord z).1.1 + pointDelta n (pStarCoord z).2 = z.1 := by
  change
    (z.1 + pointDelta n (planeSum z.1 0)) +
      pointDelta n (planeSum z.1 0) = z.1
  rw [add_assoc, module_add_self, add_zero]

private noncomputable def factorIVFrom
    {n : Nat} [NeZero n] :
      (LinearMap.ker (cubeDiffPStar (n := n)) ×
        LinearMap.ker (cubeStarIK (n := n))) →ₗ[F] FactorIV n where
  toFun p := by
    let zs : CubeStarMultiplierSolution n :=
      (cubeStarMultiplier_equiv (n := n)).symm
        (pStarCoord p.1, p.2)
    have hlam : zs.1.2 = p.1.1 := by
      rw [starEquiv_symm_lambda]
      exact pStarCoord_reconstruct p.1
    refine ⟨zs.1, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · simpa only [factorIVMap, LinearMap.prod_apply,
        Prod.fst_zero] using LinearMap.mem_ker.mp zs.2
    · change cubeDiffPStar zs.1.2 = 0
      rw [hlam]
      exact LinearMap.mem_ker.mp p.1.2
  map_add' p q := by
    apply Subtype.ext
    change
      ((cubeStarMultiplier_equiv (n := n)).symm
        (pStarCoord (p.1 + q.1), p.2 + q.2)).1 =
      ((cubeStarMultiplier_equiv (n := n)).symm
        (pStarCoord p.1, p.2)).1 +
      ((cubeStarMultiplier_equiv (n := n)).symm
        (pStarCoord q.1, q.2)).1
    rw [map_add pStarCoord]
    exact congrArg Subtype.val
      (map_add (cubeStarMultiplier_equiv (n := n)).symm
        (pStarCoord p.1, p.2) (pStarCoord q.1, q.2))
  map_smul' r p := by
    apply Subtype.ext
    change
      ((cubeStarMultiplier_equiv (n := n)).symm
        (pStarCoord (r • p.1), r • p.2)).1 =
      r •
        ((cubeStarMultiplier_equiv (n := n)).symm
          (pStarCoord p.1, p.2)).1
    rw [map_smul pStarCoord]
    exact congrArg Subtype.val
      (map_smul (cubeStarMultiplier_equiv (n := n)).symm r
        (pStarCoord p.1, p.2))

private theorem pStarCoord_of_starSolution
    {n : Nat} [NeZero n] (z : FactorIV n) :
    pStarCoord (factorIVTo z).1 =
      (cubeStarMultiplier_equiv
        (⟨z.1, congrArg Prod.fst
          (LinearMap.mem_ker.mp z.2)⟩ :
            CubeStarMultiplierSolution n)).1 := by
  let zs : CubeStarMultiplierSolution n :=
    ⟨z.1, congrArg Prod.fst (LinearMap.mem_ker.mp z.2)⟩
  let p := (cubeStarMultiplier_equiv zs).1
  have hzback :
      (cubeStarMultiplier_equiv (n := n)).symm
          (cubeStarMultiplier_equiv zs) = zs :=
    (cubeStarMultiplier_equiv (n := n)).symm_apply_apply zs
  have hlam : z.1.2 = p.1.1 + pointDelta n p.2 := by
    have h := congrArg (fun x : CubeStarMultiplierSolution n => x.1.2)
      hzback
    change
      ((cubeStarMultiplier_equiv (n := n)).symm
        (p, (cubeStarMultiplier_equiv zs).2)).1.2 = z.1.2 at h
    rw [starEquiv_symm_lambda] at h
    exact h.symm
  apply Prod.ext
  · apply Subtype.ext
    change
      z.1.2 + pointDelta n (planeSum z.1.2 0) = p.1.1
    have hpzero := LinearMap.mem_ker.mp p.1.2
    have hplane := congrFun hpzero 0
    change planeSum p.1.1 0 = 0 at hplane
    have hdelta := congrFun (planeSum_pointDelta (n := n) p.2) 0
    change planeSum (pointDelta n p.2) 0 = p.2 at hdelta
    have ha : planeSum z.1.2 0 = p.2 := by
      calc
        planeSum z.1.2 0 =
            planeSum (p.1.1 + pointDelta n p.2) 0 := by rw [hlam]
        _ = planeSum p.1.1 0 +
              planeSum (pointDelta n p.2) 0 := by
                exact congrFun
                  (map_add planeSum p.1.1 (pointDelta n p.2)) 0
        _ = p.2 := by rw [hplane, hdelta, zero_add]
    rw [ha, hlam, add_assoc, module_add_self, add_zero]
  · change planeSum z.1.2 0 = p.2
    have hpzero := congrFun (LinearMap.mem_ker.mp p.1.2) 0
    change planeSum p.1.1 0 = 0 at hpzero
    have hdelta := congrFun (planeSum_pointDelta (n := n) p.2) 0
    change planeSum (pointDelta n p.2) 0 = p.2 at hdelta
    calc
      planeSum z.1.2 0 =
          planeSum (p.1.1 + pointDelta n p.2) 0 := by rw [hlam]
      _ = planeSum p.1.1 0 +
            planeSum (pointDelta n p.2) 0 := by
              exact congrFun
                (map_add planeSum p.1.1 (pointDelta n p.2)) 0
      _ = p.2 := by rw [hpzero, hdelta, zero_add]

private noncomputable def factorIVEquiv
    {n : Nat} [NeZero n] :
    FactorIV n ≃ₗ[F]
      (LinearMap.ker (cubeDiffPStar (n := n)) ×
        LinearMap.ker (cubeStarIK (n := n))) where
  toFun := factorIVTo
  invFun := factorIVFrom
  left_inv z := by
    apply Subtype.ext
    let zs : CubeStarMultiplierSolution n :=
      ⟨z.1, congrArg Prod.fst (LinearMap.mem_ker.mp z.2)⟩
    change
      ((cubeStarMultiplier_equiv (n := n)).symm
        (pStarCoord (factorIVTo z).1,
          (cubeStarMultiplier_equiv zs).2)).1 = z.1
    rw [pStarCoord_of_starSolution z]
    exact congrArg Subtype.val
      ((cubeStarMultiplier_equiv (n := n)).symm_apply_apply zs)
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change
        ((cubeStarMultiplier_equiv (n := n)).symm
          (pStarCoord p.1, p.2)).1.2 = p.1.1
      rw [starEquiv_symm_lambda]
      exact pStarCoord_reconstruct p.1
    · change
        (cubeStarMultiplier_equiv
          ((cubeStarMultiplier_equiv (n := n)).symm
            (pStarCoord p.1, p.2))).2 = p.2
      exact congrArg Prod.snd
        ((cubeStarMultiplier_equiv (n := n)).apply_symm_apply
          (pStarCoord p.1, p.2))
  map_add' := map_add factorIVTo
  map_smul' := map_smul factorIVTo

/- The final MatrixProfile coordinate is the p*-orbit coordinate
`h(i+j,k)`. This skeleton leaves that already compiled invariant
equivalence as a one-line product composition in the owner. -/


private theorem finrank_multiplier_addition_safe
    {n : Nat} [NeZero n]
    (hI : Module.finrank F (FactorI n) = n)
    (hII : Module.finrank F (FactorII n) + n = 2 * n ^ 2 + 1)
    (hIII : Module.finrank F (FactorIII n) = n ^ 2 + n)
    (hIV : Module.finrank F (FactorIV n) = n ^ 3 + n ^ 2 + n) :
    Module.finrank F (DiamondEOEEMultiplierSolution n) + n =
      n ^ 3 + 4 * n ^ 2 + 3 * n + 1 := by
  rw [LinearEquiv.finrank_eq (multiplierFourFactorsEquiv (n := n))]
  simp only [Module.finrank_prod]
  omega

private theorem finrank_multiplier_of_four_factors
    {n : Nat} [NeZero n]
    (hI : Module.finrank F (FactorI n) = n)
    (hII : Module.finrank F (FactorII n) + n = 2 * n ^ 2 + 1)
    (hIII : Module.finrank F (FactorIII n) = n ^ 2 + n)
    (hIV : Module.finrank F (FactorIV n) = n ^ 3 + n ^ 2 + n) :
    Module.finrank F (DiamondEOEEMultiplierSolution n) =
      n ^ 3 + 4 * n ^ 2 + 2 * n + 1 := by
  have h := finrank_multiplier_addition_safe hI hII hIII hIV
  omega

/- Source-first coordinates for the four factor dimensions. -/

private theorem eoee_eq_of_add_eq_zero
    (x y : F) (h : x + y = 0) : x = y := by
  calc
    x = x + 0 := by simp
    _ = x + (y + y) := by rw [F_add_self]
    _ = (x + y) + y := by abel
    _ = y := by rw [h]; simp

private theorem factorI_i_constant
    {n : Nat} [NeZero n] (z : FactorI n) (i j k : I n) :
    z.1 i j k = z.1 0 j k := by
  let f : Profile n := fun t => z.1 t j k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz0 := congrArg Prod.snd (LinearMap.mem_ker.mp z.2)
    change cubeDiffI z.1 = 0 at hz0
    have hz := congrFun (congrFun (congrFun hz0 t) j) k
    simpa [f] using hz
  exact (cycDiff_eq_zero_iff_constant_apply F f).mp hf i

private theorem factorI_j_constant
    {n : Nat} [NeZero n] (z : FactorI n) (j k : I n) :
    z.1 0 j k = z.1 0 0 k := by
  let f : Profile n := fun t => z.1 0 t k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hp0 := congrArg Prod.fst (LinearMap.mem_ker.mp z.2)
    have hi0 := congrArg Prod.snd (LinearMap.mem_ker.mp z.2)
    change cubeDiffP z.1 = 0 at hp0
    change cubeDiffI z.1 = 0 at hi0
    have hp := congrFun (congrFun (congrFun hp0 0) (t + 1)) k
    have hi := congrFun (congrFun (congrFun hi0 0) t) k
    simp only [Pi.zero_apply] at hp hi
    change z.1 0 t k + z.1 0 (t + 1) k = 0
    change z.1 0 (t + 1) k +
      z.1 (0 + 1) ((t + 1) + (-1)) (k + 0) = 0 at hp
    change z.1 0 t k + z.1 (0 + 1) t k = 0 at hi
    rw [show (t + 1) + (-1) = t by abel, add_zero] at hp
    rw [(eoee_eq_of_add_eq_zero _ _ hi).trans
      (eoee_eq_of_add_eq_zero _ _ hp).symm, F_add_self]
  exact (cycDiff_eq_zero_iff_constant_apply F f).mp hf j

private noncomputable def factorIBuild
    {n : Nat} [NeZero n] : Profile n →ₗ[F] FactorI n where
  toFun h := ⟨fun _ _ k => h k, by
    apply LinearMap.mem_ker.mpr
    apply Prod.ext <;> funext i j k
    · change h k + h (k + 0) = 0
      rw [add_zero, F_add_self]
    · exact F_add_self _⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private noncomputable def factorIRead
    {n : Nat} [NeZero n] : FactorI n →ₗ[F] Profile n where
  toFun z := fun k => z.1 0 0 k
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private noncomputable def factorIEquiv
    {n : Nat} [NeZero n] : FactorI n ≃ₗ[F] Profile n where
  toFun := factorIRead
  invFun := factorIBuild
  left_inv z := by
    apply Subtype.ext
    funext i j k
    exact ((factorI_i_constant z i j k).trans
      (factorI_j_constant z j k)).symm
  right_inv _ := rfl
  map_add' := map_add factorIRead
  map_smul' := map_smul factorIRead

private theorem rStar_invariant
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffRStar (n := n)))
    (i j k : I n) :
    z.1 i j k = z.1 i 0 (j + k) := by
  let f : Profile n := fun t => z.1 i t (j + k - t)
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp z.2) i) t) (j + k - t)
    simp only [Pi.zero_apply] at hz
    change z.1 i t (j + k - t) +
      z.1 (i + 0) (t + 1) ((j + k - t) + (-1)) = 0 at hz
    change z.1 i t (j + k - t) +
      z.1 i (t + 1) (j + k - (t + 1)) = 0
    rw [show j + k - (t + 1) = (j + k - t) + (-1) by abel]
    simpa only [add_zero] using hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
  simpa [f, show j + k - j = k by abel] using hc

private theorem prStar_invariant
    {n : Nat} [NeZero n] (z : CubePRStarInvariant n)
    (i j k : I n) :
    z.1 i j k = z.1 (i + j + k) 0 0 := by
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) :=
    ⟨z.1, congrArg Prod.fst (LinearMap.mem_ker.mp z.2)⟩
  let zr : LinearMap.ker (cubeDiffRStar (n := n)) :=
    ⟨z.1, congrArg Prod.snd (LinearMap.mem_ker.mp z.2)⟩
  calc
    z.1 i j k = z.1 i 0 (j + k) := rStar_invariant zr i j k
    _ = z.1 i (j + k) 0 := by
      simpa using (rStar_invariant zr i (j + k) 0).symm
    _ = z.1 (i + (j + k)) 0 0 := pStar_invariant zp i (j + k) 0
    _ = z.1 (i + j + k) 0 0 := by abel

private noncomputable def prStarBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] CubePRStarInvariant n where
  toFun h := ⟨fun i j k => h (i + j + k), by
    apply LinearMap.mem_ker.mpr
    apply Prod.ext <;> funext i j k
    · change h (i + j + k) +
        h ((i + (-1)) + (j + 1) + (k + 0)) = 0
      rw [show (i + (-1)) + (j + 1) + (k + 0) =
        i + j + k by abel, F_add_self]
    · change h (i + j + k) +
        h ((i + 0) + (j + 1) + (k + (-1))) = 0
      rw [show (i + 0) + (j + 1) + (k + (-1)) =
        i + j + k by abel, F_add_self]⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private noncomputable def prStarRead
    {n : Nat} [NeZero n] :
    CubePRStarInvariant n →ₗ[F] Profile n where
  toFun z := fun s => z.1 s 0 0
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private noncomputable def prStarEquiv
    {n : Nat} [NeZero n] :
    CubePRStarInvariant n ≃ₗ[F] Profile n where
  toFun := prStarRead
  invFun := prStarBuild
  left_inv z := by
    apply Subtype.ext
    funext i j k
    exact (prStar_invariant z i j k).symm
  right_inv h := by
    funext s
    simp [prStarRead, prStarBuild]
  map_add' := map_add prStarRead
  map_smul' := map_smul prStarRead

private noncomputable def pStarBuild
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F]
      LinearMap.ker (cubeDiffPStar (n := n)) where
  toFun h := ⟨fun i j k => h (i + j) k, by
    apply LinearMap.mem_ker.mpr
    funext i j k
    change h (i + j) k + h ((i + (-1)) + (j + 1)) (k + 0) = 0
    rw [show (i + (-1)) + (j + 1) = i + j by abel,
      add_zero, F_add_self]⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private noncomputable def pStarRead
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffPStar (n := n)) →ₗ[F] MatrixProfile n where
  toFun z := fun s k => z.1 s 0 k
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private noncomputable def pStarEquiv
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffPStar (n := n)) ≃ₗ[F] MatrixProfile n where
  toFun := pStarRead
  invFun := pStarBuild
  left_inv z := by
    apply Subtype.ext
    funext i j k
    exact (pStar_invariant z i j k).symm
  right_inv h := by
    funext s k
    simp [pStarRead, pStarBuild]
  map_add' := map_add pStarRead
  map_smul' := map_smul pStarRead

private theorem finrank_FactorI
    {n : Nat} [NeZero n] :
    Module.finrank F (FactorI n) = n := by
  rw [LinearEquiv.finrank_eq (factorIEquiv (n := n))]
  exact finrank_profile

private theorem finrank_FactorII_addition_safe
    {n : Nat} [NeZero n] :
    Module.finrank F (FactorII n) + n = 2 * n ^ 2 + 1 := by
  rw [LinearEquiv.finrank_eq (cubePairPRDI_equiv (n := n))]
  have hM : Module.finrank F (MatrixProfile n) = n ^ 2 := by
    simp [MatrixProfile, Module.finrank_pi_fintype, I, ZMod.card]
    ring
  have hn : n - 1 + 1 = n :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hsquare : n ^ 2 = (n - 1) * n + n := by
    calc
      n ^ 2 = n * n := pow_two n
      _ = (n - 1 + 1) * n := by rw [hn]
      _ = (n - 1) * n + n := by ring
  simp only [Module.finrank_prod, CubeMatrixConstSumParam,
    finrank_ZeroSumProfileM, finrank_profile, hM]
  simp only [Module.finrank_self]
  omega

private theorem finrank_FactorIII
    {n : Nat} [NeZero n] :
    Module.finrank F (FactorIII n) = n ^ 2 + n := by
  rw [LinearEquiv.finrank_eq (factorIIIEquiv (n := n))]
  simp only [Module.finrank_prod]
  rw [LinearEquiv.finrank_eq (prStarEquiv (n := n))]
  rw [LinearEquiv.finrank_eq
    (cubeDiff_ker_equiv_orbitConst (n := n))]
  simp [CubeOrbitConst, MatrixProfile,
    Module.finrank_pi_fintype, I, ZMod.card]
  ring

private theorem finrank_FactorIV
    {n : Nat} [NeZero n] :
    Module.finrank F (FactorIV n) = n ^ 3 + n ^ 2 + n := by
  rw [LinearEquiv.finrank_eq (factorIVEquiv (n := n))]
  simp only [Module.finrank_prod]
  rw [LinearEquiv.finrank_eq (pStarEquiv (n := n))]
  simp only [finrank_ker_cubeStarIK]
  simp [MatrixProfile, Module.finrank_pi_fintype, I, ZMod.card]
  ring

theorem finrank_DiamondEOEEMultiplierSolution
    {n : Nat} [NeZero n] (_hn : Even n) :
    Module.finrank F (DiamondEOEEMultiplierSolution n) =
      n ^ 3 + 4 * n ^ 2 + 2 * n + 1 :=
  finrank_multiplier_of_four_factors finrank_FactorI
    finrank_FactorII_addition_safe finrank_FactorIII finrank_FactorIV

/- The exact gauge, with the mandatory constant `lambda1` coordinate. -/

private theorem jStar_invariant
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffJStar (n := n)))
    (i j k : I n) :
    z.1 i j k = z.1 i 0 k := by
  let f : Profile n := fun t => z.1 i t k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp z.2) i) t) k
    simp only [Pi.zero_apply] at hz
    change z.1 i t k + z.1 (i + 0) (t + 1) (k + 0) = 0 at hz
    simpa [f] using hz
  exact (cycDiff_eq_zero_iff_constant_apply F f).mp hf j

private theorem actualGauge_left_zero
    {n : Nat} [NeZero n] (z : DiamondEOEEMultiplierGauge n) :
    z.1.1.1 = 0 := by
  exact LinearMap.mem_ker.mp z.2

private theorem actualGauge_conditions
    {n : Nat} [NeZero n] (z : DiamondEOEEMultiplierGauge n) :
    cubeDiffJStar z.1.1.2.1 = 0 ∧
    cubeDiffPStar z.1.1.2.1 = 0 ∧
    cubeDiffJStar z.1.1.2.2 = 0 ∧
    cubeDiffPStar z.1.1.2.2 = 0 ∧
    cubeDiffRStar z.1.1.2.2 = 0 := by
  let R := diamondEOEECoeffMap z.1.1.1.1
  have hm := LinearMap.mem_ker.mp z.1.2
  have hl := actualGauge_left_zero z
  have hR : R = 0 := by
    change diamondEOEECoeffMap z.1.1.1.1 = 0
    rw [hl]
    exact LinearMap.map_zero (diamondEOEECoeffMap (n := n))
  have hJ0 := congrArg (fun x => x.2.1.2) hm
  have hp0 := congrArg (fun x => x.2.2) hm
  have hJ1 := congrArg (fun x => x.1.2.1) hm
  have hp1 := congrArg (fun x => x.1.2.2) hm
  have hr1 := congrArg (fun x => x.2.1.1) hm
  change R.1.1 + cubeDiffJStar z.1.1.2.1 = 0 at hJ0
  change cubeDiffPStar z.1.1.2.1 = 0 at hp0
  change R.1.2 + cubeDiffJStar z.1.1.2.2 = 0 at hJ1
  change cubeDiffPStar z.1.1.2.2 = 0 at hp1
  change cubeDiffRStar z.1.1.2.2 = 0 at hr1
  rw [hR] at hJ0 hJ1
  exact ⟨by simpa using hJ0, hp0, by simpa using hJ1, hp1, hr1⟩

private theorem actualGauge_lambda0_invariant
    {n : Nat} [NeZero n] (z : DiamondEOEEMultiplierGauge n)
    (i j k : I n) :
    z.1.1.2.1 i j k = z.1.1.2.1 0 0 k := by
  have hc := actualGauge_conditions z
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) := ⟨_, hc.2.1⟩
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) := ⟨_, hc.1⟩
  calc
    _ = z.1.1.2.1 (i + j) 0 k := pStar_invariant zp i j k
    _ = z.1.1.2.1 0 (i + j) k := by
      simpa using (pStar_invariant zp 0 (i + j) k).symm
    _ = _ := jStar_invariant zj 0 (i + j) k

private theorem actualGauge_lambda1_invariant
    {n : Nat} [NeZero n] (z : DiamondEOEEMultiplierGauge n)
    (i j k : I n) :
    z.1.1.2.2 i j k = z.1.1.2.2 0 0 0 := by
  have hc := actualGauge_conditions z
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) := ⟨_, hc.2.2.2.1⟩
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) := ⟨_, hc.2.2.1⟩
  let zr : LinearMap.ker (cubeDiffRStar (n := n)) := ⟨_, hc.2.2.2.2⟩
  calc
    _ = z.1.1.2.2 (i + j) 0 k := pStar_invariant zp i j k
    _ = z.1.1.2.2 0 (i + j) k := by
      simpa using (pStar_invariant zp 0 (i + j) k).symm
    _ = z.1.1.2.2 0 0 k := jStar_invariant zj 0 (i + j) k
    _ = z.1.1.2.2 0 k 0 := by
      simpa using (rStar_invariant zr 0 k 0).symm
    _ = _ := jStar_invariant zj 0 k 0

private noncomputable def actualGaugeRead
    {n : Nat} [NeZero n] :
    DiamondEOEEMultiplierGauge n →ₗ[F] (Profile n × F) where
  toFun z := (fun k => z.1.1.2.1 0 0 k, z.1.1.2.2 0 0 0)
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

private noncomputable def actualGaugeBuild
    {n : Nat} [NeZero n] :
    (Profile n × F) →ₗ[F] DiamondEOEEMultiplierGauge n where
  toFun q := by
    let lambda0 : CyclicCube n := fun _ _ k => q.1 k
    let lambda1 : CyclicCube n := fun _ _ _ => q.2
    have hJ0 : cubeDiffJStar lambda0 = 0 := by
      funext i j k
      change q.1 k + q.1 (k + 0) = 0
      rw [add_zero, F_add_self]
    have hp0 : cubeDiffPStar lambda0 = 0 := by
      funext i j k
      change q.1 k + q.1 (k + 0) = 0
      rw [add_zero, F_add_self]
    have hJ1 : cubeDiffJStar lambda1 = 0 := by
      funext i j k
      exact F_add_self _
    have hp1 : cubeDiffPStar lambda1 = 0 := by
      funext i j k
      exact F_add_self _
    have hr1 : cubeDiffRStar lambda1 = 0 := by
      funext i j k
      exact F_add_self _
    let z : DiamondEOEEMultiplierSolution n :=
      ⟨(0, (lambda0, lambda1)), by
        apply LinearMap.mem_ker.mpr
        simp [diamondEOEEMultiplierConstraintMap,
          diamondEOEECoeffMap, hJ0, hp0, hJ1, hp1, hr1]⟩
    exact ⟨z, by
      apply LinearMap.mem_ker.mpr
      rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

set_option maxHeartbeats 2000000 in
private noncomputable def actualGaugeEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEEMultiplierGauge n ≃ₗ[F] (Profile n × F) where
  toFun := actualGaugeRead (n := n)
  invFun := actualGaugeBuild (n := n)
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (actualGauge_left_zero z).symm
    · apply Prod.ext <;> funext i j k
      · exact (actualGauge_lambda0_invariant z i j k).symm
      · exact (actualGauge_lambda1_invariant z i j k).symm
  right_inv q := by
    apply Prod.ext
    · funext k
      rfl
    · rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

theorem finrank_DiamondEOEEMultiplierGauge
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEOEEMultiplierGauge n) =
      n + 1 := by
  rw [LinearEquiv.finrank_eq (actualGaugeEquiv (n := n))]
  simp [Module.finrank_prod]

theorem ker_EOEE_projection_eq_gauge
    {n : Nat} [NeZero n] :
    LinearMap.ker (diamondEOEEProjection (n := n)) =
      DiamondEOEEMultiplierGauge n := rfl

theorem finrank_EOEE_leftKernel
    {n : Nat} [NeZero n] (hn : Even n) :
    Module.finrank F (DiamondEOEELeftKernel n) =
      n ^ 3 + 4 * n ^ 2 + n := by
  letI : FiniteDimensional F (DiamondEOEELeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEOEELeftSource n).subtype Subtype.val_injective
  letI : FiniteDimensional F (DiamondEOEEMultiplierSolution n) :=
    FiniteDimensional.of_injective
      (DiamondEOEEMultiplierSolution n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (diamondEOEEProjection (n := n))
  rw [range_EOEE_projection_eq_leftKernel,
    ker_EOEE_projection_eq_gauge,
    finrank_DiamondEOEEMultiplierSolution hn,
    finrank_DiamondEOEEMultiplierGauge] at h
  omega

theorem rank_diamondEvenP_cross_EOEE_scalar
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) :
    Module.finrank F
        (LinearMap.range (diamondEOEECross (n := n))) =
      3 * n ^ 2 * (n - 1) := by
  letI : FiniteDimensional F (DiamondEOEELeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEOEELeftSource n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (diamondEOEECross (n := n))
  change Module.finrank F (LinearMap.range diamondEOEECross) +
    Module.finrank F (DiamondEOEELeftKernel n) =
      Module.finrank F (DiamondEOEELeftSource n) at h
  rw [finrank_EOEE_leftKernel hn, finrank_EOEE_leftSource] at h
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hmul : n ^ 2 * (n - 1) + n ^ 2 = n ^ 3 := by
    calc
      _ = n ^ 2 * (n - 1 + 1) := by ring
      _ = n ^ 2 * n := by rw [hnsub]
      _ = n ^ 3 := by ring
  have hthree :
      3 * n ^ 2 * (n - 1) = 3 * (n ^ 2 * (n - 1)) := by ring
  rw [hthree]
  omega

end

end Core4loop.SquareDiagonal.EvenP
