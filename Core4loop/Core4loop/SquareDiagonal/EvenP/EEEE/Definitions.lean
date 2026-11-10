import Core4loop.SquareDiagonal.EvenP.CubeOrbit

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

abbrev DiamondEEEELeftAmbient (n : Nat) :=
  ((CyclicCube n × CyclicCube n) × (CyclicCube n × CyclicCube n)) ×
    ((CyclicCube n × CyclicCube n) × (CyclicCube n × CyclicCube n))

abbrev DiamondEEEERightAmbient (n : Nat) :=
  ((CyclicCube n × CyclicCube n) × (CyclicCube n × CyclicCube n)) ×
    ((CyclicCube n × CyclicCube n) × (CyclicCube n × CyclicCube n))

noncomputable def diamondEEEELeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEEEELeftAmbient n →ₗ[F]
      ((CyclicCube n × CyclicCube n) × CyclicCube n) where
  toFun l :=
    ((cubeDiffP l.1.1.1, cubeDiffR l.2.1.1),
      cubeDiffP l.1.1.2 + cubeDiffR l.2.2.1)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable abbrev DiamondEEEELeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEEEELeftConstraintMap (n := n))

noncomputable def diamondEEEECoeffMap
    {n : Nat} [NeZero n] :
    DiamondEEEELeftAmbient n →ₗ[F]
      DiamondEEEERightAmbient n where
  toFun l :=
    (((cubeDiffI (l.1.1.1 + l.1.1.2 + l.1.2.1 + l.1.2.2) +
          cubeDiffK (l.2.1.1 + l.2.1.2 + l.2.2.1 + l.2.2.2),
        cubeDiffI (l.1.1.1 + l.1.2.1)),
       (cubeDiffI (l.1.1.1 + l.1.1.2) +
          cubeDiffK (l.2.1.1 + l.2.2.1),
        cubeDiffI l.1.1.1)),
      ((cubeDiffK (l.2.1.1 + l.2.1.2), 0),
       (cubeDiffK l.2.1.1, 0)))
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp <;> ring

noncomputable def DiamondEEEERightSource
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEEEERightAmbient n) where
  carrier := { A |
    cubeDiffJInv A.1.1.1 = 0 ∧
    cubeDiffJInv A.1.1.2 ∈ LinearMap.range (cubeDiffR (n := n)) ∧
    cubeDiffJInv A.2.1.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
    cubeDiffJInv A.2.1.2 ∈
      LinearMap.range (LinearMap.coprod
        (cubeDiffP (n := n)) (cubeDiffR (n := n))) }
  zero_mem' := by
    constructor
    · simp
    constructor
    · exact (LinearMap.range (cubeDiffR (n := n))).zero_mem
    constructor
    · exact (LinearMap.range (cubeDiffP (n := n))).zero_mem
    · exact
        (LinearMap.range
          (LinearMap.coprod (cubeDiffP (n := n))
            (cubeDiffR (n := n)))).zero_mem
  add_mem' := by
    intro A A' hA hA'
    constructor
    · simpa using congrArg₂ (· + ·) hA.1 hA'.1
    constructor
    · simpa using
        (LinearMap.range (cubeDiffR (n := n))).add_mem hA.2.1 hA'.2.1
    constructor
    · simpa using
        (LinearMap.range (cubeDiffP (n := n))).add_mem hA.2.2.1 hA'.2.2.1
    · simpa using
        (LinearMap.range
          (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))).add_mem
            hA.2.2.2 hA'.2.2.2
  smul_mem' := by
    intro r A hA
    constructor
    · simpa using congrArg (r • ·) hA.1
    constructor
    · simpa using
        (LinearMap.range (cubeDiffR (n := n))).smul_mem r hA.2.1
    constructor
    · simpa using
        (LinearMap.range (cubeDiffP (n := n))).smul_mem r hA.2.2.1
    · simpa using
        (LinearMap.range
          (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))).smul_mem
            r hA.2.2.2

namespace EEEEInternal

theorem cubeDot_smul_left
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

theorem cubeDot_smul_right
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

theorem cubeDot_add_left
    {n : Nat} [NeZero n] (x y z : CyclicCube n) :
    cubeDot (x + y) z = cubeDot x z + cubeDot y z := by
  simp only [cubeDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem cubeDot_add_right
    {n : Nat} [NeZero n] (x y z : CyclicCube n) :
    cubeDot x (y + z) = cubeDot x y + cubeDot x z := by
  simp only [cubeDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cubeDot_left_ext
    {n : Nat} [NeZero n]
    (x y : CyclicCube n)
    (h : ∀ z : CyclicCube n, cubeDot x z = cubeDot y z) :
    x = y := by
  funext i j k
  let q0 : I n × I n × I n := (i, j, k)
  let e : CyclicCube n := fun i' j' k' =>
    if (i', j', k') = q0 then 1 else 0
  have he := h e
  classical
  have hx : cubeDot x e = x i j k := by
    rw [cubeDot, Finset.sum_eq_single q0]
    · simp [e, q0]
    · intro q _ hq
      simp [e, hq]
    · simp
  have hy : cubeDot y e = y i j k := by
    rw [cubeDot, Finset.sum_eq_single q0]
    · simp [e, q0]
    · intro q _ hq
      simp [e, hq]
    · simp
  simpa [hx, hy] using he

noncomputable def cubeDotDual
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) where
  toFun c :=
    { toFun := fun f => cubeDot c f
      map_add' := by
        intro f g
        exact cubeDot_add_right c f g
      map_smul' := by
        intro r f
        exact cubeDot_smul_right r c f }
  map_add' c d := by
    apply LinearMap.ext
    intro f
    exact cubeDot_add_left c d f
  map_smul' r c := by
    apply LinearMap.ext
    intro f
    exact cubeDot_smul_left r c f

theorem cubeDotDual_injective
    {n : Nat} [NeZero n] :
    Function.Injective (cubeDotDual (n := n)) := by
  intro x y h
  apply cubeDot_left_ext
  intro z
  exact LinearMap.congr_fun h z

noncomputable def cubeDotEquiv
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] Module.Dual F (CyclicCube n) :=
  LinearEquiv.ofBijective cubeDotDual
    ⟨cubeDotDual_injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        Subspace.dual_finrank_eq.symm).mp cubeDotDual_injective⟩

noncomputable def diamondEEEERightPairing
    {n : Nat} [NeZero n] :
    DiamondEEEERightAmbient n →ₗ[F]
      Module.Dual F (DiamondEEEERightAmbient n) where
  toFun R :=
    { toFun := fun A =>
        cubeDot R.1.1.1 A.1.1.1 + cubeDot R.1.1.2 A.1.1.2 +
        cubeDot R.1.2.1 A.1.2.1 + cubeDot R.1.2.2 A.1.2.2 +
        cubeDot R.2.1.1 A.2.1.1 + cubeDot R.2.1.2 A.2.1.2 +
        cubeDot R.2.2.1 A.2.2.1 + cubeDot R.2.2.2 A.2.2.2
      map_add' := by
        intro A A'
        change
          cubeDot R.1.1.1 (A.1.1.1 + A'.1.1.1) +
          cubeDot R.1.1.2 (A.1.1.2 + A'.1.1.2) +
          cubeDot R.1.2.1 (A.1.2.1 + A'.1.2.1) +
          cubeDot R.1.2.2 (A.1.2.2 + A'.1.2.2) +
          cubeDot R.2.1.1 (A.2.1.1 + A'.2.1.1) +
          cubeDot R.2.1.2 (A.2.1.2 + A'.2.1.2) +
          cubeDot R.2.2.1 (A.2.2.1 + A'.2.2.1) +
          cubeDot R.2.2.2 (A.2.2.2 + A'.2.2.2) =
            (cubeDot R.1.1.1 A.1.1.1 + cubeDot R.1.1.2 A.1.1.2 +
             cubeDot R.1.2.1 A.1.2.1 + cubeDot R.1.2.2 A.1.2.2 +
             cubeDot R.2.1.1 A.2.1.1 + cubeDot R.2.1.2 A.2.1.2 +
             cubeDot R.2.2.1 A.2.2.1 + cubeDot R.2.2.2 A.2.2.2) +
            (cubeDot R.1.1.1 A'.1.1.1 + cubeDot R.1.1.2 A'.1.1.2 +
             cubeDot R.1.2.1 A'.1.2.1 + cubeDot R.1.2.2 A'.1.2.2 +
             cubeDot R.2.1.1 A'.2.1.1 + cubeDot R.2.1.2 A'.2.1.2 +
             cubeDot R.2.2.1 A'.2.2.1 + cubeDot R.2.2.2 A'.2.2.2)
        rw [cubeDot_add_right, cubeDot_add_right,
          cubeDot_add_right, cubeDot_add_right,
          cubeDot_add_right, cubeDot_add_right,
          cubeDot_add_right, cubeDot_add_right]
        ring
      map_smul' := by
        intro r A
        change
          cubeDot R.1.1.1 (r • A.1.1.1) +
          cubeDot R.1.1.2 (r • A.1.1.2) +
          cubeDot R.1.2.1 (r • A.1.2.1) +
          cubeDot R.1.2.2 (r • A.1.2.2) +
          cubeDot R.2.1.1 (r • A.2.1.1) +
          cubeDot R.2.1.2 (r • A.2.1.2) +
          cubeDot R.2.2.1 (r • A.2.2.1) +
          cubeDot R.2.2.2 (r • A.2.2.2) =
            r • (cubeDot R.1.1.1 A.1.1.1 +
              cubeDot R.1.1.2 A.1.1.2 +
              cubeDot R.1.2.1 A.1.2.1 +
              cubeDot R.1.2.2 A.1.2.2 +
              cubeDot R.2.1.1 A.2.1.1 +
              cubeDot R.2.1.2 A.2.1.2 +
              cubeDot R.2.2.1 A.2.2.1 +
              cubeDot R.2.2.2 A.2.2.2)
        rw [cubeDot_smul_right, cubeDot_smul_right,
          cubeDot_smul_right, cubeDot_smul_right,
          cubeDot_smul_right, cubeDot_smul_right,
          cubeDot_smul_right, cubeDot_smul_right]
        simp only [smul_eq_mul]
        ring }
  map_add' R R' := by
    apply LinearMap.ext
    intro A
    change
      cubeDot (R.1.1.1 + R'.1.1.1) A.1.1.1 +
      cubeDot (R.1.1.2 + R'.1.1.2) A.1.1.2 +
      cubeDot (R.1.2.1 + R'.1.2.1) A.1.2.1 +
      cubeDot (R.1.2.2 + R'.1.2.2) A.1.2.2 +
      cubeDot (R.2.1.1 + R'.2.1.1) A.2.1.1 +
      cubeDot (R.2.1.2 + R'.2.1.2) A.2.1.2 +
      cubeDot (R.2.2.1 + R'.2.2.1) A.2.2.1 +
      cubeDot (R.2.2.2 + R'.2.2.2) A.2.2.2 =
        (cubeDot R.1.1.1 A.1.1.1 + cubeDot R.1.1.2 A.1.1.2 +
         cubeDot R.1.2.1 A.1.2.1 + cubeDot R.1.2.2 A.1.2.2 +
         cubeDot R.2.1.1 A.2.1.1 + cubeDot R.2.1.2 A.2.1.2 +
         cubeDot R.2.2.1 A.2.2.1 + cubeDot R.2.2.2 A.2.2.2) +
        (cubeDot R'.1.1.1 A.1.1.1 + cubeDot R'.1.1.2 A.1.1.2 +
         cubeDot R'.1.2.1 A.1.2.1 + cubeDot R'.1.2.2 A.1.2.2 +
         cubeDot R'.2.1.1 A.2.1.1 + cubeDot R'.2.1.2 A.2.1.2 +
         cubeDot R'.2.2.1 A.2.2.1 + cubeDot R'.2.2.2 A.2.2.2)
    rw [cubeDot_add_left, cubeDot_add_left,
      cubeDot_add_left, cubeDot_add_left,
      cubeDot_add_left, cubeDot_add_left,
      cubeDot_add_left, cubeDot_add_left]
    ring
  map_smul' r R := by
    apply LinearMap.ext
    intro A
    change
      cubeDot (r • R.1.1.1) A.1.1.1 +
      cubeDot (r • R.1.1.2) A.1.1.2 +
      cubeDot (r • R.1.2.1) A.1.2.1 +
      cubeDot (r • R.1.2.2) A.1.2.2 +
      cubeDot (r • R.2.1.1) A.2.1.1 +
      cubeDot (r • R.2.1.2) A.2.1.2 +
      cubeDot (r • R.2.2.1) A.2.2.1 +
      cubeDot (r • R.2.2.2) A.2.2.2 =
        r • (cubeDot R.1.1.1 A.1.1.1 +
          cubeDot R.1.1.2 A.1.1.2 +
          cubeDot R.1.2.1 A.1.2.1 +
          cubeDot R.1.2.2 A.1.2.2 +
          cubeDot R.2.1.1 A.2.1.1 +
          cubeDot R.2.1.2 A.2.1.2 +
          cubeDot R.2.2.1 A.2.2.1 +
          cubeDot R.2.2.2 A.2.2.2)
    rw [cubeDot_smul_left, cubeDot_smul_left,
      cubeDot_smul_left, cubeDot_smul_left,
      cubeDot_smul_left, cubeDot_smul_left,
      cubeDot_smul_left, cubeDot_smul_left]
    simp only [smul_eq_mul]
    ring

noncomputable def diamondEEEERestrictRightDual
    {n : Nat} [NeZero n] :
    Module.Dual F (DiamondEEEERightAmbient n) →ₗ[F]
      Module.Dual F (DiamondEEEERightSource n) where
  toFun phi := phi.comp (DiamondEEEERightSource n).subtype
  map_add' phi psi := by
    ext A
    rfl
  map_smul' r phi := by
    ext A
    rfl

end EEEEInternal

noncomputable def diamondEEEECross
    {n : Nat} [NeZero n] :
    DiamondEEEELeftSource n →ₗ[F]
      Module.Dual F (DiamondEEEERightSource n) :=
  EEEEInternal.diamondEEEERestrictRightDual.comp
    (EEEEInternal.diamondEEEERightPairing.comp
      (diamondEEEECoeffMap.comp
        (DiamondEEEELeftSource n).subtype))

noncomputable abbrev DiamondEEEELeftKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEEEECross (n := n))

namespace EEEEInternal

noncomputable def cubePInvariantMultiplierMap
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  LinearMap.prod
    (cubeDiffPStar.comp (LinearMap.snd F (CyclicCube n) (CyclicCube n)))
    (LinearMap.coprod cubeDiffK cubeDiffJStar)

noncomputable def CubePInvariantMultiplierSolution
    (n : Nat) [NeZero n] :
    Submodule F (CyclicCube n × CyclicCube n) :=
  LinearMap.ker (cubePInvariantMultiplierMap (n := n))

end EEEEInternal

abbrev DiamondEEEEMultiplierAmbient
    (n : Nat) [NeZero n] :=
  DiamondEEEELeftSource n ×
    ((CyclicCube n × CyclicCube n) ×
      (CyclicCube n × CyclicCube n))

namespace EEEEInternal

abbrev ConstraintAmbient
    (n : Nat) :=
  Fin 11 → CyclicCube n

end EEEEInternal

set_option maxHeartbeats 2000000 in
-- The eleven-way `Fin` case split normalizes nested cube-product coordinates.
noncomputable def diamondEEEEMultiplierConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEEEEMultiplierAmbient n →ₗ[F]
      EEEEInternal.ConstraintAmbient n where
  toFun z :=
    let R := diamondEEEECoeffMap z.1.1
    let lambda00 := z.2.1.1
    let lambda01 := z.2.1.2
    let lambda10 := z.2.2.1
    let lambda11 := z.2.2.2
    fun q =>
      match q with
      | 0 => R.1.2.2
      | 1 => R.2.2.1
      | 2 => R.1.2.1
      | 3 => R.1.1.2 + cubeDiffJStar lambda01
      | 4 => cubeDiffRStar lambda01
      | 5 => R.2.1.1 + cubeDiffJStar lambda10
      | 6 => cubeDiffPStar lambda10
      | 7 => R.1.1.1 + cubeDiffJStar lambda00
      | 8 => cubeDiffJStar lambda11
      | 9 => cubeDiffPStar lambda11
      | 10 => cubeDiffRStar lambda11
  map_add' x y := by
    funext q
    fin_cases q <;> simp [diamondEEEECoeffMap] <;> abel
  map_smul' r x := by
    funext q
    fin_cases q <;> simp [diamondEEEECoeffMap]

noncomputable def DiamondEEEEMultiplierSolution
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEEEEMultiplierAmbient n) :=
  LinearMap.ker (diamondEEEEMultiplierConstraintMap (n := n))

noncomputable def diamondEEEEProjection
    {n : Nat} [NeZero n] :
    DiamondEEEEMultiplierSolution n →ₗ[F]
      DiamondEEEELeftSource n :=
  (LinearMap.fst F (DiamondEEEELeftSource n)
    ((CyclicCube n × CyclicCube n) ×
      (CyclicCube n × CyclicCube n))).comp
    (DiamondEEEEMultiplierSolution n).subtype

noncomputable def DiamondEEEEMultiplierGauge
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEEEEMultiplierSolution n) :=
  LinearMap.ker (diamondEEEEProjection (n := n))

end

end Core4loop.SquareDiagonal.EvenP
