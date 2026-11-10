import Core4loop.SquareDiagonal.EvenP.CubeOrbit

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

/-! The literal EEOE source.  The phase-free coordinates remain constrained. -/

abbrev DiamondEEOELeftAmbient (n : Nat) :=
  (CyclicCube n × CyclicCube n) ×
    (CyclicCube n × CyclicCube n)

abbrev DiamondEEOERightAmbient (n : Nat) :=
  (CyclicCube n × CyclicCube n) ×
    (CyclicCube n × CyclicCube n)

noncomputable def diamondEEOELeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEEOELeftAmbient n →ₗ[F]
      ((CyclicCube n × CyclicCube n) × CyclicCube n) where
  toFun l :=
    ((cubeDiffP l.1.1, cubeDiffR l.2.1),
      cubeDiffP l.1.2 + cubeDiffR l.2.2)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable abbrev DiamondEEOELeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEEOELeftConstraintMap (n := n))

noncomputable def diamondEEOECoeffMap
    {n : Nat} [NeZero n] :
    DiamondEEOELeftAmbient n →ₗ[F]
      DiamondEEOERightAmbient n where
  toFun l :=
    ((cubeDiffI (l.1.1 + l.1.2) +
        cubeDiffK (l.2.1 + l.2.2),
      cubeDiffI l.1.1),
    (cubeDiffK l.2.1, 0))
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp <;> ring

noncomputable def DiamondEEOERightSource
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEEOERightAmbient n) where
  carrier := { A |
    cubeDiffJInv A.1.1 = 0 ∧
    cubeDiffJInv A.1.2 ∈ LinearMap.range (cubeDiffR (n := n)) ∧
    cubeDiffJInv A.2.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
    cubeDiffJInv A.2.2 ∈
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
        (LinearMap.range (cubeDiffP (n := n))).add_mem
          hA.2.2.1 hA'.2.2.1
    · simpa using
        (LinearMap.range
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n)))).add_mem
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
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n)))).smul_mem
          r hA.2.2.2

namespace EEOEInternal

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
      map_add' := cubeDot_add_right c
      map_smul' := by
        intro r f
        exact cubeDot_smul_right r c f }
  map_add' c d := by
    apply LinearMap.ext
    exact cubeDot_add_left c d
  map_smul' r c := by
    apply LinearMap.ext
    exact cubeDot_smul_left r c

theorem cubeDotDual_injective
    {n : Nat} [NeZero n] :
    Function.Injective (cubeDotDual (n := n)) := by
  intro x y h
  apply cubeDot_left_ext
  intro z
  simpa [cubeDotDual] using LinearMap.congr_fun h z

noncomputable def cubeDotEquiv
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] Module.Dual F (CyclicCube n) :=
  LinearEquiv.ofBijective cubeDotDual
    ⟨cubeDotDual_injective,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        Subspace.dual_finrank_eq.symm).mp cubeDotDual_injective⟩

def ambientPhase
    {n : Nat} [NeZero n]
    (R A : DiamondEEOERightAmbient n) : F :=
  cubeDot R.1.1 A.1.1 + cubeDot R.1.2 A.1.2 +
    cubeDot R.2.1 A.2.1 + cubeDot R.2.2 A.2.2

noncomputable def ambientPairing
    {n : Nat} [NeZero n] :
    DiamondEEOERightAmbient n →ₗ[F]
      DiamondEEOERightAmbient n →ₗ[F] F :=
  LinearMap.mk₂ F ambientPhase
    (by
      intro R R' A
      change
        cubeDot (R.1.1 + R'.1.1) A.1.1 +
          cubeDot (R.1.2 + R'.1.2) A.1.2 +
          cubeDot (R.2.1 + R'.2.1) A.2.1 +
          cubeDot (R.2.2 + R'.2.2) A.2.2 =
        ambientPhase R A + ambientPhase R' A
      rw [cubeDot_add_left, cubeDot_add_left,
        cubeDot_add_left, cubeDot_add_left]
      simp only [ambientPhase]
      ring)
    (by
      intro r R A
      change
        cubeDot (r • R.1.1) A.1.1 +
          cubeDot (r • R.1.2) A.1.2 +
          cubeDot (r • R.2.1) A.2.1 +
          cubeDot (r • R.2.2) A.2.2 =
        r • ambientPhase R A
      rw [cubeDot_smul_left, cubeDot_smul_left,
        cubeDot_smul_left, cubeDot_smul_left]
      simp only [smul_eq_mul, ambientPhase]
      ring)
    (by
      intro R A A'
      change
        cubeDot R.1.1 (A.1.1 + A'.1.1) +
          cubeDot R.1.2 (A.1.2 + A'.1.2) +
          cubeDot R.2.1 (A.2.1 + A'.2.1) +
          cubeDot R.2.2 (A.2.2 + A'.2.2) =
        ambientPhase R A + ambientPhase R A'
      rw [cubeDot_add_right, cubeDot_add_right,
        cubeDot_add_right, cubeDot_add_right]
      simp only [ambientPhase]
      ring)
    (by
      intro r R A
      change
        cubeDot R.1.1 (r • A.1.1) +
          cubeDot R.1.2 (r • A.1.2) +
          cubeDot R.2.1 (r • A.2.1) +
          cubeDot R.2.2 (r • A.2.2) =
        r • ambientPhase R A
      rw [cubeDot_smul_right, cubeDot_smul_right,
        cubeDot_smul_right, cubeDot_smul_right]
      simp only [smul_eq_mul, ambientPhase]
      ring)

end EEOEInternal

noncomputable def diamondEEOECross
    {n : Nat} [NeZero n] :
    DiamondEEOELeftSource n →ₗ[F]
      Module.Dual F (DiamondEEOERightSource n) :=
  EEOEInternal.ambientPairing.compl₁₂
    (diamondEEOECoeffMap.comp
      (DiamondEEOELeftSource n).subtype)
    (DiamondEEOERightSource n).subtype

namespace EEOEInternal

/-! The two literal cross blocks. -/

noncomputable abbrev PBlockLeft
    (n : Nat) [NeZero n] :=
  LinearMap.ker (cubeDiffP (n := n))

noncomputable def RReachRight
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  (LinearMap.range (cubeDiffR (n := n))).comap
    (cubeDiffJInv (n := n))

noncomputable abbrev RBlockLeft
    (n : Nat) [NeZero n] :=
  LinearMap.ker (cubeDiffR (n := n))

noncomputable def PReachRight
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  (LinearMap.range (cubeDiffP (n := n))).comap
    (cubeDiffJInv (n := n))

noncomputable def pBlockCross
    {n : Nat} [NeZero n] :
    PBlockLeft n →ₗ[F] Module.Dual F (RReachRight n) :=
  cubeDotDual.compl₁₂
    ((cubeDiffI (n := n)).comp (PBlockLeft n).subtype)
    (RReachRight n).subtype

noncomputable def rBlockCross
    {n : Nat} [NeZero n] :
    RBlockLeft n →ₗ[F] Module.Dual F (PReachRight n) :=
  cubeDotDual.compl₁₂
    ((cubeDiffK (n := n)).comp (RBlockLeft n).subtype)
    (PReachRight n).subtype

/-! An explicit multiplier certificate for the first block. -/

abbrev PBlockMultiplierAmbient
    (n : Nat) [NeZero n] :=
  PBlockLeft n × CyclicCube n

noncomputable def pBlockMultiplierConstraintMap
    {n : Nat} [NeZero n] :
    PBlockMultiplierAmbient n →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  LinearMap.prod
    (cubeDiffRStar.comp
      (LinearMap.snd F (PBlockLeft n) (CyclicCube n)))
    (LinearMap.coprod
      ((cubeDiffI (n := n)).comp (PBlockLeft n).subtype)
      cubeDiffJStar)

noncomputable def PBlockMultiplierSolution
    (n : Nat) [NeZero n] :
    Submodule F (PBlockMultiplierAmbient n) :=
  LinearMap.ker (pBlockMultiplierConstraintMap (n := n))

noncomputable def pBlockProjection
    {n : Nat} [NeZero n] :
    PBlockMultiplierSolution n →ₗ[F] PBlockLeft n :=
  (LinearMap.fst F (PBlockLeft n) (CyclicCube n)).comp
    (PBlockMultiplierSolution n).subtype

noncomputable def PBlockMultiplierGauge
    (n : Nat) [NeZero n] :
    Submodule F (PBlockMultiplierSolution n) :=
  LinearMap.ker (pBlockProjection (n := n))

theorem cubeDiffI_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffI f i j k = f i j k + f (i + 1) j k := rfl

theorem cubeDiffK_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  change f i j k + f (i + 0) (j + 0) (k + 1) = _
  simp

theorem cubeDiffP_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffP f i j k =
      f i j k + f (i + 1) (j - 1) k := by
  change
    f i j k + f (i + 1) (j + (-1)) (k + 0) = _
  simp [sub_eq_add_neg]

theorem cubeDiffR_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffR f i j k =
      f i j k + f i (j - 1) (k + 1) := by
  change
    f i j k + f (i + 0) (j + (-1)) (k + 1) = _
  simp [sub_eq_add_neg]

theorem cubeDiffJInv_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffJInv f i j k = f i j k + f i (j - 1) k := by
  change
    f i j k + f (i + 0) (j + (-1)) (k + 0) = _
  simp [sub_eq_add_neg]

theorem cubeDiffJStar_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffJStar f i j k = f i j k + f i (j + 1) k := by
  change f i j k + f (i + 0) (j + 1) (k + 0) = _
  simp

theorem cubeDiffRStar_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffRStar f i j k =
      f i j k + f i (j + 1) (k - 1) := by
  change
    f i j k + f (i + 0) (j + 1) (k + (-1)) = _
  simp [sub_eq_add_neg]

theorem cubeDiffPStar_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffPStar f i j k =
      f i j k + f (i - 1) (j + 1) k := by
  change
    f i j k + f (i + (-1)) (j + 1) (k + 0) = _
  simp [sub_eq_add_neg]

theorem module_add_self {V : Type*}
    [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 := by
  rw [← two_smul F x, show (2 : F) = 0 by decide, zero_smul]

theorem eq_of_add_eq_zero {V : Type*}
    [AddCommGroup V] [Module F V] {x y : V}
    (h : x + y = 0) : x = y := by
  rw [← module_add_self y] at h
  exact add_right_cancel h

noncomputable def shiftZero
    {n : Nat} [NeZero n] (q : I n) :
    ZeroSumProfile n →ₗ[F] ZeroSumProfile n where
  toFun a :=
    ⟨fun s => a.1 (s + q), by
      apply LinearMap.mem_ker.mpr
      change (∑ s : I n, a.1 (s + q)) = 0
      rw [sum_shift]
      exact LinearMap.mem_ker.mp a.2⟩
  map_add' a b := by
    apply Subtype.ext
    rfl
  map_smul' r a := by
    apply Subtype.ext
    rfl

theorem primitive_zero
    {n : Nat} [NeZero n] (a : ZeroSumProfile n) :
    explicitCyclicPrimitive n a 0 = 0 := by
  simp [explicitCyclicPrimitive, explicitCyclicPrefixLinear,
    explicitCyclicPrefix, finPrefix_zero]

abbrev PBlockCoordinates (n : Nat) [NeZero n] :=
  ((Profile n × ZeroSumProfile n) × Profile n)

noncomputable def pCoordinateB
    {n : Nat} [NeZero n] :
    PBlockCoordinates n →ₗ[F] CyclicCube n where
  toFun q := fun i j k =>
    q.1.1 k +
      explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j)
  map_add' q q' := by
    funext i j k
    change
      (q.1.1 k + q'.1.1 k) +
          explicitCyclicPrimitive n
            (shiftZero k (q.1.2 + q'.1.2)) (i + j) =
        (q.1.1 k +
          explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j)) +
        (q'.1.1 k +
          explicitCyclicPrimitive n (shiftZero k q'.1.2) (i + j))
    rw [map_add (shiftZero k), map_add (explicitCyclicPrimitive n)]
    simp only [Pi.add_apply]
    abel
  map_smul' r q := by
    funext i j k
    change
      r * q.1.1 k +
          explicitCyclicPrimitive n
            (shiftZero k (r • q.1.2)) (i + j) =
        r * (q.1.1 k +
          explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j))
    rw [map_smul (shiftZero k), map_smul (explicitCyclicPrimitive n)]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

noncomputable def pCoordinateLambda
    {n : Nat} [NeZero n] :
    PBlockCoordinates n →ₗ[F] CyclicCube n where
  toFun q := fun i j k =>
    q.2 i +
      explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k)
  map_add' q q' := by
    funext i j k
    change
      (q.2 i + q'.2 i) +
          explicitCyclicPrimitive n
            (shiftZero i (q.1.2 + q'.1.2)) (j + k) =
        (q.2 i +
          explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k)) +
        (q'.2 i +
          explicitCyclicPrimitive n (shiftZero i q'.1.2) (j + k))
    rw [map_add (shiftZero i), map_add (explicitCyclicPrimitive n)]
    simp only [Pi.add_apply]
    abel
  map_smul' r q := by
    funext i j k
    change
      r * q.2 i +
          explicitCyclicPrimitive n
            (shiftZero i (r • q.1.2)) (j + k) =
        r * (q.2 i +
          explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k))
    rw [map_smul (shiftZero i), map_smul (explicitCyclicPrimitive n)]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem pCoordinateB_mem
    {n : Nat} [NeZero n] (q : PBlockCoordinates n) :
    pCoordinateB q ∈ PBlockLeft n := by
  apply LinearMap.mem_ker.mpr
  funext i j k
  rw [cubeDiffP_apply]
  change
    (q.1.1 k +
      explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j)) +
    (q.1.1 k +
      explicitCyclicPrimitive n (shiftZero k q.1.2)
        ((i + 1) + (j - 1))) = 0
  rw [show (i + 1) + (j - 1) = i + j by abel]
  exact module_add_self _

noncomputable def pCoordinateAmbient
    {n : Nat} [NeZero n] :
    PBlockCoordinates n →ₗ[F] PBlockMultiplierAmbient n where
  toFun q :=
    (⟨pCoordinateB q, pCoordinateB_mem q⟩,
      pCoordinateLambda q)
  map_add' q q' := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_add pCoordinateB q q'
    · exact map_add pCoordinateLambda q q'
  map_smul' r q := by
    apply Prod.ext
    · apply Subtype.ext
      exact map_smul pCoordinateB r q
    · exact map_smul pCoordinateLambda r q

theorem pCoordinateAmbient_mem
    {n : Nat} [NeZero n] (q : PBlockCoordinates n) :
    pCoordinateAmbient q ∈ PBlockMultiplierSolution n := by
  apply LinearMap.mem_ker.mpr
  apply Prod.ext
  · change cubeDiffRStar (pCoordinateLambda q) = 0
    funext i j k
    rw [cubeDiffRStar_apply (n := n)]
    change
      (q.2 i +
        explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k)) +
      (q.2 i +
        explicitCyclicPrimitive n (shiftZero i q.1.2)
          ((j + 1) + (k - 1))) = 0
    rw [show (j + 1) + (k - 1) = j + k by abel]
    exact module_add_self _
  · change
      cubeDiffI (pCoordinateB q) +
        cubeDiffJStar (pCoordinateLambda q) = 0
    funext i j k
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [cubeDiffI_apply (n := n), cubeDiffJStar_apply (n := n)]
    change
      ((q.1.1 k +
          explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j)) +
        (q.1.1 k +
          explicitCyclicPrimitive n (shiftZero k q.1.2)
            ((i + 1) + j))) +
      ((q.2 i +
          explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k)) +
        (q.2 i +
          explicitCyclicPrimitive n (shiftZero i q.1.2)
            ((j + 1) + k))) = 0
    have hB := congrFun
      (cycDiff_explicitCyclicPrimitive (shiftZero k q.1.2))
      (i + j)
    have hL := congrFun
      (cycDiff_explicitCyclicPrimitive (shiftZero i q.1.2))
      (j + k)
    change
      explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j) +
        explicitCyclicPrimitive n (shiftZero k q.1.2)
          ((i + j) + 1) = q.1.2.1 ((i + j) + k) at hB
    change
      explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k) +
        explicitCyclicPrimitive n (shiftZero i q.1.2)
          ((j + k) + 1) = q.1.2.1 ((j + k) + i) at hL
    rw [show (i + 1) + j = (i + j) + 1 by abel,
      show (j + 1) + k = (j + k) + 1 by abel]
    calc
      _ =
          (q.1.1 k + q.1.1 k) + (q.2 i + q.2 i) +
          ((explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j) +
            explicitCyclicPrimitive n (shiftZero k q.1.2)
              ((i + j) + 1)) +
          (explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k) +
            explicitCyclicPrimitive n (shiftZero i q.1.2)
              ((j + k) + 1))) := by abel
      _ =
          (explicitCyclicPrimitive n (shiftZero k q.1.2) (i + j) +
            explicitCyclicPrimitive n (shiftZero k q.1.2)
              ((i + j) + 1)) +
          (explicitCyclicPrimitive n (shiftZero i q.1.2) (j + k) +
            explicitCyclicPrimitive n (shiftZero i q.1.2)
              ((j + k) + 1)) := by
                rw [module_add_self, module_add_self, zero_add, zero_add]
      _ = q.1.2.1 ((i + j) + k) +
          q.1.2.1 ((j + k) + i) := by rw [hB, hL]
      _ = 0 := by
        rw [show (i + j) + k = (j + k) + i by abel]
        exact module_add_self _

noncomputable def pCoordinateBuild
    {n : Nat} [NeZero n] :
    PBlockCoordinates n →ₗ[F] PBlockMultiplierSolution n :=
  LinearMap.codRestrict (PBlockMultiplierSolution n)
    pCoordinateAmbient pCoordinateAmbient_mem

theorem pInvariant
    {n : Nat} [NeZero n] (B : PBlockLeft n)
    (i j k : I n) :
    B.1 i j k = B.1 0 (i + j) k := by
  let f : Profile n := fun t => B.1 t (i + j - t) k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hp := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp B.2) t) (i + j - t)) k
    rw [cubeDiffP_apply (n := n)] at hp
    change f t + f (t + 1) = 0
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hp
  have hc :=
    (cycDiff_eq_zero_iff_constant_apply F f).mp hf i
  simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hc

theorem solutionRStar
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n) :
    cubeDiffRStar z.1.2 = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  exact congrArg Prod.fst hz

theorem solutionCross
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n) :
    cubeDiffI z.1.1.1 + cubeDiffJStar z.1.2 = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  exact congrArg Prod.snd hz

theorem solutionCross_eq
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n) :
    cubeDiffI z.1.1.1 = cubeDiffJStar z.1.2 :=
  eq_of_add_eq_zero (solutionCross z)

theorem rStarInvariant
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n)
    (i j k : I n) :
    z.1.2 i j k = z.1.2 i 0 (j + k) := by
  let f : Profile n := fun t => z.1.2 i t (j + k - t)
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have ht := congrFun (congrFun (congrFun
      (solutionRStar z) i) t) (j + k - t)
    rw [cubeDiffRStar_apply (n := n)] at ht
    change f t + f (t + 1) = 0
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using ht
  have hc :=
    (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
  simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hc

theorem diffI_pInvariant
    {n : Nat} [NeZero n] (B : PBlockLeft n)
    (i j k : I n) :
    cubeDiffI B.1 i j k =
      cubeDiffI B.1 0 (i + j) k := by
  rw [cubeDiffI_apply (n := n), cubeDiffI_apply (n := n),
    pInvariant B i j k, pInvariant B (i + 1) j k,
    pInvariant B (0 + 1) (i + j) k]
  congr 2
  abel

theorem solutionDiffI_rStarInvariant
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n)
    (i j k : I n) :
    cubeDiffI z.1.1.1 i j k =
      cubeDiffI z.1.1.1 i 0 (j + k) := by
  rw [solutionCross_eq z]
  rw [cubeDiffJStar_apply (n := n), cubeDiffJStar_apply (n := n),
    rStarInvariant z i j k, rStarInvariant z i (j + 1) k,
    rStarInvariant z i 0 (j + k),
    rStarInvariant z i (0 + 1) (j + k)]
  rw [show j + 1 + k = 0 + 1 + (j + k) by abel]

theorem solutionDiffI_diagonal
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n)
    (s k : I n) :
    cubeDiffI z.1.1.1 s 0 k =
      cubeDiffI z.1.1.1 0 0 (s + k) := by
  calc
    cubeDiffI z.1.1.1 s 0 k =
        cubeDiffI z.1.1.1 0 s k :=
      by simpa using diffI_pInvariant z.1.1 s 0 k
    _ = cubeDiffI z.1.1.1 0 0 (s + k) :=
      solutionDiffI_rStarInvariant z 0 s k

noncomputable def pReadA
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n) :
    ZeroSumProfile n :=
  ⟨fun s => cubeDiffI z.1.1.1 0 0 s, by
    apply LinearMap.mem_ker.mpr
    change (∑ s : I n, cubeDiffI z.1.1.1 0 0 s) = 0
    calc
      (∑ s : I n, cubeDiffI z.1.1.1 0 0 s) =
          ∑ s : I n,
            (z.1.2 0 0 s + z.1.2 0 0 (s + 1)) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [solutionCross_eq z, cubeDiffJStar_apply (n := n),
          rStarInvariant z 0 (0 + 1) s]
        congr 2
        abel
      _ = (∑ s : I n, z.1.2 0 0 s) +
          ∑ s : I n, z.1.2 0 0 (s + 1) :=
        Finset.sum_add_distrib
      _ = (∑ s : I n, z.1.2 0 0 s) +
          ∑ s : I n, z.1.2 0 0 s := by
        rw [sum_shift (n := n) (1 : I n)
          (fun s => z.1.2 0 0 s)]
      _ = 0 := module_add_self _⟩

noncomputable def pCoordinateRead
    {n : Nat} [NeZero n] :
    PBlockMultiplierSolution n →ₗ[F] PBlockCoordinates n where
  toFun z :=
    ((fun k => z.1.1.1 0 0 k, pReadA z),
      fun i => z.1.2 i 0 0)
  map_add' z w := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        funext s
        change
          cubeDiffI (z.1.1.1 + w.1.1.1) 0 0 s =
            cubeDiffI z.1.1.1 0 0 s +
              cubeDiffI w.1.1.1 0 0 s
        have h := map_add (cubeDiffI (n := n))
          z.1.1.1 w.1.1.1
        simpa only [Pi.add_apply] using
          congrFun (congrFun (congrFun h 0) 0) s
    · rfl
  map_smul' r z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        funext s
        change
          cubeDiffI (r • z.1.1.1) 0 0 s =
            r • cubeDiffI z.1.1.1 0 0 s
        have h := map_smul (cubeDiffI (n := n)) r z.1.1.1
        simpa only [Pi.smul_apply] using
          congrFun (congrFun (congrFun h 0) 0) s
    · rfl

theorem primitive_eq_base_add
    {n : Nat} [NeZero n] (a : ZeroSumProfile n)
    (f : Profile n) (h : a.1 = cycDiff (n := n) F f)
    (s : I n) :
    explicitCyclicPrimitive n a s = f 0 + f s := by
  have hs := congrFun (explicitCyclicPrefix_cycDiff f) s
  change explicitCyclicPrefix a.1 s = f 0 + f s
  rw [h]
  exact hs

theorem pCoordinateBuild_B
    {n : Nat} [NeZero n] (q : PBlockCoordinates n) :
    (pCoordinateBuild q).1.1.1 = pCoordinateB q := rfl

theorem pCoordinateBuild_lambda
    {n : Nat} [NeZero n] (q : PBlockCoordinates n) :
    (pCoordinateBuild q).1.2 = pCoordinateLambda q := rfl

theorem pCoordinateRead_build
    {n : Nat} [NeZero n] (q : PBlockCoordinates n) :
    pCoordinateRead (pCoordinateBuild q) = q := by
  apply Prod.ext
  · apply Prod.ext
    · funext k
      change (pCoordinateBuild q).1.1.1 0 0 k = q.1.1 k
      rw [pCoordinateBuild_B]
      simp only [pCoordinateB, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [zero_add]
      change
        q.1.1 k +
          explicitCyclicPrimitive n (shiftZero k q.1.2) 0 =
        q.1.1 k
      rw [primitive_zero]
      simp
    · apply Subtype.ext
      funext s
      change
        cubeDiffI (pCoordinateBuild q).1.1.1 0 0 s =
          q.1.2.1 s
      rw [pCoordinateBuild_B]
      rw [cubeDiffI_apply (n := n)]
      simp only [pCoordinateB, LinearMap.coe_mk, AddHom.coe_mk,
        zero_add, add_zero]
      change
        (q.1.1 s +
          explicitCyclicPrimitive n (shiftZero s q.1.2) 0) +
        (q.1.1 s +
          explicitCyclicPrimitive n (shiftZero s q.1.2) 1) =
        q.1.2.1 s
      have h := congrFun
        (cycDiff_explicitCyclicPrimitive (shiftZero s q.1.2)) 0
      change
        explicitCyclicPrimitive n (shiftZero s q.1.2) 0 +
          explicitCyclicPrimitive n (shiftZero s q.1.2) (0 + 1) =
        q.1.2.1 (0 + s) at h
      simpa only [zero_add] using
        (show
          (q.1.1 s +
              explicitCyclicPrimitive n (shiftZero s q.1.2) 0) +
            (q.1.1 s +
              explicitCyclicPrimitive n (shiftZero s q.1.2) 1) =
            q.1.2.1 s by
          calc
            _ =
                (q.1.1 s + q.1.1 s) +
                (explicitCyclicPrimitive n (shiftZero s q.1.2) 0 +
                  explicitCyclicPrimitive n (shiftZero s q.1.2) 1) := by
                    abel
            _ = q.1.2.1 s := by
              rw [module_add_self, zero_add]
              simpa only [zero_add] using h)
  · funext i
    change (pCoordinateBuild q).1.2 i 0 0 = q.2 i
    rw [pCoordinateBuild_lambda]
    simp only [pCoordinateLambda, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [zero_add]
    change
      q.2 i +
        explicitCyclicPrimitive n (shiftZero i q.1.2) 0 =
      q.2 i
    rw [primitive_zero]
    simp

theorem pReadA_shift_eq_cycDiff_B
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n)
    (k : I n) :
    (shiftZero k (pReadA z)).1 =
      cycDiff (n := n) F (fun s => z.1.1.1 0 s k) := by
  funext s
  change
    cubeDiffI z.1.1.1 0 0 (s + k) =
      z.1.1.1 0 s k + z.1.1.1 0 (s + 1) k
  rw [← solutionDiffI_diagonal z s k,
    cubeDiffI_apply (n := n),
    pInvariant z.1.1 s 0 k,
    pInvariant z.1.1 (s + 1) 0 k]
  congr 2 <;> abel

theorem pReadA_shift_eq_cycDiff_lambda
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n)
    (i : I n) :
    (shiftZero i (pReadA z)).1 =
      cycDiff (n := n) F (fun t => z.1.2 i 0 t) := by
  funext t
  change
    cubeDiffI z.1.1.1 0 0 (t + i) =
      z.1.2 i 0 t + z.1.2 i 0 (t + 1)
  rw [show t + i = i + t by abel,
    ← solutionDiffI_diagonal z i t,
    solutionCross_eq z, cubeDiffJStar_apply (n := n),
    rStarInvariant z i (0 + 1) t]
  congr 2
  abel

theorem pCoordinateBuild_read
    {n : Nat} [NeZero n] (z : PBlockMultiplierSolution n) :
    pCoordinateBuild (pCoordinateRead z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext i j k
    change
      z.1.1.1 0 0 k +
          explicitCyclicPrimitive n
            (shiftZero k (pReadA z)) (i + j) =
        z.1.1.1 i j k
    rw [primitive_eq_base_add
      (shiftZero k (pReadA z))
      (fun s => z.1.1.1 0 s k)
      (pReadA_shift_eq_cycDiff_B z k) (i + j)]
    calc
      z.1.1.1 0 0 k +
          (z.1.1.1 0 0 k + z.1.1.1 0 (i + j) k) =
        (z.1.1.1 0 0 k + z.1.1.1 0 0 k) +
          z.1.1.1 0 (i + j) k := by abel
      _ = z.1.1.1 0 (i + j) k := by
        rw [module_add_self, zero_add]
      _ = z.1.1.1 i j k := (pInvariant z.1.1 i j k).symm
  · funext i j k
    change
      z.1.2 i 0 0 +
          explicitCyclicPrimitive n
            (shiftZero i (pReadA z)) (j + k) =
        z.1.2 i j k
    rw [primitive_eq_base_add
      (shiftZero i (pReadA z))
      (fun t => z.1.2 i 0 t)
      (pReadA_shift_eq_cycDiff_lambda z i) (j + k)]
    calc
      z.1.2 i 0 0 +
          (z.1.2 i 0 0 + z.1.2 i 0 (j + k)) =
        (z.1.2 i 0 0 + z.1.2 i 0 0) +
          z.1.2 i 0 (j + k) := by abel
      _ = z.1.2 i 0 (j + k) := by
        rw [module_add_self, zero_add]
      _ = z.1.2 i j k := (rStarInvariant z i j k).symm

noncomputable def pBlockMultiplierEquiv
    {n : Nat} [NeZero n] :
    PBlockMultiplierSolution n ≃ₗ[F] PBlockCoordinates n where
  toLinearMap := pCoordinateRead
  invFun := pCoordinateBuild
  left_inv := pCoordinateBuild_read
  right_inv := pCoordinateRead_build

theorem finrank_PBlockMultiplierSolution
    {n : Nat} [NeZero n] :
    Module.finrank F (PBlockMultiplierSolution n) =
      3 * n - 1 := by
  rw [LinearEquiv.finrank_eq (pBlockMultiplierEquiv (n := n))]
  simp only [PBlockCoordinates, Module.finrank_prod,
    finrank_profile, finrank_ZeroSumProfile]
  omega

noncomputable abbrev PBlockLeftKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (pBlockCross (n := n))

theorem dual_exists_cubeDot
    {n : Nat} [NeZero n] (phi : Module.Dual F (CyclicCube n)) :
    ∃ lambda : CyclicCube n,
      ∀ x : CyclicCube n, phi x = cubeDot lambda x := by
  let lambda := (cubeDotEquiv (n := n)).symm phi
  refine ⟨lambda, fun x => ?_⟩
  have h := LinearMap.congr_fun
    ((cubeDotEquiv (n := n)).apply_symm_apply phi) x
  exact h.symm

theorem dual_factor_of_vanishes_on_comap_range
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

theorem range_pBlockProjection_eq_leftKernel
    {n : Nat} [NeZero n] :
    LinearMap.range (pBlockProjection (n := n)) =
      PBlockLeftKernel n := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    rcases A.2 with ⟨X, hX⟩
    have hcross := solutionCross_eq z
    have hr := solutionRStar z
    change cubeDot (cubeDiffI z.1.1.1) A.1 = 0
    rw [hcross, cubeDiffJ_pairing_adjoint, hX.symm,
      ← cubeDiffR_pairing_adjoint, hr]
    simp [cubeDot]
  · intro B hB
    have hvanish (A : CyclicCube n)
        (hA : cubeDiffJInv A ∈
          LinearMap.range (cubeDiffR (n := n))) :
        cubeDotDual (cubeDiffI B.1) A = 0 := by
      let Ar : RReachRight n := ⟨A, hA⟩
      have hzero :=
        LinearMap.congr_fun (LinearMap.mem_ker.mp hB) Ar
      simpa [pBlockCross, cubeDotDual, Ar] using hzero
    rcases dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv cubeDiffR
        (cubeDotDual (cubeDiffI B.1)) hvanish with
      ⟨psi, hfactor, hann⟩
    rcases dual_exists_cubeDot psi with ⟨lambda, hpsi⟩
    have hR : cubeDiffI B.1 = cubeDiffJStar lambda := by
      apply cubeDot_left_ext
      intro A
      calc
        cubeDot (cubeDiffI B.1) A =
            psi (cubeDiffJInv A) :=
          LinearMap.congr_fun hfactor A
        _ = cubeDot lambda (cubeDiffJInv A) := hpsi _
        _ = cubeDot (cubeDiffJStar lambda) A :=
          (cubeDiffJ_pairing_adjoint lambda A).symm
    have hr : cubeDiffRStar lambda = 0 := by
      apply cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffRStar lambda) X =
            cubeDot lambda (cubeDiffR X) :=
          cubeDiffR_pairing_adjoint lambda X
        _ = psi (cubeDiffR X) := (hpsi _).symm
        _ = 0 := hann X
        _ = cubeDot 0 X := by simp [cubeDot]
    let z0 : PBlockMultiplierAmbient n := (B, lambda)
    have hz0 : pBlockMultiplierConstraintMap z0 = 0 := by
      apply Prod.ext
      · exact hr
      · change cubeDiffI B.1 + cubeDiffJStar lambda = 0
        rw [hR]
        exact module_add_self _
    exact ⟨⟨z0, hz0⟩, rfl⟩

noncomputable def pGaugeCoordinate
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] PBlockCoordinates n where
  toFun g := ((0, 0), g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pGaugeCoordinate_B_zero
    {n : Nat} [NeZero n] (g : Profile n) :
    pCoordinateB (pGaugeCoordinate g) = 0 := by
  funext i j k
  change
    0 +
      explicitCyclicPrimitive n (shiftZero k 0) (i + j) = 0
  rw [map_zero (shiftZero k), map_zero (explicitCyclicPrimitive n)]
  rfl

noncomputable def pGaugeAmbient
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] PBlockMultiplierSolution n :=
  pCoordinateBuild.comp pGaugeCoordinate

theorem pGaugeAmbient_mem
    {n : Nat} [NeZero n] (g : Profile n) :
    pGaugeAmbient g ∈ PBlockMultiplierGauge n := by
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  change pCoordinateB (pGaugeCoordinate g) = 0
  exact pGaugeCoordinate_B_zero g

noncomputable def pGaugeBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] PBlockMultiplierGauge n :=
  LinearMap.codRestrict (PBlockMultiplierGauge n)
    pGaugeAmbient pGaugeAmbient_mem

set_option synthInstance.maxHeartbeats 200000 in
-- The nested kernel-of-kernel subtype needs a larger deterministic instance budget.
noncomputable def pGaugeRead
    {n : Nat} [NeZero n] :
    PBlockMultiplierGauge n →ₗ[F] Profile n where
  toFun z := fun i => z.1.1.2 i 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The nested kernel-of-kernel subtype needs a larger deterministic instance budget.
theorem pGaugeRead_build
    {n : Nat} [NeZero n] (g : Profile n) :
    pGaugeRead (pGaugeBuild g) = g := by
  funext i
  change (pCoordinateBuild (pGaugeCoordinate g)).1.2 i 0 0 = g i
  rw [pCoordinateBuild_lambda]
  simp only [pCoordinateLambda, pGaugeCoordinate,
    LinearMap.coe_mk, AddHom.coe_mk, add_zero]
  change
    g i +
      explicitCyclicPrimitive n (shiftZero i 0) 0 = g i
  rw [map_zero (shiftZero i), map_zero (explicitCyclicPrimitive n)]
  simp

set_option synthInstance.maxHeartbeats 200000 in
-- The nested kernel-of-kernel subtype needs a larger deterministic instance budget.
theorem pGauge_left_zero
    {n : Nat} [NeZero n] (z : PBlockMultiplierGauge n) :
    z.1.1.1.1 = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  exact congrArg Subtype.val hz

set_option synthInstance.maxHeartbeats 200000 in
-- The nested kernel-of-kernel subtype needs a larger deterministic instance budget.
theorem pGauge_coordinate_read
    {n : Nat} [NeZero n] (z : PBlockMultiplierGauge n) :
    pCoordinateRead z.1 = pGaugeCoordinate (pGaugeRead z) := by
  apply Prod.ext
  · apply Prod.ext
    · funext k
      change z.1.1.1.1 0 0 k = 0
      rw [pGauge_left_zero z]
      rfl
    · apply Subtype.ext
      funext s
      change cubeDiffI z.1.1.1.1 0 0 s = 0
      rw [pGauge_left_zero z, map_zero]
      rfl
  · funext i
    change z.1.1.2 i 0 0 = z.1.1.2 i 0 0
    rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The nested kernel-of-kernel subtype needs a larger deterministic instance budget.
theorem pGaugeBuild_read
    {n : Nat} [NeZero n] (z : PBlockMultiplierGauge n) :
    pGaugeBuild (pGaugeRead z) = z := by
  apply Subtype.ext
  change
    pCoordinateBuild (pGaugeCoordinate (pGaugeRead z)) = z.1
  rw [← pGauge_coordinate_read z]
  exact pCoordinateBuild_read z.1

set_option synthInstance.maxHeartbeats 200000 in
-- The nested kernel-of-kernel subtype needs a larger deterministic instance budget.
noncomputable def pGaugeEquiv
    {n : Nat} [NeZero n] :
    PBlockMultiplierGauge n ≃ₗ[F] Profile n where
  toLinearMap := pGaugeRead
  invFun := pGaugeBuild
  left_inv := pGaugeBuild_read
  right_inv := pGaugeRead_build

set_option synthInstance.maxHeartbeats 200000 in
-- The nested kernel-of-kernel subtype needs a larger deterministic instance budget.
theorem finrank_PBlockMultiplierGauge
    {n : Nat} [NeZero n] :
    Module.finrank F (PBlockMultiplierGauge n) = n := by
  rw [LinearEquiv.finrank_eq (pGaugeEquiv (n := n))]
  exact finrank_profile

noncomputable def pLeftRead
    {n : Nat} [NeZero n] :
    PBlockLeft n →ₗ[F] MatrixProfile n where
  toFun B := fun s k => B.1 0 s k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pLeftBuildRaw
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] CyclicCube n where
  toFun M := fun i j k => M (i + j) k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pLeftBuildRaw_mem
    {n : Nat} [NeZero n] (M : MatrixProfile n) :
    pLeftBuildRaw M ∈ PBlockLeft n := by
  apply LinearMap.mem_ker.mpr
  funext i j k
  rw [cubeDiffP_apply (n := n)]
  change M (i + j) k + M ((i + 1) + (j - 1)) k = 0
  rw [show (i + 1) + (j - 1) = i + j by abel]
  exact module_add_self _

noncomputable def pLeftBuild
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] PBlockLeft n :=
  LinearMap.codRestrict (PBlockLeft n)
    pLeftBuildRaw pLeftBuildRaw_mem

noncomputable def pLeftEquiv
    {n : Nat} [NeZero n] :
    PBlockLeft n ≃ₗ[F] MatrixProfile n where
  toLinearMap := pLeftRead
  invFun := pLeftBuild
  left_inv B := by
    apply Subtype.ext
    funext i j k
    change B.1 0 (i + j) k = B.1 i j k
    exact (pInvariant B i j k).symm
  right_inv M := by
    funext s k
    change M (0 + s) k = M s k
    rw [zero_add]

theorem finrank_PBlockLeft
    {n : Nat} [NeZero n] :
    Module.finrank F (PBlockLeft n) = n ^ 2 := by
  rw [LinearEquiv.finrank_eq (pLeftEquiv (n := n))]
  simp [MatrixProfile, Module.finrank_pi_fintype,
    I, ZMod.card, pow_two]

theorem finrank_PBlockLeftKernel
    {n : Nat} [NeZero n] :
    Module.finrank F (PBlockLeftKernel n) = 2 * n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (pBlockProjection (n := n))
  rw [range_pBlockProjection_eq_leftKernel] at h
  have hker :
      LinearMap.ker (pBlockProjection (n := n)) =
        PBlockMultiplierGauge n := rfl
  rw [hker, finrank_PBlockMultiplierGauge,
    finrank_PBlockMultiplierSolution] at h
  omega

theorem rank_pBlockCross
    {n : Nat} [NeZero n] :
    Module.finrank F
      (LinearMap.range (pBlockCross (n := n))) =
      (n - 1) ^ 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (pBlockCross (n := n))
  rw [finrank_PBlockLeftKernel, finrank_PBlockLeft] at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_sub_one] at h ⊢
  have hsub : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [hsub] at h
  have hsquare : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by
    ring
  rw [hsquare] at h
  omega

/-! The second block is the literal `i ↔ k`, `p ↔ r` transport. -/

noncomputable def swapIK
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f k j i
  invFun f := fun i j k => f k j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem swapIK_swapIK
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (swapIK f) = f := rfl

theorem swapIK_cubeDiffK
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffK f) = cubeDiffI (swapIK f) := by
  funext i j k
  rw [cubeDiffI_apply (n := n)]
  change
    cubeDiffK f k j i =
      f k j i + f k j (i + 1)
  rw [cubeDiffK_apply (n := n)]

theorem swapIK_cubeDiffR
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffR f) = cubeDiffP (swapIK f) := by
  funext i j k
  rw [cubeDiffP_apply (n := n)]
  change
    cubeDiffR f k j i =
      f k j i + f k (j - 1) (i + 1)
  rw [cubeDiffR_apply (n := n)]

theorem swapIK_cubeDiffP
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffP f) = cubeDiffR (swapIK f) := by
  apply (swapIK (n := n)).injective
  rw [swapIK_swapIK, swapIK_cubeDiffR, swapIK_swapIK]

theorem swapIK_cubeDiffJInv
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffJInv f) =
      cubeDiffJInv (swapIK f) := by
  funext i j k
  rw [cubeDiffJInv_apply (n := n)]
  change
    cubeDiffJInv f k j i =
      f k j i + f k (j - 1) i
  rw [cubeDiffJInv_apply (n := n)]

def indexSwapIK {n : Nat} :
    (I n × I n × I n) ≃ (I n × I n × I n) where
  toFun q := (q.2.2, (q.2.1, q.1))
  invFun q := (q.2.2, (q.2.1, q.1))
  left_inv q := by
    rcases q with ⟨i, ⟨j, k⟩⟩
    rfl
  right_inv q := by
    rcases q with ⟨i, ⟨j, k⟩⟩
    rfl

theorem cubeDot_swap_left
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot (swapIK x) y = cubeDot x (swapIK y) := by
  rw [cubeDot, cubeDot]
  apply Fintype.sum_equiv indexSwapIK
  intro q
  rfl

theorem cubeDot_swap_both
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot (swapIK x) (swapIK y) = cubeDot x y := by
  rw [cubeDot_swap_left, swapIK_swapIK]

noncomputable def rLeftEquivP
    {n : Nat} [NeZero n] :
    RBlockLeft n ≃ₗ[F] PBlockLeft n where
  toFun B := ⟨swapIK B.1, by
    apply LinearMap.mem_ker.mpr
    rw [← swapIK_cubeDiffR, LinearMap.mem_ker.mp B.2, map_zero]⟩
  invFun B := ⟨swapIK B.1, by
    apply LinearMap.mem_ker.mpr
    rw [← swapIK_cubeDiffP, LinearMap.mem_ker.mp B.2, map_zero]⟩
  left_inv B := by
    apply Subtype.ext
    exact swapIK_swapIK B.1
  right_inv B := by
    apply Subtype.ext
    exact swapIK_swapIK B.1
  map_add' B C := by
    apply Subtype.ext
    exact map_add swapIK B.1 C.1
  map_smul' r B := by
    apply Subtype.ext
    exact map_smul swapIK r B.1

noncomputable def pReachEquivR
    {n : Nat} [NeZero n] :
    PReachRight n ≃ₗ[F] RReachRight n where
  toFun A := ⟨swapIK A.1, by
    rcases A.2 with ⟨X, hX⟩
    refine ⟨swapIK X, ?_⟩
    rw [← swapIK_cubeDiffJInv, ← swapIK_cubeDiffP, hX]⟩
  invFun A := ⟨swapIK A.1, by
    rcases A.2 with ⟨X, hX⟩
    refine ⟨swapIK X, ?_⟩
    rw [← swapIK_cubeDiffJInv, ← swapIK_cubeDiffR, hX]⟩
  left_inv A := by
    apply Subtype.ext
    exact swapIK_swapIK A.1
  right_inv A := by
    apply Subtype.ext
    exact swapIK_swapIK A.1
  map_add' A C := by
    apply Subtype.ext
    exact map_add swapIK A.1 C.1
  map_smul' r A := by
    apply Subtype.ext
    exact map_smul swapIK r A.1

theorem blockCross_swap
    {n : Nat} [NeZero n] (B : RBlockLeft n)
    (A : PReachRight n) :
    pBlockCross (rLeftEquivP B) (pReachEquivR A) =
      rBlockCross B A := by
  change
    cubeDot (cubeDiffI (swapIK B.1)) (swapIK A.1) =
      cubeDot (cubeDiffK B.1) A.1
  rw [← swapIK_cubeDiffK, cubeDot_swap_both]

theorem rBlock_mem_ker_iff
    {n : Nat} [NeZero n] (B : RBlockLeft n) :
    B ∈ LinearMap.ker (rBlockCross (n := n)) ↔
      rLeftEquivP B ∈ PBlockLeftKernel n := by
  constructor
  · intro hB
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    let A0 : PReachRight n := (pReachEquivR (n := n)).symm A
    have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp hB) A0
    rw [← blockCross_swap B A0] at hz
    simpa [A0] using hz
  · intro hB
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp hB)
      (pReachEquivR A)
    rw [blockCross_swap B A] at hz
    exact hz

noncomputable def rBlockKernelEquivP
    {n : Nat} [NeZero n] :
    LinearMap.ker (rBlockCross (n := n)) ≃ₗ[F]
      PBlockLeftKernel n where
  toFun B := ⟨rLeftEquivP B.1, (rBlock_mem_ker_iff B.1).mp B.2⟩
  invFun B := ⟨(rLeftEquivP (n := n)).symm B.1,
    (rBlock_mem_ker_iff ((rLeftEquivP (n := n)).symm B.1)).mpr
      (by
        rw [LinearEquiv.apply_symm_apply]
        exact B.2)⟩
  left_inv B := by
    apply Subtype.ext
    exact (rLeftEquivP (n := n)).symm_apply_apply B.1
  right_inv B := by
    apply Subtype.ext
    exact (rLeftEquivP (n := n)).apply_symm_apply B.1
  map_add' B C := by
    apply Subtype.ext
    exact map_add rLeftEquivP B.1 C.1
  map_smul' r B := by
    apply Subtype.ext
    exact map_smul rLeftEquivP r B.1

theorem rank_rBlockCross
    {n : Nat} [NeZero n] :
    Module.finrank F
      (LinearMap.range (rBlockCross (n := n))) =
      (n - 1) ^ 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (rBlockCross (n := n))
  have hsource :
      Module.finrank F (RBlockLeft n) = n ^ 2 :=
    (LinearEquiv.finrank_eq (rLeftEquivP (n := n))).trans
      finrank_PBlockLeft
  have hker :
      Module.finrank F (LinearMap.ker (rBlockCross (n := n))) =
        2 * n - 1 :=
    (LinearEquiv.finrank_eq (rBlockKernelEquivP (n := n))).trans
      finrank_PBlockLeftKernel
  rw [hsource, hker] at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_sub_one] at h ⊢
  have hsub : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [hsub] at h
  have hsquare : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
  rw [hsquare] at h
  omega

/-! The literal full source projects onto the two independent active blocks. -/

noncomputable def activeLeftProjection
    {n : Nat} [NeZero n] :
    DiamondEEOELeftSource n →ₗ[F]
      (PBlockLeft n × RBlockLeft n) where
  toFun l := by
    have h := LinearMap.mem_ker.mp l.2
    exact
      (⟨l.1.1.1, congrArg
          (fun q : ((CyclicCube n × CyclicCube n) × CyclicCube n) =>
            q.1.1) h⟩,
       ⟨l.1.2.1, congrArg
          (fun q : ((CyclicCube n × CyclicCube n) × CyclicCube n) =>
            q.1.2) h⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def activeLeftSection
    {n : Nat} [NeZero n] :
    (PBlockLeft n × RBlockLeft n) →ₗ[F]
      DiamondEEOELeftSource n where
  toFun q :=
    ⟨((q.1.1, 0), (q.2.1, 0)), by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · apply Prod.ext
        · exact LinearMap.mem_ker.mp q.1.2
        · exact LinearMap.mem_ker.mp q.2.2
      · change cubeDiffP 0 + cubeDiffR 0 = 0
        simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem activeLeftProjection_section
    {n : Nat} [NeZero n] (q : PBlockLeft n × RBlockLeft n) :
    activeLeftProjection (activeLeftSection q) = q := rfl

theorem activeLeftProjection_surjective
    {n : Nat} [NeZero n] :
    Function.Surjective (activeLeftProjection (n := n)) :=
  fun q => ⟨activeLeftSection q, activeLeftProjection_section q⟩

noncomputable def activeRightProjection
    {n : Nat} [NeZero n] :
  DiamondEEOERightSource n →ₗ[F]
      (RReachRight n × PReachRight n) where
  toFun A :=
    (⟨A.1.1.2, A.2.2.1⟩,
      ⟨A.1.2.1, A.2.2.2.1⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def activeRightSection
    {n : Nat} [NeZero n] :
    (RReachRight n × PReachRight n) →ₗ[F]
      DiamondEEOERightSource n where
  toFun A :=
    ⟨((0, A.1.1), (A.2.1, 0)), by
      constructor
      · simp
      constructor
      · exact A.1.2
      constructor
      · exact A.2.2
      · exact (LinearMap.range
          (LinearMap.coprod (cubeDiffP (n := n))
            (cubeDiffR (n := n)))).zero_mem⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem activeRightProjection_section
    {n : Nat} [NeZero n]
    (A : RReachRight n × PReachRight n) :
    activeRightProjection (activeRightSection A) = A := rfl

noncomputable def liftPBlockDual
    {n : Nat} [NeZero n] :
    Module.Dual F (RReachRight n) →ₗ[F]
      Module.Dual F (RReachRight n × PReachRight n) where
  toFun phi := phi.comp
    (LinearMap.fst F (RReachRight n) (PReachRight n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def liftRBlockDual
    {n : Nat} [NeZero n] :
    Module.Dual F (PReachRight n) →ₗ[F]
      Module.Dual F (RReachRight n × PReachRight n) where
  toFun phi := phi.comp
    (LinearMap.snd F (RReachRight n) (PReachRight n))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def blockPairCross
    {n : Nat} [NeZero n] :
    (PBlockLeft n × RBlockLeft n) →ₗ[F]
      Module.Dual F (RReachRight n × PReachRight n) :=
  LinearMap.coprod
    (liftPBlockDual.comp pBlockCross)
    (liftRBlockDual.comp rBlockCross)

theorem sourceAggregateConstraint
    {n : Nat} [NeZero n] (l : DiamondEEOELeftSource n) :
    cubeDiffP (l.1.1.1 + l.1.1.2) +
      cubeDiffR (l.1.2.1 + l.1.2.2) = 0 := by
  have h := LinearMap.mem_ker.mp l.2
  have hP0 : cubeDiffP l.1.1.1 = 0 :=
    congrArg (fun q => q.1.1) h
  have hR0 : cubeDiffR l.1.2.1 = 0 :=
    congrArg (fun q => q.1.2) h
  have h1 : cubeDiffP l.1.1.2 + cubeDiffR l.1.2.2 = 0 :=
    congrArg Prod.snd h
  rw [map_add, map_add, hP0, hR0, zero_add, zero_add]
  exact h1

def sourceMarginalLambda
    {n : Nat} [NeZero n]
    (l : DiamondEEOELeftSource n) : CyclicCube n :=
  fun i j k =>
    (l.1.1.1 + l.1.1.2) (i + 1) (j - 1) k +
      (l.1.2.1 + l.1.2.2) i (j - 1) (k + 1)

theorem sourceR00_eq_jStar
    {n : Nat} [NeZero n] (l : DiamondEEOELeftSource n) :
    cubeDiffI (l.1.1.1 + l.1.1.2) +
      cubeDiffK (l.1.2.1 + l.1.2.2) =
      cubeDiffJStar (sourceMarginalLambda l) := by
  let B := l.1.1.1 + l.1.1.2
  let W := l.1.2.1 + l.1.2.2
  have hs := sourceAggregateConstraint l
  funext i j k
  have hsijk := congrFun (congrFun (congrFun hs i) j) k
  simp only [Pi.add_apply, Pi.zero_apply] at hsijk ⊢
  rw [cubeDiffP_apply (n := n), cubeDiffR_apply (n := n)] at hsijk
  rw [cubeDiffI_apply (n := n), cubeDiffK_apply (n := n),
    cubeDiffJStar_apply (n := n)]
  change
    (B i j k + B (i + 1) j k) +
      (W i j k + W i j (k + 1)) =
    (B (i + 1) (j - 1) k + W i (j - 1) (k + 1)) +
      (B (i + 1) ((j + 1) - 1) k +
        W i ((j + 1) - 1) (k + 1))
  change
    (B i j k + B (i + 1) (j - 1) k) +
      (W i j k + W i (j - 1) (k + 1)) = 0 at hsijk
  rw [show (j + 1) - 1 = j by abel]
  have hEq :
      B i j k + W i j k =
        B (i + 1) (j - 1) k +
          W i (j - 1) (k + 1) := by
    apply eq_of_add_eq_zero
    calc
      (B i j k + W i j k) +
          (B (i + 1) (j - 1) k +
            W i (j - 1) (k + 1)) =
        (B i j k + B (i + 1) (j - 1) k) +
          (W i j k + W i (j - 1) (k + 1)) := by abel
      _ = 0 := hsijk
  calc
    (B i j k + B (i + 1) j k) +
        (W i j k + W i j (k + 1)) =
      (B i j k + W i j k) +
        (B (i + 1) j k + W i j (k + 1)) := by abel
    _ =
      (B (i + 1) (j - 1) k +
          W i (j - 1) (k + 1)) +
        (B (i + 1) j k + W i j (k + 1)) := by rw [hEq]

theorem sourceA00_pairing_zero
    {n : Nat} [NeZero n] (l : DiamondEEOELeftSource n)
    (A : DiamondEEOERightSource n) :
    cubeDot
      (cubeDiffI (l.1.1.1 + l.1.1.2) +
        cubeDiffK (l.1.2.1 + l.1.2.2)) A.1.1.1 = 0 := by
  rw [sourceR00_eq_jStar, cubeDiffJ_pairing_adjoint, A.2.1]
  simp [cubeDot]

theorem fullPhase_split
    {n : Nat} [NeZero n] (l : DiamondEEOELeftSource n)
    (A : DiamondEEOERightSource n) :
    diamondEEOECross l A =
      blockPairCross (activeLeftProjection l)
        (activeRightProjection A) := by
  have h00 := sourceA00_pairing_zero l A
  change
    cubeDot
        (cubeDiffI (l.1.1.1 + l.1.1.2) +
          cubeDiffK (l.1.2.1 + l.1.2.2)) A.1.1.1 +
      cubeDot (cubeDiffI l.1.1.1) A.1.1.2 +
      cubeDot (cubeDiffK l.1.2.1) A.1.2.1 +
      cubeDot 0 A.1.2.2 =
    cubeDot (cubeDiffI l.1.1.1) A.1.1.2 +
      cubeDot (cubeDiffK l.1.2.1) A.1.2.1
  rw [h00]
  simp [cubeDot]

abbrev BlockPairKernelCoordinates
    (n : Nat) [NeZero n] :=
  PBlockLeftKernel n ×
    LinearMap.ker (rBlockCross (n := n))

noncomputable def blockPairKernelRead
    {n : Nat} [NeZero n] :
    LinearMap.ker (blockPairCross (n := n)) →ₗ[F]
      BlockPairKernelCoordinates n where
  toFun z := by
    have hz := LinearMap.mem_ker.mp z.2
    have hp : z.1.1 ∈ PBlockLeftKernel n := by
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro A
      have hA := LinearMap.congr_fun hz
        (A, (0 : PReachRight n))
      change pBlockCross z.1.1 A + rBlockCross z.1.2 0 = 0 at hA
      simpa using hA
    have hr : z.1.2 ∈ LinearMap.ker (rBlockCross (n := n)) := by
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro A
      have hA := LinearMap.congr_fun hz
        ((0 : RReachRight n), A)
      change pBlockCross z.1.1 0 + rBlockCross z.1.2 A = 0 at hA
      simpa using hA
    exact (⟨z.1.1, hp⟩, ⟨z.1.2, hr⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def blockPairKernelBuild
    {n : Nat} [NeZero n] :
    BlockPairKernelCoordinates n →ₗ[F]
      LinearMap.ker (blockPairCross (n := n)) where
  toFun q := ⟨(q.1.1, q.2.1), by
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hp := LinearMap.congr_fun (LinearMap.mem_ker.mp q.1.2) A.1
    have hr := LinearMap.congr_fun (LinearMap.mem_ker.mp q.2.2) A.2
    change pBlockCross q.1.1 A.1 + rBlockCross q.2.1 A.2 = 0
    rw [hp, hr]
    simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def blockPairKernelEquiv
    {n : Nat} [NeZero n] :
    LinearMap.ker (blockPairCross (n := n)) ≃ₗ[F]
      BlockPairKernelCoordinates n where
  toLinearMap := blockPairKernelRead
  invFun := blockPairKernelBuild
  left_inv _ := rfl
  right_inv _ := rfl

theorem rank_blockPairCross
    {n : Nat} [NeZero n] :
    Module.finrank F
      (LinearMap.range (blockPairCross (n := n))) =
      2 * (n - 1) ^ 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (blockPairCross (n := n))
  have hsource :
      Module.finrank F (PBlockLeft n × RBlockLeft n) =
        n ^ 2 + n ^ 2 := by
    rw [Module.finrank_prod, finrank_PBlockLeft]
    exact congrArg (n ^ 2 + ·)
      ((LinearEquiv.finrank_eq
        (rLeftEquivP (n := n))).trans finrank_PBlockLeft)
  have hker :
      Module.finrank F
          (LinearMap.ker (blockPairCross (n := n))) =
        (2 * n - 1) + (2 * n - 1) := by
    rw [LinearEquiv.finrank_eq
      (blockPairKernelEquiv (n := n)),
      Module.finrank_prod, finrank_PBlockLeftKernel]
    exact congrArg (2 * n - 1 + ·)
      ((LinearEquiv.finrank_eq
        (rBlockKernelEquivP (n := n))).trans
          finrank_PBlockLeftKernel)
  rw [hsource, hker] at h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_sub_one] at h ⊢
  have hsub : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [hsub] at h
  have hid :
      (m + 1) ^ 2 + (m + 1) ^ 2 =
        2 * m ^ 2 + ((2 * m + 1) + (2 * m + 1)) := by
    ring
  rw [hid] at h
  omega

theorem rank_blockPairCross_add
    {n : Nat} [NeZero n] :
    Module.finrank F
      (LinearMap.range (blockPairCross (n := n))) =
      Module.finrank F
          (LinearMap.range (pBlockCross (n := n))) +
        Module.finrank F
          (LinearMap.range (rBlockCross (n := n))) := by
  rw [rank_blockPairCross, rank_pBlockCross, rank_rBlockCross]
  ring

noncomputable def reducedCrossOnFull
    {n : Nat} [NeZero n] :
    DiamondEEOELeftSource n →ₗ[F]
      Module.Dual F (RReachRight n × PReachRight n) :=
  blockPairCross.comp activeLeftProjection

theorem ker_fullCross_eq_reducedCross
    {n : Nat} [NeZero n] :
    LinearMap.ker (diamondEEOECross (n := n)) =
      LinearMap.ker (reducedCrossOnFull (n := n)) := by
  ext l
  constructor
  · intro hl
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hfull := LinearMap.congr_fun
      (LinearMap.mem_ker.mp hl) (activeRightSection A)
    rw [fullPhase_split] at hfull
    simpa [reducedCrossOnFull] using hfull
  · intro hl
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hred := LinearMap.congr_fun
      (LinearMap.mem_ker.mp hl) (activeRightProjection A)
    rw [fullPhase_split]
    simpa [reducedCrossOnFull] using hred

theorem range_reducedCrossOnFull_eq_blockPair
    {n : Nat} [NeZero n] :
    LinearMap.range (reducedCrossOnFull (n := n)) =
      LinearMap.range (blockPairCross (n := n)) := by
  apply le_antisymm
  · rintro _ ⟨l, rfl⟩
    exact ⟨activeLeftProjection l, rfl⟩
  · rintro _ ⟨q, rfl⟩
    rcases activeLeftProjection_surjective q with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    change blockPairCross (activeLeftProjection l) = blockPairCross q
    rw [hl]

theorem rank_fullCross_eq_blockPair
    {n : Nat} [NeZero n] :
    Module.finrank F
      (LinearMap.range (diamondEEOECross (n := n))) =
      Module.finrank F
        (LinearMap.range (blockPairCross (n := n))) := by
  have hfull := LinearMap.finrank_range_add_finrank_ker
    (diamondEEOECross (n := n))
  have hred := LinearMap.finrank_range_add_finrank_ker
    (reducedCrossOnFull (n := n))
  rw [ker_fullCross_eq_reducedCross] at hfull
  rw [range_reducedCrossOnFull_eq_blockPair] at hred
  omega

theorem rank_fullCross
    {n : Nat} [NeZero n] :
    Module.finrank F
      (LinearMap.range (diamondEEOECross (n := n))) =
      2 * (n - 1) ^ 2 := by
  rw [rank_fullCross_eq_blockPair, rank_blockPairCross]






end EEOEInternal

theorem rank_diamondEvenP_cross_EEOE_scalar
    {n : Nat} [NeZero n] (_hn2 : 2 ≤ n) (_hn : Even n) :
    Module.finrank F
      (LinearMap.range (diamondEEOECross (n := n))) =
      2 * (n - 1) ^ 2 :=
  EEOEInternal.rank_fullCross

end

end Core4loop.SquareDiagonal.EvenP
