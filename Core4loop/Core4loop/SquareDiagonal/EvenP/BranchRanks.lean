import Core4loop.SquareDiagonal.EvenP.BWSymmetry
import Core4loop.SquareDiagonal.EvenP.EEEE

open scoped BigOperators

set_option linter.unnecessarySeqFocus false

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 500000

/-!
Literal scalar carriers and scalar cross ranks for the even-`P` Diamond
branches.  This file deliberately stops before the pointed tail/source split.
-/

/-! ### The literal EOOO carrier -/

abbrev DiamondEOOOLeftAmbient (n : Nat) :=
  CyclicCube n × CyclicCube n

noncomputable def diamondEOOOLeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEOOOLeftAmbient n →ₗ[F] CyclicCube n :=
  LinearMap.coprod cubeDiffP cubeDiffR

noncomputable abbrev DiamondEOOOLeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEOOOLeftConstraintMap (n := n))

noncomputable def diamondEOOOCoeffMap
    {n : Nat} [NeZero n] :
    DiamondEOOOLeftAmbient n →ₗ[F] CyclicCube n :=
  LinearMap.coprod cubeDiffI cubeDiffK

noncomputable def DiamondEOOORightSource
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  (LinearMap.range
    (LinearMap.coprod (cubeDiffP (n := n))
      (cubeDiffR (n := n)))).comap
        (cubeDiffJInv (n := n))

noncomputable def diamondEOOOCross
    {n : Nat} [NeZero n] :
    DiamondEOOOLeftSource n →ₗ[F]
      Module.Dual F (DiamondEOOORightSource n) :=
  (BWSymmetryInternal.restrictDual (DiamondEOOORightSource n)).comp
    (EEOEInternal.cubeDotDual.comp
      (diamondEOOOCoeffMap.comp (DiamondEOOOLeftSource n).subtype))

noncomputable abbrev DiamondEOOOLeftKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEOOOCross (n := n))

/-! ### The literal EOEO carrier -/

abbrev DiamondEOEOLeftAmbient (n : Nat) :=
  (CyclicCube n × CyclicCube n) ×
    (CyclicCube n × CyclicCube n)

abbrev DiamondEOEORightAmbient (n : Nat) :=
  CyclicCube n × CyclicCube n

noncomputable def diamondEOEOLeftConstraintMap
    {n : Nat} [NeZero n] :
    DiamondEOEOLeftAmbient n →ₗ[F] CyclicCube n where
  toFun l := cubeDiffP l.1.1 + cubeDiffR l.2.1
  map_add' x y := by
    ext
    simp
    abel
  map_smul' r x := by
    ext
    simp [mul_add]

noncomputable abbrev DiamondEOEOLeftSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondEOEOLeftConstraintMap (n := n))

noncomputable def diamondEOEOCoeffMap
    {n : Nat} [NeZero n] :
    DiamondEOEOLeftAmbient n →ₗ[F] DiamondEOEORightAmbient n where
  toFun l :=
    (cubeDiffI (l.1.1 + l.1.2) +
        cubeDiffK (l.2.1 + l.2.2),
      cubeDiffI l.1.1 + cubeDiffK l.2.1)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp

noncomputable def DiamondEOEORightSource
    (n : Nat) [NeZero n] :
    Submodule F (DiamondEOEORightAmbient n) :=
  ((LinearMap.range
      (LinearMap.coprod (cubeDiffP (n := n))
        (cubeDiffR (n := n)))).comap
      (cubeDiffJInv (n := n))).prod ⊤

noncomputable def diamondEOEOCross
    {n : Nat} [NeZero n] :
    DiamondEOEOLeftSource n →ₗ[F]
      Module.Dual F (DiamondEOEORightSource n) :=
  (BWSymmetryInternal.restrictDual (DiamondEOEORightSource n)).comp
    (BWSymmetryInternal.pairPairing.comp
      (diamondEOEOCoeffMap.comp (DiamondEOEOLeftSource n).subtype))

/-! ### Common starred-invariant coordinates -/

namespace BranchRanksInternal

noncomputable def cubePRStarMap
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] (CyclicCube n × CyclicCube n) :=
  LinearMap.prod cubeDiffPStar cubeDiffRStar

noncomputable def LambdaPR
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (cubePRStarMap (n := n))

theorem lambdaPR_conditions
    {n : Nat} [NeZero n] (z : LambdaPR n) :
    cubeDiffPStar z.1 = 0 ∧ cubeDiffRStar z.1 = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩

theorem lambdaPR_invariant
    {n : Nat} [NeZero n] (z : LambdaPR n)
    (i j k : I n) :
    z.1 i j k = z.1 (i + j + k) 0 0 := by
  have hc := lambdaPR_conditions z
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) :=
    ⟨z.1, hc.1⟩
  let zr : LinearMap.ker (cubeDiffRStar (n := n)) :=
    ⟨z.1, hc.2⟩
  calc
    z.1 i j k = z.1 i 0 (j + k) :=
      EEEEInternal.rStar_invariant zr i j k
    _ = z.1 i (j + k) 0 := by
      simpa using
        (EEEEInternal.rStar_invariant zr i (j + k) 0).symm
    _ = z.1 (i + (j + k)) 0 0 :=
      EEEEInternal.pStar_invariant zp i (j + k) 0
    _ = z.1 (i + j + k) 0 0 := by rw [add_assoc]

noncomputable def lambdaPRRead
    {n : Nat} [NeZero n] :
    LambdaPR n →ₗ[F] Profile n where
  toFun z := fun t => z.1 t 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def lambdaPRBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] LambdaPR n where
  toFun h :=
    ⟨fun i j k => h (i + j + k), by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext <;> funext i j k
      · change
          h (i + j + k) +
            h ((i + (-1)) + (j + 1) + (k + 0)) = 0
        rw [show (i + (-1)) + (j + 1) + (k + 0) =
          i + j + k by abel]
        exact F_add_self _
      · change
          h (i + j + k) +
            h ((i + 0) + (j + 1) + (k + (-1))) = 0
        rw [show (i + 0) + (j + 1) + (k + (-1)) =
          i + j + k by abel]
        exact F_add_self _⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def lambdaPREquiv
    {n : Nat} [NeZero n] :
    LambdaPR n ≃ₗ[F] Profile n where
  toFun := lambdaPRRead
  invFun := lambdaPRBuild
  left_inv z := by
    apply Subtype.ext
    funext i j k
    exact (lambdaPR_invariant z i j k).symm
  right_inv h := by
    funext t
    change h (t + 0 + 0) = h t
    simp
  map_add' := map_add lambdaPRRead
  map_smul' := map_smul lambdaPRRead

theorem finrank_LambdaPR
    {n : Nat} [NeZero n] :
    Module.finrank F (LambdaPR n) = n := by
  rw [LinearEquiv.finrank_eq (lambdaPREquiv (n := n))]
  exact finrank_profile

theorem lambdaPR_cubeDiffR
    {n : Nat} [NeZero n] (z : LambdaPR n) :
    cubeDiffR z.1 = 0 := by
  funext i j k
  change z.1 i j k + z.1 (i + 0) (j + (-1)) (k + 1) = 0
  rw [lambdaPR_invariant z i j k,
    lambdaPR_invariant z (i + 0) (j + (-1)) (k + 1)]
  rw [show i + 0 + (j + (-1)) + (k + 1) =
    i + j + k by abel]
  exact F_add_self _

theorem lambdaPR_cubeDiffK_eq_JStar
    {n : Nat} [NeZero n] (z : LambdaPR n) :
    cubeDiffK z.1 = cubeDiffJStar z.1 := by
  funext i j k
  change
    z.1 i j k + z.1 (i + 0) (j + 0) (k + 1) =
      z.1 i j k + z.1 (i + 0) (j + 1) (k + 0)
  congr 1
  rw [lambdaPR_invariant z (i + 0) (j + 0) (k + 1),
    lambdaPR_invariant z (i + 0) (j + 1) (k + 0)]
  abel

/-! ### EOOO multiplier factorization -/

abbrev EOOOMultiplierAmbient
    (n : Nat) [NeZero n] :=
  DiamondEOOOLeftSource n × CyclicCube n

noncomputable def eoooMultiplierConstraintMap
    {n : Nat} [NeZero n] :
    EOOOMultiplierAmbient n →ₗ[F]
      (CyclicCube n × CyclicCube n × CyclicCube n) where
  toFun z :=
    (diamondEOOOCoeffMap z.1.1 + cubeDiffJStar z.2,
      cubeDiffPStar z.2, cubeDiffRStar z.2)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable def EOOOMultiplierSolution
    (n : Nat) [NeZero n] :
    Submodule F (EOOOMultiplierAmbient n) :=
  LinearMap.ker (eoooMultiplierConstraintMap (n := n))

noncomputable def eoooProjection
    {n : Nat} [NeZero n] :
    EOOOMultiplierSolution n →ₗ[F] DiamondEOOOLeftSource n :=
  (LinearMap.fst F (DiamondEOOOLeftSource n) (CyclicCube n)).comp
    (EOOOMultiplierSolution n).subtype

noncomputable def EOOOMultiplierGauge
    (n : Nat) [NeZero n] :
    Submodule F (EOOOMultiplierSolution n) :=
  LinearMap.ker (eoooProjection (n := n))

noncomputable def eoooToFactors
    {n : Nat} [NeZero n] :
    EOOOMultiplierSolution n →ₗ[F]
      (LambdaPR n × CubePairPRDISolution n) where
  toFun z := by
    have hz := LinearMap.mem_ker.mp z.2
    have hp : cubeDiffPStar z.1.2 = 0 := by
      exact congrArg (fun x => x.2.1) hz
    have hr : cubeDiffRStar z.1.2 = 0 := by
      exact congrArg (fun x => x.2.2) hz
    let lambda : LambdaPR n :=
      ⟨z.1.2, LinearMap.mem_ker.mpr (Prod.ext hp hr)⟩
    refine (lambda, ⟨(z.1.1.1.1, z.1.1.1.2 + z.1.2), ?_⟩)
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · change
        cubeDiffP z.1.1.1.1 +
          cubeDiffR (z.1.1.1.2 + z.1.2) = 0
      rw [map_add, lambdaPR_cubeDiffR lambda, add_zero]
      exact LinearMap.mem_ker.mp z.1.1.2
    · have hcoeff : diamondEOOOCoeffMap z.1.1.1 +
          cubeDiffJStar z.1.2 = 0 :=
        congrArg Prod.fst hz
      change
        cubeDiffI z.1.1.1.1 +
          cubeDiffK (z.1.1.1.2 + z.1.2) = 0
      rw [map_add, lambdaPR_cubeDiffK_eq_JStar lambda]
      simpa [diamondEOOOCoeffMap, add_assoc] using hcoeff
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      ext <;> simp <;> abel
  map_smul' r z := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      ext <;> simp [smul_eq_mul]

noncomputable def eoooFromFactors
    {n : Nat} [NeZero n] :
    (LambdaPR n × CubePairPRDISolution n) →ₗ[F]
      EOOOMultiplierSolution n where
  toFun q := by
    let B := q.2.1.1
    let W := q.2.1.2 + q.1.1
    let lraw : DiamondEOOOLeftAmbient n := (B, W)
    have hq := LinearMap.mem_ker.mp q.2.2
    have hsource : lraw ∈ DiamondEOOOLeftSource n := by
      apply LinearMap.mem_ker.mpr
      have hpr : cubeDiffP B + cubeDiffR q.2.1.2 = 0 :=
        congrArg Prod.fst hq
      change cubeDiffP B + cubeDiffR W = 0
      rw [map_add, lambdaPR_cubeDiffR q.1, add_zero]
      exact hpr
    let l : DiamondEOOOLeftSource n := ⟨lraw, hsource⟩
    refine ⟨(l, q.1.1), ?_⟩
    apply LinearMap.mem_ker.mpr
    have hdi : cubeDiffI B + cubeDiffK q.2.1.2 = 0 :=
      congrArg Prod.snd hq
    apply Prod.ext
    · change
        cubeDiffI B + cubeDiffK W + cubeDiffJStar q.1.1 = 0
      rw [show cubeDiffK W =
          cubeDiffK q.2.1.2 + cubeDiffJStar q.1.1 by
            simp only [W, map_add, lambdaPR_cubeDiffK_eq_JStar q.1]]
      rw [← add_assoc, hdi, zero_add, EEEEInternal.cube_add_self]
    · apply Prod.ext
      · exact (lambdaPR_conditions q.1).1
      · exact (lambdaPR_conditions q.1).2
  map_add' q r := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp <;> abel
    · rfl
  map_smul' r q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp [smul_eq_mul]
    · rfl

noncomputable def eoooMultiplierEquiv
    {n : Nat} [NeZero n] :
    EOOOMultiplierSolution n ≃ₗ[F]
      (LambdaPR n × CubePairPRDISolution n) where
  toFun := eoooToFactors
  invFun := eoooFromFactors
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp [eoooToFactors, eoooFromFactors]
      rw [add_assoc, F_add_self, add_zero]
    · rfl
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      ext <;> simp [eoooToFactors, eoooFromFactors]
      rw [add_assoc, F_add_self, add_zero]
  map_add' := map_add eoooToFactors
  map_smul' := map_smul eoooToFactors

set_option maxHeartbeats 1200000 in
theorem range_eoooProjection_eq_leftKernel
    {n : Nat} [NeZero n] :
    LinearMap.range (eoooProjection (n := n)) =
      DiamondEOOOLeftKernel n := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hc := LinearMap.mem_ker.mp z.2
    have hRadd :
        diamondEOOOCoeffMap z.1.1.1 +
            cubeDiffJStar z.1.2 = 0 :=
      congrArg Prod.fst hc
    have hp : cubeDiffPStar z.1.2 = 0 :=
      congrArg (fun q => q.2.1) hc
    have hr : cubeDiffRStar z.1.2 = 0 :=
      congrArg (fun q => q.2.2) hc
    have hR :
        diamondEOOOCoeffMap z.1.1.1 =
          cubeDiffJStar z.1.2 :=
      EEEEInternal.cube_eq_of_add_eq_zero hRadd
    rcases A.2 with ⟨q, hq⟩
    change cubeDot (diamondEOOOCoeffMap z.1.1.1) A.1 = 0
    change
      cubeDiffP q.1 + cubeDiffR q.2 =
        cubeDiffJInv A.1 at hq
    rw [hR, cubeDiffJ_pairing_adjoint, ← hq,
      EEEEInternal.cubeDot_add_right,
      ← cubeDiffP_pairing_adjoint,
      ← cubeDiffR_pairing_adjoint, hp, hr]
    simp [cubeDot]
  · intro l hl
    let phi : Module.Dual F (CyclicCube n) :=
      EEOEInternal.cubeDotDual (diamondEOOOCoeffMap l.1)
    have hvanish :
        ∀ A : CyclicCube n,
          cubeDiffJInv A ∈
              LinearMap.range
                (LinearMap.coprod
                  (cubeDiffP (n := n)) (cubeDiffR (n := n))) →
            phi A = 0 := by
      intro A hA
      let As : DiamondEOOORightSource n := ⟨A, hA⟩
      have hz := LinearMap.mem_ker.mp hl
      exact LinearMap.congr_fun hz As
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        (cubeDiffJInv (n := n))
        (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))
        phi hvanish with
      ⟨psi, hphi, hann⟩
    rcases EEEEInternal.dual_exists_cubeDot psi with
      ⟨lambda, hlambda⟩
    have hR :
        diamondEOOOCoeffMap l.1 =
          cubeDiffJStar lambda := by
      apply EEEEInternal.cubeDot_left_ext
      intro A
      calc
        cubeDot (diamondEOOOCoeffMap l.1) A =
            phi A := rfl
        _ = psi (cubeDiffJInv A) :=
          LinearMap.congr_fun hphi A
        _ = cubeDot lambda (cubeDiffJInv A) :=
          hlambda _
        _ = cubeDot (cubeDiffJStar lambda) A :=
          (cubeDiffJ_pairing_adjoint lambda A).symm
    have hp : cubeDiffPStar lambda = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffPStar lambda) X =
            cubeDot lambda (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda X
        _ = psi (cubeDiffP X) := (hlambda _).symm
        _ = psi (cubeDiffP X + cubeDiffR 0) := by simp
        _ = 0 := hann (X, 0)
        _ = cubeDot 0 X := by simp [cubeDot]
    have hr : cubeDiffRStar lambda = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffRStar lambda) X =
            cubeDot lambda (cubeDiffR X) :=
          cubeDiffR_pairing_adjoint lambda X
        _ = psi (cubeDiffR X) := (hlambda _).symm
        _ = psi (cubeDiffP 0 + cubeDiffR X) := by simp
        _ = 0 := hann (0, X)
        _ = cubeDot 0 X := by simp [cubeDot]
    refine ⟨⟨(l, lambda), ?_⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    change
      (diamondEOOOCoeffMap l.1 + cubeDiffJStar lambda,
        cubeDiffPStar lambda, cubeDiffRStar lambda) = 0
    apply Prod.ext
    · rw [hR]
      exact EEEEInternal.cube_add_self _
    · apply Prod.ext
      · exact hp
      · exact hr

noncomputable def eoooGaugeToLambda11
    {n : Nat} [NeZero n] :
    EOOOMultiplierGauge n →ₗ[F] EEEEInternal.Lambda11Factor n where
  toFun z := by
    have hleft := LinearMap.mem_ker.mp z.2
    change z.1.1.1 = 0 at hleft
    have hc := LinearMap.mem_ker.mp z.1.2
    refine ⟨z.1.1.2, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · apply Prod.ext
      · have hcoeff := congrArg Prod.fst hc
        change
          diamondEOOOCoeffMap z.1.1.1 +
            cubeDiffJStar z.1.1.2 = 0 at hcoeff
        have hzcoeff :
            diamondEOOOCoeffMap z.1.1.1.1 = 0 := by
          rw [hleft]
          rfl
        change cubeDiffJStar z.1.1.2 = 0
        rw [hzcoeff, zero_add] at hcoeff
        exact hcoeff
      · exact congrArg (fun q => q.2.1) hc
    · exact congrArg (fun q => q.2.2) hc
  map_add' z w := by
    apply Subtype.ext
    rfl
  map_smul' r z := by
    apply Subtype.ext
    rfl

noncomputable def eoooGaugeFromLambda11
    {n : Nat} [NeZero n] :
    EEEEInternal.Lambda11Factor n →ₗ[F]
      EOOOMultiplierGauge n where
  toFun q := by
    have hq := EEEEInternal.lambda11_conditions q
    let l : DiamondEOOOLeftSource n := 0
    let z : EOOOMultiplierSolution n :=
      ⟨(l, q.1), by
        apply LinearMap.mem_ker.mpr
        apply Prod.ext
        · change 0 + cubeDiffJStar q.1 = 0
          simpa using hq.1
        · exact Prod.ext hq.2.1 hq.2.2⟩
    refine ⟨z, ?_⟩
    apply LinearMap.mem_ker.mpr
    rfl
  map_add' q r := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  map_smul' r q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

noncomputable def eoooGaugeEquivLambda11
    {n : Nat} [NeZero n] :
    EOOOMultiplierGauge n ≃ₗ[F]
      EEEEInternal.Lambda11Factor n where
  toFun := eoooGaugeToLambda11
  invFun := eoooGaugeFromLambda11
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact LinearMap.mem_ker.mp z.2 |>.symm
    · change z.1.1.2 = z.1.1.2
      rfl
  right_inv q := by
    apply Subtype.ext
    change q.1 = q.1
    rfl
  map_add' := map_add eoooGaugeToLambda11
  map_smul' := map_smul eoooGaugeToLambda11

theorem finrank_EOOOMultiplierSolution
    {n : Nat} [NeZero n] :
    Module.finrank F (EOOOMultiplierSolution n) =
      2 * n ^ 2 + 1 := by
  rw [LinearEquiv.finrank_eq (eoooMultiplierEquiv (n := n))]
  simp only [Module.finrank_prod, finrank_LambdaPR]
  have hpair := EEEEInternal.finrank_pair_addition_safe (n := n)
  omega

theorem finrank_EOOOMultiplierGauge
    {n : Nat} [NeZero n] :
    Module.finrank F (EOOOMultiplierGauge n) = 1 := by
  rw [LinearEquiv.finrank_eq
    (eoooGaugeEquivLambda11 (n := n))]
  exact EEEEInternal.finrank_Lambda11Factor

theorem finrank_EOOOLeftSource
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEOOOLeftSource n) = n ^ 3 + n := by
  have hs :
      DiamondEOOOLeftSource n = EEEEInternal.PRSource n := by
    rfl
  rw [hs]
  rw [LinearEquiv.finrank_eq
    (EEEEInternal.prSourceEquivStar (n := n))]
  exact finrank_ker_cubeStarIK

theorem finrank_EOOOLeftKernel
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEOOOLeftKernel n) =
      2 * n ^ 2 := by
  letI : FiniteDimensional F (EOOOMultiplierSolution n) :=
    FiniteDimensional.of_injective
      (EOOOMultiplierSolution n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (eoooProjection (n := n))
  rw [range_eoooProjection_eq_leftKernel] at h
  change
    Module.finrank F (DiamondEOOOLeftKernel n) +
      Module.finrank F (EOOOMultiplierGauge n) =
        Module.finrank F (EOOOMultiplierSolution n) at h
  rw [finrank_EOOOMultiplierGauge,
    finrank_EOOOMultiplierSolution] at h
  omega

/-! ### EOOE multiplier factorization -/

noncomputable def LambdaP
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (cubeDiffPStar (n := n))

noncomputable def lambdaPRead
    {n : Nat} [NeZero n] :
    LambdaP n →ₗ[F] MatrixProfile n where
  toFun z := fun s k => z.1 s 0 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def lambdaPBuild
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] LambdaP n where
  toFun h := ⟨fun i j k => h (i + j) k, by
    apply LinearMap.mem_ker.mpr
    funext i j k
    change h (i + j) k +
      h ((i + (-1)) + (j + 1)) (k + 0) = 0
    rw [show (i + (-1)) + (j + 1) = i + j by abel,
      add_zero, F_add_self]⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def lambdaPEquiv
    {n : Nat} [NeZero n] :
    LambdaP n ≃ₗ[F] MatrixProfile n where
  toFun := lambdaPRead
  invFun := lambdaPBuild
  left_inv z := by
    apply Subtype.ext
    funext i j k
    exact (EEEEInternal.pStar_invariant z i j k).symm
  right_inv h := by
    funext s k
    change h (s + 0) k = h s k
    simp
  map_add' := map_add lambdaPRead
  map_smul' := map_smul lambdaPRead

theorem finrank_LambdaP
    {n : Nat} [NeZero n] :
    Module.finrank F (LambdaP n) = n ^ 2 := by
  rw [LinearEquiv.finrank_eq (lambdaPEquiv (n := n))]
  simp [MatrixProfile, Module.finrank_pi_fintype, I, ZMod.card]
  ring

theorem lambdaP_cubeDiffP
    {n : Nat} [NeZero n] (z : LambdaP n) :
    cubeDiffP z.1 = 0 := by
  funext i j k
  change z.1 i j k + z.1 (i + 1) (j + (-1)) (k + 0) = 0
  rw [EEEEInternal.pStar_invariant z i j k,
    EEEEInternal.pStar_invariant z (i + 1) (j + (-1)) (k + 0)]
  rw [show i + 1 + (j + (-1)) = i + j by abel,
    add_zero, F_add_self]

theorem lambdaP_cubeDiffI_eq_JStar
    {n : Nat} [NeZero n] (z : LambdaP n) :
    cubeDiffI z.1 = cubeDiffJStar z.1 := by
  funext i j k
  change
    z.1 i j k + z.1 (i + 1) j k =
      z.1 i j k + z.1 (i + 0) (j + 1) (k + 0)
  congr 1
  rw [EEEEInternal.pStar_invariant z (i + 1) j k,
    EEEEInternal.pStar_invariant z (i + 0) (j + 1) (k + 0)]
  abel

theorem cubeDiffP_zero_to_PStar
    {n : Nat} [NeZero n] {x : CyclicCube n}
    (hx : cubeDiffP x = 0) :
    cubeDiffPStar x = 0 := by
  funext i j k
  have h := congrFun (congrFun (congrFun hx
    (i + (-1))) (j + 1)) k
  simp only [Pi.zero_apply] at h
  change
    x i j k + x (i + (-1)) (j + 1) (k + 0) = 0
  change
    x (i + (-1)) (j + 1) k +
      x ((i + (-1)) + 1) ((j + 1) + (-1)) (k + 0) = 0 at h
  rw [show (i + (-1)) + 1 = i by abel,
    show (j + 1) + (-1) = j by abel, add_zero] at h
  simpa [add_comm] using h

theorem cubeDiffP_zero_I_eq_JStar
    {n : Nat} [NeZero n] {x : CyclicCube n}
    (hx : cubeDiffP x = 0) :
    cubeDiffI x = cubeDiffJStar x := by
  funext i j k
  have h := congrFun (congrFun (congrFun hx i) (j + 1)) k
  simp only [Pi.zero_apply] at h
  change
    x i j k + x (i + 1) j k =
      x i j k + x (i + 0) (j + 1) (k + 0)
  change
    x i (j + 1) k +
      x (i + 1) ((j + 1) + (-1)) (k + 0) = 0 at h
  rw [show (j + 1) + (-1) = j by abel, add_zero] at h
  have heq : x i (j + 1) k = x (i + 1) j k :=
    EEEEInternal.eq_of_add_eq_zero _ _ h
  simp only [add_zero]
  rw [heq]

abbrev EOOEMultiplierAmbient
    (n : Nat) [NeZero n] :=
  DiamondEOOELeftSource n ×
    (CyclicCube n × CyclicCube n)

noncomputable def eooeMultiplierConstraintMap
    {n : Nat} [NeZero n] :
    EOOEMultiplierAmbient n →ₗ[F]
      (Fin 5 → CyclicCube n) where
  toFun z := fun q =>
    match q with
    | 0 => (diamondEOOECoeffMap z.1.1).1 +
        cubeDiffJStar z.2.1
    | 1 => (diamondEOOECoeffMap z.1.1).2 +
        cubeDiffJStar z.2.2
    | 2 => cubeDiffPStar z.2.1
    | 3 => cubeDiffPStar z.2.2
    | 4 => cubeDiffRStar z.2.2
  map_add' x y := by
    funext q
    fin_cases q <;> simp [diamondEOOECoeffMap] <;> abel
  map_smul' r x := by
    funext q
    fin_cases q <;> simp [diamondEOOECoeffMap]

noncomputable def EOOEMultiplierSolution
    (n : Nat) [NeZero n] :
    Submodule F (EOOEMultiplierAmbient n) :=
  LinearMap.ker (eooeMultiplierConstraintMap (n := n))

noncomputable def eooeProjection
    {n : Nat} [NeZero n] :
    EOOEMultiplierSolution n →ₗ[F] DiamondEOOELeftSource n :=
  (LinearMap.fst F (DiamondEOOELeftSource n)
    (CyclicCube n × CyclicCube n)).comp
      (EOOEMultiplierSolution n).subtype

noncomputable def EOOEMultiplierGauge
    (n : Nat) [NeZero n] :
    Submodule F (EOOEMultiplierSolution n) :=
  LinearMap.ker (eooeProjection (n := n))

abbrev EOOEFactors
    (n : Nat) [NeZero n] :=
  (LambdaPR n × EEEEInternal.BaseBFactor n) ×
    (LambdaP n × CubePairPRDISolution n)

noncomputable def eooeToFactors
    {n : Nat} [NeZero n] :
    EOOEMultiplierSolution n →ₗ[F] EOOEFactors n where
  toFun z := by
    let l := z.1.1.1
    let B0 := l.1.1
    let B1 := l.1.2
    let W0 := l.2
    let lambda0 := z.1.2.1
    let lambda1 := z.1.2.2
    have hleft := LinearMap.mem_ker.mp z.1.1.2
    have hPB0 : cubeDiffP B0 = 0 := by
      exact congrArg Prod.fst hleft
    have hPB1W : cubeDiffP B1 + cubeDiffR W0 = 0 := by
      exact congrArg Prod.snd hleft
    have hm := LinearMap.mem_ker.mp z.2
    have h0 := congrFun hm (0 : Fin 5)
    have h1 := congrFun hm (1 : Fin 5)
    have hp0 := congrFun hm (2 : Fin 5)
    have hp1 := congrFun hm (3 : Fin 5)
    have hr1 := congrFun hm (4 : Fin 5)
    change
      cubeDiffI (B0 + B1) + cubeDiffK W0 +
        cubeDiffJStar lambda0 = 0 at h0
    change cubeDiffI B0 + cubeDiffJStar lambda1 = 0 at h1
    change cubeDiffPStar lambda0 = 0 at hp0
    change cubeDiffPStar lambda1 = 0 at hp1
    change cubeDiffRStar lambda1 = 0 at hr1
    let lp1 : LambdaPR n :=
      ⟨lambda1, LinearMap.mem_ker.mpr (Prod.ext hp1 hr1)⟩
    let h : EEEEInternal.BaseBFactor n :=
      ⟨B0 + lambda1, by
        apply LinearMap.mem_ker.mpr
        apply Prod.ext
        · change cubeDiffP (B0 + lambda1) = 0
          rw [map_add, lambdaP_cubeDiffP
            (show LambdaP n from ⟨lambda1, hp1⟩),
            hPB0, zero_add]
        · change cubeDiffI (B0 + lambda1) = 0
          rw [map_add,
            lambdaP_cubeDiffI_eq_JStar
              (show LambdaP n from ⟨lambda1, hp1⟩)]
          exact h1⟩
    let mu : LambdaP n :=
      ⟨lambda0 + B0, by
        apply LinearMap.mem_ker.mpr
        rw [map_add, hp0, cubeDiffP_zero_to_PStar hPB0,
          zero_add]⟩
    let pair : CubePairPRDISolution n :=
      ⟨(B1 + mu.1, W0), by
        apply LinearMap.mem_ker.mpr
        apply Prod.ext
        · change cubeDiffP (B1 + mu.1) + cubeDiffR W0 = 0
          rw [map_add, lambdaP_cubeDiffP mu]
          simpa only [add_zero] using hPB1W
        · change cubeDiffI (B1 + mu.1) + cubeDiffK W0 = 0
          rw [map_add, lambdaP_cubeDiffI_eq_JStar mu]
          change
            cubeDiffI B1 + cubeDiffJStar (lambda0 + B0) +
              cubeDiffK W0 = 0
          rw [map_add]
          rw [show cubeDiffJStar B0 = cubeDiffI B0 by
            exact (cubeDiffP_zero_I_eq_JStar hPB0).symm]
          calc
            cubeDiffI B1 +
                (cubeDiffJStar lambda0 + cubeDiffI B0) +
                cubeDiffK W0 =
              cubeDiffI B0 + cubeDiffI B1 +
                cubeDiffK W0 + cubeDiffJStar lambda0 := by abel
            _ = 0 := by simpa only [map_add] using h0⟩
    exact ((lp1, h), (mu, pair))
  map_add' z w := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        change
          (z.1.1.1.1.1 + w.1.1.1.1.1) +
              (z.1.2.2 + w.1.2.2) =
            (z.1.1.1.1.1 + z.1.2.2) +
              (w.1.1.1.1.1 + w.1.2.2)
        abel
    · apply Prod.ext
      · apply Subtype.ext
        change
          (z.1.2.1 + w.1.2.1) +
              (z.1.1.1.1.1 + w.1.1.1.1.1) =
            (z.1.2.1 + z.1.1.1.1.1) +
              (w.1.2.1 + w.1.1.1.1.1)
        abel
      · apply Subtype.ext
        apply Prod.ext
        · change
            (z.1.1.1.1.2 + w.1.1.1.1.2) +
                ((z.1.2.1 + w.1.2.1) +
                  (z.1.1.1.1.1 + w.1.1.1.1.1)) =
              (z.1.1.1.1.2 +
                  (z.1.2.1 + z.1.1.1.1.1)) +
                (w.1.1.1.1.2 +
                  (w.1.2.1 + w.1.1.1.1.1))
          abel
        · rfl
  map_smul' r z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        change
          r • z.1.1.1.1.1 + r • z.1.2.2 =
            r • (z.1.1.1.1.1 + z.1.2.2)
        rw [smul_add]
    · apply Prod.ext
      · apply Subtype.ext
        change
          r • z.1.2.1 + r • z.1.1.1.1.1 =
            r • (z.1.2.1 + z.1.1.1.1.1)
        rw [smul_add]
      · apply Subtype.ext
        apply Prod.ext
        · change
            r • z.1.1.1.1.2 +
                (r • z.1.2.1 + r • z.1.1.1.1.1) =
              r • (z.1.1.1.1.2 +
                (z.1.2.1 + z.1.1.1.1.1))
          simp only [smul_add]
        · rfl

noncomputable def eooeFromFactorsLeftRaw
    {n : Nat} [NeZero n] :
    EOOEFactors n →ₗ[F] DiamondEOOELeftAmbient n where
  toFun q :=
    ((q.1.2.1 + q.1.1.1,
      q.2.2.1.1 + q.2.1.1), q.2.2.1.2)
  map_add' q r := by
    ext <;> simp <;> abel
  map_smul' r q := by
    ext <;> simp [smul_eq_mul]

theorem eooeFromFactorsLeftRaw_mem
    {n : Nat} [NeZero n] (q : EOOEFactors n) :
    eooeFromFactorsLeftRaw q ∈ DiamondEOOELeftSource n := by
  have hlp1 := lambdaPR_conditions q.1.1
  have hh := LinearMap.mem_ker.mp q.1.2.2
  have hhP : cubeDiffP q.1.2.1 = 0 := by
    exact congrArg Prod.fst hh
  have hpair := LinearMap.mem_ker.mp q.2.2.2
  apply LinearMap.mem_ker.mpr
  apply Prod.ext
  · change cubeDiffP (q.1.2.1 + q.1.1.1) = 0
    rw [map_add, hhP,
      lambdaP_cubeDiffP
        (show LambdaP n from ⟨q.1.1.1, hlp1.1⟩),
      zero_add]
  · change
      cubeDiffP (q.2.2.1.1 + q.2.1.1) +
        cubeDiffR q.2.2.1.2 = 0
    rw [map_add, lambdaP_cubeDiffP q.2.1, add_zero]
    exact congrArg Prod.fst hpair

noncomputable def eooeFromFactorsLeft
    {n : Nat} [NeZero n] :
    EOOEFactors n →ₗ[F] DiamondEOOELeftSource n :=
  LinearMap.codRestrict (DiamondEOOELeftSource n)
    eooeFromFactorsLeftRaw eooeFromFactorsLeftRaw_mem

noncomputable def eooeFromFactorsLambda
    {n : Nat} [NeZero n] :
    EOOEFactors n →ₗ[F] (CyclicCube n × CyclicCube n) where
  toFun q :=
    (q.2.1.1 + (q.1.2.1 + q.1.1.1), q.1.1.1)
  map_add' q r := by
    ext <;> simp <;> abel
  map_smul' r q := by
    ext <;> simp [smul_eq_mul]

noncomputable def eooeFromFactorsAmbient
    {n : Nat} [NeZero n] :
    EOOEFactors n →ₗ[F] EOOEMultiplierAmbient n :=
  LinearMap.prod eooeFromFactorsLeft eooeFromFactorsLambda

theorem eooeFromFactorsAmbient_mem
    {n : Nat} [NeZero n] (q : EOOEFactors n) :
    eooeFromFactorsAmbient q ∈ EOOEMultiplierSolution n := by
  have hlp1 := lambdaPR_conditions q.1.1
  have hh := LinearMap.mem_ker.mp q.1.2.2
  have hhP : cubeDiffP q.1.2.1 = 0 := congrArg Prod.fst hh
  have hhI : cubeDiffI q.1.2.1 = 0 := congrArg Prod.snd hh
  have hpair := LinearMap.mem_ker.mp q.2.2.2
  have hpairDI :
      cubeDiffI q.2.2.1.1 + cubeDiffK q.2.2.1.2 = 0 :=
    congrArg Prod.snd hpair
  let lp1P : LambdaP n := ⟨q.1.1.1, hlp1.1⟩
  have hhJ : cubeDiffJStar q.1.2.1 = 0 := by
    rw [← cubeDiffP_zero_I_eq_JStar hhP, hhI]
  apply LinearMap.mem_ker.mpr
  funext t
  fin_cases t
  all_goals
    simp only [eooeFromFactorsAmbient, LinearMap.prod_apply,
      eooeFromFactorsLeft,
      eooeFromFactorsLeftRaw, eooeFromFactorsLambda,
      eooeMultiplierConstraintMap]
  · change
      cubeDiffI
          ((q.1.2.1 + q.1.1.1) +
            (q.2.2.1.1 + q.2.1.1)) +
        cubeDiffK q.2.2.1.2 +
        cubeDiffJStar
          (q.2.1.1 + (q.1.2.1 + q.1.1.1)) = 0
    calc
      _ =
          (cubeDiffI q.2.2.1.1 + cubeDiffK q.2.2.1.2) +
            (cubeDiffJStar q.1.1.1 +
              cubeDiffJStar q.1.1.1) +
            (cubeDiffJStar q.2.1.1 +
              cubeDiffJStar q.2.1.1) := by
        simp only [map_add]
        rw [hhI, hhJ, lambdaP_cubeDiffI_eq_JStar lp1P,
          lambdaP_cubeDiffI_eq_JStar q.2.1]
        abel
      _ = 0 := by
        rw [hpairDI, zero_add,
          EEEEInternal.cube_add_self, zero_add,
          EEEEInternal.cube_add_self]
  · change
      cubeDiffI (q.1.2.1 + q.1.1.1) +
        cubeDiffJStar q.1.1.1 = 0
    rw [map_add, hhI, zero_add,
      lambdaP_cubeDiffI_eq_JStar lp1P,
      EEEEInternal.cube_add_self]
  · change
      cubeDiffPStar
        (q.2.1.1 + (q.1.2.1 + q.1.1.1)) = 0
    rw [map_add, map_add, LinearMap.mem_ker.mp q.2.1.2,
      cubeDiffP_zero_to_PStar hhP, hlp1.1]
    simp
  · exact hlp1.1
  · exact hlp1.2

noncomputable def eooeFromFactors
    {n : Nat} [NeZero n] :
    EOOEFactors n →ₗ[F] EOOEMultiplierSolution n :=
  LinearMap.codRestrict (EOOEMultiplierSolution n)
    eooeFromFactorsAmbient eooeFromFactorsAmbient_mem

noncomputable def eooeMultiplierEquiv
    {n : Nat} [NeZero n] :
    EOOEMultiplierSolution n ≃ₗ[F] EOOEFactors n where
  toFun := eooeToFactors
  invFun := eooeFromFactors
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp [eooeToFactors, eooeFromFactors,
        eooeFromFactorsAmbient, eooeFromFactorsLeft,
        eooeFromFactorsLeftRaw, eooeFromFactorsLambda]
      all_goals
        (abel_nf <;>
          simp only [two_smul, F_add_self, add_zero])
    · ext <;> simp [eooeToFactors, eooeFromFactors,
        eooeFromFactorsAmbient, eooeFromFactorsLeft,
        eooeFromFactorsLeftRaw, eooeFromFactorsLambda]
      all_goals
        (abel_nf <;>
          simp only [two_smul, F_add_self, add_zero])
  right_inv q := by
    apply Prod.ext
    · apply Prod.ext <;> apply Subtype.ext
      · rfl
      · ext <;> simp [eooeToFactors, eooeFromFactors,
          eooeFromFactorsAmbient, eooeFromFactorsLeft,
          eooeFromFactorsLeftRaw, eooeFromFactorsLambda]
        all_goals
          (abel_nf <;>
            simp only [two_smul, F_add_self, add_zero])
    · apply Prod.ext <;> apply Subtype.ext
      · ext <;> simp [eooeToFactors, eooeFromFactors,
          eooeFromFactorsAmbient, eooeFromFactorsLeft,
          eooeFromFactorsLeftRaw, eooeFromFactorsLambda]
        all_goals
          (abel_nf <;>
            simp only [two_smul, F_add_self, add_zero])
      · ext <;> simp [eooeToFactors, eooeFromFactors,
          eooeFromFactorsAmbient, eooeFromFactorsLeft,
          eooeFromFactorsLeftRaw, eooeFromFactorsLambda]
        all_goals
          (abel_nf <;>
            simp only [two_smul, F_add_self, add_zero])
  map_add' := map_add eooeToFactors
  map_smul' := map_smul eooeToFactors

set_option maxHeartbeats 1200000 in
-- Reverse exactness constructs two finite-dual factorizations.
theorem range_eooeProjection_eq_leftKernel
    {n : Nat} [NeZero n] :
    LinearMap.range (eooeProjection (n := n)) =
      LinearMap.ker (diamondEOOECross (n := n)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hm := LinearMap.mem_ker.mp z.2
    have h0 := congrFun hm (0 : Fin 5)
    have h1 := congrFun hm (1 : Fin 5)
    have hp0 := congrFun hm (2 : Fin 5)
    have hp1 := congrFun hm (3 : Fin 5)
    have hr1 := congrFun hm (4 : Fin 5)
    change
      (diamondEOOECoeffMap z.1.1.1).1 +
        cubeDiffJStar z.1.2.1 = 0 at h0
    change
      (diamondEOOECoeffMap z.1.1.1).2 +
        cubeDiffJStar z.1.2.2 = 0 at h1
    change cubeDiffPStar z.1.2.1 = 0 at hp0
    change cubeDiffPStar z.1.2.2 = 0 at hp1
    change cubeDiffRStar z.1.2.2 = 0 at hr1
    have hR0 :
        (diamondEOOECoeffMap z.1.1.1).1 =
          cubeDiffJStar z.1.2.1 :=
      EEEEInternal.cube_eq_of_add_eq_zero h0
    have hR1 :
        (diamondEOOECoeffMap z.1.1.1).2 =
          cubeDiffJStar z.1.2.2 :=
      EEEEInternal.cube_eq_of_add_eq_zero h1
    rcases A.2.1 with ⟨X0, hX0⟩
    rcases A.2.2 with ⟨X1, hX1⟩
    change
      cubeDot (diamondEOOECoeffMap z.1.1.1).1 A.1.1 +
        cubeDot (diamondEOOECoeffMap z.1.1.1).2 A.1.2 = 0
    have hz0 :=
      EEEEInternal.pairing_zero_of_j_range_p
        (diamondEOOECoeffMap z.1.1.1).1 z.1.2.1
          A.1.1 X0 hR0 hp0 hX0.symm
    have hz1 :
        cubeDot (diamondEOOECoeffMap z.1.1.1).2 A.1.2 = 0 := by
      change cubeDiffP X1.1 + cubeDiffR X1.2 =
        cubeDiffJInv A.1.2 at hX1
      rw [hR1, cubeDiffJ_pairing_adjoint, ← hX1,
        EEEEInternal.cubeDot_add_right,
        ← cubeDiffP_pairing_adjoint,
        ← cubeDiffR_pairing_adjoint, hp1, hr1]
      simp [cubeDot]
    rw [hz0, hz1, add_zero]
  · intro l hl
    let R := diamondEOOECoeffMap l.1
    have hcross (A : DiamondEOOERightSource n) :
        cubeDot R.1 A.1.1 + cubeDot R.2 A.1.2 = 0 := by
      have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hl) A
      exact h
    let phi0 : Module.Dual F (CyclicCube n) :=
      EEOEInternal.cubeDotDual R.1
    have hvanish0 :
        ∀ A : CyclicCube n,
          cubeDiffJInv A ∈ LinearMap.range (cubeDiffP (n := n)) →
            phi0 A = 0 := by
      intro A hA
      let As : DiamondEOOERightSource n :=
        ⟨(A, 0), ⟨hA, by simp⟩⟩
      simpa [As, phi0, R, EEOEInternal.cubeDotDual,
        BWSymmetryInternal.pairPhase, cubeDot] using hcross As
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv cubeDiffP phi0 hvanish0 with
      ⟨psi0, hphi0, hann0⟩
    rcases EEEEInternal.dual_exists_cubeDot psi0 with
      ⟨lambda0, hlambda0⟩
    have hR0 : R.1 = cubeDiffJStar lambda0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A
      calc
        cubeDot R.1 A = phi0 A := rfl
        _ = psi0 (cubeDiffJInv A) :=
          LinearMap.congr_fun hphi0 A
        _ = cubeDot lambda0 (cubeDiffJInv A) := hlambda0 _
        _ = cubeDot (cubeDiffJStar lambda0) A :=
          (cubeDiffJ_pairing_adjoint lambda0 A).symm
    have hp0 : cubeDiffPStar lambda0 = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffPStar lambda0) X =
            cubeDot lambda0 (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda0 X
        _ = psi0 (cubeDiffP X) := (hlambda0 _).symm
        _ = 0 := hann0 X
        _ = cubeDot 0 X := by simp [cubeDot]
    let phi1 : Module.Dual F (CyclicCube n) :=
      EEOEInternal.cubeDotDual R.2
    have hvanish1 :
        ∀ A : CyclicCube n,
          cubeDiffJInv A ∈ LinearMap.range
              (LinearMap.coprod (cubeDiffP (n := n))
                (cubeDiffR (n := n))) →
            phi1 A = 0 := by
      intro A hA
      let As : DiamondEOOERightSource n :=
        ⟨(0, A), ⟨by simp, hA⟩⟩
      simpa [As, phi1, R, EEOEInternal.cubeDotDual,
        BWSymmetryInternal.pairPhase, cubeDot] using hcross As
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv
        (LinearMap.coprod (cubeDiffP (n := n))
          (cubeDiffR (n := n)))
        phi1 hvanish1 with
      ⟨psi1, hphi1, hann1⟩
    rcases EEEEInternal.dual_exists_cubeDot psi1 with
      ⟨lambda1, hlambda1⟩
    have hR1 : R.2 = cubeDiffJStar lambda1 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A
      calc
        cubeDot R.2 A = phi1 A := rfl
        _ = psi1 (cubeDiffJInv A) :=
          LinearMap.congr_fun hphi1 A
        _ = cubeDot lambda1 (cubeDiffJInv A) := hlambda1 _
        _ = cubeDot (cubeDiffJStar lambda1) A :=
          (cubeDiffJ_pairing_adjoint lambda1 A).symm
    have hp1 : cubeDiffPStar lambda1 = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffPStar lambda1) X =
            cubeDot lambda1 (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda1 X
        _ = psi1 (cubeDiffP X) := (hlambda1 _).symm
        _ = psi1 (cubeDiffP X + cubeDiffR 0) := by simp
        _ = 0 := hann1 (X, 0)
        _ = cubeDot 0 X := by simp [cubeDot]
    have hr1 : cubeDiffRStar lambda1 = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffRStar lambda1) X =
            cubeDot lambda1 (cubeDiffR X) :=
          cubeDiffR_pairing_adjoint lambda1 X
        _ = psi1 (cubeDiffR X) := (hlambda1 _).symm
        _ = psi1 (cubeDiffP 0 + cubeDiffR X) := by simp
        _ = 0 := hann1 (0, X)
        _ = cubeDot 0 X := by simp [cubeDot]
    refine ⟨⟨(l, (lambda0, lambda1)), ?_⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext t
    fin_cases t
    · change R.1 + cubeDiffJStar lambda0 = 0
      rw [hR0, EEEEInternal.cube_add_self]
    · change R.2 + cubeDiffJStar lambda1 = 0
      rw [hR1, EEEEInternal.cube_add_self]
    · exact hp0
    · exact hp1
    · exact hr1

noncomputable def lambdaPJMap
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] (CyclicCube n × CyclicCube n) :=
  LinearMap.prod cubeDiffPStar cubeDiffJStar

noncomputable def LambdaPJ
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (lambdaPJMap (n := n))

theorem lambdaPJ_conditions
    {n : Nat} [NeZero n] (z : LambdaPJ n) :
    cubeDiffPStar z.1 = 0 ∧ cubeDiffJStar z.1 = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  exact ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩

theorem lambdaPJ_k_only
    {n : Nat} [NeZero n] (z : LambdaPJ n)
    (i j k : I n) :
    z.1 i j k = z.1 0 0 k := by
  have hc := lambdaPJ_conditions z
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) :=
    ⟨z.1, hc.1⟩
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) :=
    ⟨z.1, hc.2⟩
  calc
    z.1 i j k = z.1 (i + j) 0 k :=
      EEEEInternal.pStar_invariant zp i j k
    _ = z.1 0 (i + j) k := by
      simpa using
        (EEEEInternal.pStar_invariant zp 0 (i + j) k).symm
    _ = z.1 0 0 k :=
      EEEEInternal.jStar_invariant zj 0 (i + j) k

noncomputable def lambdaPJRead
    {n : Nat} [NeZero n] :
    LambdaPJ n →ₗ[F] Profile n where
  toFun z := fun k => z.1 0 0 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def lambdaPJBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] LambdaPJ n where
  toFun h :=
    ⟨fun _ _ k => h k, by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext <;> funext i j k
      · change h k + h (k + 0) = 0
        rw [add_zero, F_add_self]
      · change h k + h (k + 0) = 0
        rw [add_zero, F_add_self]⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def lambdaPJEquiv
    {n : Nat} [NeZero n] :
    LambdaPJ n ≃ₗ[F] Profile n where
  toFun := lambdaPJRead
  invFun := lambdaPJBuild
  left_inv z := by
    apply Subtype.ext
    funext i j k
    exact (lambdaPJ_k_only z i j k).symm
  right_inv _ := rfl
  map_add' := map_add lambdaPJRead
  map_smul' := map_smul lambdaPJRead

theorem finrank_LambdaPJ
    {n : Nat} [NeZero n] :
    Module.finrank F (LambdaPJ n) = n := by
  rw [LinearEquiv.finrank_eq (lambdaPJEquiv (n := n))]
  exact finrank_profile

noncomputable def eooeGaugeToFactors
    {n : Nat} [NeZero n] :
    EOOEMultiplierGauge n →ₗ[F]
      (LambdaPJ n × EEEEInternal.Lambda11Factor n) where
  toFun z := by
    have hleft := LinearMap.mem_ker.mp z.2
    change z.1.1.1 = 0 at hleft
    have hm := LinearMap.mem_ker.mp z.1.2
    have h0 := congrFun hm (0 : Fin 5)
    have h1 := congrFun hm (1 : Fin 5)
    have hp0 := congrFun hm (2 : Fin 5)
    have hp1 := congrFun hm (3 : Fin 5)
    have hr1 := congrFun hm (4 : Fin 5)
    change
      (diamondEOOECoeffMap z.1.1.1.1).1 +
        cubeDiffJStar z.1.1.2.1 = 0 at h0
    change
      (diamondEOOECoeffMap z.1.1.1.1).2 +
        cubeDiffJStar z.1.1.2.2 = 0 at h1
    change cubeDiffPStar z.1.1.2.1 = 0 at hp0
    change cubeDiffPStar z.1.1.2.2 = 0 at hp1
    change cubeDiffRStar z.1.1.2.2 = 0 at hr1
    have hcoeff :
        diamondEOOECoeffMap z.1.1.1.1 = 0 := by
      rw [hleft]
      rfl
    refine
      (⟨z.1.1.2.1, LinearMap.mem_ker.mpr
          (Prod.ext hp0 ?_)⟩,
        ⟨z.1.1.2.2, LinearMap.mem_ker.mpr
          (Prod.ext (Prod.ext ?_ hp1) hr1)⟩)
    · have hc0 :
          (diamondEOOECoeffMap z.1.1.1.1).1 = 0 := by
        simpa using congrArg Prod.fst hcoeff
      change cubeDiffJStar z.1.1.2.1 = 0
      simpa only [hc0, zero_add] using h0
    · have hc1 :
          (diamondEOOECoeffMap z.1.1.1.1).2 = 0 := by
        simpa using congrArg Prod.snd hcoeff
      change cubeDiffJStar z.1.1.2.2 = 0
      simpa only [hc1, zero_add] using h1
  map_add' z w := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' r z := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

noncomputable def eooeGaugeFromFactors
    {n : Nat} [NeZero n] :
    (LambdaPJ n × EEEEInternal.Lambda11Factor n) →ₗ[F]
      EOOEMultiplierGauge n where
  toFun q := by
    have hq0 := lambdaPJ_conditions q.1
    have hq1 := EEEEInternal.lambda11_conditions q.2
    let l : DiamondEOOELeftSource n := 0
    let z : EOOEMultiplierSolution n :=
      ⟨(l, (q.1.1, q.2.1)), by
        apply LinearMap.mem_ker.mpr
        funext t
        fin_cases t
        · simpa [l, eooeMultiplierConstraintMap,
            diamondEOOECoeffMap] using hq0.2
        · simpa [l, eooeMultiplierConstraintMap,
            diamondEOOECoeffMap] using hq1.1
        · exact hq0.1
        · exact hq1.2.1
        · exact hq1.2.2⟩
    refine ⟨z, ?_⟩
    apply LinearMap.mem_ker.mpr
    rfl
  map_add' q r := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  map_smul' r q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

noncomputable def eooeGaugeEquiv
    {n : Nat} [NeZero n] :
    EOOEMultiplierGauge n ≃ₗ[F]
      (LambdaPJ n × EEEEInternal.Lambda11Factor n) where
  toFun := eooeGaugeToFactors
  invFun := eooeGaugeFromFactors
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show z.1.1.1 = 0 from
        LinearMap.mem_ker.mp z.2).symm
    · change (z.1.1.2.1, z.1.1.2.2) =
        (z.1.1.2.1, z.1.1.2.2)
      rfl
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' := map_add eooeGaugeToFactors
  map_smul' := map_smul eooeGaugeToFactors

noncomputable def eooeLeftSourceToFactors
    {n : Nat} [NeZero n] :
    DiamondEOOELeftSource n →ₗ[F]
      (LinearMap.ker (cubeDiffP (n := n)) ×
        EEEEInternal.PRSource n) where
  toFun z := by
    have hz := LinearMap.mem_ker.mp z.2
    exact
      (⟨z.1.1.1, congrArg Prod.fst hz⟩,
        ⟨(z.1.1.2, z.1.2), congrArg Prod.snd hz⟩)
  map_add' _ _ := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

noncomputable def eooeLeftSourceFromFactors
    {n : Nat} [NeZero n] :
    (LinearMap.ker (cubeDiffP (n := n)) ×
        EEEEInternal.PRSource n) →ₗ[F]
      DiamondEOOELeftSource n where
  toFun q :=
    ⟨((q.1.1, q.2.1.1), q.2.1.2), by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact LinearMap.mem_ker.mp q.1.2
      · exact LinearMap.mem_ker.mp q.2.2⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 100000 in
noncomputable def eooeLeftSourceEquiv
    {n : Nat} [NeZero n] :
    DiamondEOOELeftSource n ≃ₗ[F]
      (LinearMap.ker (cubeDiffP (n := n)) ×
        EEEEInternal.PRSource n) where
  toFun := eooeLeftSourceToFactors
  invFun := eooeLeftSourceFromFactors
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' := map_add eooeLeftSourceToFactors
  map_smul' := map_smul eooeLeftSourceToFactors

theorem finrank_EOOELeftSource
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEOOELeftSource n) =
      n ^ 3 + n ^ 2 + n := by
  rw [LinearEquiv.finrank_eq
    (eooeLeftSourceEquiv (n := n))]
  have hP :
      Module.finrank F
          (LinearMap.ker (cubeDiffP (n := n))) =
        n ^ 2 := by
    rw [LinearEquiv.finrank_eq
      (EEEEInternal.pKerEquivIKer (n := n))]
    rw [LinearEquiv.finrank_eq
      (cubeDiff_ker_equiv_orbitConst (n := n))]
    simp [CubeOrbitConst, MatrixProfile,
      Module.finrank_pi_fintype, I, ZMod.card]
    ring
  have hPR :
      Module.finrank F (EEEEInternal.PRSource n) =
        n ^ 3 + n := by
    rw [LinearEquiv.finrank_eq
      (EEEEInternal.prSourceEquivStar (n := n))]
    exact finrank_ker_cubeStarIK
  simp only [Module.finrank_prod, hP, hPR]
  ring

theorem finrank_EOOEMultiplierSolution
    {n : Nat} [NeZero n] :
    Module.finrank F (EOOEMultiplierSolution n) =
      3 * n ^ 2 + n + 1 := by
  rw [LinearEquiv.finrank_eq (eooeMultiplierEquiv (n := n))]
  simp only [EOOEFactors, Module.finrank_prod,
    finrank_LambdaPR, EEEEInternal.finrank_BaseBFactor,
    finrank_LambdaP]
  have hpair := EEEEInternal.finrank_pair_addition_safe (n := n)
  omega

theorem finrank_EOOEMultiplierGauge
    {n : Nat} [NeZero n] :
    Module.finrank F (EOOEMultiplierGauge n) = n + 1 := by
  rw [LinearEquiv.finrank_eq (eooeGaugeEquiv (n := n))]
  simp [Module.finrank_prod, finrank_LambdaPJ,
    EEEEInternal.finrank_Lambda11Factor]

theorem finrank_EOOELeftKernel
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.ker (diamondEOOECross (n := n))) =
      3 * n ^ 2 := by
  letI : FiniteDimensional F (EOOEMultiplierSolution n) :=
    FiniteDimensional.of_injective
      (EOOEMultiplierSolution n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (eooeProjection (n := n))
  rw [range_eooeProjection_eq_leftKernel] at h
  have hker :
      LinearMap.ker (eooeProjection (n := n)) =
        EOOEMultiplierGauge n := rfl
  rw [hker] at h
  rw [finrank_EOOEMultiplierGauge,
    finrank_EOOEMultiplierSolution] at h
  omega

/-! ### EOEO shear and unequal blocks -/

noncomputable def eoeoLeftShear
    {n : Nat} [NeZero n] :
    DiamondEOEOLeftSource n ≃ₗ[F]
      ((CyclicCube n × CyclicCube n) ×
        DiamondEOOOLeftSource n) where
  toFun l := by
    let free : CyclicCube n × CyclicCube n :=
      (l.1.1.1 + l.1.1.2, l.1.2.1 + l.1.2.2)
    let constrainedRaw : DiamondEOOOLeftAmbient n :=
      (l.1.1.1, l.1.2.1)
    have hc : constrainedRaw ∈ DiamondEOOOLeftSource n := by
      apply LinearMap.mem_ker.mpr
      exact LinearMap.mem_ker.mp l.2
    exact (free, ⟨constrainedRaw, hc⟩)
  invFun q := by
    let B0 := q.2.1.1
    let W0 := q.2.1.2
    let lraw : DiamondEOEOLeftAmbient n :=
      ((B0, q.1.1 + B0), (W0, q.1.2 + W0))
    refine ⟨lraw, ?_⟩
    apply LinearMap.mem_ker.mpr
    exact LinearMap.mem_ker.mp q.2.2
  left_inv l := by
    apply Subtype.ext
    ext <;> simp
    all_goals
      (abel_nf <;>
        simp only [two_smul, F_add_self, zero_add])
  right_inv q := by
    apply Prod.ext
    · ext <;> simp
      all_goals
        (abel_nf <;>
          simp only [two_smul, F_add_self, zero_add])
    · apply Subtype.ext
      rfl
  map_add' l m := by
    apply Prod.ext
    · ext <;> simp <;> abel
    · apply Subtype.ext
      rfl
  map_smul' r l := by
    apply Prod.ext
    · ext <;> simp [smul_eq_mul]
    · apply Subtype.ext
      rfl

noncomputable def eoeoRightEquiv
    {n : Nat} [NeZero n] :
    DiamondEOEORightSource n ≃ₗ[F]
      (DiamondEOOORightSource n × CyclicCube n) where
  toFun A := (⟨A.1.1, A.2.1⟩, A.1.2)
  invFun A := ⟨(A.1.1, A.2), ⟨A.1.2, trivial⟩⟩
  left_inv A := by
    apply Subtype.ext
    rfl
  right_inv A := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def eoeoFreeRestrictedCross
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F]
      Module.Dual F (DiamondEOOORightSource n) :=
  (BWSymmetryInternal.restrictDual (DiamondEOOORightSource n)).comp
    (EEOEInternal.cubeDotDual.comp
      (diamondEOOOCoeffMap (n := n)))

noncomputable def eoeoConstrainedFreeCross
    {n : Nat} [NeZero n] :
    DiamondEOOOLeftSource n →ₗ[F]
      Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp
    (diamondEOOOCoeffMap.comp
      (DiamondEOOOLeftSource n).subtype)

noncomputable def eoeoBlockCross
    {n : Nat} [NeZero n] :
    ((CyclicCube n × CyclicCube n) ×
        DiamondEOOOLeftSource n) →ₗ[F]
      Module.Dual F
        (DiamondEOOORightSource n × CyclicCube n) :=
  (Module.dualProdDualEquivDual F
    (DiamondEOOORightSource n) (CyclicCube n)).toLinearMap.comp
      ((eoeoFreeRestrictedCross (n := n)).prodMap
        (eoeoConstrainedFreeCross (n := n)))

theorem eoeo_shear_phase
    {n : Nat} [NeZero n]
    (l : DiamondEOEOLeftSource n)
    (A : DiamondEOEORightSource n) :
    eoeoBlockCross (n := n) (eoeoLeftShear l)
        (eoeoRightEquiv A) =
      diamondEOEOCross (n := n) l A := by
  change
    cubeDot
        (diamondEOOOCoeffMap
          ((eoeoLeftShear l).1)) A.1.1 +
      cubeDot
        (diamondEOOOCoeffMap
          ((eoeoLeftShear l).2.1)) A.1.2 =
      BWSymmetryInternal.pairPhase
        (diamondEOEOCoeffMap l.1) A.1
  simp only [eoeoLeftShear, LinearEquiv.coe_mk,
    diamondEOOOCoeffMap, LinearMap.coprod_apply,
    diamondEOEOCoeffMap, BWSymmetryInternal.pairPhase]
  rfl

theorem rank_eoeo_eq_blockCross
    {n : Nat} [NeZero n] :
    Module.finrank F (LinearMap.range (diamondEOEOCross (n := n))) =
      Module.finrank F (LinearMap.range (eoeoBlockCross (n := n))) := by
  exact LinearEquiv.finrank_eq
    (BWSymmetryInternal.rangeTransportEquiv
      (diamondEOEOCross (n := n))
      (eoeoBlockCross (n := n))
      (eoeoLeftShear (n := n))
      (eoeoRightEquiv (n := n))
      eoeo_shear_phase)

noncomputable def eoeoConstrainedKernelToPair
    {n : Nat} [NeZero n] :
    LinearMap.ker (eoeoConstrainedFreeCross (n := n)) →ₗ[F]
      CubePairPRDISolution n where
  toFun z := by
    have hcoeff :
        diamondEOOOCoeffMap z.1.1 = 0 := by
      apply EEOEInternal.cubeDotDual_injective
      have hz := LinearMap.mem_ker.mp z.2
      simpa only [eoeoConstrainedFreeCross, LinearMap.comp_apply,
        map_zero] using hz
    refine ⟨z.1.1, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · exact LinearMap.mem_ker.mp z.1.2
    · exact hcoeff
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def eoeoConstrainedKernelFromPair
    {n : Nat} [NeZero n] :
    CubePairPRDISolution n →ₗ[F]
      LinearMap.ker (eoeoConstrainedFreeCross (n := n)) where
  toFun q := by
    have hq := LinearMap.mem_ker.mp q.2
    let l : DiamondEOOOLeftSource n :=
      ⟨q.1, LinearMap.mem_ker.mpr (congrArg Prod.fst hq)⟩
    refine ⟨l, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    change cubeDot (diamondEOOOCoeffMap q.1) A = 0
    have hc : diamondEOOOCoeffMap q.1 = 0 :=
      congrArg Prod.snd hq
    rw [hc]
    simp [cubeDot]
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def eoeoConstrainedKernelEquivPair
    {n : Nat} [NeZero n] :
    LinearMap.ker (eoeoConstrainedFreeCross (n := n)) ≃ₗ[F]
      CubePairPRDISolution n where
  toFun := eoeoConstrainedKernelToPair
  invFun := eoeoConstrainedKernelFromPair
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change z.1.1 = z.1.1
    rfl
  right_inv q := by
    apply Subtype.ext
    change q.1 = q.1
    rfl
  map_add' := map_add eoeoConstrainedKernelToPair
  map_smul' := map_smul eoeoConstrainedKernelToPair

theorem eoeoConstrained_rank_addition_safe
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (eoeoConstrainedFreeCross (n := n))) +
        (2 * n ^ 2 + 1) =
      n ^ 3 + 2 * n := by
  letI : FiniteDimensional F (DiamondEOOOLeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEOOOLeftSource n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (eoeoConstrainedFreeCross (n := n))
  rw [LinearEquiv.finrank_eq
    (eoeoConstrainedKernelEquivPair (n := n))] at h
  have hpair :=
    EEEEInternal.finrank_pair_addition_safe (n := n)
  rw [finrank_EOOOLeftSource] at h
  omega

theorem eoeoConstrained_rank
    {n : Nat} [NeZero n] (hn2 : 2 ≤ n) :
    Module.finrank F
        (LinearMap.range (eoeoConstrainedFreeCross (n := n))) =
      n ^ 3 - 2 * n ^ 2 + 2 * n - 1 := by
  have h := eoeoConstrained_rank_addition_safe (n := n)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 :=
    ⟨n - 2, by omega⟩
  ring_nf at h ⊢
  omega

abbrev EOEOFreeMultiplierAmbient
    (n : Nat) [NeZero n] :=
  (CyclicCube n × CyclicCube n) × CyclicCube n

noncomputable def eoeoFreeMultiplierConstraintMap
    {n : Nat} [NeZero n] :
    EOEOFreeMultiplierAmbient n →ₗ[F]
      ((CyclicCube n × CyclicCube n) × CyclicCube n) where
  toFun z :=
    ((diamondEOOOCoeffMap z.1 + cubeDiffJStar z.2,
      cubeDiffPStar z.2), cubeDiffRStar z.2)
  map_add' x y := by
    ext <;> simp <;> abel
  map_smul' r x := by
    ext <;> simp [mul_add]

noncomputable def EOEOFreeMultiplierSolution
    (n : Nat) [NeZero n] :
    Submodule F (EOEOFreeMultiplierAmbient n) :=
  LinearMap.ker (eoeoFreeMultiplierConstraintMap (n := n))

noncomputable def eoeoFreeProjection
    {n : Nat} [NeZero n] :
    EOEOFreeMultiplierSolution n →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  (LinearMap.fst F (CyclicCube n × CyclicCube n)
    (CyclicCube n)).comp
      (EOEOFreeMultiplierSolution n).subtype

noncomputable def EOEOFreeMultiplierGauge
    (n : Nat) [NeZero n] :
    Submodule F (EOEOFreeMultiplierSolution n) :=
  LinearMap.ker (eoeoFreeProjection (n := n))

noncomputable def eoeoFreeToFactors
    {n : Nat} [NeZero n] :
    EOEOFreeMultiplierSolution n →ₗ[F]
      (LambdaPR n × LinearMap.ker (cubeStarIK (n := n))) where
  toFun z := by
    have hm := LinearMap.mem_ker.mp z.2
    have hp : cubeDiffPStar z.1.2 = 0 :=
      congrArg (fun q => q.1.2) hm
    have hr : cubeDiffRStar z.1.2 = 0 :=
      congrArg Prod.snd hm
    let lambda : LambdaPR n :=
      ⟨z.1.2, LinearMap.mem_ker.mpr (Prod.ext hp hr)⟩
    refine (lambda, ⟨(z.1.1.1, z.1.1.2 + z.1.2), ?_⟩)
    apply LinearMap.mem_ker.mpr
    have hcoeff :
        diamondEOOOCoeffMap z.1.1 +
          cubeDiffJStar z.1.2 = 0 :=
      congrArg (fun q => q.1.1) hm
    change
      cubeDiffI z.1.1.1 +
        cubeDiffK (z.1.1.2 + z.1.2) = 0
    rw [map_add, lambdaPR_cubeDiffK_eq_JStar lambda]
    simpa [diamondEOOOCoeffMap, add_assoc] using hcoeff
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      ext <;> simp <;> abel
  map_smul' r z := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      ext <;> simp [smul_eq_mul]

noncomputable def eoeoFreeFromFactors
    {n : Nat} [NeZero n] :
    (LambdaPR n × LinearMap.ker (cubeStarIK (n := n))) →ₗ[F]
      EOEOFreeMultiplierSolution n where
  toFun q := by
    have hl := lambdaPR_conditions q.1
    have hk := LinearMap.mem_ker.mp q.2.2
    refine ⟨((q.2.1.1, q.2.1.2 + q.1.1), q.1.1), ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · apply Prod.ext
      · change
          cubeDiffI q.2.1.1 +
              cubeDiffK (q.2.1.2 + q.1.1) +
            cubeDiffJStar q.1.1 = 0
        rw [map_add, lambdaPR_cubeDiffK_eq_JStar q.1]
        rw [← add_assoc]
        change
          cubeStarIK q.2.1 +
              cubeDiffJStar q.1.1 +
            cubeDiffJStar q.1.1 = 0
        rw [hk, zero_add, EEEEInternal.cube_add_self]
      · exact hl.1
    · exact hl.2
  map_add' q r := by
    apply Subtype.ext
    ext <;> simp <;> abel
  map_smul' r q := by
    apply Subtype.ext
    ext <;> simp [smul_eq_mul]

noncomputable def eoeoFreeMultiplierEquiv
    {n : Nat} [NeZero n] :
    EOEOFreeMultiplierSolution n ≃ₗ[F]
      (LambdaPR n × LinearMap.ker (cubeStarIK (n := n))) where
  toFun := eoeoFreeToFactors
  invFun := eoeoFreeFromFactors
  left_inv z := by
    apply Subtype.ext
    ext <;> simp [eoeoFreeToFactors, eoeoFreeFromFactors]
    all_goals
      rw [add_assoc, F_add_self, add_zero]
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      change q.1.1 = q.1.1
      rfl
    · apply Subtype.ext
      ext <;> simp [eoeoFreeToFactors, eoeoFreeFromFactors]
      rw [add_assoc, F_add_self, add_zero]
  map_add' := map_add eoeoFreeToFactors
  map_smul' := map_smul eoeoFreeToFactors

set_option maxHeartbeats 1200000 in
-- Exactness for the free-to-restricted EOEO block.
theorem range_eoeoFreeProjection_eq_kernel
    {n : Nat} [NeZero n] :
    LinearMap.range (eoeoFreeProjection (n := n)) =
      LinearMap.ker (eoeoFreeRestrictedCross (n := n)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hc := LinearMap.mem_ker.mp z.2
    have hRadd :
        diamondEOOOCoeffMap z.1.1 +
            cubeDiffJStar z.1.2 = 0 :=
      congrArg (fun q => q.1.1) hc
    have hp : cubeDiffPStar z.1.2 = 0 :=
      congrArg (fun q => q.1.2) hc
    have hr : cubeDiffRStar z.1.2 = 0 :=
      congrArg Prod.snd hc
    have hR :
        diamondEOOOCoeffMap z.1.1 =
          cubeDiffJStar z.1.2 :=
      EEEEInternal.cube_eq_of_add_eq_zero hRadd
    rcases A.2 with ⟨q, hq⟩
    change cubeDot (diamondEOOOCoeffMap z.1.1) A.1 = 0
    change
      cubeDiffP q.1 + cubeDiffR q.2 =
        cubeDiffJInv A.1 at hq
    rw [hR, cubeDiffJ_pairing_adjoint, ← hq,
      EEEEInternal.cubeDot_add_right,
      ← cubeDiffP_pairing_adjoint,
      ← cubeDiffR_pairing_adjoint, hp, hr]
    simp [cubeDot]
  · intro l hl
    let phi : Module.Dual F (CyclicCube n) :=
      EEOEInternal.cubeDotDual (diamondEOOOCoeffMap l)
    have hvanish :
        ∀ A : CyclicCube n,
          cubeDiffJInv A ∈
              LinearMap.range
                (LinearMap.coprod
                  (cubeDiffP (n := n)) (cubeDiffR (n := n))) →
            phi A = 0 := by
      intro A hA
      let As : DiamondEOOORightSource n := ⟨A, hA⟩
      exact LinearMap.congr_fun (LinearMap.mem_ker.mp hl) As
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        (cubeDiffJInv (n := n))
        (LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n)))
        phi hvanish with
      ⟨psi, hphi, hann⟩
    rcases EEEEInternal.dual_exists_cubeDot psi with
      ⟨lambda, hlambda⟩
    have hR :
        diamondEOOOCoeffMap l =
          cubeDiffJStar lambda := by
      apply EEEEInternal.cubeDot_left_ext
      intro A
      calc
        cubeDot (diamondEOOOCoeffMap l) A =
            phi A := rfl
        _ = psi (cubeDiffJInv A) :=
          LinearMap.congr_fun hphi A
        _ = cubeDot lambda (cubeDiffJInv A) := hlambda _
        _ = cubeDot (cubeDiffJStar lambda) A :=
          (cubeDiffJ_pairing_adjoint lambda A).symm
    have hp : cubeDiffPStar lambda = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffPStar lambda) X =
            cubeDot lambda (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda X
        _ = psi (cubeDiffP X) := (hlambda _).symm
        _ = psi (cubeDiffP X + cubeDiffR 0) := by simp
        _ = 0 := hann (X, 0)
        _ = cubeDot 0 X := by simp [cubeDot]
    have hr : cubeDiffRStar lambda = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffRStar lambda) X =
            cubeDot lambda (cubeDiffR X) :=
          cubeDiffR_pairing_adjoint lambda X
        _ = psi (cubeDiffR X) := (hlambda _).symm
        _ = psi (cubeDiffP 0 + cubeDiffR X) := by simp
        _ = 0 := hann (0, X)
        _ = cubeDot 0 X := by simp [cubeDot]
    refine ⟨⟨(l, lambda), ?_⟩, rfl⟩
    apply LinearMap.mem_ker.mpr
    change
      ((diamondEOOOCoeffMap l + cubeDiffJStar lambda,
          cubeDiffPStar lambda), cubeDiffRStar lambda) = 0
    apply Prod.ext
    · apply Prod.ext
      · rw [hR]
        exact EEEEInternal.cube_add_self _
      · exact hp
    · exact hr

noncomputable def eoeoFreeGaugeToLambda11
    {n : Nat} [NeZero n] :
    EOEOFreeMultiplierGauge n →ₗ[F]
      EEEEInternal.Lambda11Factor n where
  toFun z := by
    have hleft := LinearMap.mem_ker.mp z.2
    change z.1.1.1 = 0 at hleft
    have hc := LinearMap.mem_ker.mp z.1.2
    refine ⟨z.1.1.2, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · apply Prod.ext
      · have hcoeff := congrArg (fun q => q.1.1) hc
        change
          diamondEOOOCoeffMap z.1.1.1 +
            cubeDiffJStar z.1.1.2 = 0 at hcoeff
        have hzcoeff :
            diamondEOOOCoeffMap z.1.1.1 = 0 := by
          rw [hleft]
          rfl
        rw [hzcoeff, zero_add] at hcoeff
        exact hcoeff
      · exact congrArg (fun q => q.1.2) hc
    · have hr := congrArg Prod.snd hc
      change cubeDiffRStar z.1.1.2 = 0 at hr
      exact hr
  map_add' z w := by
    apply Subtype.ext
    rfl
  map_smul' r z := by
    apply Subtype.ext
    rfl

noncomputable def eoeoFreeGaugeFromLambda11
    {n : Nat} [NeZero n] :
    EEEEInternal.Lambda11Factor n →ₗ[F]
      EOEOFreeMultiplierGauge n where
  toFun q := by
    have hq := EEEEInternal.lambda11_conditions q
    let z : EOEOFreeMultiplierSolution n :=
      ⟨((0, 0), q.1), by
        apply LinearMap.mem_ker.mpr
        apply Prod.ext
        · apply Prod.ext
          · simpa [eoeoFreeMultiplierConstraintMap,
              diamondEOOOCoeffMap] using hq.1
          · exact hq.2.1
        · exact hq.2.2⟩
    refine ⟨z, ?_⟩
    apply LinearMap.mem_ker.mpr
    rfl
  map_add' q r := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' r q := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def eoeoFreeGaugeEquiv
    {n : Nat} [NeZero n] :
    EOEOFreeMultiplierGauge n ≃ₗ[F]
      EEEEInternal.Lambda11Factor n where
  toFun := eoeoFreeGaugeToLambda11
  invFun := eoeoFreeGaugeFromLambda11
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show z.1.1.1 = 0 from
        LinearMap.mem_ker.mp z.2).symm
    · change z.1.1.2 = z.1.1.2
      rfl
  right_inv q := by
    apply Subtype.ext
    change q.1 = q.1
    rfl
  map_add' := map_add eoeoFreeGaugeToLambda11
  map_smul' := map_smul eoeoFreeGaugeToLambda11

theorem finrank_EOEOFreeMultiplierSolution
    {n : Nat} [NeZero n] :
    Module.finrank F (EOEOFreeMultiplierSolution n) =
      n ^ 3 + 2 * n := by
  rw [LinearEquiv.finrank_eq (eoeoFreeMultiplierEquiv (n := n))]
  simp only [Module.finrank_prod, finrank_LambdaPR,
    finrank_ker_cubeStarIK]
  ring

theorem finrank_EOEOFreeMultiplierGauge
    {n : Nat} [NeZero n] :
    Module.finrank F (EOEOFreeMultiplierGauge n) = 1 := by
  rw [LinearEquiv.finrank_eq (eoeoFreeGaugeEquiv (n := n))]
  exact EEEEInternal.finrank_Lambda11Factor

theorem finrank_EOEOFreeKernel
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.ker (eoeoFreeRestrictedCross (n := n))) =
      n ^ 3 + 2 * n - 1 := by
  letI : FiniteDimensional F (EOEOFreeMultiplierSolution n) :=
    FiniteDimensional.of_injective
      (EOEOFreeMultiplierSolution n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (eoeoFreeProjection (n := n))
  rw [range_eoeoFreeProjection_eq_kernel] at h
  have hker :
      LinearMap.ker (eoeoFreeProjection (n := n)) =
        EOEOFreeMultiplierGauge n := rfl
  rw [hker, finrank_EOEOFreeMultiplierGauge,
    finrank_EOEOFreeMultiplierSolution] at h
  omega

theorem eoeoFree_rank
    {n : Nat} [NeZero n] (hn2 : 2 ≤ n) :
    Module.finrank F
        (LinearMap.range (eoeoFreeRestrictedCross (n := n))) =
      n ^ 3 - 2 * n + 1 := by
  letI : FiniteDimensional F
      (CyclicCube n × CyclicCube n) := inferInstance
  have h := LinearMap.finrank_range_add_finrank_ker
    (eoeoFreeRestrictedCross (n := n))
  rw [finrank_EOEOFreeKernel] at h
  have hdom :
      Module.finrank F (CyclicCube n × CyclicCube n) =
        2 * n ^ 3 := by
    simp [CyclicCube, Module.finrank_pi_fintype,
      I, ZMod.card, pow_succ, mul_assoc]
    ring
  rw [hdom] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 :=
    ⟨n - 2, by omega⟩
  ring_nf at h ⊢
  omega

noncomputable def eoeoBlockKernelToProduct
    {n : Nat} [NeZero n] :
    LinearMap.ker (eoeoBlockCross (n := n)) →ₗ[F]
      (LinearMap.ker (eoeoFreeRestrictedCross (n := n)) ×
        LinearMap.ker (eoeoConstrainedFreeCross (n := n))) where
  toFun z := by
    have hz := LinearMap.mem_ker.mp z.2
    have hp :
        ((eoeoFreeRestrictedCross (n := n)).prodMap
          (eoeoConstrainedFreeCross (n := n))) z.1 = 0 := by
      apply (Module.dualProdDualEquivDual F
        (DiamondEOOORightSource n) (CyclicCube n)).injective
      change
        (Module.dualProdDualEquivDual F
            (DiamondEOOORightSource n) (CyclicCube n))
            (((eoeoFreeRestrictedCross (n := n)).prodMap
              (eoeoConstrainedFreeCross (n := n))) z.1) =
          (Module.dualProdDualEquivDual F
            (DiamondEOOORightSource n) (CyclicCube n)) 0
      rw [map_zero]
      exact hz
    exact
      (⟨z.1.1, congrArg Prod.fst hp⟩,
        ⟨z.1.2, congrArg Prod.snd hp⟩)
  map_add' _ _ := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' _ _ := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

noncomputable def eoeoBlockKernelFromProduct
    {n : Nat} [NeZero n] :
    (LinearMap.ker (eoeoFreeRestrictedCross (n := n)) ×
        LinearMap.ker (eoeoConstrainedFreeCross (n := n))) →ₗ[F]
      LinearMap.ker (eoeoBlockCross (n := n)) where
  toFun q := by
    refine ⟨(q.1.1, q.2.1), ?_⟩
    apply LinearMap.mem_ker.mpr
    change
      (Module.dualProdDualEquivDual F
        (DiamondEOOORightSource n) (CyclicCube n))
          (eoeoFreeRestrictedCross q.1.1,
            eoeoConstrainedFreeCross q.2.1) = 0
    rw [LinearMap.mem_ker.mp q.1.2,
      LinearMap.mem_ker.mp q.2.2]
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def eoeoBlockKernelEquiv
    {n : Nat} [NeZero n] :
    LinearMap.ker (eoeoBlockCross (n := n)) ≃ₗ[F]
      (LinearMap.ker (eoeoFreeRestrictedCross (n := n)) ×
        LinearMap.ker (eoeoConstrainedFreeCross (n := n))) where
  toFun := eoeoBlockKernelToProduct
  invFun := eoeoBlockKernelFromProduct
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' := map_add eoeoBlockKernelToProduct
  map_smul' := map_smul eoeoBlockKernelToProduct

theorem finrank_eoeoBlockKernel
    {n : Nat} [NeZero n] (hn2 : 2 ≤ n) :
    Module.finrank F
        (LinearMap.ker (eoeoBlockCross (n := n))) =
      n ^ 3 + 2 * n ^ 2 + n := by
  rw [LinearEquiv.finrank_eq (eoeoBlockKernelEquiv (n := n))]
  simp only [Module.finrank_prod, finrank_EOEOFreeKernel]
  rw [LinearEquiv.finrank_eq
    (eoeoConstrainedKernelEquivPair (n := n))]
  have hpair :=
    EEEEInternal.finrank_pair_addition_safe (n := n)
  have hpairExact :
      Module.finrank F (CubePairPRDISolution n) =
        2 * n ^ 2 - n + 1 := by
    have hsub :
        Module.finrank F (CubePairPRDISolution n) =
          (2 * n ^ 2 + 1) - n :=
      Nat.eq_sub_of_add_eq hpair
    rw [hsub]
    have hnle : n ≤ n ^ 2 := Nat.le_pow (by decide)
    omega
  rw [hpairExact]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 :=
    ⟨n - 2, by omega⟩
  ring_nf
  omega

theorem eoeoBlock_rank
    {n : Nat} [NeZero n] (hn2 : 2 ≤ n) :
    Module.finrank F
        (LinearMap.range (eoeoBlockCross (n := n))) =
      2 * n ^ 2 * (n - 1) := by
  letI : FiniteDimensional F
      ((CyclicCube n × CyclicCube n) ×
        DiamondEOOOLeftSource n) :=
    inferInstance
  have h := LinearMap.finrank_range_add_finrank_ker
    (eoeoBlockCross (n := n))
  rw [finrank_eoeoBlockKernel hn2] at h
  have hfree :
      Module.finrank F (CyclicCube n × CyclicCube n) =
        2 * n ^ 3 := by
    simp [CyclicCube, Module.finrank_pi_fintype,
      I, ZMod.card, pow_succ, mul_assoc]
    ring
  have hdom :
      Module.finrank F
          ((CyclicCube n × CyclicCube n) ×
            DiamondEOOOLeftSource n) =
        3 * n ^ 3 + n := by
    simp only [Module.finrank_prod, hfree, finrank_EOOOLeftSource]
    ring
  rw [hdom] at h
  have hpoly :
      2 * n ^ 2 * (n - 1) +
          (n ^ 3 + 2 * n ^ 2 + n) =
        3 * n ^ 3 + n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 :=
      ⟨n - 2, by omega⟩
    have hm : m + 2 - 1 = m + 1 := by omega
    rw [hm]
    ring
  omega

end BranchRanksInternal

theorem rank_diamondEvenP_cross_EOOO_scalar
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (_hn : Even n) :
    Module.finrank F
        (LinearMap.range (diamondEOOOCross (n := n))) =
      n * (n - 1) ^ 2 := by
  letI : FiniteDimensional F (DiamondEOOOLeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEOOOLeftSource n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (diamondEOOOCross (n := n))
  change
    Module.finrank F (LinearMap.range diamondEOOOCross) +
      Module.finrank F (DiamondEOOOLeftKernel n) =
        Module.finrank F (DiamondEOOOLeftSource n) at h
  rw [BranchRanksInternal.finrank_EOOOLeftKernel,
    BranchRanksInternal.finrank_EOOOLeftSource] at h
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hpoly :
      n * (n - 1) ^ 2 + 2 * n ^ 2 = n ^ 3 + n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

theorem rank_diamondEvenP_cross_EOOE_scalar
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (_hn : Even n) :
    Module.finrank F
        (LinearMap.range (diamondEOOECross (n := n))) =
      n * (n - 1) ^ 2 := by
  letI : FiniteDimensional F (DiamondEOOELeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEOOELeftSource n).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker
    (diamondEOOECross (n := n))
  rw [BranchRanksInternal.finrank_EOOELeftKernel,
    BranchRanksInternal.finrank_EOOELeftSource] at h
  have hpoly :
      n * (n - 1) ^ 2 + 3 * n ^ 2 =
        n ^ 3 + n ^ 2 + n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

theorem rank_diamondEvenP_cross_EOEO_scalar
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (_hn : Even n) :
    Module.finrank F
        (LinearMap.range (diamondEOEOCross (n := n))) =
      2 * n ^ 2 * (n - 1) := by
  rw [BranchRanksInternal.rank_eoeo_eq_blockCross]
  exact BranchRanksInternal.eoeoBlock_rank hn2

theorem rank_diamondEvenP_cross_EEOO_scalar
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) :
    Module.finrank F
        (LinearMap.range (diamondEEOOCross (n := n))) =
      n * (n - 1) ^ 2 := by
  rw [rank_EEOO_eq_EOOE]
  exact rank_diamondEvenP_cross_EOOE_scalar hn2 hn

theorem rank_diamondEvenP_cross_EEEO_scalar
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) :
    Module.finrank F
        (LinearMap.range (diamondEEEOCross (n := n))) =
      3 * n ^ 2 * (n - 1) := by
  rw [rank_EEEO_eq_EOEE]
  exact rank_diamondEvenP_cross_EOEE_scalar hn2 hn

end

end Core4loop.SquareDiagonal.EvenP
