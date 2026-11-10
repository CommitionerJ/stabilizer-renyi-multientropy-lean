import Core4loop.SquareDiagonal.EvenP.TailPrototypeBlocks

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

/-!
# The isolated EOEE W block

At one W-tail index after the nested pointed-coordinate decomposition, the
literal left coordinates are

* `u = BΣ-tail`, constrained by `cubeDiffP u = 0`;
* `v = BK-tail`, which is free.

The literal right coordinates are

* `a = A-point-tail`, which is free;
* `d = D-tail`, constrained by
  `cubeDiffJInv d ∈ LinearMap.range cubeDiffP`.

With cube indices `(i,j,k)`, the raw phase is

`∑ i,j,k, (cubeDiffI u) i j k * a i j k
          + (cubeDiffI v) i j k * d i j k`.

Equivalently it is `cubeDot (cubeDiffI u) a +
cubeDot (cubeDiffI v) d`.  The shears below send

`(u,v) ↦ (u+v,u)` and `(a,d) ↦ (d,a+d)`.

The post-shear phase has two active blocks:

`cubeDot (cubeDiffI (u+v)) d + cubeDot (cubeDiffI u) (a+d)`.

The full EOEE source equivalences and the W-tail multiplicity belong to the
later total-EOEE owner; this file proves only this exact isolated block.
-/

/-- The literal left order `(BΣ-tail, BK-tail)`. -/
noncomputable abbrev DiamondEOEEWLeftSource
    (n : Nat) [NeZero n] :=
  EEOEInternal.PBlockLeft n × CyclicCube n

/-- The literal right order `(A-point-tail, D-tail)` before the right shear. -/
noncomputable abbrev DiamondEOEEWRightNatural
    (n : Nat) [NeZero n] :=
  CyclicCube n × EEOEInternal.PReachRight n

/-- The exact order `(D-tail, A-point-tail + D-tail)` after the right shear. -/
noncomputable abbrev DiamondEOEEWRightSource
    (n : Nat) [NeZero n] :=
  EEOEInternal.PReachRight n × CyclicCube n

private theorem eoeeW_add_self
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 :=
  (add_eq_zero_iff_eq_of_F_module x x).2 rfl

/-- The left shear `(u,v) ↦ (u+v,u)`. -/
noncomputable def diamondEOEEWLeftShear
    {n : Nat} [NeZero n] :
    DiamondEOEEWLeftSource n ≃ₗ[F]
      (CyclicCube n × EEOEInternal.PBlockLeft n) where
  toFun x := (x.1.1 + x.2, x.1)
  invFun x := (x.2, x.1 + x.2.1)
  left_inv x := by
    apply Prod.ext
    · rfl
    · change x.1.1 + x.2 + x.1.1 = x.2
      calc
        x.1.1 + x.2 + x.1.1 =
            (x.1.1 + x.1.1) + x.2 := by abel
        _ = 0 + x.2 := by rw [eoeeW_add_self]
        _ = x.2 := zero_add _
  right_inv x := by
    apply Prod.ext
    · change x.2.1 + (x.1 + x.2.1) = x.1
      calc
        x.2.1 + (x.1 + x.2.1) =
            (x.2.1 + x.2.1) + x.1 := by abel
        _ = 0 + x.1 := by rw [eoeeW_add_self]
        _ = x.1 := zero_add _
    · rfl
  map_add' x y := by
    apply Prod.ext
    · change
        (x.1.1 + y.1.1) + (x.2 + y.2) =
          (x.1.1 + x.2) + (y.1.1 + y.2)
      abel
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · change r • x.1.1 + r • x.2 = r • (x.1.1 + x.2)
      rw [smul_add]
    · rfl

@[simp] theorem diamondEOEEWLeftShear_apply
    {n : Nat} [NeZero n]
    (x : DiamondEOEEWLeftSource n) :
    diamondEOEEWLeftShear x = (x.1.1 + x.2, x.1) :=
  rfl

@[simp] theorem diamondEOEEWLeftShear_symm_apply
    {n : Nat} [NeZero n]
    (x : CyclicCube n × EEOEInternal.PBlockLeft n) :
    (diamondEOEEWLeftShear (n := n)).symm x =
      (x.2, x.1 + x.2.1) :=
  rfl

/-- The right shear `(a,d) ↦ (d,a+d)`. -/
noncomputable def diamondEOEEWRightShear
    {n : Nat} [NeZero n] :
    DiamondEOEEWRightNatural n ≃ₗ[F]
      DiamondEOEEWRightSource n where
  toFun x := (x.2, x.1 + x.2.1)
  invFun x := (x.2 + x.1.1, x.1)
  left_inv x := by
    apply Prod.ext
    · change x.1 + x.2.1 + x.2.1 = x.1
      rw [add_assoc, EEEEInternal.cube_add_self, add_zero]
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · change x.2 + x.1.1 + x.1.1 = x.2
      rw [add_assoc, EEEEInternal.cube_add_self, add_zero]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · change
        (x.1 + y.1) + (x.2.1 + y.2.1) =
          (x.1 + x.2.1) + (y.1 + y.2.1)
      abel
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · change r • x.1 + r • x.2.1 = r • (x.1 + x.2.1)
      rw [smul_add]

@[simp] theorem diamondEOEEWRightShear_apply
    {n : Nat} [NeZero n]
    (x : DiamondEOEEWRightNatural n) :
    diamondEOEEWRightShear x = (x.2, x.1 + x.2.1) :=
  rfl

@[simp] theorem diamondEOEEWRightShear_symm_apply
    {n : Nat} [NeZero n]
    (x : DiamondEOEEWRightSource n) :
    (diamondEOEEWRightShear (n := n)).symm x =
      (x.2 + x.1.1, x.1) :=
  rfl

private noncomputable def diamondEOEEWRightForget
    {n : Nat} [NeZero n] :
    DiamondEOEEWRightSource n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun x := (x.1.1, x.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def diamondEOEEWRightNaturalForget
    {n : Nat} [NeZero n] :
    DiamondEOEEWRightNatural n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun x := (x.1, x.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The exact post-left-shear coefficient `(I(u+v), Iu)`. -/
noncomputable def diamondEOEEWCoeffMap
    {n : Nat} [NeZero n] :
    DiamondEOEEWLeftSource n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun x :=
    (cubeDiffI (x.1.1 + x.2), cubeDiffI x.1.1)
  map_add' x y := by
    apply Prod.ext
    · change
        cubeDiffI ((x.1.1 + y.1.1) + (x.2 + y.2)) =
          cubeDiffI (x.1.1 + x.2) + cubeDiffI (y.1.1 + y.2)
      simp only [map_add]
      abel
    · simp
  map_smul' r x := by
    apply Prod.ext
    · change
        cubeDiffI (r • x.1.1 + r • x.2) =
          r • cubeDiffI (x.1.1 + x.2)
      rw [← smul_add, map_smul]
    · simp

private noncomputable def diamondEOEEWNaturalCoeffMap
    {n : Nat} [NeZero n] :
    DiamondEOEEWLeftSource n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun x := (cubeDiffI x.1.1, cubeDiffI x.2)
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' r x := by
    apply Prod.ext <;> simp

/-- The isolated W cross on the exact post-right-shear carrier. -/
noncomputable def diamondEOEEWCross
    {n : Nat} [NeZero n] :
    DiamondEOEEWLeftSource n →ₗ[F]
      Module.Dual F (DiamondEOEEWRightSource n) :=
  BWSymmetryInternal.pairPairing.compl₁₂
    diamondEOEEWCoeffMap diamondEOEEWRightForget

private noncomputable def diamondEOEEWNaturalCross
    {n : Nat} [NeZero n] :
    DiamondEOEEWLeftSource n →ₗ[F]
      Module.Dual F (DiamondEOEEWRightNatural n) :=
  BWSymmetryInternal.pairPairing.compl₁₂
    diamondEOEEWNaturalCoeffMap diamondEOEEWRightNaturalForget

@[simp] theorem diamondEOEEWCross_apply
    {n : Nat} [NeZero n]
    (x : DiamondEOEEWLeftSource n)
    (y : DiamondEOEEWRightSource n) :
    diamondEOEEWCross x y =
      cubeDot (cubeDiffI (x.1.1 + x.2)) y.1.1 +
        cubeDot (cubeDiffI x.1.1) y.2 :=
  rfl

private theorem diamondEOEEW_natural_phase_square
    {n : Nat} [NeZero n]
    (x : DiamondEOEEWLeftSource n)
    (y : DiamondEOEEWRightNatural n) :
    diamondEOEEWCross x (diamondEOEEWRightShear y) =
      diamondEOEEWNaturalCross x y := by
  change
    cubeDot (cubeDiffI (x.1.1 + x.2)) y.2.1 +
        cubeDot (cubeDiffI x.1.1) (y.1 + y.2.1) =
      cubeDot (cubeDiffI x.1.1) y.1 +
        cubeDot (cubeDiffI x.2) y.2.1
  simp only [map_add, EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  abel_nf
  simp only [two_smul, F_add_self, zero_add]

/-- The active block from a free cube to the dual of `PReachRight`. -/
noncomputable def diamondEOEEWPreachBlock
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (EEOEInternal.PReachRight n) :=
  EEOEInternal.cubeDotDual.compl₁₂
    (cubeDiffI (n := n))
    (EEOEInternal.PReachRight n).subtype

/-- The active block from `ker P` to the dual of a free cube. -/
noncomputable def diamondEOEEWKerPFreeBlock
    {n : Nat} [NeZero n] :
    EEOEInternal.PBlockLeft n →ₗ[F]
      Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp
    ((cubeDiffI (n := n)).comp
      (EEOEInternal.PBlockLeft n).subtype)

/-- The honest two-active-block normal form. -/
noncomputable def diamondEOEEWTwoBlockCross
    {n : Nat} [NeZero n] :
    (CyclicCube n × EEOEInternal.PBlockLeft n) →ₗ[F]
      Module.Dual F
        (EEOEInternal.PReachRight n × CyclicCube n) :=
  diamondCrossProd
    (diamondEOEEWPreachBlock (n := n))
    (diamondEOEEWKerPFreeBlock (n := n))

/-- The pointwise phase square; both displayed summands remain active. -/
theorem diamondEOEEW_phase_two_blocks
    {n : Nat} [NeZero n]
    (x : DiamondEOEEWLeftSource n)
    (y : DiamondEOEEWRightSource n) :
    diamondEOEEWTwoBlockCross (diamondEOEEWLeftShear x) y =
      diamondEOEEWCross x y := by
  rfl

/-- The range transport induced by the exact left shear. -/
noncomputable def diamondEOEEW_twoBlockRangeEquiv
    {n : Nat} [NeZero n] :
    LinearMap.range (diamondEOEEWCross (n := n)) ≃ₗ[F]
      LinearMap.range (diamondEOEEWTwoBlockCross (n := n)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (diamondEOEEWCross (n := n))
    (diamondEOEEWTwoBlockCross (n := n))
    (diamondEOEEWLeftShear (n := n))
    (LinearEquiv.refl F (DiamondEOEEWRightSource n))
    (diamondEOEEW_phase_two_blocks (n := n))

private noncomputable def eoeeWKerPFreeKernelToBase
    {n : Nat} [NeZero n] :
    LinearMap.ker (diamondEOEEWKerPFreeBlock (n := n)) →ₗ[F]
      EEEEInternal.BaseBFactor n where
  toFun x := by
    refine ⟨x.1.1, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · change cubeDiffP x.1.1 = 0
      exact LinearMap.mem_ker.mp x.1.2
    · apply EEOEInternal.cubeDotDual_injective
      have hx := LinearMap.mem_ker.mp x.2
      change
        EEOEInternal.cubeDotDual (cubeDiffI x.1.1) = 0 at hx
      simpa using hx
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

private noncomputable def eoeeWKerPFreeKernelFromBase
    {n : Nat} [NeZero n] :
    EEEEInternal.BaseBFactor n →ₗ[F]
      LinearMap.ker (diamondEOEEWKerPFreeBlock (n := n)) where
  toFun x := by
    have hx := LinearMap.mem_ker.mp x.2
    have hp : cubeDiffP x.1 = 0 := congrArg Prod.fst hx
    have hi : cubeDiffI x.1 = 0 := congrArg Prod.snd hx
    let u : EEOEInternal.PBlockLeft n :=
      ⟨x.1, hp⟩
    refine ⟨u, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    change cubeDot (cubeDiffI x.1) y = 0
    rw [hi]
    simp [cubeDot]
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def eoeeWKerPFreeKernelEquivBase
    {n : Nat} [NeZero n] :
    LinearMap.ker (diamondEOEEWKerPFreeBlock (n := n)) ≃ₗ[F]
      EEEEInternal.BaseBFactor n where
  toFun := eoeeWKerPFreeKernelToBase
  invFun := eoeeWKerPFreeKernelFromBase
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change x.1.1 = x.1.1
    rfl
  right_inv x := by
    apply Subtype.ext
    change x.1 = x.1
    rfl
  map_add' := map_add eoeeWKerPFreeKernelToBase
  map_smul' := map_smul eoeeWKerPFreeKernelToBase

/-- The `ker P`-to-free block has rank `n(n-1)`. -/
theorem rank_diamondEOEEWKerPFreeBlock
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (diamondEOEEWKerPFreeBlock (n := n))) =
      n * (n - 1) := by
  letI : FiniteDimensional F (EEOEInternal.PBlockLeft n) :=
    FiniteDimensional.of_injective
      (EEOEInternal.PBlockLeft n).subtype Subtype.val_injective
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondEOEEWKerPFreeBlock (n := n))
  rw [LinearEquiv.finrank_eq
    (eoeeWKerPFreeKernelEquivBase (n := n)),
    EEEEInternal.finrank_BaseBFactor,
    EEOEInternal.finrank_PBlockLeft] at h
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_sub_one, pow_two, Nat.succ_eq_add_one] at h ⊢
  ring_nf at h ⊢
  omega

private abbrev EOEEWFreePReachMultiplierAmbient
    (n : Nat) [NeZero n] :=
  CyclicCube n × CyclicCube n

private noncomputable def eoeeWFreePReachMultiplierConstraint
    {n : Nat} [NeZero n] :
    EOEEWFreePReachMultiplierAmbient n →ₗ[F]
      (CyclicCube n × CyclicCube n) where
  toFun x :=
    (cubeDiffI x.1 + cubeDiffJStar x.2,
      cubeDiffPStar x.2)
  map_add' x y := by
    apply Prod.ext
    · simp
      abel
    · simp
  map_smul' r x := by
    apply Prod.ext
    · simp
    · simp

private noncomputable def EOEEWFreePReachMultiplierSolution
    (n : Nat) [NeZero n] : Submodule F
      (EOEEWFreePReachMultiplierAmbient n) :=
  LinearMap.ker (eoeeWFreePReachMultiplierConstraint (n := n))

private noncomputable def eoeeWFreePReachProjection
    {n : Nat} [NeZero n] :
    EOEEWFreePReachMultiplierSolution n →ₗ[F] CyclicCube n :=
  (LinearMap.fst F (CyclicCube n) (CyclicCube n)).comp
    (EOEEWFreePReachMultiplierSolution n).subtype

private noncomputable def EOEEWFreePReachMultiplierGauge
    (n : Nat) [NeZero n] :
    Submodule F (EOEEWFreePReachMultiplierSolution n) :=
  LinearMap.ker (eoeeWFreePReachProjection (n := n))

private theorem eoeeW_range_projection_eq_kernel
    {n : Nat} [NeZero n] :
    LinearMap.range (eoeeWFreePReachProjection (n := n)) =
      LinearMap.ker (diamondEOEEWPreachBlock (n := n)) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    have hz := LinearMap.mem_ker.mp z.2
    have h0 := congrArg Prod.fst hz
    have hp := congrArg Prod.snd hz
    change cubeDiffI z.1.1 + cubeDiffJStar z.1.2 = 0 at h0
    change cubeDiffPStar z.1.2 = 0 at hp
    have hI :
        cubeDiffI z.1.1 = cubeDiffJStar z.1.2 :=
      EEEEInternal.cube_eq_of_add_eq_zero h0
    rcases A.2 with ⟨X, hX⟩
    change cubeDot (cubeDiffI z.1.1) A.1 = 0
    change cubeDiffP X = cubeDiffJInv A.1 at hX
    rw [hI, cubeDiffJ_pairing_adjoint, ← hX,
      ← cubeDiffP_pairing_adjoint, hp]
    simp [cubeDot]
  · intro B hB
    let phi : Module.Dual F (CyclicCube n) :=
      EEOEInternal.cubeDotDual (cubeDiffI B)
    have hvanish :
        ∀ A : CyclicCube n,
          cubeDiffJInv A ∈
              LinearMap.range (cubeDiffP (n := n)) →
            phi A = 0 := by
      intro A hA
      let Ar : EEOEInternal.PReachRight n := ⟨A, hA⟩
      have hz := LinearMap.congr_fun (LinearMap.mem_ker.mp hB) Ar
      simpa [diamondEOEEWPreachBlock, phi,
        EEOEInternal.cubeDotDual] using hz
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv cubeDiffP phi hvanish with
      ⟨psi, hphi, hann⟩
    rcases EEEEInternal.dual_exists_cubeDot psi with
      ⟨lambda, hlambda⟩
    have hI :
        cubeDiffI B = cubeDiffJStar lambda := by
      apply EEEEInternal.cubeDot_left_ext
      intro A
      calc
        cubeDot (cubeDiffI B) A = phi A := rfl
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
        _ = 0 := hann X
        _ = cubeDot 0 X := by simp [cubeDot]
    let z : EOEEWFreePReachMultiplierAmbient n := (B, lambda)
    have hz :
        eoeeWFreePReachMultiplierConstraint z = 0 := by
      apply Prod.ext
      · change cubeDiffI B + cubeDiffJStar lambda = 0
        rw [hI]
        exact EEEEInternal.cube_add_self _
      · exact hp
    exact ⟨⟨z, hz⟩, rfl⟩

private noncomputable def eoeeWFreePReachSolutionToFactors
    {n : Nat} [NeZero n] :
    EOEEWFreePReachMultiplierSolution n →ₗ[F]
      (BranchRanksInternal.LambdaP n ×
        LinearMap.ker (cubeDiffI (n := n))) where
  toFun z := by
    have hz := LinearMap.mem_ker.mp z.2
    have h0 := congrArg Prod.fst hz
    have hp := congrArg Prod.snd hz
    change cubeDiffI z.1.1 + cubeDiffJStar z.1.2 = 0 at h0
    change cubeDiffPStar z.1.2 = 0 at hp
    let lambda : BranchRanksInternal.LambdaP n :=
      ⟨z.1.2, hp⟩
    refine (lambda, ⟨z.1.1 + z.1.2, ?_⟩)
    apply LinearMap.mem_ker.mpr
    rw [map_add,
      BranchRanksInternal.lambdaP_cubeDiffI_eq_JStar lambda]
    exact h0
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change
        (x.1.1 + y.1.1) + (x.1.2 + y.1.2) =
          (x.1.1 + x.1.2) + (y.1.1 + y.1.2)
      abel
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change r • x.1.1 + r • x.1.2 =
        r • (x.1.1 + x.1.2)
      rw [smul_add]

private noncomputable def eoeeWFreePReachSolutionFromFactors
    {n : Nat} [NeZero n] :
    (BranchRanksInternal.LambdaP n ×
        LinearMap.ker (cubeDiffI (n := n))) →ₗ[F]
      EOEEWFreePReachMultiplierSolution n where
  toFun q := by
    let z : EOEEWFreePReachMultiplierAmbient n :=
      (q.2.1 + q.1.1, q.1.1)
    refine ⟨z, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · change
        cubeDiffI (q.2.1 + q.1.1) +
          cubeDiffJStar q.1.1 = 0
      rw [map_add, LinearMap.mem_ker.mp q.2.2,
        zero_add,
        BranchRanksInternal.lambdaP_cubeDiffI_eq_JStar q.1]
      exact EEEEInternal.cube_add_self _
    · exact LinearMap.mem_ker.mp q.1.2
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · change
        (x.2.1 + y.2.1) + (x.1.1 + y.1.1) =
          (x.2.1 + x.1.1) + (y.2.1 + y.1.1)
      abel
    · rfl
  map_smul' r x := by
    apply Subtype.ext
    apply Prod.ext
    · change r • x.2.1 + r • x.1.1 =
        r • (x.2.1 + x.1.1)
      rw [smul_add]
    · rfl

private noncomputable def eoeeWFreePReachSolutionEquivFactors
    {n : Nat} [NeZero n] :
    EOEEWFreePReachMultiplierSolution n ≃ₗ[F]
      (BranchRanksInternal.LambdaP n ×
        LinearMap.ker (cubeDiffI (n := n))) where
  toFun := eoeeWFreePReachSolutionToFactors
  invFun := eoeeWFreePReachSolutionFromFactors
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change z.1.1 + z.1.2 + z.1.2 = z.1.1
      rw [add_assoc, EEEEInternal.cube_add_self, add_zero]
    · rfl
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change q.2.1 + q.1.1 + q.1.1 = q.2.1
      rw [add_assoc, EEEEInternal.cube_add_self, add_zero]
  map_add' := map_add eoeeWFreePReachSolutionToFactors
  map_smul' := map_smul eoeeWFreePReachSolutionToFactors

private noncomputable def eoeeWFreePReachGaugeToLambdaPJ
    {n : Nat} [NeZero n] :
    EOEEWFreePReachMultiplierGauge n →ₗ[F]
      BranchRanksInternal.LambdaPJ n where
  toFun z := by
    have hB := LinearMap.mem_ker.mp z.2
    have hz := LinearMap.mem_ker.mp z.1.2
    have h0 := congrArg Prod.fst hz
    have hp := congrArg Prod.snd hz
    change z.1.1.1 = 0 at hB
    change cubeDiffI z.1.1.1 + cubeDiffJStar z.1.1.2 = 0 at h0
    change cubeDiffPStar z.1.1.2 = 0 at hp
    refine ⟨z.1.1.2, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · exact hp
    · rw [hB, map_zero, zero_add] at h0
      exact h0
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

private noncomputable def eoeeWFreePReachGaugeFromLambdaPJ
    {n : Nat} [NeZero n] :
    BranchRanksInternal.LambdaPJ n →ₗ[F]
      EOEEWFreePReachMultiplierGauge n where
  toFun q := by
    have hq := BranchRanksInternal.lambdaPJ_conditions q
    let zraw : EOEEWFreePReachMultiplierAmbient n := (0, q.1)
    let z : EOEEWFreePReachMultiplierSolution n :=
      ⟨zraw, by
        apply LinearMap.mem_ker.mpr
        apply Prod.ext
        · change 0 + cubeDiffJStar q.1 = 0
          simpa using hq.2
        · exact hq.1⟩
    refine ⟨z, ?_⟩
    apply LinearMap.mem_ker.mpr
    rfl
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · rfl
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · rfl

private noncomputable def eoeeWFreePReachGaugeEquivLambdaPJ
    {n : Nat} [NeZero n] :
    EOEEWFreePReachMultiplierGauge n ≃ₗ[F]
      BranchRanksInternal.LambdaPJ n where
  toFun := eoeeWFreePReachGaugeToLambdaPJ
  invFun := eoeeWFreePReachGaugeFromLambdaPJ
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change (0 : CyclicCube n) = z.1.1.1
      exact (LinearMap.mem_ker.mp z.2).symm
    · rfl
  right_inv q := by
    apply Subtype.ext
    rfl
  map_add' := map_add eoeeWFreePReachGaugeToLambdaPJ
  map_smul' := map_smul eoeeWFreePReachGaugeToLambdaPJ

private theorem eoeeW_finrank_cube
    {n : Nat} [NeZero n] :
    Module.finrank F (CyclicCube n) = n ^ 3 := by
  simp [CyclicCube, Module.finrank_pi_fintype,
    I, ZMod.card, pow_succ, mul_assoc]

private theorem eoeeW_finrank_ker_I
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.ker (cubeDiffI (n := n))) =
      n ^ 2 := by
  rw [LinearEquiv.finrank_eq
    (cubeDiff_ker_equiv_orbitConst (n := n))]
  simp [CubeOrbitConst, MatrixProfile,
    Module.finrank_pi_fintype, I, ZMod.card, pow_two]

private theorem eoeeW_finrank_freePReach_solution
    {n : Nat} [NeZero n] :
    Module.finrank F (EOEEWFreePReachMultiplierSolution n) =
      2 * n ^ 2 := by
  rw [LinearEquiv.finrank_eq
    (eoeeWFreePReachSolutionEquivFactors (n := n))]
  simp only [Module.finrank_prod,
    BranchRanksInternal.finrank_LambdaP,
    eoeeW_finrank_ker_I]
  omega

private theorem eoeeW_finrank_freePReach_gauge
    {n : Nat} [NeZero n] :
    Module.finrank F (EOEEWFreePReachMultiplierGauge n) = n := by
  rw [LinearEquiv.finrank_eq
    (eoeeWFreePReachGaugeEquivLambdaPJ (n := n))]
  exact BranchRanksInternal.finrank_LambdaPJ

private theorem eoeeW_finrank_freePReach_kernel
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.ker (diamondEOEEWPreachBlock (n := n))) =
      2 * n ^ 2 - n := by
  letI : FiniteDimensional F
      (EOEEWFreePReachMultiplierSolution n) :=
    FiniteDimensional.of_injective
      (EOEEWFreePReachMultiplierSolution n).subtype
      Subtype.val_injective
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (eoeeWFreePReachProjection (n := n))
  rw [eoeeW_range_projection_eq_kernel] at h
  change
    Module.finrank F
        (LinearMap.ker (diamondEOEEWPreachBlock (n := n))) +
      Module.finrank F (EOEEWFreePReachMultiplierGauge n) =
        Module.finrank F (EOEEWFreePReachMultiplierSolution n) at h
  rw [eoeeW_finrank_freePReach_gauge,
    eoeeW_finrank_freePReach_solution] at h
  omega

/-- The free-to-`PReachRight` block has rank `n(n-1)^2`. -/
theorem rank_diamondEOEEWPreachBlock
    {n : Nat} [NeZero n] (hn2 : 2 ≤ n) :
    Module.finrank F
        (LinearMap.range (diamondEOEEWPreachBlock (n := n))) =
      n * (n - 1) ^ 2 := by
  letI : FiniteDimensional F (CyclicCube n) := inferInstance
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondEOEEWPreachBlock (n := n))
  rw [eoeeW_finrank_freePReach_kernel, eoeeW_finrank_cube] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 :=
    ⟨n - 2, by omega⟩
  have hm : m + 2 - 1 = m + 1 := by omega
  rw [hm]
  ring_nf at h ⊢
  omega

/-- The full isolated W cross has rank `n^2(n-1)`. -/
theorem rank_diamondEOEEWCross
    {n : Nat} [NeZero n] (hn2 : 2 ≤ n) :
    Module.finrank F
        (LinearMap.range (diamondEOEEWCross (n := n))) =
      n ^ 2 * (n - 1) := by
  calc
    Module.finrank F
        (LinearMap.range (diamondEOEEWCross (n := n))) =
        Module.finrank F
          (LinearMap.range (diamondEOEEWTwoBlockCross (n := n))) :=
      LinearEquiv.finrank_eq diamondEOEEW_twoBlockRangeEquiv
    _ =
        Module.finrank F
            (LinearMap.range (diamondEOEEWPreachBlock (n := n))) +
          Module.finrank F
            (LinearMap.range (diamondEOEEWKerPFreeBlock (n := n))) :=
      finrank_range_diamondCrossProd
        (diamondEOEEWPreachBlock (n := n))
        (diamondEOEEWKerPFreeBlock (n := n))
    _ = n ^ 2 * (n - 1) := by
      rw [rank_diamondEOEEWPreachBlock hn2,
        rank_diamondEOEEWKerPFreeBlock]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 :=
        ⟨n - 2, by omega⟩
      have hm : m + 2 - 1 = m + 1 := by omega
      rw [hm]
      ring

/-- The two-block source agrees with the single-`I` prototype only in rank. -/
theorem rank_diamondEOEEWCross_eq_singleI
    {n : Nat} [NeZero n] (hn2 : 2 ≤ n) :
    Module.finrank F
        (LinearMap.range (diamondEOEEWCross (n := n))) =
      Module.finrank F
        (LinearMap.range (diamondTailSingleICross (n := n))) := by
  rw [rank_diamondEOEEWCross hn2, rank_diamondTailSingleICross]

end

end Core4loop.SquareDiagonal.EvenP
