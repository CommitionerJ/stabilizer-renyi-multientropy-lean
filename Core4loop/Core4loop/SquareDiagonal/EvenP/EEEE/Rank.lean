import Core4loop.SquareDiagonal.EvenP.EEEE.Projection
import Core4loop.SquareDiagonal.EvenP.EEEE.Factors
import Core4loop.SquareDiagonal.EvenP.EEEE.Gauge

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace EEEEInternal

noncomputable def prShear
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
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

theorem prShear_cubeDiffP
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    prShear (cubeDiffP f) = cubeDiffI (prShear f) := by
  funext i s k
  change
    f i (s - i - k) k +
        f (i + 1) ((s - i - k) + (-1)) (k + 0) =
      f i (s - i - k) k +
        f (i + 1) (s - (i + 1) - k) k
  congr 2
  · abel
  · simp

theorem cubeDiffK_apply
    {n : Nat} [NeZero n]
    (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  change f i j k + f (i + 0) (j + 0) (k + 1) = _
  simp

theorem prShear_cubeDiffR
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    prShear (cubeDiffR f) = cubeDiffK (prShear f) := by
  funext i s k
  have hk :
      cubeDiffK (prShear f) i s k =
        f i (s - i - k) k +
          f i (s - i - (k + 1)) (k + 1) := by
    rw [cubeDiffK_apply]
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

noncomputable def pKerEquivIKer
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffP (n := n)) ≃ₗ[F]
      LinearMap.ker (cubeDiffI (n := n)) where
  toFun z := ⟨prShear z.1, by
    apply LinearMap.mem_ker.mpr
    rw [← prShear_cubeDiffP]
    rw [LinearMap.mem_ker.mp z.2, map_zero]⟩
  invFun z := ⟨(prShear (n := n)).symm z.1, by
    apply LinearMap.mem_ker.mpr
    apply (prShear (n := n)).injective
    rw [map_zero, prShear_cubeDiffP, LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_ker.mp z.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (prShear (n := n)).symm_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact (prShear (n := n)).apply_symm_apply z.1
  map_add' z w := by
    apply Subtype.ext
    exact map_add prShear z.1 w.1
  map_smul' r z := by
    apply Subtype.ext
    exact map_smul prShear r z.1

noncomputable def rKerEquivKKer
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffR (n := n)) ≃ₗ[F]
      LinearMap.ker (cubeDiffK (n := n)) where
  toFun z := ⟨prShear z.1, by
    apply LinearMap.mem_ker.mpr
    rw [← prShear_cubeDiffR]
    rw [LinearMap.mem_ker.mp z.2, map_zero]⟩
  invFun z := ⟨(prShear (n := n)).symm z.1, by
    apply LinearMap.mem_ker.mpr
    apply (prShear (n := n)).injective
    rw [map_zero, prShear_cubeDiffR, LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_ker.mp z.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (prShear (n := n)).symm_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact (prShear (n := n)).apply_symm_apply z.1
  map_add' z w := by
    apply Subtype.ext
    exact map_add prShear z.1 w.1
  map_smul' r z := by
    apply Subtype.ext
    exact map_smul prShear r z.1

noncomputable def sourceSwapIK
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f k j i
  invFun f := fun i j k => f k j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sourceSwapIK_cubeDiffK
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    sourceSwapIK (cubeDiffK f) = cubeDiffI (sourceSwapIK f) := by
  funext i j k
  simp [sourceSwapIK]

noncomputable def kKerEquivIKer
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffK (n := n)) ≃ₗ[F]
      LinearMap.ker (cubeDiffI (n := n)) where
  toFun z := ⟨sourceSwapIK z.1, by
    apply LinearMap.mem_ker.mpr
    rw [← sourceSwapIK_cubeDiffK]
    rw [LinearMap.mem_ker.mp z.2, map_zero]⟩
  invFun z := ⟨(sourceSwapIK (n := n)).symm z.1, by
    apply LinearMap.mem_ker.mpr
    apply (sourceSwapIK (n := n)).injective
    rw [map_zero, sourceSwapIK_cubeDiffK, LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_ker.mp z.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (sourceSwapIK (n := n)).symm_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact (sourceSwapIK (n := n)).apply_symm_apply z.1
  map_add' z w := by
    apply Subtype.ext
    exact map_add sourceSwapIK z.1 w.1
  map_smul' r z := by
    apply Subtype.ext
    exact map_smul sourceSwapIK r z.1

noncomputable def rKerEquivIKer
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffR (n := n)) ≃ₗ[F]
      LinearMap.ker (cubeDiffI (n := n)) :=
  (rKerEquivKKer (n := n)).trans (kKerEquivIKer (n := n))

noncomputable def prSourceMap
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) →ₗ[F] CyclicCube n :=
  LinearMap.coprod cubeDiffP cubeDiffR

noncomputable def PRSource
    (n : Nat) [NeZero n] :=
  LinearMap.ker (prSourceMap (n := n))

noncomputable def prSourceEquivStar
    {n : Nat} [NeZero n] :
    PRSource n ≃ₗ[F] LinearMap.ker (cubeStarIK (n := n)) where
  toFun z := ⟨(prShear z.1.1, prShear z.1.2), by
    apply LinearMap.mem_ker.mpr
    change cubeDiffI (prShear z.1.1) +
      cubeDiffK (prShear z.1.2) = 0
    rw [← prShear_cubeDiffP, ← prShear_cubeDiffR, ← map_add]
    have hz := LinearMap.mem_ker.mp z.2
    change cubeDiffP z.1.1 + cubeDiffR z.1.2 = 0 at hz
    rw [hz, map_zero]⟩
  invFun z := ⟨((prShear (n := n)).symm z.1.1,
      (prShear (n := n)).symm z.1.2), by
    apply LinearMap.mem_ker.mpr
    apply (prShear (n := n)).injective
    change
      prShear
        (cubeDiffP ((prShear (n := n)).symm z.1.1) +
          cubeDiffR ((prShear (n := n)).symm z.1.2)) = 0
    rw [map_add, prShear_cubeDiffP, prShear_cubeDiffR]
    simp only [LinearEquiv.apply_symm_apply]
    exact LinearMap.mem_ker.mp z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;>
      exact (prShear (n := n)).symm_apply_apply _
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;>
      exact (prShear (n := n)).apply_symm_apply _
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext <;> exact map_add prShear _ _
  map_smul' r z := by
    apply Subtype.ext
    apply Prod.ext <;> exact map_smul prShear r _

noncomputable def leftSourceEquiv
    {n : Nat} [NeZero n] :
    DiamondEEEELeftSource n ≃ₗ[F]
      (((LinearMap.ker (cubeDiffP (n := n)) ×
          LinearMap.ker (cubeDiffR (n := n))) × PRSource n) ×
        ((CyclicCube n × CyclicCube n) ×
          (CyclicCube n × CyclicCube n))) where
  toFun l := by
    have h := LinearMap.mem_ker.mp l.2
    exact
      (((⟨l.1.1.1.1,
          congrArg
            (fun x : ((CyclicCube n × CyclicCube n) × CyclicCube n) =>
              x.1.1) h⟩,
          ⟨l.1.2.1.1,
            congrArg
              (fun x : ((CyclicCube n × CyclicCube n) × CyclicCube n) =>
                x.1.2) h⟩),
        ⟨(l.1.1.1.2, l.1.2.2.1), congrArg Prod.snd h⟩),
      ((l.1.1.2.1, l.1.1.2.2), (l.1.2.1.2, l.1.2.2.2)))
  invFun q :=
    ⟨(((q.1.1.1.1, q.1.2.1.1), q.2.1),
      ((q.1.1.2.1, q.2.2.1), (q.1.2.1.2, q.2.2.2))), by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · apply Prod.ext
        · exact LinearMap.mem_ker.mp q.1.1.1.2
        · exact LinearMap.mem_ker.mp q.1.1.2.2
      · exact LinearMap.mem_ker.mp q.1.2.2⟩
  left_inv l := by rfl
  right_inv q := by rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

theorem finrank_leftSource
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEEEELeftSource n) =
      5 * n ^ 3 + 2 * n ^ 2 + n := by
  rw [LinearEquiv.finrank_eq (leftSourceEquiv (n := n))]
  have hP :
      Module.finrank F (LinearMap.ker (cubeDiffP (n := n))) =
        Module.finrank F (CubeOrbitConst n) :=
    (LinearEquiv.finrank_eq (pKerEquivIKer (n := n))).trans
      (LinearEquiv.finrank_eq
        (cubeDiff_ker_equiv_orbitConst (n := n)))
  have hR :
      Module.finrank F (LinearMap.ker (cubeDiffR (n := n))) =
        Module.finrank F (CubeOrbitConst n) :=
    (LinearEquiv.finrank_eq (rKerEquivIKer (n := n))).trans
      (LinearEquiv.finrank_eq
        (cubeDiff_ker_equiv_orbitConst (n := n)))
  have hPR :
      Module.finrank F (PRSource n) = n ^ 3 + n :=
    (LinearEquiv.finrank_eq
      (prSourceEquivStar (n := n))).trans
        finrank_ker_cubeStarIK
  have hC :
      Module.finrank F (CubeOrbitConst n) = n ^ 2 := by
    simp [CubeOrbitConst, MatrixProfile, Module.finrank_pi_fintype,
      I, ZMod.card, pow_two]
  have hCube :
      Module.finrank F (CyclicCube n) = n ^ 3 := by
    simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
      pow_succ, mul_assoc]
  simp only [Module.finrank_prod, hP, hR, hPR, hC, hCube]
  ring

end EEEEInternal

set_option maxSynthPendingDepth 16

theorem finrank_EEEE_leftKernel_add
    {n : Nat} [NeZero n] (hn : Even n) :
    Module.finrank F (DiamondEEEELeftKernel n) + 3 * n =
      2 * n ^ 3 + 5 * n ^ 2 + 4 := by
  letI : AddCommGroup (CyclicCube n × CyclicCube n) := inferInstance
  letI : Module F (CyclicCube n × CyclicCube n) := inferInstance
  letI : FiniteDimensional F (CyclicCube n × CyclicCube n) :=
    inferInstance
  let CubeFour :=
    (CyclicCube n × CyclicCube n) ×
      (CyclicCube n × CyclicCube n)
  letI : AddCommGroup CubeFour := inferInstance
  letI : Module F CubeFour := inferInstance
  letI : FiniteDimensional F CubeFour := inferInstance
  letI : AddCommGroup (DiamondEEEELeftAmbient n) := inferInstance
  letI : Module F (DiamondEEEELeftAmbient n) := inferInstance
  letI : FiniteDimensional F (DiamondEEEELeftAmbient n) :=
    inferInstance
  letI : AddCommGroup (DiamondEEEELeftSource n) := inferInstance
  letI : Module F (DiamondEEEELeftSource n) := inferInstance
  letI : FiniteDimensional F (DiamondEEEELeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEEEELeftSource n).subtype Subtype.val_injective
  letI : AddCommGroup (DiamondEEEEMultiplierAmbient n) := inferInstance
  letI : Module F (DiamondEEEEMultiplierAmbient n) := inferInstance
  letI : FiniteDimensional F (DiamondEEEEMultiplierAmbient n) :=
    inferInstance
  letI : AddCommGroup (DiamondEEEEMultiplierSolution n) :=
    inferInstance
  letI : Module F (DiamondEEEEMultiplierSolution n) :=
    inferInstance
  letI : FiniteDimensional F (DiamondEEEEMultiplierSolution n) :=
    FiniteDimensional.of_injective
      (DiamondEEEEMultiplierSolution n).subtype Subtype.val_injective
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondEEEEProjection (n := n))
  rw [range_EEEE_projection_eq_leftKernel,
    ker_EEEE_projection_eq_gauge,
    finrank_DiamondEEEEMultiplierGauge] at hnull
  have hMultiplier :=
    finrank_DiamondEEEEMultiplierSolution_add
      (n := n) hn
  ring_nf at hnull hMultiplier ⊢
  omega

theorem rank_diamondEvenP_cross_EEEE_scalar
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) :
    Module.finrank F
        (LinearMap.range (diamondEEEECross (n := n))) =
      (n - 1) * (3 * n ^ 2 + 4) := by
  letI : AddCommGroup (CyclicCube n × CyclicCube n) := inferInstance
  letI : Module F (CyclicCube n × CyclicCube n) := inferInstance
  letI : FiniteDimensional F (CyclicCube n × CyclicCube n) :=
    inferInstance
  let CubeFour :=
    (CyclicCube n × CyclicCube n) ×
      (CyclicCube n × CyclicCube n)
  letI : AddCommGroup CubeFour := inferInstance
  letI : Module F CubeFour := inferInstance
  letI : FiniteDimensional F CubeFour := inferInstance
  letI : AddCommGroup (DiamondEEEELeftAmbient n) := inferInstance
  letI : Module F (DiamondEEEELeftAmbient n) := inferInstance
  letI : FiniteDimensional F (DiamondEEEELeftAmbient n) :=
    inferInstance
  letI : AddCommGroup (DiamondEEEELeftSource n) := inferInstance
  letI : Module F (DiamondEEEELeftSource n) := inferInstance
  letI : FiniteDimensional F (DiamondEEEELeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEEEELeftSource n).subtype Subtype.val_injective
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondEEEECross (n := n))
  change
    Module.finrank F
        (LinearMap.range (diamondEEEECross (n := n))) +
      Module.finrank F (DiamondEEEELeftKernel n) =
        Module.finrank F (DiamondEEEELeftSource n) at hnull
  rw [EEEEInternal.finrank_leftSource] at hnull
  have hKernel := finrank_EEEE_leftKernel_add (n := n) hn
  have hpoly :
      (n - 1) * (3 * n ^ 2 + 4) +
          (2 * n ^ 3 + 5 * n ^ 2 + 4) =
        (5 * n ^ 3 + 2 * n ^ 2 + n) + 3 * n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

end

end Core4loop.SquareDiagonal.EvenP
