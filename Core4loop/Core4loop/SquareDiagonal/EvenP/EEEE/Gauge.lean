import Core4loop.SquareDiagonal.EvenP.EEEE.Definitions

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace EEEEInternal

theorem gaugeJStarInvariant
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

theorem gaugePStarInvariant
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

theorem gaugeRStarInvariant
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

structure GaugeConditions
    {n : Nat} [NeZero n]
    (lambda00 lambda01 lambda10 lambda11 : CyclicCube n) : Prop where
  lambda00J : cubeDiffJStar lambda00 = 0
  lambda01J : cubeDiffJStar lambda01 = 0
  lambda01R : cubeDiffRStar lambda01 = 0
  lambda10J : cubeDiffJStar lambda10 = 0
  lambda10P : cubeDiffPStar lambda10 = 0
  lambda11J : cubeDiffJStar lambda11 = 0
  lambda11P : cubeDiffPStar lambda11 = 0
  lambda11R : cubeDiffRStar lambda11 = 0

theorem gaugeLeftZero
    {n : Nat} [NeZero n] (z : DiamondEEEEMultiplierGauge n) :
    z.1.1.1 = 0 := by
  exact LinearMap.mem_ker.mp z.2

theorem gaugeConditions
    {n : Nat} [NeZero n] (z : DiamondEEEEMultiplierGauge n) :
    GaugeConditions
      z.1.1.2.1.1 z.1.1.2.1.2 z.1.1.2.2.1 z.1.1.2.2.2 := by
  let R := diamondEEEECoeffMap z.1.1.1.1
  have hm := LinearMap.mem_ker.mp z.1.2
  have hl := gaugeLeftZero z
  have hR : R = 0 := by
    change diamondEEEECoeffMap z.1.1.1.1 = 0
    rw [hl]
    exact LinearMap.map_zero (diamondEEEECoeffMap (n := n))
  have h3 := congrFun hm (3 : Fin 11)
  have h4 := congrFun hm (4 : Fin 11)
  have h5 := congrFun hm (5 : Fin 11)
  have h6 := congrFun hm (6 : Fin 11)
  have h7 := congrFun hm (7 : Fin 11)
  have h8 := congrFun hm (8 : Fin 11)
  have h9 := congrFun hm (9 : Fin 11)
  have h10 := congrFun hm (10 : Fin 11)
  simp only [Pi.zero_apply] at h3 h4 h5 h6 h7 h8 h9 h10
  change R.1.1.2 + cubeDiffJStar z.1.1.2.1.2 = 0 at h3
  change cubeDiffRStar z.1.1.2.1.2 = 0 at h4
  change R.2.1.1 + cubeDiffJStar z.1.1.2.2.1 = 0 at h5
  change cubeDiffPStar z.1.1.2.2.1 = 0 at h6
  change R.1.1.1 + cubeDiffJStar z.1.1.2.1.1 = 0 at h7
  change cubeDiffJStar z.1.1.2.2.2 = 0 at h8
  change cubeDiffPStar z.1.1.2.2.2 = 0 at h9
  change cubeDiffRStar z.1.1.2.2.2 = 0 at h10
  rw [hR] at h3 h5 h7
  exact
    { lambda00J := by simpa using h7
      lambda01J := by simpa using h3
      lambda01R := h4
      lambda10J := by simpa using h5
      lambda10P := h6
      lambda11J := h8
      lambda11P := h9
      lambda11R := h10 }

theorem gaugeLambda00Invariant
    {n : Nat} [NeZero n] (z : DiamondEEEEMultiplierGauge n)
    (i j k : I n) :
    z.1.1.2.1.1 i j k = z.1.1.2.1.1 i 0 k := by
  have hc := gaugeConditions z
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) :=
    ⟨_, hc.lambda00J⟩
  exact gaugeJStarInvariant zj i j k

theorem gaugeLambda01Invariant
    {n : Nat} [NeZero n] (z : DiamondEEEEMultiplierGauge n)
    (i j k : I n) :
    z.1.1.2.1.2 i j k = z.1.1.2.1.2 i 0 0 := by
  have hc := gaugeConditions z
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) :=
    ⟨_, hc.lambda01J⟩
  let zr : LinearMap.ker (cubeDiffRStar (n := n)) :=
    ⟨_, hc.lambda01R⟩
  calc
    _ = z.1.1.2.1.2 i 0 k := gaugeJStarInvariant zj i j k
    _ = z.1.1.2.1.2 i k 0 := by
      simpa using (gaugeRStarInvariant zr i k 0).symm
    _ = _ := gaugeJStarInvariant zj i k 0

theorem gaugeLambda10Invariant
    {n : Nat} [NeZero n] (z : DiamondEEEEMultiplierGauge n)
    (i j k : I n) :
    z.1.1.2.2.1 i j k = z.1.1.2.2.1 0 0 k := by
  have hc := gaugeConditions z
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) :=
    ⟨_, hc.lambda10J⟩
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) :=
    ⟨_, hc.lambda10P⟩
  calc
    _ = z.1.1.2.2.1 (i + j) 0 k := gaugePStarInvariant zp i j k
    _ = z.1.1.2.2.1 0 (i + j) k := by
      simpa using (gaugePStarInvariant zp 0 (i + j) k).symm
    _ = _ := gaugeJStarInvariant zj 0 (i + j) k

theorem gaugeLambda11Invariant
    {n : Nat} [NeZero n] (z : DiamondEEEEMultiplierGauge n)
    (i j k : I n) :
    z.1.1.2.2.2 i j k = z.1.1.2.2.2 0 0 0 := by
  have hc := gaugeConditions z
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) :=
    ⟨_, hc.lambda11J⟩
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) :=
    ⟨_, hc.lambda11P⟩
  let zr : LinearMap.ker (cubeDiffRStar (n := n)) :=
    ⟨_, hc.lambda11R⟩
  calc
    _ = z.1.1.2.2.2 (i + j) 0 k := gaugePStarInvariant zp i j k
    _ = z.1.1.2.2.2 0 (i + j) k := by
      simpa using (gaugePStarInvariant zp 0 (i + j) k).symm
    _ = z.1.1.2.2.2 0 0 k := gaugeJStarInvariant zj 0 (i + j) k
    _ = z.1.1.2.2.2 0 k 0 := by
      simpa using (gaugeRStarInvariant zr 0 k 0).symm
    _ = _ := gaugeJStarInvariant zj 0 k 0

abbrev GaugeCoordinates (n : Nat) :=
  MatrixProfile n × Profile n × Profile n × F

set_option synthInstance.maxHeartbeats 100000 in
-- The nested kernel subtype requires a larger deterministic synthesis budget.
noncomputable def gaugeRead
    {n : Nat} [NeZero n] :
    DiamondEEEEMultiplierGauge n →ₗ[F] GaugeCoordinates n where
  toFun z :=
    (fun i k => z.1.1.2.1.1 i 0 k,
      fun i => z.1.1.2.1.2 i 0 0,
      fun k => z.1.1.2.2.1 0 0 k,
      z.1.1.2.2.2 0 0 0)
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The nested kernel subtype requires a larger deterministic synthesis budget.
noncomputable def gaugeBuild
    {n : Nat} [NeZero n] :
    GaugeCoordinates n →ₗ[F] DiamondEEEEMultiplierGauge n where
  toFun q := by
    let lambda00 : CyclicCube n := fun i _ k => q.1 i k
    let lambda01 : CyclicCube n := fun i _ _ => q.2.1 i
    let lambda10 : CyclicCube n := fun _ _ k => q.2.2.1 k
    let lambda11 : CyclicCube n := fun _ _ _ => q.2.2.2
    have hJ00 : cubeDiffJStar lambda00 = 0 := by
      funext i j k
      change q.1 i k + q.1 (i + 0) (k + 0) = 0
      simp only [add_zero, F_add_self]
    have hJ01 : cubeDiffJStar lambda01 = 0 := by
      funext i j k
      change q.2.1 i + q.2.1 (i + 0) = 0
      simp only [add_zero, F_add_self]
    have hR01 : cubeDiffRStar lambda01 = 0 := by
      funext i j k
      change q.2.1 i + q.2.1 (i + 0) = 0
      simp only [add_zero, F_add_self]
    have hJ10 : cubeDiffJStar lambda10 = 0 := by
      funext i j k
      change q.2.2.1 k + q.2.2.1 (k + 0) = 0
      simp only [add_zero, F_add_self]
    have hP10 : cubeDiffPStar lambda10 = 0 := by
      funext i j k
      change q.2.2.1 k + q.2.2.1 (k + 0) = 0
      simp only [add_zero, F_add_self]
    have hJ11 : cubeDiffJStar lambda11 = 0 := by
      funext i j k
      exact F_add_self _
    have hP11 : cubeDiffPStar lambda11 = 0 := by
      funext i j k
      exact F_add_self _
    have hR11 : cubeDiffRStar lambda11 = 0 := by
      funext i j k
      exact F_add_self _
    let z : DiamondEEEEMultiplierSolution n :=
      ⟨(0, ((lambda00, lambda01), (lambda10, lambda11))), by
        apply LinearMap.mem_ker.mpr
        funext t
        fin_cases t <;>
          simp [diamondEEEEMultiplierConstraintMap,
            diamondEEEECoeffMap, hJ00, hJ01, hR01, hJ10, hP10,
            hJ11, hP11, hR11]⟩
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

set_option synthInstance.maxHeartbeats 100000 in
-- The nested kernel subtype requires a larger deterministic synthesis budget.
noncomputable def gaugeEquiv
    {n : Nat} [NeZero n] :
    DiamondEEEEMultiplierGauge n ≃ₗ[F] GaugeCoordinates n where
  toFun := gaugeRead (n := n)
  invFun := gaugeBuild (n := n)
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (gaugeLeftZero z).symm
    · apply Prod.ext
      · apply Prod.ext
        · funext i j k
          exact (gaugeLambda00Invariant z i j k).symm
        · funext i j k
          exact (gaugeLambda01Invariant z i j k).symm
      · apply Prod.ext
        · funext i j k
          exact (gaugeLambda10Invariant z i j k).symm
        · funext i j k
          exact (gaugeLambda11Invariant z i j k).symm
  right_inv q := by
    apply Prod.ext
    · funext i k
      rfl
    · apply Prod.ext
      · funext i
        rfl
      · apply Prod.ext
        · funext k
          rfl
        · rfl
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

end EEEEInternal

set_option synthInstance.maxHeartbeats 100000 in
-- The nested kernel subtype requires a larger deterministic synthesis budget.
theorem finrank_DiamondEEEEMultiplierGauge
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEEEEMultiplierGauge n) =
      (n + 1) ^ 2 := by
  rw [LinearEquiv.finrank_eq (EEEEInternal.gaugeEquiv (n := n))]
  simp [EEEEInternal.GaugeCoordinates, MatrixProfile,
    Module.finrank_pi_fintype, Module.finrank_prod, I, ZMod.card]
  ring

theorem ker_EEEE_projection_eq_gauge
    {n : Nat} [NeZero n] :
    LinearMap.ker (diamondEEEEProjection (n := n)) =
      DiamondEEEEMultiplierGauge n := rfl

end

end Core4loop.SquareDiagonal.EvenP
