import Core4loop.CompleteGraph.EvenAllLarge.Definitions

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

/-! ## The two component equations reconstruct the single H-dual equation -/

theorem k4EvenPBaseAmbientCross_eq_dualMap_of_multiplier
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPLeft n b c d ×
      Module.Dual F (CFun4 n 1 b d))
    (hz : z ∈ K4EvenPBaseMultiplierSolution n b c d) :
    k4EvenPBaseAmbientCross z.1 =
      (k4EvenPBaseRightMap
        (n := n) (b := b) (c := c) (d := d)).dualMap z.2 := by
  have h :=
    (k4EvenPBaseMultiplierSolution_mem_iff z).mp hz
  apply LinearMap.ext
  intro r
  have hD := LinearMap.congr_fun h.2.1 r.1
  have hS := LinearMap.congr_fun h.2.2 r.2
  rw [k4EvenPBaseAmbientCross_apply]
  change _ = z.2
    (k4EvenPBaseRightMap
      (n := n) (b := b) (c := c) (d := d) r)
  rw [k4EvenPBaseRightMap_apply]
  rw [map_add, ← hD, ← hS]
  rfl

/-! ## Exact projection range -/

theorem range_k4EvenPBaseProjection_eq_ker_baseCross
    {n b c d : Nat} [NeZero n] :
    LinearMap.range
        (k4EvenPBaseProjection
          (n := n) (b := b) (c := c) (d := d)) =
      LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d)) := by
  ext sigma
  constructor
  · rintro ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro r
    change k4EvenPBaseAmbientCross z.1.1 r.1 = 0
    rw [k4EvenPBaseAmbientCross_eq_dualMap_of_multiplier z.1 z.2]
    change z.1.2
      (k4EvenPBaseRightMap
        (n := n) (b := b) (c := c) (d := d) r.1) = 0
    rw [LinearMap.mem_ker.mp r.2, map_zero]
  · intro hsigma
    have hann :
        k4EvenPBaseAmbientCross sigma ∈
          (LinearMap.ker
            (k4EvenPBaseRightMap
              (n := n) (b := b) (c := c) (d := d))).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro r hr
      have hzero := LinearMap.congr_fun
        (LinearMap.mem_ker.mp hsigma)
        (⟨r, hr⟩ : K4EvenPBaseRight n b c d)
      exact hzero
    have hrange :
        k4EvenPBaseAmbientCross sigma ∈
          LinearMap.range
            (k4EvenPBaseRightMap
              (n := n) (b := b) (c := c) (d := d)).dualMap := by
      rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
      exact hann
    rcases hrange with ⟨lambda, hlambda⟩
    let z : K4EvenPLeft n b c d ×
        Module.Dual F (CFun4 n 1 b d) :=
      (sigma, lambda)
    have hD :
        (diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap lambda =
          k4EvenPBaseRoot sigma := by
      apply LinearMap.ext
      intro A
      have h := LinearMap.congr_fun hlambda
        (A, (0 : K4EvenPSlice n b c d))
      change lambda
          (k4EvenPBaseRightMap
            (n := n) (b := b) (c := c) (d := d)
            (A, (0 : K4EvenPSlice n b c d))) =
        k4EvenPBaseAmbientCross sigma
          (A, (0 : K4EvenPSlice n b c d)) at h
      rw [k4EvenPBaseRightMap_apply,
        k4EvenPBaseAmbientCross_apply] at h
      simpa using h
    have hS :
        (squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)).dualMap lambda =
          k4EvenPGPolarAmbient sigma.1 := by
      apply LinearMap.ext
      intro K
      have h := LinearMap.congr_fun hlambda
        ((0 : AFun4 n b c d), K)
      change lambda
          (k4EvenPBaseRightMap
            (n := n) (b := b) (c := c) (d := d)
            ((0 : AFun4 n b c d), K)) =
        k4EvenPBaseAmbientCross sigma
          ((0 : AFun4 n b c d), K) at h
      rw [k4EvenPBaseRightMap_apply,
        k4EvenPBaseAmbientCross_apply] at h
      simpa using h
    have hz : z ∈ K4EvenPBaseMultiplierSolution n b c d :=
      (k4EvenPBaseMultiplierSolution_mem_iff z).mpr
        ⟨LinearMap.mem_ker.mp sigma.2, hD, hS⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    rfl

/-! ## Explicit projection-kernel gauge coordinates -/

set_option synthInstance.maxHeartbeats 2000000 in
-- The nested projection-gauge subtype requires a larger instance budget.
noncomputable def k4EvenPBaseGaugeRead
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseGauge n b c d →ₗ[F]
      K4EvenPBaseGaugeLambda n b c d where
  toFun z :=
    ⟨z.1.1.2, by
      apply (k4EvenPBaseGaugeLambda_mem_iff z.1.1.2).mpr
      have hsolution :=
        (k4EvenPBaseMultiplierSolution_mem_iff z.1.1).mp z.1.2
      have hsigma := LinearMap.mem_ker.mp z.2
      change z.1.1.1 = 0 at hsigma
      constructor
      · simpa [hsigma] using hsolution.2.1
      · simpa [hsigma] using hsolution.2.2⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

private noncomputable def k4EvenPBaseGaugeRawBuild
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseGaugeLambda n b c d →ₗ[F]
      K4EvenPBaseMultiplierSolution n b c d where
  toFun lambda :=
    ⟨(0, lambda.1), by
      apply (k4EvenPBaseMultiplierSolution_mem_iff
        ((0 : K4EvenPLeft n b c d), lambda.1)).mpr
      have h :=
        (k4EvenPBaseGaugeLambda_mem_iff lambda.1).mp lambda.2
      exact ⟨by simp, by simpa using h.1, by simpa using h.2⟩⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- The nested projection-gauge subtype requires a larger instance budget.
noncomputable def k4EvenPBaseGaugeBuild
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseGaugeLambda n b c d →ₗ[F]
      K4EvenPBaseGauge n b c d where
  toFun lambda :=
    ⟨k4EvenPBaseGaugeRawBuild lambda, by
      apply LinearMap.mem_ker.mpr
      rfl⟩
  map_add' x y := by
    apply Subtype.ext
    exact (k4EvenPBaseGaugeRawBuild
      (n := n) (b := b) (c := c) (d := d)).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact (k4EvenPBaseGaugeRawBuild
      (n := n) (b := b) (c := c) (d := d)).map_smul r x

set_option synthInstance.maxHeartbeats 2000000 in
-- The nested projection-gauge subtype requires a larger instance budget.
@[simp] theorem k4EvenPBaseGaugeRead_build
    {n b c d : Nat} [NeZero n]
    (lambda : K4EvenPBaseGaugeLambda n b c d) :
    k4EvenPBaseGaugeRead
        (k4EvenPBaseGaugeBuild lambda) = lambda := by
  apply Subtype.ext
  rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- The nested projection-gauge subtype requires a larger instance budget.
@[simp] theorem k4EvenPBaseGaugeBuild_read
    {n b c d : Nat} [NeZero n]
    (z : K4EvenPBaseGauge n b c d) :
    k4EvenPBaseGaugeBuild
        (k4EvenPBaseGaugeRead z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hsigma := LinearMap.mem_ker.mp z.2
    change z.1.1.1 = 0 at hsigma
    exact hsigma.symm
  · rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- The nested projection-gauge subtype requires a larger instance budget.
noncomputable def k4EvenPBaseGaugeEquiv
    {n b c d : Nat} [NeZero n] :
    K4EvenPBaseGauge n b c d ≃ₗ[F]
      K4EvenPBaseGaugeLambda n b c d where
  toLinearMap := k4EvenPBaseGaugeRead
  invFun := k4EvenPBaseGaugeBuild
  left_inv := k4EvenPBaseGaugeBuild_read
  right_inv := k4EvenPBaseGaugeRead_build

set_option synthInstance.maxHeartbeats 2000000 in
-- The nested projection-gauge subtype requires a larger instance budget.
theorem finrank_k4EvenPBaseGauge_eq_gaugeLambda
    {n b c d : Nat} [NeZero n] :
    Module.finrank F (K4EvenPBaseGauge n b c d) =
      Module.finrank F (K4EvenPBaseGaugeLambda n b c d) :=
  LinearEquiv.finrank_eq k4EvenPBaseGaugeEquiv

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
