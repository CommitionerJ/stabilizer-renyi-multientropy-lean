import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Rank.FactorRanks

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

/-! ## Source-zero and literal Fin-11 rewrapping -/

private theorem k4ScalarGauge_left_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2) :
    z.1.1.1 = 0 := by
  have h := LinearMap.mem_ker.mp z.2
  simpa only [scalarMultiplierProjection_apply] using h

private theorem k4Gauge_to_diamond_mem
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2) :
    (0, z.1.1.2) ∈ DiamondEEEEMultiplierSolution n := by
  apply LinearMap.mem_ker.mpr
  have hz := LinearMap.mem_ker.mp z.1.2
  rw [scalarMultiplierConstraintMap_apply] at hz
  have hl := k4ScalarGauge_left_zero hn2 hn hb2 hc2 hd2 z
  have hKCoeff :
      scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1.1.1 = 0 := by
    rw [hl]
    exact LinearMap.map_zero _
  have hDCoeff :
      diamondEEEECoeffMap (0 : DiamondEEEELeftAmbient n) = 0 :=
    LinearMap.map_zero _
  have h3 := congrFun hz (3 : Fin 11)
  have h4 := congrFun hz (4 : Fin 11)
  have h5 := congrFun hz (5 : Fin 11)
  have h6 := congrFun hz (6 : Fin 11)
  have h7 := congrFun hz (7 : Fin 11)
  have h8 := congrFun hz (8 : Fin 11)
  have h9 := congrFun hz (9 : Fin 11)
  have h10 := congrFun hz (10 : Fin 11)
  simp only [Pi.zero_apply] at h3 h4 h5 h6 h7 h8 h9 h10
  change
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1.1.1).1.1.2 +
      cubeDiffJStar z.1.1.2.1.2 = 0 at h3
  change cubeDiffRStar z.1.1.2.1.2 = 0 at h4
  change
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1.1.1).2.1.1 +
      cubeDiffJStar z.1.1.2.2.1 = 0 at h5
  change cubeDiffPStar z.1.1.2.2.1 = 0 at h6
  change
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1.1.1).1.1.1 +
      cubeDiffJStar z.1.1.2.1.1 = 0 at h7
  change cubeDiffJStar z.1.1.2.2.2 = 0 at h8
  change cubeDiffPStar z.1.1.2.2.2 = 0 at h9
  change cubeDiffRStar z.1.1.2.2.2 = 0 at h10
  rw [hKCoeff] at h3 h5 h7
  have hJ01 : cubeDiffJStar z.1.1.2.1.2 = 0 := by simpa using h3
  have hJ10 : cubeDiffJStar z.1.1.2.2.1 = 0 := by simpa using h5
  have hJ00 : cubeDiffJStar z.1.1.2.1.1 = 0 := by simpa using h7
  funext t
  fin_cases t <;>
    simp [diamondEEEEMultiplierConstraintMap, hDCoeff,
      hJ00, hJ01, h4, hJ10, h6, h8, h9, h10]

noncomputable def k4ScalarGaugeRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2 →ₗ[F]
      DiamondEEEEMultiplierGauge n where
  toFun z :=
    ⟨⟨(0, z.1.1.2),
        k4Gauge_to_diamond_mem hn2 hn hb2 hc2 hd2 z⟩,
      by apply LinearMap.mem_ker.mpr; rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private theorem diamondGauge_to_k4_mem
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : DiamondEEEEMultiplierGauge n) :
    (0, z.1.1.2) ∈
      K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 := by
  apply LinearMap.mem_ker.mpr
  have hKCoeff :
      scalarCoeffMap hn2 hn hb2 hc2 hd2
          (0 : K4BaseMixedScalarSector n) = 0 :=
    LinearMap.map_zero _
  have hc := EEEEInternal.gaugeConditions z
  funext t
  fin_cases t <;>
    simp [scalarMultiplierConstraintMap_apply, hKCoeff,
      hc.lambda00J, hc.lambda01J, hc.lambda01R,
      hc.lambda10J, hc.lambda10P, hc.lambda11J,
      hc.lambda11P, hc.lambda11R]

noncomputable def k4ScalarGaugeBuild
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEEEEMultiplierGauge n →ₗ[F]
      K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2 where
  toFun z :=
    ⟨⟨(0, z.1.1.2),
        diamondGauge_to_k4_mem hn2 hn hb2 hc2 hd2 z⟩,
      by apply LinearMap.mem_ker.mpr; rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-! ## Bilateral read/build laws and the gauge equivalence -/

theorem k4ScalarGaugeBuild_read
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2) :
    k4ScalarGaugeBuild hn2 hn hb2 hc2 hd2
        (k4ScalarGaugeRead hn2 hn hb2 hc2 hd2 z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (k4ScalarGauge_left_zero hn2 hn hb2 hc2 hd2 z).symm
  · rfl

theorem k4ScalarGaugeRead_build
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : DiamondEEEEMultiplierGauge n) :
    k4ScalarGaugeRead hn2 hn hb2 hc2 hd2
        (k4ScalarGaugeBuild hn2 hn hb2 hc2 hd2 z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (EEEEInternal.gaugeLeftZero z).symm
  · rfl

noncomputable def k4ScalarMultiplierGaugeEquivDiamond
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2 ≃ₗ[F]
      DiamondEEEEMultiplierGauge n where
  toFun := k4ScalarGaugeRead hn2 hn hb2 hc2 hd2
  invFun := k4ScalarGaugeBuild hn2 hn hb2 hc2 hd2
  left_inv := k4ScalarGaugeBuild_read hn2 hn hb2 hc2 hd2
  right_inv := k4ScalarGaugeRead_build hn2 hn hb2 hc2 hd2
  map_add' := map_add (k4ScalarGaugeRead hn2 hn hb2 hc2 hd2)
  map_smul' := map_smul (k4ScalarGaugeRead hn2 hn hb2 hc2 hd2)

theorem finrank_K4ScalarMultiplierGauge
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2) =
      (n + 1) ^ 2 := by
  rw [LinearEquiv.finrank_eq
    (k4ScalarMultiplierGaugeEquivDiamond
      hn2 hn hb2 hc2 hd2)]
  exact finrank_DiamondEEEEMultiplierGauge

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
