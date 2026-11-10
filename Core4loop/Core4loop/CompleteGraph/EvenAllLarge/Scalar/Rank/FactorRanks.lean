import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Rank.TransportedP

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

/-! ## Literal Base rows and their semantic kernels -/

theorem baseBRow_cycDiff_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) (i j k : I n) :
    baseBRow hn2 hn hb2 hc2 hd2 p i j k =
      cycDiff F p (i + j + k) := by
  rw [baseBRow_normalized, EEOEInternal.cubeDiffI_apply,
    cycDiff_apply]
  change p (j + (k + i)) + p (j + (k + (i + 1))) =
    p (i + j + k) + p (i + j + k + 1)
  congr 1 <;> congr 1 <;> abel

theorem baseWRow_cycDiff_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) (i j k : I n) :
    baseWRow hn2 hn hb2 hc2 hd2 p i j k =
      cycDiff F p (i + j + k) := by
  rw [baseWRow_normalized, EEOEInternal.cubeDiffK_apply,
    cycDiff_apply]
  change p (j + (k + i)) + p (j + ((k + 1) + i)) =
    p (i + j + k) + p (i + j + k + 1)
  congr 1 <;> congr 1 <;> abel

private theorem baseBRow_eq_zero_iff_cycDiff
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    baseBRow hn2 hn hb2 hc2 hd2 p = 0 ↔
      cycDiff F p = 0 := by
  constructor
  · intro h
    funext s
    have hs := congrFun (congrFun (congrFun h s) 0) 0
    simpa only [baseBRow_cycDiff_apply, add_zero] using hs
  · intro h
    funext i j k
    have hs := congrFun h (i + j + k)
    simpa only [baseBRow_cycDiff_apply] using hs

private theorem baseWRow_eq_zero_iff_cycDiff
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (p : Profile n) :
    baseWRow hn2 hn hb2 hc2 hd2 p = 0 ↔
      cycDiff F p = 0 := by
  constructor
  · intro h
    funext s
    have hs := congrFun (congrFun (congrFun h s) 0) 0
    simpa only [baseWRow_cycDiff_apply, add_zero] using hs
  · intro h
    funext i j k
    have hs := congrFun h (i + j + k)
    simpa only [baseWRow_cycDiff_apply] using hs

noncomputable def k4ScalarBaseBFactorEquivCycDiff
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ≃ₗ[F]
      LinearMap.ker (cycDiff (n := n) F) where
  toFun z := ⟨z.1, LinearMap.mem_ker.mpr
    ((baseBRow_eq_zero_iff_cycDiff hn2 hn hb2 hc2 hd2 z.1).1
      (LinearMap.mem_ker.mp z.2))⟩
  invFun z := ⟨z.1, LinearMap.mem_ker.mpr
    ((baseBRow_eq_zero_iff_cycDiff hn2 hn hb2 hc2 hd2 z.1).2
      (LinearMap.mem_ker.mp z.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4ScalarBaseWFactorEquivCycDiff
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2 ≃ₗ[F]
      LinearMap.ker (cycDiff (n := n) F) where
  toFun z := ⟨z.1, LinearMap.mem_ker.mpr
    ((baseWRow_eq_zero_iff_cycDiff hn2 hn hb2 hc2 hd2 z.1).1
      (LinearMap.mem_ker.mp z.2))⟩
  invFun z := ⟨z.1, LinearMap.mem_ker.mpr
    ((baseWRow_eq_zero_iff_cycDiff hn2 hn hb2 hc2 hd2 z.1).2
      (LinearMap.mem_ker.mp z.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4ScalarBaseBFactorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ≃ₗ[F] F :=
  (k4ScalarBaseBFactorEquivCycDiff hn2 hn hb2 hc2 hd2).trans
    (cycDiffKerEquiv F)

noncomputable def k4ScalarBaseWFactorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2 ≃ₗ[F] F :=
  (k4ScalarBaseWFactorEquivCycDiff hn2 hn hb2 hc2 hd2).trans
    (cycDiffKerEquiv F)

theorem finrank_K4ScalarBaseBFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F (K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2) = 1 := by
  rw [LinearEquiv.finrank_eq
    (k4ScalarBaseBFactorEquiv hn2 hn hb2 hc2 hd2)]
  exact Module.finrank_self F

theorem finrank_K4ScalarBaseWFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F (K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) = 1 := by
  rw [LinearEquiv.finrank_eq
    (k4ScalarBaseWFactorEquiv hn2 hn hb2 hc2 hd2)]
  exact Module.finrank_self F

/-! ## Addition-safe factor and multiplier-solution ranks -/

theorem finrank_K4ScalarFaithfulSevenFactors_add
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (K4ScalarFaithfulSevenFactors hn2 hn hb2 hc2 hd2) + 3 * n =
      2 * n ^ 3 + 6 * n ^ 2 + 7 := by
  letI : Module.Finite F
      (K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2) := inferInstance
  letI : Module.Finite F
      (K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) := inferInstance
  letI : Module.Finite F (CubePairPRDISolution n) := inferInstance
  letI : Module.Finite F
      (K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) := inferInstance
  letI : Module.Finite F
      (K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) := inferInstance
  letI : Module.Finite F (StarFactor n) := inferInstance
  letI : Module.Finite F (Lambda11Factor n) := inferInstance
  letI : Module.Finite F
      (K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ×
        K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) := inferInstance
  letI : Module.Finite F
      ((K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ×
          K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) ×
        CubePairPRDISolution n) := inferInstance
  letI : Module.Finite F
      (((K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ×
            K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) ×
          CubePairPRDISolution n) ×
        K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) := inferInstance
  letI : Module.Finite F
      ((((K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ×
              K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) ×
            CubePairPRDISolution n) ×
          K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) ×
        K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) := inferInstance
  letI : Module.Finite F
      (((((K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ×
                K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) ×
              CubePairPRDISolution n) ×
            K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) ×
          K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) ×
        StarFactor n) := inferInstance
  unfold K4ScalarFaithfulSevenFactors
  simp only [Module.finrank_prod]
  rw [finrank_K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2,
    finrank_K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2,
    EEEEInternal.finrank_StarFactor,
    EEEEInternal.finrank_Lambda11Factor]
  have hPair := EEEEInternal.finrank_pair_addition_safe (n := n)
  have hR := finrank_K4ScalarTransportedRFactor_add
    hn2 hn hb2 hc2 hd2
  have hP := finrank_K4ScalarTransportedPFactor_add
    hn2 hn hb2 hc2 hd2
  omega

theorem finrank_K4ScalarMultiplierSolution_add
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2) + 3 * n =
      2 * n ^ 3 + 6 * n ^ 2 + 7 := by
  rw [LinearEquiv.finrank_eq
    (k4ScalarMultiplierFaithfulSevenFactorsEquiv
      hn2 hn hb2 hc2 hd2)]
  exact finrank_K4ScalarFaithfulSevenFactors_add
    hn2 hn hb2 hc2 hd2

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
