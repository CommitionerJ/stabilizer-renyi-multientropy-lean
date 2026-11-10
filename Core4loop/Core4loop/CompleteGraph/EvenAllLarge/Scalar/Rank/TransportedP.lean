import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Rank.TransportedR

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

/-! ## The frozen transported-P coordinate chart -/

noncomputable def k4ScalarPShearEquiv
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X := fun i j k => X i (i + j - k) k
  invFun X := fun i j k => X i (j - i + k) k
  left_inv X := by
    funext i j k
    dsimp
    congr 3
    all_goals abel
  right_inv X := by
    funext i j k
    dsimp
    congr 3
    all_goals abel
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem k4ScalarPShearEquiv_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) (i j k : I n) :
    k4ScalarPShearEquiv X i j k = X i (i + j - k) k := rfl

@[simp] theorem k4ScalarPShearEquiv_symm_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) (i j k : I n) :
    k4ScalarPShearEquiv.symm X i j k = X i (j - i + k) k := rfl

@[simp] theorem k4ScalarPShearEquiv_symm_apply_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) :
    k4ScalarPShearEquiv.symm (k4ScalarPShearEquiv X) = X :=
  k4ScalarPShearEquiv.left_inv X

@[simp] theorem k4ScalarPShearEquiv_apply_symm_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) :
    k4ScalarPShearEquiv (k4ScalarPShearEquiv.symm X) = X :=
  k4ScalarPShearEquiv.right_inv X

private noncomputable abbrev pShiftE2
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n :=
  k4ScalarRTranslateEquiv 0 1 0

private noncomputable abbrev pShiftNegE1
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n :=
  k4ScalarRTranslateEquiv (-1) 0 0

private noncomputable abbrev pShiftNegE1PosE2
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n :=
  k4ScalarRTranslateEquiv (-1) 1 0

/-! ## Four ambient P operator identities -/

theorem k4ScalarP_forward_operator0
    {n : Nat} [NeZero n] (W mu : CyclicCube n) :
    cubeDiffK (pShiftE2 (k4ScalarPShearEquiv W)) +
        cubeDiffJStar (k4ScalarPShearEquiv (mu + W)) =
      k4ScalarPShearEquiv (cubeDiffK W + cubeDiffJStar mu) := by
  funext i j k
  simp only [Pi.add_apply, EEOEInternal.cubeDiffK_apply,
    EEOEInternal.cubeDiffJStar_apply,
    k4ScalarRTranslateEquiv_apply, k4ScalarPShearEquiv_apply, add_zero]
  have h1 : i + (j + 1) - k = i + j - k + 1 := by abel
  have h2 : i + (j + 1) - (k + 1) = i + j - k := by abel
  rw [h1, h2]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]

theorem k4ScalarP_forward_operator1
    {n : Nat} [NeZero n] (W mu : CyclicCube n) :
    k4ScalarPShearEquiv
        ((k4ScalarKappaWCoeff W + cubeDiffPStar mu) +
          pShiftNegE1 (cubeDiffK W + cubeDiffJStar mu)) =
      cubeDiffPStar (k4ScalarPShearEquiv (mu + W)) := by
  funext i j k
  simp only [Pi.add_apply, EEOEInternal.cubeDiffK_apply,
    EEOEInternal.cubeDiffJStar_apply,
    EEOEInternal.cubeDiffPStar_apply,
    k4ScalarKappaWCoeff, LinearMap.coe_mk, AddHom.coe_mk,
    k4ScalarRTranslateEquiv_apply, k4ScalarPShearEquiv_apply, add_zero]
  have h : (i - 1) + (j + 1) - k = i + j - k := by abel
  rw [h]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]

theorem k4ScalarP_reverse_operator0
    {n : Nat} [NeZero n] (W mu : CyclicCube n) :
    cubeDiffK W + cubeDiffJStar mu =
      k4ScalarPShearEquiv.symm
        (cubeDiffK (pShiftE2 (k4ScalarPShearEquiv W)) +
          cubeDiffJStar (k4ScalarPShearEquiv (mu + W))) := by
  rw [k4ScalarP_forward_operator0]
  exact (k4ScalarPShearEquiv.left_inv _).symm

theorem k4ScalarP_reverse_operator1
    {n : Nat} [NeZero n] (W mu : CyclicCube n) :
    k4ScalarKappaWCoeff W + cubeDiffPStar mu =
      k4ScalarPShearEquiv.symm
        (cubeDiffPStar (k4ScalarPShearEquiv (mu + W)) +
          pShiftNegE1PosE2
            (cubeDiffK (pShiftE2 (k4ScalarPShearEquiv W)) +
              cubeDiffJStar (k4ScalarPShearEquiv (mu + W)))) := by
  funext i j k
  simp only [Pi.add_apply, EEOEInternal.cubeDiffK_apply,
    EEOEInternal.cubeDiffJStar_apply,
    EEOEInternal.cubeDiffPStar_apply,
    k4ScalarKappaWCoeff, LinearMap.coe_mk, AddHom.coe_mk,
    k4ScalarRTranslateEquiv_apply, k4ScalarPShearEquiv_apply,
    k4ScalarPShearEquiv_symm_apply, add_zero]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, add_zero]

/-! ## Literal K4 equations in the transported-W coordinates -/

private theorem transportedP_literal_H0
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) :
    cubeDiffK z.1.1.1 +
        cubeDiffJStar (k4ScalarWFreeSection z.1.1 + z.1.2) = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  have h0 := congrArg Prod.fst hz
  rw [transportedPMap_apply] at h0
  rw [transportedWRow_normalized,
    actualAddedWRead_pureWFree] at h0
  simpa only [map_add, add_assoc] using h0

private theorem transportedP_literal_H1
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) :
    k4ScalarKappaWCoeff z.1.1.1 +
        cubeDiffPStar (k4ScalarWFreeSection z.1.1 + z.1.2) = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  have h1 := congrArg Prod.snd hz
  rw [transportedPMap_apply] at h1
  change cubeDiffPStar z.1.2 = 0 at h1
  rw [map_add, cubeDiffPStar_k4ScalarWFreeSection, h1]
  simp only [add_zero]
  exact EEEEInternal.module_add_self
    (k4ScalarKappaWCoeff z.1.1.1)

/-! ## Forward map to the standard P factor -/

noncomputable def k4ScalarTransportedPToPFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2 →ₗ[F]
      PFactor n where
  toFun z := by
    let W : CyclicCube n := z.1.1.1
    let mu : CyclicCube n := k4ScalarWFreeSection z.1.1 + z.1.2
    let A : CyclicCube n := pShiftE2 (k4ScalarPShearEquiv W)
    let Lambda : CyclicCube n := k4ScalarPShearEquiv (mu + W)
    have hH0 : cubeDiffK W + cubeDiffJStar mu = 0 := by
      exact transportedP_literal_H0 hn2 hn hb2 hc2 hd2 z
    have hH1 : k4ScalarKappaWCoeff W + cubeDiffPStar mu = 0 := by
      exact transportedP_literal_H1 hn2 hn hb2 hc2 hd2 z
    have hG0 : cubeDiffK A + cubeDiffJStar Lambda = 0 := by
      have h := k4ScalarP_forward_operator0 W mu
      simpa only [W, mu, A, Lambda, hH0, map_zero] using h
    have hG1 : cubeDiffPStar Lambda = 0 := by
      have h := k4ScalarP_forward_operator1 W mu
      simpa only [W, mu, Lambda, hH0, hH1, map_zero, zero_add] using h.symm
    refine ⟨(A, Lambda), ?_⟩
    apply LinearMap.mem_ker.mpr
    change (cubeDiffPStar Lambda, cubeDiffK A + cubeDiffJStar Lambda) = 0
    exact Prod.ext hG1 hG0
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext
    · simp
    · simp
      abel
  map_smul' a z := by
    apply Subtype.ext
    apply Prod.ext <;> simp

@[simp] theorem k4ScalarTransportedPToPFactor_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) :
    (k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2 z).1.1 =
      pShiftE2 (k4ScalarPShearEquiv z.1.1.1) := rfl

@[simp] theorem k4ScalarTransportedPToPFactor_second
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) :
    (k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2 z).1.2 =
      k4ScalarPShearEquiv
        ((k4ScalarWFreeSection z.1.1 + z.1.2) + z.1.1.1) := rfl

/-! ## Reverse coordinates and ANN-P recovery -/

private noncomputable def pFactorFirst
    {n : Nat} [NeZero n] : PFactor n →ₗ[F] CyclicCube n :=
  (LinearMap.fst F (CyclicCube n) (CyclicCube n)).comp
    (PFactor n).subtype

private noncomputable def pFactorSecond
    {n : Nat} [NeZero n] : PFactor n →ₗ[F] CyclicCube n :=
  (LinearMap.snd F (CyclicCube n) (CyclicCube n)).comp
    (PFactor n).subtype

private noncomputable def recoveredWRaw
    {n : Nat} [NeZero n] : PFactor n →ₗ[F] CyclicCube n :=
  k4ScalarPShearEquiv.symm.toLinearMap.comp
    (pShiftE2.symm.toLinearMap.comp pFactorFirst)

private noncomputable def recoveredPNu
    {n : Nat} [NeZero n] : PFactor n →ₗ[F] CyclicCube n :=
  k4ScalarPShearEquiv.symm.toLinearMap.comp pFactorSecond

private noncomputable def recoveredPMu
    {n : Nat} [NeZero n] : PFactor n →ₗ[F] CyclicCube n :=
  recoveredPNu + recoveredWRaw

private theorem recoveredP_standard_coordinates
    {n : Nat} [NeZero n] (q : PFactor n) :
    pShiftE2 (k4ScalarPShearEquiv (recoveredWRaw q)) = q.1.1 ∧
      k4ScalarPShearEquiv (recoveredPMu q + recoveredWRaw q) = q.1.2 := by
  constructor
  · simp [recoveredWRaw, pFactorFirst]
  · simp only [recoveredPMu, LinearMap.add_apply, recoveredPNu,
      recoveredWRaw, pFactorFirst, pFactorSecond,
      LinearMap.coe_comp, Function.comp_apply]
    rw [add_assoc, EEEEInternal.module_add_self, add_zero]
    simp

private theorem pFactor_rows_zero
    {n : Nat} [NeZero n] (q : PFactor n) :
    cubeDiffPStar q.1.2 = 0 ∧
      cubeDiffK q.1.1 + cubeDiffJStar q.1.2 = 0 := by
  have hq := LinearMap.mem_ker.mp q.2
  change
    (cubeDiffPStar q.1.2,
      cubeDiffK q.1.1 + cubeDiffJStar q.1.2) = 0 at hq
  exact ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩

private theorem recoveredP_H0
    {n : Nat} [NeZero n] (q : PFactor n) :
    cubeDiffK (recoveredWRaw q) +
        cubeDiffJStar (recoveredPMu q) = 0 := by
  have h := k4ScalarP_reverse_operator0
    (recoveredWRaw q) (recoveredPMu q)
  rw [recoveredP_standard_coordinates q |>.1,
    recoveredP_standard_coordinates q |>.2,
    (pFactor_rows_zero q).2, map_zero] at h
  exact h

private theorem recoveredP_H1
    {n : Nat} [NeZero n] (q : PFactor n) :
    k4ScalarKappaWCoeff (recoveredWRaw q) +
        cubeDiffPStar (recoveredPMu q) = 0 := by
  have h := k4ScalarP_reverse_operator1
    (recoveredWRaw q) (recoveredPMu q)
  rw [recoveredP_standard_coordinates q |>.1,
    recoveredP_standard_coordinates q |>.2,
    (pFactor_rows_zero q).1, (pFactor_rows_zero q).2,
    zero_add, map_zero] at h
  exact h

theorem k4ScalarP_recoveredW_mem
    {n : Nat} [NeZero n] (q : PFactor n) :
    k4ScalarPShearEquiv.symm (pShiftE2.symm q.1.1) ∈
      LinearMap.ker (k4PHeadCross (n := n)).flip := by
  change recoveredWRaw q ∈ LinearMap.ker (k4PHeadCross (n := n)).flip
  rw [mem_ker_k4PHeadCross_flip_iff_kappaWCoeff_mem_range_PStar]
  refine ⟨recoveredPMu q, ?_⟩
  exact (EEOEInternal.eq_of_add_eq_zero (recoveredP_H1 q)).symm

private noncomputable def recoveredW
    {n : Nat} [NeZero n] : PFactor n →ₗ[F] K4WFreeHeadRadical n where
  toFun q := ⟨recoveredWRaw q, by
    simpa only [recoveredWRaw, pFactorFirst, LinearMap.coe_comp,
      Function.comp_apply] using k4ScalarP_recoveredW_mem q⟩
  map_add' q r := by
    apply Subtype.ext
    exact map_add recoveredWRaw q r
  map_smul' a q := by
    apply Subtype.ext
    exact map_smul recoveredWRaw a q

private noncomputable def recoveredPLambda
    {n : Nat} [NeZero n] : PFactor n →ₗ[F] CyclicCube n :=
  recoveredPMu + k4ScalarWFreeSection.comp recoveredW

private theorem recoveredP_literal_mem
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : PFactor n) :
    (recoveredW q, recoveredPLambda q) ∈
      K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2 := by
  apply LinearMap.mem_ker.mpr
  rw [transportedPMap_apply]
  apply Prod.ext
  · rw [transportedWRow_normalized, actualAddedWRead_pureWFree]
    simp only [recoveredPLambda, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, map_add]
    have h := recoveredP_H0 q
    calc
      _ = (cubeDiffK (recoveredW q).1 + cubeDiffJStar (recoveredPMu q)) +
          (cubeDiffJStar (k4ScalarWFreeSection (recoveredW q)) +
            cubeDiffJStar (k4ScalarWFreeSection (recoveredW q))) := by abel
      _ = 0 := by
        rw [EEEEInternal.module_add_self, add_zero]
        exact h
  · change cubeDiffPStar (recoveredPLambda q) = 0
    simp only [recoveredPLambda, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, map_add,
      cubeDiffPStar_k4ScalarWFreeSection]
    change cubeDiffPStar (recoveredPMu q) +
      k4ScalarKappaWCoeff (recoveredWRaw q) = 0
    simpa only [add_comm] using recoveredP_H1 q

noncomputable def k4ScalarPFactorToTransportedP
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    PFactor n →ₗ[F]
      K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2 where
  toFun q := ⟨(recoveredW q, recoveredPLambda q),
    recoveredP_literal_mem hn2 hn hb2 hc2 hd2 q⟩
  map_add' q r := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_add recoveredW q r
    · exact map_add recoveredPLambda q r
  map_smul' a q := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_smul recoveredW a q
    · exact map_smul recoveredPLambda a q

@[simp] theorem k4ScalarPFactorToTransportedP_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : PFactor n) :
    (k4ScalarPFactorToTransportedP hn2 hn hb2 hc2 hd2 q).1.1.1 =
      k4ScalarPShearEquiv.symm (pShiftE2.symm q.1.1) := rfl

@[simp] theorem k4ScalarPFactorToTransportedP_second
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : PFactor n) :
    (k4ScalarPFactorToTransportedP hn2 hn hb2 hc2 hd2 q).1.2 =
      (k4ScalarPShearEquiv.symm q.1.2 +
        k4ScalarPShearEquiv.symm (pShiftE2.symm q.1.1)) +
          k4ScalarWFreeSection
            (k4ScalarPFactorToTransportedP hn2 hn hb2 hc2 hd2 q).1.1 := rfl

/-! ## Bilateral inverse laws and the exact P-factor equivalence -/

theorem k4ScalarPFactorToTransportedP_left_inv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) :
    k4ScalarPFactorToTransportedP hn2 hn hb2 hc2 hd2
        (k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2 z) = z := by
  have hW :
      (k4ScalarPFactorToTransportedP hn2 hn hb2 hc2 hd2
        (k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2 z)).1.1 =
        z.1.1 := by
    apply Subtype.ext
    simp
  apply Subtype.ext
  apply Prod.ext
  · exact hW
  · simp only [k4ScalarPFactorToTransportedP_second,
      k4ScalarTransportedPToPFactor_first,
      k4ScalarTransportedPToPFactor_second]
    rw [hW]
    simp
    abel_nf
    simp only [two_smul, EEEEInternal.module_add_self, zero_add]
    rw [add_zero]

theorem k4ScalarTransportedPToPFactor_right_inv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : PFactor n) :
    k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2
        (k4ScalarPFactorToTransportedP hn2 hn hb2 hc2 hd2 q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · exact (recoveredP_standard_coordinates q).1
  · simp only [k4ScalarTransportedPToPFactor_second,
      k4ScalarPFactorToTransportedP_first,
      k4ScalarPFactorToTransportedP_second]
    have h := (recoveredP_standard_coordinates q).2
    rw [← h]
    apply congrArg k4ScalarPShearEquiv
    abel_nf
    simp only [two_smul, EEEEInternal.module_add_self, zero_add]
    rw [k4ScalarPShearEquiv_symm_apply_apply, add_zero]

noncomputable def k4ScalarTransportedPFactorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2 ≃ₗ[F]
      PFactor n where
  toFun := k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2
  invFun := k4ScalarPFactorToTransportedP hn2 hn hb2 hc2 hd2
  left_inv := k4ScalarPFactorToTransportedP_left_inv hn2 hn hb2 hc2 hd2
  right_inv := k4ScalarTransportedPToPFactor_right_inv hn2 hn hb2 hc2 hd2
  map_add' := map_add (k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2)
  map_smul' := map_smul (k4ScalarTransportedPToPFactor hn2 hn hb2 hc2 hd2)

theorem finrank_K4ScalarTransportedPFactor_add
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) + n =
      2 * n ^ 2 + 1 := by
  rw [LinearEquiv.finrank_eq
    (k4ScalarTransportedPFactorEquiv hn2 hn hb2 hc2 hd2)]
  exact finrank_PFactor_addition_safe

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
