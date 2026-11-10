import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Rank.FreeRadicals

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

/-! ## The frozen transported-R coordinate chart -/

noncomputable def k4ScalarRTranslateEquiv
    {n : Nat} [NeZero n] (u v w : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X := fun i j k => X (i + u) (j + v) (k + w)
  invFun X := fun i j k => X (i - u) (j - v) (k - w)
  left_inv X := by
    funext i j k
    dsimp
    congr 3 <;> abel
  right_inv X := by
    funext i j k
    dsimp
    congr 3 <;> abel
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem k4ScalarRTranslateEquiv_apply
    {n : Nat} [NeZero n] (u v w : I n)
    (X : CyclicCube n) (i j k : I n) :
    k4ScalarRTranslateEquiv u v w X i j k =
      X (i + u) (j + v) (k + w) := rfl

@[simp] theorem k4ScalarRTranslateEquiv_symm_apply
    {n : Nat} [NeZero n] (u v w : I n)
    (X : CyclicCube n) (i j k : I n) :
    (k4ScalarRTranslateEquiv u v w).symm X i j k =
      X (i - u) (j - v) (k - w) := rfl

noncomputable def k4ScalarRShearEquiv
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X := fun i j k => X i (j + k - i) (-k)
  invFun X := fun i j k => X i (j + i + k) (-k)
  left_inv X := by
    funext i j k
    dsimp
    congr 3 <;> abel
  right_inv X := by
    funext i j k
    dsimp
    congr 3 <;> abel
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem k4ScalarRShearEquiv_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) (i j k : I n) :
    k4ScalarRShearEquiv X i j k = X i (j + k - i) (-k) := rfl

@[simp] theorem k4ScalarRShearEquiv_symm_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) (i j k : I n) :
    k4ScalarRShearEquiv.symm X i j k = X i (j + i + k) (-k) := rfl

@[simp] theorem k4ScalarRShearEquiv_symm_apply_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) :
    k4ScalarRShearEquiv.symm (k4ScalarRShearEquiv X) = X :=
  k4ScalarRShearEquiv.left_inv X

@[simp] theorem k4ScalarRShearEquiv_apply_symm_apply
    {n : Nat} [NeZero n] (X : CyclicCube n) :
    k4ScalarRShearEquiv (k4ScalarRShearEquiv.symm X) = X :=
  k4ScalarRShearEquiv.right_inv X

private noncomputable abbrev rShiftE2
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n :=
  k4ScalarRTranslateEquiv 0 1 0

private noncomputable abbrev rShiftNegE3
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n :=
  k4ScalarRTranslateEquiv 0 0 (-1)

private noncomputable abbrev rShiftE3SubE2
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n :=
  k4ScalarRTranslateEquiv 0 (-1) 1

/-! ## Four ambient operator identities -/

theorem k4ScalarR_forward_operator0
    {n : Nat} [NeZero n] (B mu : CyclicCube n) :
    cubeDiffI (rShiftE2 (k4ScalarRShearEquiv B)) +
        cubeDiffJStar (k4ScalarRShearEquiv (mu + B)) =
      k4ScalarRShearEquiv (cubeDiffI B + cubeDiffJStar mu) := by
  funext i j k
  simp only [Pi.add_apply, EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffJStar_apply,
    k4ScalarRTranslateEquiv_apply, k4ScalarRShearEquiv_apply,
    add_zero]
  have h1 : j + 1 + k - (i + 1) = j + k - i := by abel
  have h2 : j + 1 + k - i = j + k - i + 1 := by abel
  rw [h1, h2]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]

theorem k4ScalarR_forward_operator1
    {n : Nat} [NeZero n] (B mu : CyclicCube n) :
    k4ScalarRShearEquiv
        ((k4ScalarKappaBCoeff B + cubeDiffRStar mu) +
          rShiftNegE3 (cubeDiffI B + cubeDiffJStar mu)) =
      rShiftE3SubE2
        (cubeDiffRStar (k4ScalarRShearEquiv (mu + B))) := by
  funext i j k
  simp only [Pi.add_apply, EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffJStar_apply,
    EEOEInternal.cubeDiffRStar_apply,
    k4ScalarKappaBCoeff, LinearMap.coe_mk, AddHom.coe_mk,
    k4ScalarRTranslateEquiv_apply, k4ScalarRShearEquiv_apply, add_zero]
  have h0 : -k - 1 = -(k + 1) := by abel
  have h1 : -k + -1 = -(k + 1) := by abel
  have h2 : j + -1 + (k + 1) - i = j + k - i := by abel
  have h3 : k + 1 - 1 = k := by abel
  have h4 : j + -1 + 1 + k - i = j + k - i := by abel
  rw [h0, h1, h2, h3, h4]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, zero_add]

theorem k4ScalarR_reverse_operator0
    {n : Nat} [NeZero n] (B mu : CyclicCube n) :
    cubeDiffI B + cubeDiffJStar mu =
      k4ScalarRShearEquiv.symm
        (cubeDiffI (rShiftE2 (k4ScalarRShearEquiv B)) +
          cubeDiffJStar (k4ScalarRShearEquiv (mu + B))) := by
  rw [k4ScalarR_forward_operator0]
  exact (k4ScalarRShearEquiv.left_inv _).symm

theorem k4ScalarR_reverse_operator1
    {n : Nat} [NeZero n] (B mu : CyclicCube n) :
    k4ScalarKappaBCoeff B + cubeDiffRStar mu =
      k4ScalarRShearEquiv.symm
        (rShiftE3SubE2
          (cubeDiffRStar (k4ScalarRShearEquiv (mu + B)) +
            (cubeDiffI (rShiftE2 (k4ScalarRShearEquiv B)) +
              cubeDiffJStar (k4ScalarRShearEquiv (mu + B))))) := by
  funext i j k
  simp only [Pi.add_apply, EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffJStar_apply,
    EEOEInternal.cubeDiffRStar_apply,
    k4ScalarKappaBCoeff, LinearMap.coe_mk, AddHom.coe_mk,
    k4ScalarRTranslateEquiv_apply, k4ScalarRShearEquiv_apply,
    k4ScalarRShearEquiv_symm_apply, add_zero]
  have h0 : j + i + k + -1 + (-k + 1) - i = j := by abel
  have h1 : -(-k + 1) = k - 1 := by abel
  have h2 : j + i + k + -1 + 1 + (-k + 1 - 1) - i = j := by abel
  have h3 : -(-k + 1 - 1) = k := by abel
  have h4 : j + i + k + -1 + 1 + (-k + 1) - i = j + 1 := by abel
  have h5 : j + i + k + -1 + 1 + (-k + 1) - (i + 1) = j := by abel
  rw [h0, h1, h2, h3, h4, h5]
  abel_nf
  simp only [two_smul, EEEEInternal.module_add_self, add_zero]

/-! ## Literal K4 equations in the full transported coordinates -/

private theorem transportedR_literal_H0
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) :
    cubeDiffI z.1.1.1 +
        cubeDiffJStar (k4ScalarBFreeSection z.1.1 + z.1.2) = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  have h0 := congrArg Prod.fst hz
  rw [transportedRMap_apply] at h0
  rw [transportedBRow_normalized,
    actualAddedBRead_pureBFree] at h0
  simpa only [map_add, add_assoc] using h0

private theorem transportedR_literal_H1
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) :
    k4ScalarKappaBCoeff z.1.1.1 +
        cubeDiffRStar (k4ScalarBFreeSection z.1.1 + z.1.2) = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  have h1 := congrArg Prod.snd hz
  rw [transportedRMap_apply] at h1
  change cubeDiffRStar z.1.2 = 0 at h1
  rw [map_add, cubeDiffRStar_k4ScalarBFreeSection, h1]
  simp only [add_zero]
  exact EEEEInternal.module_add_self
    (k4ScalarKappaBCoeff z.1.1.1)

/-! ## Forward map to the standard R factor -/

noncomputable def k4ScalarTransportedRToRFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2 →ₗ[F]
      RFactor n where
  toFun z := by
    let B : CyclicCube n := z.1.1.1
    let mu : CyclicCube n := k4ScalarBFreeSection z.1.1 + z.1.2
    let A : CyclicCube n := rShiftE2 (k4ScalarRShearEquiv B)
    let Lambda : CyclicCube n := k4ScalarRShearEquiv (mu + B)
    have hH0 : cubeDiffI B + cubeDiffJStar mu = 0 := by
      exact transportedR_literal_H0 hn2 hn hb2 hc2 hd2 z
    have hH1 : k4ScalarKappaBCoeff B + cubeDiffRStar mu = 0 := by
      exact transportedR_literal_H1 hn2 hn hb2 hc2 hd2 z
    have hG0 : cubeDiffI A + cubeDiffJStar Lambda = 0 := by
      have h := k4ScalarR_forward_operator0 B mu
      simpa only [B, mu, A, Lambda, hH0, map_zero] using h
    have hShiftG1 : rShiftE3SubE2 (cubeDiffRStar Lambda) = 0 := by
      have h := k4ScalarR_forward_operator1 B mu
      simpa only [B, mu, Lambda, hH0, hH1, map_zero, zero_add] using h.symm
    have hG1 : cubeDiffRStar Lambda = 0 := by
      apply rShiftE3SubE2.injective
      simpa only [map_zero] using hShiftG1
    refine ⟨(A, Lambda), ?_⟩
    apply LinearMap.mem_ker.mpr
    change (cubeDiffRStar Lambda, cubeDiffI A + cubeDiffJStar Lambda) = 0
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

@[simp] theorem k4ScalarTransportedRToRFactor_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) :
    (k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2 z).1.1 =
      rShiftE2 (k4ScalarRShearEquiv z.1.1.1) := rfl

@[simp] theorem k4ScalarTransportedRToRFactor_second
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) :
    (k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2 z).1.2 =
      k4ScalarRShearEquiv
        ((k4ScalarBFreeSection z.1.1 + z.1.2) + z.1.1.1) := rfl

/-! ## Reverse coordinates and ANN-R recovery -/

private noncomputable def rFactorFirst
    {n : Nat} [NeZero n] : RFactor n →ₗ[F] CyclicCube n :=
  (LinearMap.fst F (CyclicCube n) (CyclicCube n)).comp
    (RFactor n).subtype

private noncomputable def rFactorSecond
    {n : Nat} [NeZero n] : RFactor n →ₗ[F] CyclicCube n :=
  (LinearMap.snd F (CyclicCube n) (CyclicCube n)).comp
    (RFactor n).subtype

private noncomputable def recoveredBRaw
    {n : Nat} [NeZero n] : RFactor n →ₗ[F] CyclicCube n :=
  k4ScalarRShearEquiv.symm.toLinearMap.comp
    (rShiftE2.symm.toLinearMap.comp rFactorFirst)

private noncomputable def recoveredNu
    {n : Nat} [NeZero n] : RFactor n →ₗ[F] CyclicCube n :=
  k4ScalarRShearEquiv.symm.toLinearMap.comp rFactorSecond

private noncomputable def recoveredMu
    {n : Nat} [NeZero n] : RFactor n →ₗ[F] CyclicCube n :=
  recoveredNu + recoveredBRaw

private theorem recovered_standard_coordinates
    {n : Nat} [NeZero n] (q : RFactor n) :
    rShiftE2 (k4ScalarRShearEquiv (recoveredBRaw q)) = q.1.1 ∧
      k4ScalarRShearEquiv (recoveredMu q + recoveredBRaw q) = q.1.2 := by
  constructor
  · simp [recoveredBRaw, rFactorFirst]
  · simp only [recoveredMu, LinearMap.add_apply, recoveredNu,
      recoveredBRaw, rFactorFirst, rFactorSecond,
      LinearMap.coe_comp, Function.comp_apply]
    rw [add_assoc, EEEEInternal.module_add_self, add_zero]
    simp

private theorem rFactor_rows_zero
    {n : Nat} [NeZero n] (q : RFactor n) :
    cubeDiffRStar q.1.2 = 0 ∧
      cubeDiffI q.1.1 + cubeDiffJStar q.1.2 = 0 := by
  have hq := LinearMap.mem_ker.mp q.2
  change
    (cubeDiffRStar q.1.2,
      cubeDiffI q.1.1 + cubeDiffJStar q.1.2) = 0 at hq
  exact ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩

private theorem recovered_H0
    {n : Nat} [NeZero n] (q : RFactor n) :
    cubeDiffI (recoveredBRaw q) +
        cubeDiffJStar (recoveredMu q) = 0 := by
  have h := k4ScalarR_reverse_operator0
    (recoveredBRaw q) (recoveredMu q)
  rw [recovered_standard_coordinates q |>.1,
    recovered_standard_coordinates q |>.2,
    (rFactor_rows_zero q).2, map_zero] at h
  exact h

private theorem recovered_H1
    {n : Nat} [NeZero n] (q : RFactor n) :
    k4ScalarKappaBCoeff (recoveredBRaw q) +
        cubeDiffRStar (recoveredMu q) = 0 := by
  have h := k4ScalarR_reverse_operator1
    (recoveredBRaw q) (recoveredMu q)
  rw [recovered_standard_coordinates q |>.1,
    recovered_standard_coordinates q |>.2,
    (rFactor_rows_zero q).1, (rFactor_rows_zero q).2,
    zero_add, map_zero] at h
  exact h

theorem k4ScalarR_recoveredB_mem
    {n : Nat} [NeZero n] (q : RFactor n) :
    k4ScalarRShearEquiv.symm (rShiftE2.symm q.1.1) ∈
      LinearMap.ker (k4RHeadCross (n := n)) := by
  change recoveredBRaw q ∈ LinearMap.ker (k4RHeadCross (n := n))
  rw [mem_ker_k4RHeadCross_iff_kappaBCoeff_mem_range_RStar]
  refine ⟨recoveredMu q, ?_⟩
  exact (EEOEInternal.eq_of_add_eq_zero (recovered_H1 q)).symm

private noncomputable def recoveredB
    {n : Nat} [NeZero n] : RFactor n →ₗ[F] K4BFreeHeadRadical n where
  toFun q := ⟨recoveredBRaw q, by
    simpa only [recoveredBRaw, rFactorFirst, LinearMap.coe_comp,
      Function.comp_apply] using k4ScalarR_recoveredB_mem q⟩
  map_add' q r := by
    apply Subtype.ext
    exact map_add recoveredBRaw q r
  map_smul' a q := by
    apply Subtype.ext
    exact map_smul recoveredBRaw a q

private noncomputable def recoveredLambda
    {n : Nat} [NeZero n] : RFactor n →ₗ[F] CyclicCube n :=
  recoveredMu + k4ScalarBFreeSection.comp recoveredB

private theorem recovered_literal_mem
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : RFactor n) :
    (recoveredB q, recoveredLambda q) ∈
      K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2 := by
  apply LinearMap.mem_ker.mpr
  rw [transportedRMap_apply]
  apply Prod.ext
  · rw [transportedBRow_normalized, actualAddedBRead_pureBFree]
    simp only [recoveredLambda, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, map_add]
    have h := recovered_H0 q
    calc
      _ = (cubeDiffI (recoveredB q).1 + cubeDiffJStar (recoveredMu q)) +
          (cubeDiffJStar (k4ScalarBFreeSection (recoveredB q)) +
            cubeDiffJStar (k4ScalarBFreeSection (recoveredB q))) := by abel
      _ = 0 := by
        rw [EEEEInternal.module_add_self, add_zero]
        exact h
  · change cubeDiffRStar (recoveredLambda q) = 0
    simp only [recoveredLambda, LinearMap.add_apply,
      LinearMap.coe_comp, Function.comp_apply, map_add,
      cubeDiffRStar_k4ScalarBFreeSection]
    change cubeDiffRStar (recoveredMu q) +
      k4ScalarKappaBCoeff (recoveredBRaw q) = 0
    simpa only [add_comm] using recovered_H1 q

noncomputable def k4ScalarRFactorToTransportedR
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    RFactor n →ₗ[F]
      K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2 where
  toFun q := ⟨(recoveredB q, recoveredLambda q),
    recovered_literal_mem hn2 hn hb2 hc2 hd2 q⟩
  map_add' q r := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_add recoveredB q r
    · exact map_add recoveredLambda q r
  map_smul' a q := by
    apply Subtype.ext
    apply Prod.ext
    · exact map_smul recoveredB a q
    · exact map_smul recoveredLambda a q

@[simp] theorem k4ScalarRFactorToTransportedR_first
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : RFactor n) :
    (k4ScalarRFactorToTransportedR hn2 hn hb2 hc2 hd2 q).1.1.1 =
      k4ScalarRShearEquiv.symm (rShiftE2.symm q.1.1) := rfl

@[simp] theorem k4ScalarRFactorToTransportedR_second
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : RFactor n) :
    (k4ScalarRFactorToTransportedR hn2 hn hb2 hc2 hd2 q).1.2 =
      (k4ScalarRShearEquiv.symm q.1.2 +
        k4ScalarRShearEquiv.symm (rShiftE2.symm q.1.1)) +
          k4ScalarBFreeSection
            (k4ScalarRFactorToTransportedR hn2 hn hb2 hc2 hd2 q).1.1 := rfl

/-! ## Bilateral inverse laws and the exact factor equivalence -/

theorem k4ScalarRFactorToTransportedR_left_inv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) :
    k4ScalarRFactorToTransportedR hn2 hn hb2 hc2 hd2
        (k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2 z) = z := by
  have hB :
      (k4ScalarRFactorToTransportedR hn2 hn hb2 hc2 hd2
        (k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2 z)).1.1 =
        z.1.1 := by
    apply Subtype.ext
    simp
  apply Subtype.ext
  apply Prod.ext
  · exact hB
  · simp only [k4ScalarRFactorToTransportedR_second,
      k4ScalarTransportedRToRFactor_first,
      k4ScalarTransportedRToRFactor_second]
    rw [hB]
    simp
    abel_nf
    simp only [two_smul, EEEEInternal.module_add_self, zero_add]
    rw [add_zero]

theorem k4ScalarTransportedRToRFactor_right_inv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : RFactor n) :
    k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2
        (k4ScalarRFactorToTransportedR hn2 hn hb2 hc2 hd2 q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · exact (recovered_standard_coordinates q).1
  · simp only [k4ScalarTransportedRToRFactor_second,
      k4ScalarRFactorToTransportedR_first,
      k4ScalarRFactorToTransportedR_second]
    have h := (recovered_standard_coordinates q).2
    rw [← h]
    apply congrArg k4ScalarRShearEquiv
    abel_nf
    simp only [two_smul, EEEEInternal.module_add_self, zero_add]
    rw [k4ScalarRShearEquiv_symm_apply_apply, add_zero]

noncomputable def k4ScalarTransportedRFactorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2 ≃ₗ[F]
      RFactor n where
  toFun := k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2
  invFun := k4ScalarRFactorToTransportedR hn2 hn hb2 hc2 hd2
  left_inv := k4ScalarRFactorToTransportedR_left_inv hn2 hn hb2 hc2 hd2
  right_inv := k4ScalarTransportedRToRFactor_right_inv hn2 hn hb2 hc2 hd2
  map_add' := map_add (k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2)
  map_smul' := map_smul (k4ScalarTransportedRToRFactor hn2 hn hb2 hc2 hd2)

theorem finrank_K4ScalarTransportedRFactor_add
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) + n =
      2 * n ^ 2 + 1 := by
  rw [LinearEquiv.finrank_eq
    (k4ScalarTransportedRFactorEquiv hn2 hn hb2 hc2 hd2)]
  exact finrank_RFactor_addition_safe

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
