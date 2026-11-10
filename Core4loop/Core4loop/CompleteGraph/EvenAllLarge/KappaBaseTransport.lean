import Core4loop.CompleteGraph.EvenAllLarge.BaseQZero
import Core4loop.SquareDiagonal.EvenP.TotalEEEE.Rank

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.GPolarRankPrep

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.CubeCompat

noncomputable section

/-! ## Exact cyclic permutations -/

noncomputable def k4TP
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f (-j) i k
  invFun g := fun i j k => g j (-i) k
  left_inv f := by
    funext i j k
    simp
  right_inv g := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4TR
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f i k (-j)
  invFun g := fun i j k => g i (-k) j
  left_inv f := by
    funext i j k
    simp
  right_inv g := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem k4TP_cubeDiffI_to_J
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    cubeDiffJInv (k4TP f) = k4TP (cubeDiffI f) := by
  funext i j k
  rw [EEOEInternal.cubeDiffJInv_apply]
  change f (-j) i k + f (-(j - 1)) i k =
    f (-j) i k + f (-j + 1) i k
  congr 3
  abel

theorem k4TR_cubeDiffK_to_J
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    cubeDiffJInv (k4TR f) = k4TR (cubeDiffK f) := by
  funext i j k
  rw [EEOEInternal.cubeDiffJInv_apply]
  change f i k (-j) + f i k (-(j - 1)) =
    cubeDiffK f i k (-j)
  rw [EEOEInternal.cubeDiffK_apply]
  congr 3
  abel

theorem k4TP_cubeDiffK
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    k4TP (cubeDiffK f) = cubeDiffK (k4TP f) := by
  funext i j k
  rw [EEOEInternal.cubeDiffK_apply]
  change cubeDiffK f (-j) i k =
    k4TP f i j k + k4TP f i j (k + 1)
  rw [EEOEInternal.cubeDiffK_apply]
  rfl

theorem k4TR_cubeDiffI
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    k4TR (cubeDiffI f) = cubeDiffI (k4TR f) := by
  funext i j k
  rw [EEOEInternal.cubeDiffI_apply]
  change cubeDiffI f i k (-j) =
    k4TR f i j k + k4TR f (i + 1) j k
  rw [EEOEInternal.cubeDiffI_apply]
  rfl

/-! ## Restricted P/R-kernel to J-kernel equivalences -/

noncomputable def k4PKerToJKernel
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffP (n := n)) ≃ₗ[F]
      T37RightP1.T37JKernel n where
  toFun B :=
    ⟨k4TP (EEEEInternal.prShear B.1), by
      apply LinearMap.mem_ker.mpr
      rw [k4TP_cubeDiffI_to_J, ← EEEEInternal.prShear_cubeDiffP,
        LinearMap.mem_ker.mp B.2]
      exact map_zero (k4TP (n := n))⟩
  invFun q :=
    ⟨(EEEEInternal.prShear (n := n)).symm ((k4TP (n := n)).symm q.1), by
      apply LinearMap.mem_ker.mpr
      apply (EEEEInternal.prShear (n := n)).injective
      rw [map_zero, EEEEInternal.prShear_cubeDiffP]
      apply (k4TP (n := n)).injective
      rw [map_zero, ← k4TP_cubeDiffI_to_J]
      simpa only [LinearEquiv.apply_symm_apply] using
        (LinearMap.mem_ker.mp q.2)⟩
  left_inv B := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp
  map_add' B B' := by
    apply Subtype.ext
    simp
  map_smul' r B := by
    apply Subtype.ext
    simp

noncomputable def k4RKerToJKernel
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffR (n := n)) ≃ₗ[F]
      T37RightP1.T37JKernel n where
  toFun W :=
    ⟨k4TR (EEEEInternal.prShear W.1), by
      apply LinearMap.mem_ker.mpr
      rw [k4TR_cubeDiffK_to_J, ← EEEEInternal.prShear_cubeDiffR,
        LinearMap.mem_ker.mp W.2]
      exact map_zero (k4TR (n := n))⟩
  invFun q :=
    ⟨(EEEEInternal.prShear (n := n)).symm ((k4TR (n := n)).symm q.1), by
      apply LinearMap.mem_ker.mpr
      apply (EEEEInternal.prShear (n := n)).injective
      rw [map_zero, EEEEInternal.prShear_cubeDiffR]
      apply (k4TR (n := n)).injective
      rw [map_zero, ← k4TR_cubeDiffK_to_J]
      simpa only [LinearEquiv.apply_symm_apply] using
        (LinearMap.mem_ker.mp q.2)⟩
  left_inv W := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp
  map_add' W W' := by
    apply Subtype.ext
    simp
  map_smul' r W := by
    apply Subtype.ext
    simp

/-! ## Pairing invariance -/

theorem cubeDot_k4TP
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot (k4TP X) (k4TP Y) = cubeDot X Y := by
  unfold cubeDot k4TP
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    { toFun := fun q : I n × I n × I n =>
        (q.2.1, -q.1, q.2.2)
      invFun := fun q : I n × I n × I n =>
        (-q.2.1, q.1, q.2.2)
      left_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp
      right_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp }
  symm
  apply Fintype.sum_equiv e
  intro q
  simp [e]

theorem cubeDot_k4TR
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot (k4TR X) (k4TR Y) = cubeDot X Y := by
  unfold cubeDot k4TR
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    { toFun := fun q : I n × I n × I n =>
        (q.1, -q.2.2, q.2.1)
      invFun := fun q : I n × I n × I n =>
        (q.1, q.2.2, -q.2.1)
      left_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp
      right_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp }
  symm
  apply Fintype.sum_equiv e
  intro q
  simp [e]

/-! ## P-kernel phase transport -/

theorem k4PKer_shift
    {n : Nat} [NeZero n]
    (B : LinearMap.ker (cubeDiffP (n := n)))
    (i j k : I n) :
    B.1 i (j + 1) k = B.1 (i + 1) j k := by
  have hzero := congrFun (congrFun (congrFun
    (LinearMap.mem_ker.mp B.2) i) (j + 1)) k
  rw [EEOEInternal.cubeDiffP_apply] at hzero
  apply (add_eq_zero_iff_eq_of_F_module _ _).mp at hzero
  simpa only [show j + 1 - 1 = j by abel] using hzero

theorem k4Kappa_pker_prShear
    {n : Nat} [NeZero n]
    (B : LinearMap.ker (cubeDiffP (n := n)))
    (W : CyclicCube n) :
    cubeDot (cubeDiffK (EEEEInternal.prShear W))
        (EEEEInternal.prShear B.1) =
      k4CubeKappa B.1 W := by
  unfold cubeDot k4CubeKappa EEEEInternal.prShear
  simp_rw [EEOEInternal.cubeDiffK_apply]
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
      { toFun := fun q : I n × I n × I n =>
          (q.1, q.1 + q.2.1 + q.2.2, q.2.2)
        invFun := fun q : I n × I n × I n =>
          (q.1, q.2.1 - q.1 - q.2.2, q.2.2)
        left_inv := by
          intro q
          rcases q with ⟨i, j, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl
        right_inv := by
          intro q
          rcases q with ⟨i, s, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl }
    symm
    apply Fintype.sum_equiv e
    intro q
    simp [e]
    ring_nf
  · let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
      { toFun := fun q : I n × I n × I n =>
          (q.1, q.1 + (q.2.1 + 1) + q.2.2, q.2.2)
        invFun := fun q : I n × I n × I n =>
          (q.1, q.2.1 - q.1 - q.2.2 - 1, q.2.2)
        left_inv := by
          intro q
          rcases q with ⟨i, j, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl
        right_inv := by
          intro q
          rcases q with ⟨i, s, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl }
    symm
    apply Fintype.sum_equiv e
    intro q
    simp only [e, Equiv.coe_fn_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hW :
        q.1 + (q.2.1 + 1) + q.2.2 - q.1 - (q.2.2 + 1) =
          q.2.1 := by abel
    have hB :
        q.1 + (q.2.1 + 1) + q.2.2 - q.1 - q.2.2 =
          q.2.1 + 1 := by abel
    rw [hW, hB, k4PKer_shift]
    ring_nf

theorem k4Kappa_pker_base_transport
    {n : Nat} [NeZero n]
    (B : LinearMap.ker (cubeDiffP (n := n)))
    (W : CyclicCube n) :
    TotalEEEERankInternal.freeToJKernelK
        (k4TP (EEEEInternal.prShear W))
        (k4PKerToJKernel B) =
      k4CubeKappa B.1 W := by
  change cubeDot
      (cubeDiffK (k4TP (EEEEInternal.prShear W)))
      (k4TP (EEEEInternal.prShear B.1)) =
    k4CubeKappa B.1 W
  rw [← k4TP_cubeDiffK, cubeDot_k4TP]
  exact k4Kappa_pker_prShear B W

/-! ## R-kernel phase transport -/

theorem k4RKer_shift
    {n : Nat} [NeZero n]
    (W : LinearMap.ker (cubeDiffR (n := n)))
    (i j k : I n) :
    W.1 i (j + 1) k = W.1 i j (k + 1) := by
  have hzero := congrFun (congrFun (congrFun
    (LinearMap.mem_ker.mp W.2) i) (j + 1)) k
  rw [EEOEInternal.cubeDiffR_apply] at hzero
  apply (add_eq_zero_iff_eq_of_F_module _ _).mp at hzero
  simpa only [show j + 1 - 1 = j by abel] using hzero

theorem k4Kappa_rker_prShear
    {n : Nat} [NeZero n]
    (B : CyclicCube n)
    (W : LinearMap.ker (cubeDiffR (n := n))) :
    cubeDot (cubeDiffI (EEEEInternal.prShear B))
        (EEEEInternal.prShear W.1) =
      k4CubeKappa B W.1 := by
  unfold cubeDot k4CubeKappa EEEEInternal.prShear
  simp_rw [EEOEInternal.cubeDiffI_apply]
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
      { toFun := fun q : I n × I n × I n =>
          (q.1, q.1 + q.2.1 + q.2.2, q.2.2)
        invFun := fun q : I n × I n × I n =>
          (q.1, q.2.1 - q.1 - q.2.2, q.2.2)
        left_inv := by
          intro q
          rcases q with ⟨i, j, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl
        right_inv := by
          intro q
          rcases q with ⟨i, s, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl }
    symm
    apply Fintype.sum_equiv e
    intro q
    simp [e]
    ring_nf
  · let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
      { toFun := fun q : I n × I n × I n =>
          (q.1, q.1 + (q.2.1 + 1) + q.2.2, q.2.2)
        invFun := fun q : I n × I n × I n =>
          (q.1, q.2.1 - q.1 - q.2.2 - 1, q.2.2)
        left_inv := by
          intro q
          rcases q with ⟨i, j, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl
        right_inv := by
          intro q
          rcases q with ⟨i, s, k⟩
          apply Prod.ext
          · rfl
          · apply Prod.ext
            · simp [sub_eq_add_neg]
              abel
            · rfl }
    symm
    apply Fintype.sum_equiv e
    intro q
    simp only [e, Equiv.coe_fn_mk, LinearEquiv.coe_mk,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hB :
        q.1 + (q.2.1 + 1) + q.2.2 - (q.1 + 1) - q.2.2 =
          q.2.1 := by abel
    have hW :
        q.1 + (q.2.1 + 1) + q.2.2 - q.1 - q.2.2 =
          q.2.1 + 1 := by abel
    rw [hB, hW, k4RKer_shift]

theorem k4Kappa_rker_base_transport
    {n : Nat} [NeZero n]
    (B : CyclicCube n)
    (W : LinearMap.ker (cubeDiffR (n := n))) :
    TotalEEEERankInternal.freeToJKernelI
        (k4TR (EEEEInternal.prShear B))
        (k4RKerToJKernel W) =
      k4CubeKappa B W.1 := by
  change cubeDot
      (cubeDiffI (k4TR (EEEEInternal.prShear B)))
      (k4TR (EEEEInternal.prShear W.1)) =
    k4CubeKappa B W.1
  rw [← k4TR_cubeDiffI, cubeDot_k4TR]
  exact k4Kappa_rker_prShear B W

end

end Core4loop.CompleteGraph.EvenP.GPolarRankPrep
