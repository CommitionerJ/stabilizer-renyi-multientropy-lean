import Core4loop.CompleteGraph.PreC.Reduction
import Core4loop.CompleteGraph.ScalarCycle.CycleCertificate
import Core4loop.ZeroSumSpaces.ExplicitCyclicPrefix

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.ScalarCycle

noncomputable section

private def scalarVec {n : Nat} [NeZero n] (t : I n) : Vec n 1 :=
  vecSingle Nat.zero_lt_one t

private theorem vecSum_scalarVec
    {n : Nat} [NeZero n] (t : I n) :
    vecSum (scalarVec t) = t := by
  exact vecSum_vecSingle Nat.zero_lt_one t

private theorem scalarVec_vecSum
    {n : Nat} [NeZero n] (v : Vec n 1) :
    scalarVec (vecSum v) = v := by
  funext q
  fin_cases q
  simp [scalarVec, vecSum, vecSingle]

private theorem vec_eq_scalarVec_iff
    {n : Nat} [NeZero n] (v : Vec n 1) (t : I n) :
    v = scalarVec t ↔ vecSum v = t := by
  constructor
  · intro h
    rw [h, vecSum_scalarVec]
  · intro h
    rw [← h, scalarVec_vecSum]

private theorem vecSum_add_one_eq_iff
    {n : Nat} [NeZero n] (v : Vec n 1) (t : I n) :
    vecSum v + 1 = t ↔ v = scalarVec (t - 1) := by
  rw [vec_eq_scalarVec_iff]
  constructor
  · intro h
    calc
      vecSum v = (vecSum v + 1) - 1 := by
        exact (add_sub_cancel_right (vecSum v) 1).symm
      _ = t - 1 := by rw [h]
  · intro h
    rw [h, sub_add_cancel]

private noncomputable def scalarVecEquiv
    (n : Nat) [NeZero n] : I n ≃ Vec n 1 where
  toFun := scalarVec
  invFun := vecSum
  left_inv := vecSum_scalarVec
  right_inv := scalarVec_vecSum

private theorem scalarVec_inj
    {n : Nat} [NeZero n] {s t : I n} :
    scalarVec s = scalarVec t ↔ s = t :=
  (scalarVecEquiv n).injective.eq_iff

private theorem sum_vecOne_reindex
    {n : Nat} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : Vec n 1 → M) :
    (∑ v : Vec n 1, f v) = ∑ t : I n, f (scalarVec t) := by
  exact ((scalarVecEquiv n).sum_comp f).symm

private theorem pVecOne_eq_zeroVec
    {n : Nat} [NeZero n] (p : PVec n 1) :
    p = (zeroVec : PVec n 1) := by
  funext q
  exact Fin.elim0 q

private theorem sum_pVecOne
    {n : Nat} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : PVec n 1 → M) :
    (∑ p : PVec n 1, f p) = f (zeroVec : PVec n 1) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    exact (hp (pVecOne_eq_zeroVec p)).elim
  · simp

noncomputable def k4ScalarA
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) : K4Cube n :=
  fun i j k => x.1.1 (scalarVec i) (scalarVec j) (scalarVec k)

noncomputable def k4ScalarB
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) : K4Cube n :=
  fun i j k =>
    x.1.2.1 (zeroVec : PVec n 1) i (scalarVec j) (scalarVec k)

noncomputable def k4ScalarW
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) : K4Cube n :=
  fun i j k =>
    x.1.2.2 (zeroVec : PVec n 1) (scalarVec i) (scalarVec j) k

noncomputable def k4ScalarZ
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) : K4Cube n :=
  cyclicDiffX (k4ScalarB x) + cyclicDiffZ (k4ScalarW x)

noncomputable def k4ScalarC
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) : K4Cube n :=
  fun i j k => explicitCyclicPrefix (fun t => k4ScalarZ x i t k) j

private def k4ScalarDualBRead
    {n : Nat} [NeZero n]
    (C W : K4Cube n) : K4Cube n :=
  fun i j k =>
    C i j k + C (i - 1) (j + 1) k
      + W i j k + W (i - 1) j (k + 1)

noncomputable def k4ScalarR
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) : K4Cube n :=
  fun i j k =>
    explicitCyclicPrefix
      (fun t => k4ScalarDualBRead (k4ScalarC x) (k4ScalarW x) t j k)
      (i + 1)

private def cPoint
    {n : Nat} [NeZero n] (i j k : I n) : CFun4 n 1 1 1 :=
  fun p y sz w =>
    if (p, y, sz, w) =
        ((zeroVec : PVec n 1), scalarVec i, j, scalarVec k)
    then 1 else 0

private def rootPoint
    {n : Nat} [NeZero n] (i j k : I n) : RootTarget n 1 1 1 :=
  fun y z w =>
    if (y, z, w) = (scalarVec i, scalarVec j, scalarVec k)
    then 1 else 0

private theorem coeffApply_cPoint
    {n : Nat} [NeZero n]
    (D : CFun4 n 1 1 1) (i j k : I n) :
    coeffApply (cFun4Equiv n 1 1 1 D)
        (cFun4Equiv n 1 1 1 (cPoint i j k)) =
      D (zeroVec : PVec n 1) (scalarVec i) j (scalarVec k) := by
  classical
  unfold coeffApply cFun4Equiv cPoint
  rw [Finset.sum_eq_single
    ((zeroVec : PVec n 1), scalarVec i, j, scalarVec k)]
  · simp
  · intro u _ hu
    rcases u with ⟨p, y, sz, w⟩
    have hne :
        (p, y, sz, w) ≠
          ((zeroVec : PVec n 1), scalarVec i, j, scalarVec k) := hu
    change
      (if (p, y, sz, w) =
          ((zeroVec : PVec n 1), scalarVec i, j, scalarVec k)
        then 1 else 0) * D p y sz w = 0
    rw [if_neg hne, zero_mul]
  · simp

private theorem coeffApplyA_rootPoint
    {n : Nat} [NeZero n]
    (A : AFun4 n 1 1 1) (i j k : I n) :
    coeffApplyA (rootPoint i j k) A =
      A (scalarVec i) (scalarVec j) (scalarVec k) := by
  classical
  unfold coeffApplyA coeffApply aFun4Equiv rootPoint
  rw [Finset.sum_eq_single (scalarVec i, scalarVec j, scalarVec k)]
  · simp
  · intro u _ hu
    rcases u with ⟨y, z, w⟩
    have hne :
        (y, z, w) ≠ (scalarVec i, scalarVec j, scalarVec k) := hu
    change
      A y z w *
        (if (y, z, w) = (scalarVec i, scalarVec j, scalarVec k)
          then 1 else 0) = 0
    rw [if_neg hne, mul_zero]
  · simp

private theorem KCMap_cPoint
    {n : Nat} [NeZero n] (i j k : I n) :
    KCMap (n := n) (a := 1) (b := 1) (c := 1) (d := 1)
        (cPoint i j k) =
      rootPoint i j k + rootPoint i (j - 1) k := by
  funext y z w
  change
    (∑ p : PVec n 1,
      (cPoint i j k p y (vecSum z) w
        + cPoint i j k p y (vecSum z + 1) w)) =
      rootPoint i j k y z w + rootPoint i (j - 1) k y z w
  rw [sum_pVecOne]
  simp only [cPoint, rootPoint]
  simp only [Prod.mk.injEq, true_and]
  simp only [vecSum_add_one_eq_iff, vec_eq_scalarVec_iff]

private theorem coeffApplyA_KCMap_cPoint
    {n : Nat} [NeZero n]
    (A : AFun4 n 1 1 1) (i j k : I n) :
    coeffApplyA
        (KCMap (n := n) (a := 1) (b := 1) (c := 1) (d := 1)
          (cPoint i j k)) A =
      A (scalarVec i) (scalarVec j) (scalarVec k)
        + A (scalarVec i) (scalarVec (j - 1)) (scalarVec k) := by
  rw [KCMap_cPoint]
  rw [coeffApplyA_eq_sum]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [← coeffApplyA_eq_sum, ← coeffApplyA_eq_sum]
  rw [coeffApplyA_rootPoint, coeffApplyA_rootPoint]

private theorem squareCompat_cPoint_coeff
    {n : Nat} [NeZero n]
    (B : BFun4 n 1 1 1) (W : WFun4 n 1 1 1)
    (i j k : I n) :
    coeffApply
        (cFun4Equiv n 1 1 1
          (squareCompat (n := n) (a := 1) (b := 1) (c := 1) (d := 1)
            (B, W)))
        (cFun4Equiv n 1 1 1 (cPoint i j k)) =
      B (zeroVec : PVec n 1) i (scalarVec j) (scalarVec k)
        + B (zeroVec : PVec n 1) (i + 1)
            (scalarVec (j - 1)) (scalarVec k)
        + W (zeroVec : PVec n 1) (scalarVec i)
            (scalarVec j) k
        + W (zeroVec : PVec n 1) (scalarVec i)
            (scalarVec (j - 1)) (k + 1) := by
  rw [coeffApply_cPoint]
  change
    squareCompatFun B W (zeroVec : PVec n 1) (scalarVec i) j
        (scalarVec k) = _
  unfold squareCompatFun
  have h0 :
      (∑ z : ZVec n 1,
        if vecSum z = j then
          betaB B (zeroVec : PVec n 1) (scalarVec i) z (scalarVec k)
            + xiW W (zeroVec : PVec n 1) (scalarVec i) z (scalarVec k)
        else 0) =
      betaB B (zeroVec : PVec n 1) (scalarVec i)
          (scalarVec j) (scalarVec k)
        + xiW W (zeroVec : PVec n 1) (scalarVec i)
          (scalarVec j) (scalarVec k) := by
    classical
    rw [Finset.sum_eq_single (scalarVec j)]
    · simp [vecSum_scalarVec]
    · intro z _ hz
      by_cases hs : vecSum z = j
      · exact (hz ((vec_eq_scalarVec_iff z j).2 hs)).elim
      · simp [hs]
    · simp
  have h1 :
      (∑ z : ZVec n 1,
        if vecSum z + 1 = j then
          gammaB B (zeroVec : PVec n 1) (scalarVec i) z (scalarVec k)
            + zetaW W (zeroVec : PVec n 1) (scalarVec i) z (scalarVec k)
        else 0) =
      gammaB B (zeroVec : PVec n 1) (scalarVec i)
          (scalarVec (j - 1)) (scalarVec k)
        + zetaW W (zeroVec : PVec n 1) (scalarVec i)
          (scalarVec (j - 1)) (scalarVec k) := by
    classical
    rw [Finset.sum_eq_single (scalarVec (j - 1))]
    · simp [vecSum_scalarVec, sub_add_cancel]
    · intro z _ hz
      by_cases hs : vecSum z + 1 = j
      · exact (hz ((vecSum_add_one_eq_iff z j).1 hs)).elim
      · simp [hs]
    · simp
  rw [h0, h1]
  simp only [betaB, gammaB, xiW, zetaW, vecSum_scalarVec]
  ring

theorem k4Scalar_source_compat
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4SingletonCompatRelation (k4ScalarA x) (k4ScalarB x) (k4ScalarW x) := by
  intro i j k
  have hx :
      k4PreCMap (n := n) (a := 1) (b := 1) (c := 1) (d := 1) x.1 = 0 :=
    LinearMap.mem_ker.mp x.2
  have hpoint := congrArg
    (fun L : CFun4 n 1 1 1 →ₗ[F] F => L (cPoint i j k)) hx
  change
    k4CPhaseCoeffClean x.1.1 x.1.2.1 x.1.2.2 (cPoint i j k) = 0
    at hpoint
  change
    coeffApplyA
        (KCMap (n := n) (a := 1) (b := 1) (c := 1) (d := 1)
          (cPoint i j k)) x.1.1
      + coeffApply
          (cFun4Equiv n 1 1 1
            (squareCompat
              (n := n) (a := 1) (b := 1) (c := 1) (d := 1)
              (x.1.2.1, x.1.2.2)))
          (cFun4Equiv n 1 1 1 (cPoint i j k)) = 0 at hpoint
  rw [coeffApplyA_KCMap_cPoint, squareCompat_cPoint_coeff] at hpoint
  simp only [k4ScalarA, k4ScalarB, k4ScalarW, cubeBackwardDiffY]
  ring_nf at hpoint ⊢
  exact hpoint

theorem k4Scalar_Z_sum
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4SingletonZSumRelation (k4ScalarZ x) := by
  intro i k
  have hs :
      (∑ j : I n,
        (k4ScalarB x i j k + k4ScalarB x (i + 1) (j - 1) k
          + k4ScalarW x i j k + k4ScalarW x i (j - 1) (k + 1)
          + cubeBackwardDiffY (k4ScalarA x) i j k)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    exact k4Scalar_source_compat x i j k
  have hB :=
    sum_shift (n := n) (-1 : I n)
      (fun j => k4ScalarB x (i + 1) j k)
  have hW :=
    sum_shift (n := n) (-1 : I n)
      (fun j => k4ScalarW x i j (k + 1))
  have hA :=
    sum_shift (n := n) (-1 : I n)
      (fun j => k4ScalarA x i j k)
  simp only [cubeBackwardDiffY, Finset.sum_add_distrib, sub_eq_add_neg] at hs
  rw [hB, hW, hA] at hs
  have htarget :
      (∑ j : I n, k4ScalarB x i j k)
        + (∑ j : I n, k4ScalarB x (i + 1) j k)
        + (∑ j : I n, k4ScalarW x i j k)
        + (∑ j : I n, k4ScalarW x i j (k + 1)) = 0 := by
    ring_nf at hs ⊢
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero] at hs
    exact hs
  simpa only [k4ScalarZ, Pi.add_apply, cyclicDiffX, cyclicDiffZ,
    Finset.sum_add_distrib, add_assoc] using htarget

theorem k4Scalar_source_root
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4SingletonRootRelation (k4ScalarB x) (k4ScalarW x) (k4ScalarZ x) := by
  intro i j k
  simp only [k4ScalarZ, Pi.add_apply]
  ring_nf
  simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]

theorem k4Scalar_source_dualZ
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4SingletonDualZRelation (k4ScalarC x) (k4ScalarZ x) := by
  intro i j k
  let u : ZeroSumProfile n :=
    ⟨fun t => k4ScalarZ x i t k,
      LinearMap.mem_ker.mpr (k4Scalar_Z_sum x i k)⟩
  have h := congrFun (cycDiff_explicitCyclicPrimitive u) j
  change
    explicitCyclicPrefix (fun t => k4ScalarZ x i t k) j
        + explicitCyclicPrefix (fun t => k4ScalarZ x i t k) (j + 1)
      = k4ScalarZ x i j k
  simpa [explicitCyclicPrimitive, u] using h

private theorem source_relations_imply_closure
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4Closure (k4ScalarB x) (k4ScalarC x) (k4ScalarW x) := by
  intro i j k
  have hr := k4Scalar_source_root x i j k
  have hz := k4Scalar_source_dualZ x i j k
  rw [hr, hz]
  ring_nf
  simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]

private theorem dualBRead_sum_zero
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) (j k : I n) :
    (∑ i : I n,
      k4ScalarDualBRead (k4ScalarC x) (k4ScalarW x) i j k) = 0 := by
  have hs :
      (∑ i : I n,
        (cyclicDiffX (k4ScalarB x) i j k
          + cyclicDiffY (k4ScalarC x) i j k
          + cyclicDiffZ (k4ScalarW x) i j k)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact source_relations_imply_closure x i j k
  have hBm :=
    sum_shift (n := n) (1 : I n)
      (fun i => k4ScalarB x i j k)
  have hCm :=
    sum_shift (n := n) (-1 : I n)
      (fun i => k4ScalarC x i (j + 1) k)
  have hWm :=
    sum_shift (n := n) (-1 : I n)
      (fun i => k4ScalarW x i j (k + 1))
  simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ,
    Finset.sum_add_distrib] at hs
  rw [hBm] at hs
  have hread :
      (∑ i : I n, k4ScalarC x i j k)
        + (∑ i : I n, k4ScalarC x i (j + 1) k)
        + (∑ i : I n, k4ScalarW x i j k)
        + (∑ i : I n, k4ScalarW x i j (k + 1)) = 0 := by
    ring_nf at hs ⊢
    simp only [show (2 : F) = 0 by decide, mul_zero, zero_add] at hs
    exact hs
  simp only [k4ScalarDualBRead, Finset.sum_add_distrib, sub_eq_add_neg]
  rw [hCm, hWm]
  exact hread

private theorem shifted_prefix_backward_diff
    {n : Nat} [NeZero n]
    (u : Profile n) (hu : (∑ t : I n, u t) = 0) (i : I n) :
    explicitCyclicPrefix u (i + 1)
        + explicitCyclicPrefix u (i - 1 + 1) = u i := by
  let zu : ZeroSumProfile n :=
    ⟨u, LinearMap.mem_ker.mpr hu⟩
  have h := congrFun (cycDiff_explicitCyclicPrimitive zu) i
  change
    explicitCyclicPrefix u i + explicitCyclicPrefix u (i + 1) = u i at h
  have hi : i - 1 + 1 = i := by ring
  rw [hi]
  simpa [add_comm] using h

theorem k4Scalar_source_dualB
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4SingletonDualBRelation (k4ScalarR x) (k4ScalarC x) (k4ScalarW x) := by
  intro i j k
  have hp := shifted_prefix_backward_diff
    (fun t => k4ScalarDualBRead (k4ScalarC x) (k4ScalarW x) t j k)
    (dualBRead_sum_zero x j k) i
  simp only [k4ScalarDualBRead] at hp
  simp only [cubeBackwardDiffX, k4ScalarR]
  simp only [k4ScalarDualBRead]
  rw [add_assoc]
  rw [hp]
  ring_nf
  simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]

private theorem source_root_pair_eq
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    coeffApplyA
        (KBMap (n := n) (a := 1) (b := 1) (c := 1) (d := 1) x.1.2.1 +
          KWMap (n := n) (a := 1) (b := 1) (c := 1) (d := 1) x.1.2.2)
        x.1.1 =
      cubePair (k4ScalarA x) (k4ScalarZ x) := by
  classical
  rw [coeffApplyA_eq_sum]
  unfold KBMap KWMap dyB dwW betaB gammaB xiW zetaW
  simp only [Pi.add_apply]
  simp_rw [sum_pVecOne]
  simp_rw [sum_vecOne_reindex]
  unfold cubePair k4ScalarA k4ScalarZ k4ScalarB k4ScalarW
  simp only [Pi.add_apply, cyclicDiffX, cyclicDiffZ]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, vecSum_scalarVec]

private theorem source_BW_pair_eq
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4BWPhaseClean x.1.2.1 x.1.2.2 =
      cubePair (k4ScalarB x) (k4ScalarW x) +
        cubePair
          (fun i j k => k4ScalarB x (i + 1) j k)
          (fun i j k => k4ScalarW x i j (k + 1)) := by
  classical
  unfold k4BWPhaseClean
  simp_rw [sum_pVecOne]
  simp_rw [sum_vecOne_reindex]
  simp only [betaB, gammaB, xiW, zetaW, vecSum_scalarVec]
  unfold cubePair k4ScalarB k4ScalarW
  conv_lhs => rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  conv_lhs => rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_add_distrib]

private theorem F_eq_of_add_eq_zero {a b : F} (h : a + b = 0) :
    a = b := by
  calc
    a = a + 0 := by rw [add_zero]
    _ = a + (b + b) := by rw [F_add_self]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

private theorem cubePair_comm
    {n : Nat} [NeZero n] (f g : K4Cube n) :
    cubePair f g = cubePair g f := by
  unfold cubePair
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

private theorem cubePair_add_right
    {n : Nat} [NeZero n] (f g h : K4Cube n) :
    cubePair f (g + h) = cubePair f g + cubePair f h := by
  unfold cubePair
  simp only [Pi.add_apply, mul_add]
  simp_rw [Finset.sum_add_distrib]

private theorem cubePair_add_left
    {n : Nat} [NeZero n] (f g h : K4Cube n) :
    cubePair (f + g) h = cubePair f h + cubePair g h := by
  unfold cubePair
  simp only [Pi.add_apply, add_mul]
  simp_rw [Finset.sum_add_distrib]

private theorem cubePair_congr_right
    {n : Nat} [NeZero n] (f g h : K4Cube n)
    (heq : ∀ i j k, g i j k = h i j k) :
    cubePair f g = cubePair f h := by
  unfold cubePair
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  rw [heq]

private theorem cubePair_congr_left
    {n : Nat} [NeZero n] (f g h : K4Cube n)
    (heq : ∀ i j k, f i j k = g i j k) :
    cubePair f h = cubePair g h := by
  rw [cubePair_comm f h, cubePair_comm g h]
  exact cubePair_congr_right h f g heq

private theorem cubePair_shiftX_right
    {n : Nat} [NeZero n] (a : I n) (f g : K4Cube n) :
    cubePair f (fun i j k => g (i + a) j k) =
      cubePair (fun i j k => f (i - a) j k) g := by
  classical
  unfold cubePair
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have hs := sum_shift (n := n) a
    (fun i => f (i - a) j k * g i j k)
  simpa only [add_sub_cancel_right] using hs

private theorem cubePair_shiftY_right
    {n : Nat} [NeZero n] (a : I n) (f g : K4Cube n) :
    cubePair f (fun i j k => g i (j + a) k) =
      cubePair (fun i j k => f i (j - a) k) g := by
  classical
  unfold cubePair
  have hs := sum_shift (n := n) a
    (fun j => ∑ k : I n, ∑ i : I n, f i (j - a) k * g i j k)
  simpa only [add_sub_cancel_right] using hs

private def compatBPart
    {n : Nat} [NeZero n] (B : K4Cube n) : K4Cube n :=
  fun i j k => B i j k + B (i + 1) (j - 1) k

private def dualBCPart
    {n : Nat} [NeZero n] (C : K4Cube n) : K4Cube n :=
  fun i j k => C i j k + C (i - 1) (j + 1) k

private def dualBWPart
    {n : Nat} [NeZero n] (W : K4Cube n) : K4Cube n :=
  fun i j k => W i j k + W (i - 1) j (k + 1)

private def shiftXCube
    {n : Nat} [NeZero n] (f : K4Cube n) : K4Cube n :=
  fun i j k => f (i + 1) j k

private def shiftZCube
    {n : Nat} [NeZero n] (f : K4Cube n) : K4Cube n :=
  fun i j k => f i j (k + 1)

private noncomputable def literalCubeQ
    {n : Nat} [NeZero n] (A B W : K4Cube n) : F :=
  cubePair A (cyclicDiffX B + cyclicDiffZ W) +
    cubePair B W + cubePair (shiftXCube B) (shiftZCube W)

private theorem cubePair_cyclicDiffX_adjoint
    {n : Nat} [NeZero n] (R B : K4Cube n) :
    cubePair R (cyclicDiffX B) =
      cubePair (cubeBackwardDiffX R) B := by
  have hx :
      cubePair R (fun i j k => B (i + 1) j k) =
        cubePair (fun i j k => R (i - 1) j k) B :=
    cubePair_shiftX_right (1 : I n) R B
  unfold cubePair at hx
  unfold cubePair cyclicDiffX cubeBackwardDiffX
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib] at hx ⊢
  rw [hx]

private theorem cubePair_backwardDiffY_adjoint
    {n : Nat} [NeZero n] (C A : K4Cube n) :
    cubePair C (cubeBackwardDiffY A) =
      cubePair (cyclicDiffY C) A := by
  have hy :
      cubePair C (fun i j k => A i (j - 1) k) =
        cubePair (fun i j k => C i (j + 1) k) A := by
    have h := cubePair_shiftY_right (-1 : I n) C A
    simpa only [sub_eq_add_neg, neg_neg] using h
  unfold cubePair at hy
  unfold cubePair cubeBackwardDiffY cyclicDiffY
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib] at hy ⊢
  rw [hy]

private theorem cubePair_dualBCPart
    {n : Nat} [NeZero n] (C B : K4Cube n) :
    cubePair (dualBCPart C) B =
      cubePair C (compatBPart B) := by
  have hcross :
      cubePair (fun i j k => C (i - 1) (j + 1) k) B =
        cubePair C (fun i j k => B (i + 1) (j - 1) k) := by
    calc
      cubePair (fun i j k => C (i - 1) (j + 1) k) B =
          cubePair B (fun i j k => C (i - 1) (j + 1) k) :=
        cubePair_comm _ _
      _ = cubePair
            (fun i j k => B (i + 1) j k)
            (fun i j k => C i (j + 1) k) := by
          have h := cubePair_shiftX_right (-1 : I n) B
            (fun i j k => C i (j + 1) k)
          simpa only [sub_eq_add_neg, neg_neg] using h
      _ = cubePair
            (fun i j k => B (i + 1) (j - 1) k) C := by
          have h := cubePair_shiftY_right (1 : I n)
            (fun i j k => B (i + 1) j k) C
          exact h
      _ = cubePair C (fun i j k => B (i + 1) (j - 1) k) :=
        cubePair_comm _ _
  unfold dualBCPart compatBPart
  change
    cubePair
        (C + fun i j k => C (i - 1) (j + 1) k) B =
      cubePair C
        (B + fun i j k => B (i + 1) (j - 1) k)
  rw [cubePair_add_left, cubePair_add_right]
  rw [cubePair_comm C B, hcross]

private theorem cubePair_dualBWPart
    {n : Nat} [NeZero n] (W B : K4Cube n) :
    cubePair (dualBWPart W) B =
      cubePair B W + cubePair (shiftXCube B) (shiftZCube W) := by
  have hcross :
      cubePair (fun i j k => W (i - 1) j (k + 1)) B =
        cubePair (shiftXCube B) (shiftZCube W) := by
    calc
      cubePair (fun i j k => W (i - 1) j (k + 1)) B =
          cubePair B (fun i j k => W (i - 1) j (k + 1)) :=
        cubePair_comm _ _
      _ = cubePair
            (fun i j k => B (i + 1) j k)
            (fun i j k => W i j (k + 1)) := by
          have h := cubePair_shiftX_right (-1 : I n) B
            (fun i j k => W i j (k + 1))
          simpa only [sub_eq_add_neg, neg_neg] using h
      _ = cubePair (shiftXCube B) (shiftZCube W) := rfl
  unfold dualBWPart
  change
    cubePair
        (W + fun i j k => W (i - 1) j (k + 1)) B =
      cubePair B W + cubePair (shiftXCube B) (shiftZCube W)
  rw [cubePair_add_left, cubePair_comm W B, hcross]

private theorem literalCubeQ_eq_singletonDefect
    {n : Nat} [NeZero n]
    (A R B C W Z : K4Cube n)
    (hcompat : k4SingletonCompatRelation A B W)
    (hroot : k4SingletonRootRelation B W Z)
    (hdualB : k4SingletonDualBRelation R C W)
    (hdualZ : k4SingletonDualZRelation C Z) :
    literalCubeQ A B W = k4SingletonDefect R C W := by
  have hcl : k4Closure B C W := by
    intro i j k
    have hr := hroot i j k
    have hz := hdualZ i j k
    simp only [cyclicDiffX, cyclicDiffY, cyclicDiffZ] at hr hz ⊢
    rw [hr, hz]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, add_zero]
  have hdiffs :
      cubePair R (cyclicDiffZ W) + cubePair R (cyclicDiffY C) =
        cubePair R (cyclicDiffX B) := by
    have hpoint : ∀ i j k,
        cyclicDiffZ W i j k + cyclicDiffY C i j k =
          cyclicDiffX B i j k := by
      intro i j k
      apply F_eq_of_add_eq_zero
      simpa only [add_assoc, add_comm, add_left_comm] using hcl i j k
    rw [← cubePair_add_right]
    exact cubePair_congr_right R
      (cyclicDiffZ W + cyclicDiffY C) (cyclicDiffX B) hpoint
  have hback :
      cubeBackwardDiffX R = dualBCPart C + dualBWPart W := by
    funext i j k
    apply F_eq_of_add_eq_zero
    simpa only [dualBCPart, dualBWPart, Pi.add_apply,
      add_assoc] using hdualB i j k
  have hcompatField :
      compatBPart B + cubeTyInvTzSum W = cubeBackwardDiffY A := by
    funext i j k
    apply F_eq_of_add_eq_zero
    simpa only [compatBPart, cubeTyInvTzSum, cubeBackwardDiffY,
      Pi.add_apply, add_assoc] using hcompat i j k
  have hzField :
      cyclicDiffX B + cyclicDiffZ W = Z := by
    funext i j k
    have hr := hroot i j k
    simp only [Pi.add_apply]
    rw [hr]
    ring_nf
    simp only [show (2 : F) = 0 by decide, mul_zero, zero_add]
  apply Eq.symm
  calc
    k4SingletonDefect R C W =
        (cubePair R (cyclicDiffZ W) + cubePair R (cyclicDiffY C)) +
          cubePair C (cubeTyInvTzSum W) := by
      rfl
    _ = cubePair R (cyclicDiffX B) +
          cubePair C (cubeTyInvTzSum W) := by
      rw [hdiffs]
    _ = cubePair (cubeBackwardDiffX R) B +
          cubePair C (cubeTyInvTzSum W) := by
      rw [cubePair_cyclicDiffX_adjoint]
    _ = cubePair (dualBCPart C + dualBWPart W) B +
          cubePair C (cubeTyInvTzSum W) := by
      rw [hback]
    _ = (cubePair C (compatBPart B) +
            (cubePair B W +
              cubePair (shiftXCube B) (shiftZCube W))) +
          cubePair C (cubeTyInvTzSum W) := by
      rw [cubePair_add_left, cubePair_dualBCPart,
        cubePair_dualBWPart]
    _ = (cubePair C (compatBPart B) +
            cubePair C (cubeTyInvTzSum W)) +
          cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W) := by
      ring
    _ = cubePair C (compatBPart B + cubeTyInvTzSum W) +
          cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W) := by
      rw [cubePair_add_right]
    _ = cubePair C (cubeBackwardDiffY A) +
          cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W) := by
      rw [hcompatField]
    _ = cubePair (cyclicDiffY C) A +
          cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W) := by
      rw [cubePair_backwardDiffY_adjoint]
    _ = cubePair Z A +
          cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W) := by
      apply congrArg
        (fun t => t + cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W))
      exact cubePair_congr_left
        (cyclicDiffY C) Z A hdualZ
    _ = cubePair A Z +
          cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W) := by
      rw [cubePair_comm]
    _ = cubePair A (cyclicDiffX B + cyclicDiffZ W) +
          cubePair B W +
          cubePair (shiftXCube B) (shiftZCube W) := by
      rw [hzField]
    _ = literalCubeQ A B W := rfl

private theorem k4PreCQ_eq_literalCubeQ
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4PreCQ x =
      literalCubeQ (k4ScalarA x) (k4ScalarB x) (k4ScalarW x) := by
  unfold k4PreCQ literalCubeQ
  rw [source_root_pair_eq, source_BW_pair_eq]
  change
    cubePair (k4ScalarA x)
          (cyclicDiffX (k4ScalarB x) + cyclicDiffZ (k4ScalarW x)) +
        (cubePair (k4ScalarB x) (k4ScalarW x) +
          cubePair
            (fun i j k => k4ScalarB x (i + 1) j k)
            (fun i j k => k4ScalarW x i j (k + 1))) =
      (cubePair (k4ScalarA x)
          (cyclicDiffX (k4ScalarB x) + cyclicDiffZ (k4ScalarW x)) +
        cubePair (k4ScalarB x) (k4ScalarW x)) +
          cubePair
            (fun i j k => k4ScalarB x (i + 1) j k)
            (fun i j k => k4ScalarW x i j (k + 1))
  exact (add_assoc _ _ _).symm

theorem k4ScalarQ_eq_singletonDefect
    {n : Nat} [NeZero n]
    (x : K4PreCSource n 1 1 1 1) :
    k4PreCQ x =
      k4SingletonDefect (k4ScalarR x) (k4ScalarC x) (k4ScalarW x) := by
  rw [k4PreCQ_eq_literalCubeQ]
  exact literalCubeQ_eq_singletonDefect
    (k4ScalarA x) (k4ScalarR x) (k4ScalarB x)
    (k4ScalarC x) (k4ScalarW x) (k4ScalarZ x)
    (k4Scalar_source_compat x)
    (k4Scalar_source_root x)
    (k4Scalar_source_dualB x)
    (k4Scalar_source_dualZ x)

end

end Core4loop.CompleteGraph.ScalarCycle
