import Core4loop.CompleteGraph.EvenAllLarge.RadicalAggregateSplit

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.CompleteGraph.CubeCompat

noncomputable section

attribute [local instance] Fintype.ofFinite

/-! ## The literal diagonal shear for the K4 kappa pairing -/

private noncomputable def k4KappaCoeff
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n where
  toFun B := fun i j k => B i j k + B (i + 1) j (k - 1)
  map_add' B B' := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' r B := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

private theorem k4CubeKappa_eq_cubeDot_coeff
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W = cubeDot (k4KappaCoeff B) W := by
  unfold k4CubeKappa cubeDot k4KappaCoeff
  change
    (∑ q : I n × I n × I n,
      (B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2 +
        B (q.1 + 1) q.2.1 q.2.2 * W q.1 q.2.1 (q.2.2 + 1))) =
      ∑ q : I n × I n × I n,
        (B q.1 q.2.1 q.2.2 + B (q.1 + 1) q.2.1 (q.2.2 - 1)) *
          W q.1 q.2.1 q.2.2
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.refl (I n)) (Equiv.addRight (1 : I n)))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

noncomputable def k4KappaIKShear
    {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f i j (k - i)
  invFun g := fun i j k => g i j (k + i)
  left_inv f := by
    funext i j k
    simp only
    congr 3
    abel
  right_inv g := by
    funext i j k
    simp only
    congr 3
    abel
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem k4KappaIKShear_coeff
    {n : Nat} [NeZero n] (B : CyclicCube n) :
    k4KappaIKShear (k4KappaCoeff B) =
      cubeDiffI (k4KappaIKShear B) := by
  funext i j k
  rw [EEOEInternal.cubeDiffI_apply]
  change
    B i j (k - i) + B (i + 1) j ((k - i) - 1) =
      B i j (k - i) + B (i + 1) j (k - (i + 1))
  have hindex : (k - i) - 1 = k - (i + 1) := by abel
  rw [hindex]

private theorem cubeDot_k4KappaIKShear
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot (k4KappaIKShear X) (k4KappaIKShear Y) = cubeDot X Y := by
  unfold cubeDot k4KappaIKShear
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    { toFun := fun q => (q.1, q.2.1, q.2.2 + q.1)
      invFun := fun q => (q.1, q.2.1, q.2.2 - q.1)
      left_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp only [Prod.mk.injEq, true_and]
        abel
      right_inv := by
        intro q
        rcases q with ⟨i, j, k⟩
        simp only [Prod.mk.injEq, true_and]
        abel }
  symm
  apply Fintype.sum_equiv e
  intro q
  simp [e]

theorem k4CubeKappa_diagonalShear
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    cubeDot
        (cubeDiffI (k4KappaIKShear B))
        (k4KappaIKShear W) =
      k4CubeKappa B W := by
  rw [← k4KappaIKShear_coeff]
  rw [cubeDot_k4KappaIKShear]
  exact (k4CubeKappa_eq_cubeDot_coeff B W).symm

/-! ## Literal pointed aggregate coordinates -/

noncomputable abbrev K4BAggregateCoords
    (n c : Nat) [NeZero n] :=
  ((LinearMap.ker (cubeDiffP (n := n))) × CyclicCube n) ×
    DiamondEvenAxisValueTailZero n c (CyclicCube n)

noncomputable abbrev K4WAggregateCoords
    (n c : Nat) [NeZero n] :=
  (CyclicCube n × LinearMap.ker (cubeDiffR (n := n))) ×
    DiamondEvenAxisValueTailZero n c (CyclicCube n)

noncomputable def k4BAggregateCoordEquiv
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) :
    K4BAggregateLeft n c ≃ₗ[F] K4BAggregateCoords n c where
  toFun B :=
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let x := E B.1
    ((⟨x.1.1, by
        have hB := LinearMap.mem_ker.mp B.2
        rw [k4BAggregateConstraint_apply] at hB
        simpa only [k4AggregatePDiff,
          pointedSrcEvenValueEquiv_apply_sigma] using hB⟩,
      x.1.2), x.2)
  invFun x :=
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1.1, x.1.2), x.2)
    ⟨E.symm y, by
      apply LinearMap.mem_ker.mpr
      rw [k4BAggregateConstraint_apply]
      change cubeDiffP (∑ zt, E.symm y zt) = 0
      have hsum : (∑ zt, E.symm y zt) = x.1.1.1 := by
        rw [← pointedSrcEvenValueEquiv_apply_sigma
          (zeroVec : PVec n c) (even_card_PVec hn hc2)]
        change (E (E.symm y)).1.1 = x.1.1.1
        rw [E.apply_symm_apply]
      rw [hsum]
      exact x.1.1.2⟩
  left_inv B := by
    apply Subtype.ext
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    apply E.injective
    change E (E.symm (((E B.1).1.1, (E B.1).1.2), (E B.1).2)) = E B.1
    rw [E.apply_symm_apply]
  right_inv x := by
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1.1, x.1.2), x.2)
    have h := E.apply_symm_apply y
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z => z.1.1) h
      · exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_add' B B' := by
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_add B.1 B'.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z => z.1.1) h
      · exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_smul' r B := by
    let E := diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_smul r B.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun z => z.1.1) h
      · exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h

noncomputable def k4WAggregateCoordEquiv
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) :
    K4WAggregateLeft n c ≃ₗ[F] K4WAggregateCoords n c where
  toFun W :=
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y := E W.1
    ((y.1.1, ⟨y.1.2, by
        have hW := LinearMap.mem_ker.mp W.2
        rw [k4WAggregateConstraint_apply] at hW
        rw [TotalEEEERightInternal.axisDualHead_eq_totalSum
          (CyclicCube n) hn hc2 W.1]
        simpa only [k4AggregateRDiff] using hW⟩), y.2)
  invFun x :=
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1, x.1.2.1), x.2)
    ⟨E.symm y, by
      apply LinearMap.mem_ker.mpr
      rw [k4WAggregateConstraint_apply]
      change cubeDiffR (∑ zt, E.symm y zt) = 0
      have hsum := TotalEEEERightInternal.axisDualHead_eq_totalSum
        (CyclicCube n) hn hc2 (E.symm y)
      change (E (E.symm y)).1.2 = (∑ zt, E.symm y zt) at hsum
      rw [E.apply_symm_apply] at hsum
      rw [← hsum]
      exact x.1.2.2⟩
  left_inv W := by
    apply Subtype.ext
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    apply E.injective
    change E (E.symm (((E W.1).1.1, (E W.1).1.2), (E W.1).2)) = E W.1
    rw [E.apply_symm_apply]
  right_inv x := by
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    let y : PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) :=
      ((x.1.1, x.1.2.1), x.2)
    have h := E.apply_symm_apply y
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) h
      · apply Subtype.ext
        exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_add' W W' := by
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_add W.1 W'.1
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) h
      · apply Subtype.ext
        exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h
  map_smul' r W := by
    let E := diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2
    have h := E.map_smul r W.1
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun z => z.1.1) h
      · apply Subtype.ext
        exact congrArg (fun z => z.1.2) h
    · exact congrArg (fun z => z.2) h

/-! ## The exact three-block aggregate pairing -/

noncomputable def k4PHeadCross
    {n : Nat} [NeZero n] :
    LinearMap.ker (cubeDiffP (n := n)) →ₗ[F]
      Module.Dual F (CyclicCube n) :=
  (k4CubeKappaLinear (n := n)).comp
    (LinearMap.ker (cubeDiffP (n := n))).subtype

noncomputable def k4RHeadCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      Module.Dual F (LinearMap.ker (cubeDiffR (n := n))) :=
  (LinearMap.dualMap
      (LinearMap.ker (cubeDiffR (n := n))).subtype).comp
    (k4CubeKappaLinear (n := n))

@[simp] theorem k4PHeadCross_apply
    {n : Nat} [NeZero n]
    (B : LinearMap.ker (cubeDiffP (n := n)))
    (W : CyclicCube n) :
    k4PHeadCross B W = k4CubeKappa B.1 W := rfl

@[simp] theorem k4RHeadCross_apply
    {n : Nat} [NeZero n]
    (B : CyclicCube n)
    (W : LinearMap.ker (cubeDiffR (n := n))) :
    k4RHeadCross B W = k4CubeKappa B W.1 := rfl

noncomputable def k4AggregateCrossModel
    {n c : Nat} [NeZero n] :
    K4BAggregateCoords n c →ₗ[F]
      Module.Dual F (K4WAggregateCoords n c) :=
  diamondCrossProd
    (diamondCrossProd
      (k4PHeadCross (n := n))
      (k4RHeadCross (n := n)))
    (diamondTailAmplify
      (n := n) (k := c) (k4CubeKappaLinear (n := n)))

theorem k4AggregateCrossModel_phase
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (B : K4BAggregateLeft n c)
    (W : K4WAggregateLeft n c) :
    k4AggregateCrossModel
        (k4BAggregateCoordEquiv hn hc2 B)
        (k4WAggregateCoordEquiv hn hc2 W) =
      k4ZAggregateCross B W := by
  let x := diamondEvenAxisSrcCoordEquiv
    (n := n) (k := c) (CyclicCube n) hn hc2 B.1
  let y := diamondEvenAxisDualCoordEquiv
    (n := n) (k := c) (CyclicCube n) hn hc2 W.1
  change
    (k4CubeKappa x.1.1 y.1.1 +
        k4CubeKappa x.1.2 y.1.2) +
      (∑ t, k4CubeKappa (x.2.1 t) (y.2.1 t)) =
        k4AggregateKappaScalar B.1 W.1
  rw [k4AggregateKappaScalar]
  exact (pointedEvenValue_pairing
    (zeroVec : PVec n c) (even_card_PVec hn hc2)
    (k4CubeKappaLinear (n := n)) B.1 W.1).symm

/-! ## The full hyperbolic kernel splits into its two half kernels -/

theorem k4AggregateHyperbolicPolar_mem_ker_iff
    {n c : Nat} [NeZero n]
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    x ∈ LinearMap.ker (k4AggregateHyperbolicPolar (n := n) (c := c)) ↔
      x.1 ∈ LinearMap.ker (k4ZAggregateCross (n := n) (c := c)) ∧
        x.2 ∈ LinearMap.ker
          (k4ZAggregateCross (n := n) (c := c)).flip := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    constructor
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro W
      have hpoint := LinearMap.congr_fun hx (0, W)
      simpa [k4AggregateHyperbolicPolar_apply,
        k4AggregatePolarScalar] using hpoint
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro B
      have hpoint := LinearMap.congr_fun hx (B, 0)
      change
        k4ZAggregateCross x.1 0 + k4ZAggregateCross B x.2 = 0 at hpoint
      rw [map_zero, zero_add] at hpoint
      exact hpoint
  · rintro ⟨hB, hW⟩
    apply LinearMap.ext
    intro y
    rw [k4AggregateHyperbolicPolar_apply, k4AggregatePolarScalar]
    have hB0 := LinearMap.mem_ker.mp hB
    have hW0 := LinearMap.mem_ker.mp hW
    rw [LinearMap.congr_fun hB0 y.2]
    change 0 + (k4ZAggregateCross (n := n) (c := c)).flip x.2 y.1 = 0
    rw [LinearMap.congr_fun hW0 y.1]
    simp

noncomputable def k4AggregatePolarKernelReadHalf
    {n c : Nat} [NeZero n] :
    K4AggregatePolarKernel n c →ₗ[F]
      (LinearMap.ker (k4ZAggregateCross (n := n) (c := c)) ×
        LinearMap.ker (k4ZAggregateCross (n := n) (c := c)).flip) where
  toFun x :=
    (⟨x.1.1, (k4AggregateHyperbolicPolar_mem_ker_iff x.1).mp x.2 |>.1⟩,
      ⟨x.1.2, (k4AggregateHyperbolicPolar_mem_ker_iff x.1).mp x.2 |>.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4AggregatePolarKernelBuildHalf
    {n c : Nat} [NeZero n] :
    (LinearMap.ker (k4ZAggregateCross (n := n) (c := c)) ×
        LinearMap.ker (k4ZAggregateCross (n := n) (c := c)).flip) →ₗ[F]
      K4AggregatePolarKernel n c where
  toFun x :=
    ⟨(x.1.1, x.2.1),
      (k4AggregateHyperbolicPolar_mem_ker_iff
        (x.1.1, x.2.1)).mpr ⟨x.1.2, x.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem k4AggregatePolarKernelReadHalf_build
    {n c : Nat} [NeZero n]
    (x : LinearMap.ker (k4ZAggregateCross (n := n) (c := c)) ×
      LinearMap.ker (k4ZAggregateCross (n := n) (c := c)).flip) :
    k4AggregatePolarKernelReadHalf
        (k4AggregatePolarKernelBuildHalf x) = x := by
  ext <;> rfl

@[simp] theorem k4AggregatePolarKernelBuildHalf_read
    {n c : Nat} [NeZero n]
    (x : K4AggregatePolarKernel n c) :
    k4AggregatePolarKernelBuildHalf
        (k4AggregatePolarKernelReadHalf x) = x := by
  apply Subtype.ext
  rfl

noncomputable def k4AggregatePolarKernelEquivHalfKernels
    {n c : Nat} [NeZero n] :
    K4AggregatePolarKernel n c ≃ₗ[F]
      (LinearMap.ker (k4ZAggregateCross (n := n) (c := c)) ×
        LinearMap.ker (k4ZAggregateCross (n := n) (c := c)).flip) where
  toLinearMap := k4AggregatePolarKernelReadHalf
  invFun := k4AggregatePolarKernelBuildHalf
  left_inv := k4AggregatePolarKernelBuildHalf_read
  right_inv := k4AggregatePolarKernelReadHalf_build

/-! ## Ambient Kappa radicals in explicit matrix coordinates -/

noncomputable abbrev K4BScalarRadical
    (n : Nat) [NeZero n] :=
  LinearMap.ker (k4PHeadCross (n := n))

noncomputable abbrev K4WScalarRadical
    (n : Nat) [NeZero n] :=
  LinearMap.ker (k4RHeadCross (n := n)).flip

noncomputable abbrev K4BFreeHeadRadical
    (n : Nat) [NeZero n] :=
  LinearMap.ker (k4RHeadCross (n := n))

noncomputable abbrev K4WFreeHeadRadical
    (n : Nat) [NeZero n] :=
  LinearMap.ker (k4PHeadCross (n := n)).flip

noncomputable abbrev K4BZTailRadical
    (n c : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c
    (LinearMap.ker (k4CubeKappaLinear (n := n)))

noncomputable abbrev K4WZTailRadical
    (n c : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c
    (LinearMap.ker (k4CubeKappaLinear (n := n)).flip)

private noncomputable def k4KappaTransposeCoeff
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] CyclicCube n where
  toFun W := fun i j k => W i j k + W (i - 1) j (k + 1)
  map_add' W W' := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' r W := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

private theorem k4CubeKappa_eq_cubeDot_transposeCoeff
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W = cubeDot B (k4KappaTransposeCoeff W) := by
  unfold k4CubeKappa cubeDot k4KappaTransposeCoeff
  change
    (∑ q : I n × I n × I n,
      (B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2 +
        B (q.1 + 1) q.2.1 q.2.2 * W q.1 q.2.1 (q.2.2 + 1))) =
      ∑ q : I n × I n × I n,
        B q.1 q.2.1 q.2.2 *
          (W q.1 q.2.1 q.2.2 + W (q.1 - 1) q.2.1 (q.2.2 + 1))
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.addRight (1 : I n))
      (Equiv.refl (I n × I n))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

private theorem cubeDot_comm
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

private theorem k4KappaKernel_coeff_zero
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (k4CubeKappaLinear (n := n))) :
    k4KappaCoeff X.1 = 0 := by
  apply EEEEInternal.cubeDot_left_ext
  intro W
  calc
    cubeDot (k4KappaCoeff X.1) W = k4CubeKappa X.1 W :=
      (k4CubeKappa_eq_cubeDot_coeff X.1 W).symm
    _ = k4CubeKappaLinear X.1 W := rfl
    _ = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp X.2) W
    _ = cubeDot 0 W := by simp [cubeDot]

private theorem k4KappaFlipKernel_coeff_zero
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (k4CubeKappaLinear (n := n)).flip) :
    k4KappaTransposeCoeff X.1 = 0 := by
  apply EEEEInternal.cubeDot_left_ext
  intro B
  calc
    cubeDot (k4KappaTransposeCoeff X.1) B =
        cubeDot B (k4KappaTransposeCoeff X.1) := cubeDot_comm _ _
    _ = k4CubeKappa B X.1 :=
      (k4CubeKappa_eq_cubeDot_transposeCoeff B X.1).symm
    _ = (k4CubeKappaLinear (n := n)).flip X.1 B := rfl
    _ = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp X.2) B
    _ = cubeDot 0 B := by simp [cubeDot]

private theorem k4KappaKernel_diagonal_invariant
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (k4CubeKappaLinear (n := n)))
    (i j k : I n) :
    X.1 i j k = X.1 0 j (k + i) := by
  let f : Profile n := fun t => X.1 t j (k + i - t)
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (k4KappaKernel_coeff_zero X) t) j) (k + i - t)
    simp only [Pi.zero_apply] at hz
    change
      X.1 t j (k + i - t) +
        X.1 (t + 1) j ((k + i - t) - 1) = 0 at hz
    change
      X.1 t j (k + i - t) +
        X.1 (t + 1) j (k + i - (t + 1)) = 0
    rw [show k + i - (t + 1) = (k + i - t) - 1 by abel]
    exact hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf i
  simpa [f] using hc

private theorem k4KappaFlipKernel_diagonal_invariant
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (k4CubeKappaLinear (n := n)).flip)
    (i j k : I n) :
    X.1 i j k = X.1 0 j (k + i) := by
  let f : Profile n := fun t => X.1 t j (k + i - t)
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (k4KappaFlipKernel_coeff_zero X) (t + 1)) j)
      (k + i - (t + 1))
    simp only [Pi.zero_apply] at hz
    change
      X.1 (t + 1) j (k + i - (t + 1)) +
        X.1 ((t + 1) - 1) j (k + i - (t + 1) + 1) = 0 at hz
    change
      X.1 t j (k + i - t) +
        X.1 (t + 1) j (k + i - (t + 1)) = 0
    rw [add_comm]
    simpa only [show (t + 1) - 1 = t by abel,
      show k + i - (t + 1) + 1 = k + i - t by abel] using hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf i
  simpa [f] using hc

private noncomputable def k4KappaMatrixCubeBuild
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F] CyclicCube n where
  toFun M := fun i j k => M j (k + i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem k4KappaMatrixCubeBuild_coeff_zero
    {n : Nat} [NeZero n] (M : MatrixProfile n) :
    k4KappaCoeff (k4KappaMatrixCubeBuild M) = 0 := by
  funext i j k
  change M j (k + i) + M j ((k - 1) + (i + 1)) = 0
  rw [show (k - 1) + (i + 1) = k + i by abel]
  exact F_add_self _

private theorem k4KappaMatrixCubeBuild_transposeCoeff_zero
    {n : Nat} [NeZero n] (M : MatrixProfile n) :
    k4KappaTransposeCoeff (k4KappaMatrixCubeBuild M) = 0 := by
  funext i j k
  change M j (k + i) + M j ((k + 1) + (i - 1)) = 0
  rw [show (k + 1) + (i - 1) = k + i by abel]
  exact F_add_self _

noncomputable def k4KappaKernelRead
    {n : Nat} [NeZero n] :
    LinearMap.ker (k4CubeKappaLinear (n := n)) →ₗ[F]
      MatrixProfile n where
  toFun X := fun j k => X.1 0 j k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4KappaKernelBuild
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F]
      LinearMap.ker (k4CubeKappaLinear (n := n)) where
  toFun M :=
    ⟨k4KappaMatrixCubeBuild M, by
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro W
      change k4CubeKappa (k4KappaMatrixCubeBuild M) W = 0
      rw [k4CubeKappa_eq_cubeDot_coeff,
        k4KappaMatrixCubeBuild_coeff_zero]
      simp [cubeDot]⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

@[simp] theorem k4KappaKernelRead_build
    {n : Nat} [NeZero n] (M : MatrixProfile n) :
    k4KappaKernelRead (k4KappaKernelBuild M) = M := by
  funext j k
  change M j (k + 0) = M j k
  simp

@[simp] theorem k4KappaKernelBuild_read
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (k4CubeKappaLinear (n := n))) :
    k4KappaKernelBuild (k4KappaKernelRead X) = X := by
  apply Subtype.ext
  funext i j k
  change X.1 0 j (k + i) = X.1 i j k
  exact (k4KappaKernel_diagonal_invariant X i j k).symm

noncomputable def k4KappaKernelEquivMatrix
    {n : Nat} [NeZero n] :
    LinearMap.ker (k4CubeKappaLinear (n := n)) ≃ₗ[F]
      MatrixProfile n where
  toLinearMap := k4KappaKernelRead
  invFun := k4KappaKernelBuild
  left_inv := k4KappaKernelBuild_read
  right_inv := k4KappaKernelRead_build

noncomputable def k4KappaFlipKernelRead
    {n : Nat} [NeZero n] :
    LinearMap.ker (k4CubeKappaLinear (n := n)).flip →ₗ[F]
      MatrixProfile n where
  toFun X := fun j k => X.1 0 j k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4KappaFlipKernelBuild
    {n : Nat} [NeZero n] :
    MatrixProfile n →ₗ[F]
      LinearMap.ker (k4CubeKappaLinear (n := n)).flip where
  toFun M :=
    ⟨k4KappaMatrixCubeBuild M, by
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro B
      change k4CubeKappa B (k4KappaMatrixCubeBuild M) = 0
      rw [k4CubeKappa_eq_cubeDot_transposeCoeff,
        k4KappaMatrixCubeBuild_transposeCoeff_zero]
      simp [cubeDot]⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

@[simp] theorem k4KappaFlipKernelRead_build
    {n : Nat} [NeZero n] (M : MatrixProfile n) :
    k4KappaFlipKernelRead (k4KappaFlipKernelBuild M) = M := by
  funext j k
  change M j (k + 0) = M j k
  simp

@[simp] theorem k4KappaFlipKernelBuild_read
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (k4CubeKappaLinear (n := n)).flip) :
    k4KappaFlipKernelBuild (k4KappaFlipKernelRead X) = X := by
  apply Subtype.ext
  funext i j k
  change X.1 0 j (k + i) = X.1 i j k
  exact (k4KappaFlipKernel_diagonal_invariant X i j k).symm

noncomputable def k4KappaFlipKernelEquivMatrix
    {n : Nat} [NeZero n] :
    LinearMap.ker (k4CubeKappaLinear (n := n)).flip ≃ₗ[F]
      MatrixProfile n where
  toLinearMap := k4KappaFlipKernelRead
  invFun := k4KappaFlipKernelBuild
  left_inv := k4KappaFlipKernelBuild_read
  right_inv := k4KappaFlipKernelRead_build

noncomputable def k4BZTailRadicalEquivMatrix
    {n c : Nat} [NeZero n] :
    K4BZTailRadical n c ≃ₗ[F]
      DiamondEvenAxisValueTailZero n c (MatrixProfile n) :=
  TotalEOEEInternal.TailCoordHelpers.tailZeroCongr
    (zeroVec : PVec n c) (k4KappaKernelEquivMatrix (n := n))

noncomputable def k4WZTailRadicalEquivMatrix
    {n c : Nat} [NeZero n] :
    K4WZTailRadical n c ≃ₗ[F]
      DiamondEvenAxisValueTailZero n c (MatrixProfile n) :=
  TotalEOEEInternal.TailCoordHelpers.tailZeroCongr
    (zeroVec : PVec n c) (k4KappaFlipKernelEquivMatrix (n := n))

/-! ## The two scalar head radicals -/

private theorem k4PHead_invariant
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (cubeDiffP (n := n)))
    (i j k : I n) :
    X.1 i j k = X.1 (i + j) 0 k := by
  let f : Profile n := fun t => X.1 t (i + j - t) k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp X.2) t) (i + j - t)) k
    simp only [Pi.zero_apply] at hz
    rw [EEOEInternal.cubeDiffP_apply] at hz
    change
      X.1 t (i + j - t) k +
        X.1 (t + 1) (i + j - (t + 1)) k = 0
    rw [show i + j - (t + 1) = (i + j - t) - 1 by abel]
    simpa only [add_zero] using hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf
  have h := (hc i).trans (hc (i + j)).symm
  change
    X.1 i (i + j - i) k =
      X.1 (i + j) (i + j - (i + j)) k at h
  simpa only [show i + j - i = j by abel,
    show i + j - (i + j) = 0 by abel] using h

private theorem k4RHead_invariant
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (cubeDiffR (n := n)))
    (i j k : I n) :
    X.1 i j k = X.1 i 0 (j + k) := by
  let f : Profile n := fun t => X.1 i t (j + k - t)
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp X.2) i) (t + 1))
      (j + k - (t + 1))
    simp only [Pi.zero_apply] at hz
    rw [EEOEInternal.cubeDiffR_apply] at hz
    change f t + f (t + 1) = 0
    rw [add_comm]
    simpa only [add_zero,
      show (t + 1) - 1 = t by abel,
      show j + k - (t + 1) + 1 = j + k - t by abel] using hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
  simpa [f] using hc

private theorem k4PHeadScalar_invariant
    {n : Nat} [NeZero n]
    (X : K4BScalarRadical n)
    (i j k : I n) :
    X.1.1 i j k = X.1.1 (i + j + k) 0 0 := by
  let K : LinearMap.ker (k4CubeKappaLinear (n := n)) :=
    ⟨X.1.1, by
      apply LinearMap.mem_ker.mpr
      change k4PHeadCross X.1 = 0
      exact LinearMap.mem_ker.mp X.2⟩
  have hK (i' j' k' : I n) :
      X.1.1 i' j' k' = X.1.1 0 j' (k' + i') :=
    k4KappaKernel_diagonal_invariant K i' j' k'
  calc
    X.1.1 i j k = X.1.1 (i + j) 0 k :=
      k4PHead_invariant X.1 i j k
    _ = X.1.1 0 0 (k + (i + j)) := hK (i + j) 0 k
    _ = X.1.1 (i + j + k) 0 0 := by
      rw [hK (i + j + k) 0 0]
      exact congrArg (fun t => X.1.1 0 0 t) (by abel)

private theorem k4RHeadScalar_invariant
    {n : Nat} [NeZero n]
    (X : K4WScalarRadical n)
    (i j k : I n) :
    X.1.1 i j k = X.1.1 (i + j + k) 0 0 := by
  let K : LinearMap.ker (k4CubeKappaLinear (n := n)).flip :=
    ⟨X.1.1, by
      apply LinearMap.mem_ker.mpr
      change (k4RHeadCross (n := n)).flip X.1 = 0
      exact LinearMap.mem_ker.mp X.2⟩
  have hK (i' j' k' : I n) :
      X.1.1 i' j' k' = X.1.1 0 j' (k' + i') :=
    k4KappaFlipKernel_diagonal_invariant K i' j' k'
  calc
    X.1.1 i j k = X.1.1 i 0 (j + k) :=
      k4RHead_invariant X.1 i j k
    _ = X.1.1 0 0 ((j + k) + i) := hK i 0 (j + k)
    _ = X.1.1 (i + j + k) 0 0 := by
      rw [hK (i + j + k) 0 0]
      exact congrArg (fun t => X.1.1 0 0 t) (by abel)

noncomputable def k4PHeadScalarRead
    {n : Nat} [NeZero n] :
    K4BScalarRadical n →ₗ[F] Profile n where
  toFun X := fun s => X.1.1 s 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4PHeadScalarBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] K4BScalarRadical n where
  toFun h :=
    let M : MatrixProfile n := fun j k => h (j + k)
    let K := k4KappaKernelBuild M
    let P : LinearMap.ker (cubeDiffP (n := n)) :=
      ⟨K.1, by
        apply LinearMap.mem_ker.mpr
        funext i j k
        rw [EEOEInternal.cubeDiffP_apply]
        change h (j + (k + i)) + h ((j - 1) + (k + (i + 1))) = 0
        rw [show (j - 1) + (k + (i + 1)) = j + (k + i) by abel]
        exact F_add_self _⟩
    ⟨P, by
      apply LinearMap.mem_ker.mpr
      change k4CubeKappaLinear K.1 = 0
      exact LinearMap.mem_ker.mp K.2⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp] theorem k4PHeadScalarRead_build
    {n : Nat} [NeZero n] (h : Profile n) :
    k4PHeadScalarRead (k4PHeadScalarBuild h) = h := by
  funext s
  change h (0 + (0 + s)) = h s
  simp

@[simp] theorem k4PHeadScalarBuild_read
    {n : Nat} [NeZero n] (X : K4BScalarRadical n) :
    k4PHeadScalarBuild (k4PHeadScalarRead X) = X := by
  apply Subtype.ext
  apply Subtype.ext
  funext i j k
  change X.1.1 (j + (k + i)) 0 0 = X.1.1 i j k
  rw [show j + (k + i) = i + j + k by abel]
  exact (k4PHeadScalar_invariant X i j k).symm

noncomputable def k4PHeadScalarEquiv
    {n : Nat} [NeZero n] :
    K4BScalarRadical n ≃ₗ[F] Profile n where
  toLinearMap := k4PHeadScalarRead
  invFun := k4PHeadScalarBuild
  left_inv := k4PHeadScalarBuild_read
  right_inv := k4PHeadScalarRead_build

noncomputable def k4RHeadScalarRead
    {n : Nat} [NeZero n] :
    K4WScalarRadical n →ₗ[F] Profile n where
  toFun X := fun s => X.1.1 s 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4RHeadScalarBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] K4WScalarRadical n where
  toFun h :=
    let M : MatrixProfile n := fun j k => h (j + k)
    let K := k4KappaFlipKernelBuild M
    let R : LinearMap.ker (cubeDiffR (n := n)) :=
      ⟨K.1, by
        apply LinearMap.mem_ker.mpr
        funext i j k
        rw [EEOEInternal.cubeDiffR_apply]
        change h (j + (k + i)) + h ((j - 1) + ((k + 1) + i)) = 0
        rw [show (j - 1) + ((k + 1) + i) = j + (k + i) by abel]
        exact F_add_self _⟩
    ⟨R, by
      apply LinearMap.mem_ker.mpr
      change (k4CubeKappaLinear (n := n)).flip K.1 = 0
      exact LinearMap.mem_ker.mp K.2⟩
  map_add' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp] theorem k4RHeadScalarRead_build
    {n : Nat} [NeZero n] (h : Profile n) :
    k4RHeadScalarRead (k4RHeadScalarBuild h) = h := by
  funext s
  change h (0 + (0 + s)) = h s
  simp

@[simp] theorem k4RHeadScalarBuild_read
    {n : Nat} [NeZero n] (X : K4WScalarRadical n) :
    k4RHeadScalarBuild (k4RHeadScalarRead X) = X := by
  apply Subtype.ext
  apply Subtype.ext
  funext i j k
  change X.1.1 (j + (k + i)) 0 0 = X.1.1 i j k
  rw [show j + (k + i) = i + j + k by abel]
  exact (k4RHeadScalar_invariant X i j k).symm

noncomputable def k4RHeadScalarEquiv
    {n : Nat} [NeZero n] :
    K4WScalarRadical n ≃ₗ[F] Profile n where
  toLinearMap := k4RHeadScalarRead
  invFun := k4RHeadScalarBuild
  left_inv := k4RHeadScalarBuild_read
  right_inv := k4RHeadScalarRead_build

/-! ## Pointwise membership in the three-block model -/

private theorem diamondCrossProd_mem_ker_iff
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommGroup U₁] [Module F U₁]
    [AddCommGroup U₂] [Module F U₂]
    [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂)
    (x : U₁ × U₂) :
    x ∈ LinearMap.ker (diamondCrossProd f g) ↔
      x.1 ∈ LinearMap.ker f ∧ x.2 ∈ LinearMap.ker g := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    constructor
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      have hpoint := LinearMap.congr_fun hx (y, 0)
      change f x.1 y + g x.2 0 = 0 at hpoint
      simpa only [map_zero, LinearMap.zero_apply, add_zero] using hpoint
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      have hpoint := LinearMap.congr_fun hx (0, y)
      change f x.1 0 + g x.2 y = 0 at hpoint
      simpa only [map_zero, LinearMap.zero_apply, zero_add] using hpoint
  · rintro ⟨hf, hg⟩
    apply LinearMap.ext
    intro y
    change f x.1 y.1 + g x.2 y.2 = 0
    rw [LinearMap.congr_fun (LinearMap.mem_ker.mp hf) y.1,
      LinearMap.congr_fun (LinearMap.mem_ker.mp hg) y.2]
    simp

private theorem diamondCrossProd_flip_mem_ker_iff
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommGroup U₁] [Module F U₁]
    [AddCommGroup U₂] [Module F U₂]
    [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂)
    (x : V₁ × V₂) :
    x ∈ LinearMap.ker (diamondCrossProd f g).flip ↔
      x.1 ∈ LinearMap.ker f.flip ∧
        x.2 ∈ LinearMap.ker g.flip := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    constructor
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      have hpoint := LinearMap.congr_fun hx (y, 0)
      change f y x.1 + g 0 x.2 = 0 at hpoint
      change f y x.1 = 0
      simpa using hpoint
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      have hpoint := LinearMap.congr_fun hx (0, y)
      change f 0 x.1 + g y x.2 = 0 at hpoint
      change g y x.2 = 0
      simpa using hpoint
  · rintro ⟨hf, hg⟩
    apply LinearMap.ext
    intro y
    change f y.1 x.1 + g y.2 x.2 = 0
    have hf0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hf) y.1
    have hg0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hg) y.2
    change f y.1 x.1 = 0 at hf0
    change g y.2 x.2 = 0 at hg0
    rw [hf0, hg0]
    simp

private theorem k4AggregateCrossModel_mem_ker_iff
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4BAggregateCoords n c) :
    x ∈ LinearMap.ker (k4AggregateCrossModel (n := n) (c := c)) ↔
      x.1.1 ∈ LinearMap.ker (k4PHeadCross (n := n)) ∧
        x.1.2 ∈ LinearMap.ker (k4RHeadCross (n := n)) ∧
          ∀ t, k4CubeKappaLinear (x.2.1 t) = 0 := by
  unfold k4AggregateCrossModel
  rw [diamondCrossProd_mem_ker_iff,
    diamondCrossProd_mem_ker_iff]
  constructor
  · rintro ⟨⟨hP, hR⟩, hT⟩
    refine ⟨hP, hR, ?_⟩
    exact (diamondTailAmplify_eq_zero_iff hn2 hn hc2
      (k4CubeKappaLinear (n := n)) x.2).mp
        (LinearMap.mem_ker.mp hT)
  · rintro ⟨hP, hR, hT⟩
    refine ⟨⟨hP, hR⟩, ?_⟩
    apply LinearMap.mem_ker.mpr
    exact (diamondTailAmplify_eq_zero_iff hn2 hn hc2
      (k4CubeKappaLinear (n := n)) x.2).mpr hT

private theorem diamondTailAmplify_flip
    {n c : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V) :
    (diamondTailAmplify (n := n) (k := c) f).flip =
      diamondTailAmplify (n := n) (k := c) f.flip := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

private theorem k4AggregateCrossModel_flip_mem_ker_iff
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4WAggregateCoords n c) :
    x ∈ LinearMap.ker (k4AggregateCrossModel (n := n) (c := c)).flip ↔
      x.1.1 ∈ LinearMap.ker (k4PHeadCross (n := n)).flip ∧
        x.1.2 ∈ LinearMap.ker (k4RHeadCross (n := n)).flip ∧
          ∀ t, (k4CubeKappaLinear (n := n)).flip (x.2.1 t) = 0 := by
  unfold k4AggregateCrossModel
  rw [diamondCrossProd_flip_mem_ker_iff,
    diamondCrossProd_flip_mem_ker_iff]
  constructor
  · rintro ⟨⟨hP, hR⟩, hT⟩
    refine ⟨hP, hR, ?_⟩
    have hzero := LinearMap.mem_ker.mp hT
    rw [diamondTailAmplify_flip] at hzero
    exact (diamondTailAmplify_eq_zero_iff hn2 hn hc2
      (k4CubeKappaLinear (n := n)).flip x.2).mp hzero
  · rintro ⟨hP, hR, hT⟩
    refine ⟨⟨hP, hR⟩, ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [diamondTailAmplify_flip]
    exact (diamondTailAmplify_eq_zero_iff hn2 hn hc2
      (k4CubeKappaLinear (n := n)).flip x.2).mpr hT

private theorem k4ZAggregateCross_mem_ker_iff_coordinates
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (B : K4BAggregateLeft n c) :
    B ∈ LinearMap.ker (k4ZAggregateCross (n := n) (c := c)) ↔
      let x := k4BAggregateCoordEquiv hn hc2 B
      x.1.1 ∈ LinearMap.ker (k4PHeadCross (n := n)) ∧
        x.1.2 ∈ LinearMap.ker (k4RHeadCross (n := n)) ∧
          ∀ t, k4CubeKappaLinear (x.2.1 t) = 0 := by
  let x := k4BAggregateCoordEquiv hn hc2 B
  rw [← k4AggregateCrossModel_mem_ker_iff hn2 hn hc2 x]
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hB
    apply LinearMap.ext
    intro y
    let W := (k4WAggregateCoordEquiv hn hc2).symm y
    calc
      k4AggregateCrossModel x y =
          k4ZAggregateCross B W := by
            simpa only [x, W, LinearEquiv.apply_symm_apply] using
              k4AggregateCrossModel_phase hn hc2 B W
      _ = 0 := LinearMap.congr_fun hB W
  · intro hx
    apply LinearMap.ext
    intro W
    calc
      k4ZAggregateCross B W =
          k4AggregateCrossModel x (k4WAggregateCoordEquiv hn hc2 W) :=
            (k4AggregateCrossModel_phase hn hc2 B W).symm
      _ = 0 := LinearMap.congr_fun hx _

private theorem k4ZAggregateCross_flip_mem_ker_iff_coordinates
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (W : K4WAggregateLeft n c) :
    W ∈ LinearMap.ker (k4ZAggregateCross (n := n) (c := c)).flip ↔
      let x := k4WAggregateCoordEquiv hn hc2 W
      x.1.1 ∈ LinearMap.ker (k4PHeadCross (n := n)).flip ∧
        x.1.2 ∈ LinearMap.ker (k4RHeadCross (n := n)).flip ∧
          ∀ t, (k4CubeKappaLinear (n := n)).flip (x.2.1 t) = 0 := by
  let x := k4WAggregateCoordEquiv hn hc2 W
  rw [← k4AggregateCrossModel_flip_mem_ker_iff hn2 hn hc2 x]
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hW
    apply LinearMap.ext
    intro y
    let B := (k4BAggregateCoordEquiv hn hc2).symm y
    calc
      (k4AggregateCrossModel (n := n) (c := c)).flip x y =
          (k4ZAggregateCross (n := n) (c := c)).flip W B := by
            simpa only [x, B, LinearEquiv.apply_symm_apply] using
              k4AggregateCrossModel_phase hn hc2 B W
      _ = 0 := LinearMap.congr_fun hW B
  · intro hx
    apply LinearMap.ext
    intro B
    calc
      (k4ZAggregateCross (n := n) (c := c)).flip W B =
          (k4AggregateCrossModel (n := n) (c := c)).flip x
            (k4BAggregateCoordEquiv hn hc2 B) :=
              (k4AggregateCrossModel_phase hn hc2 B W).symm
      _ = 0 := LinearMap.congr_fun hx _

set_option maxHeartbeats 2000000 in
-- Normalizing the two transported pointed-coordinate equivalences and all
-- six subtype clauses exceeds the default budget deterministically.
theorem k4AggregatePolar_mem_ker_iff_coordinates
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    x ∈ LinearMap.ker (k4AggregateHyperbolicPolar (n := n) (c := c)) ↔
      let B := k4BAggregateCoordEquiv hn hc2 x.1
      let W := k4WAggregateCoordEquiv hn hc2 x.2
      B.1.1 ∈ LinearMap.ker (k4PHeadCross (n := n)) ∧
        B.1.2 ∈ LinearMap.ker (k4RHeadCross (n := n)) ∧
          (∀ t, k4CubeKappaLinear (B.2.1 t) = 0) ∧
            W.1.1 ∈ LinearMap.ker (k4PHeadCross (n := n)).flip ∧
              W.1.2 ∈ LinearMap.ker (k4RHeadCross (n := n)).flip ∧
                ∀ t, (k4CubeKappaLinear (n := n)).flip (W.2.1 t) = 0 := by
  rw [k4AggregateHyperbolicPolar_mem_ker_iff,
    k4ZAggregateCross_mem_ker_iff_coordinates hn2 hn hc2,
    k4ZAggregateCross_flip_mem_ker_iff_coordinates hn2 hn hc2]
  tauto

/-! ## Formula-defined half-kernel coordinates -/

private noncomputable def k4BHalfKernelCoordinateEquiv
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    LinearMap.ker (k4ZAggregateCross (n := n) (c := c)) ≃ₗ[F]
      ((K4BScalarRadical n × K4BFreeHeadRadical n) ×
        K4BZTailRadical n c) where
  toFun x := by
    let y := k4BAggregateCoordEquiv hn hc2 x.1
    have h := (k4ZAggregateCross_mem_ker_iff_coordinates
      hn2 hn hc2 x.1).mp x.2
    exact
      ((⟨y.1.1, h.1⟩, ⟨y.1.2, h.2.1⟩),
        ⟨fun t => ⟨y.2.1 t, h.2.2 t⟩, by
          apply LinearMap.mem_ker.mpr
          change (∑ t, (⟨y.2.1 t, h.2.2 t⟩ :
            LinearMap.ker (k4CubeKappaLinear (n := n)))) = 0
          apply Subtype.ext
          simpa only [Submodule.coe_sum, Submodule.coe_zero] using
            pointedValueTailZero_sum y.2⟩)
  invFun z := by
    let yTail : DiamondEvenAxisValueTailZero n c (CyclicCube n) :=
      ⟨fun t => (z.2.1 t).1, by
        apply LinearMap.mem_ker.mpr
        have hz := pointedValueTailZero_sum z.2
        simpa only [Submodule.coe_sum] using congrArg Subtype.val hz⟩
    let y : K4BAggregateCoords n c :=
      ((z.1.1.1, z.1.2.1), yTail)
    let B := (k4BAggregateCoordEquiv hn hc2).symm y
    refine ⟨B, (k4ZAggregateCross_mem_ker_iff_coordinates
      hn2 hn hc2 B).mpr ?_⟩
    have hcoords : k4BAggregateCoordEquiv hn hc2 B = y := by
      exact (k4BAggregateCoordEquiv hn hc2).apply_symm_apply y
    rw [hcoords]
    exact ⟨z.1.1.2, z.1.2.2, fun t => (z.2.1 t).2⟩
  left_inv x := by
    apply Subtype.ext
    let E := k4BAggregateCoordEquiv hn hc2
    apply E.injective
    change E (E.symm (((E x.1).1.1, (E x.1).1.2), (E x.1).2)) = E x.1
    rw [E.apply_symm_apply]
  right_inv z := by
    let E := k4BAggregateCoordEquiv hn hc2
    let yTail : DiamondEvenAxisValueTailZero n c (CyclicCube n) :=
      ⟨fun t => (z.2.1 t).1, by
        apply LinearMap.mem_ker.mpr
        have hz := pointedValueTailZero_sum z.2
        simpa only [Submodule.coe_sum] using congrArg Subtype.val hz⟩
    let y : K4BAggregateCoords n c :=
      ((z.1.1.1, z.1.2.1), yTail)
    have h := E.apply_symm_apply y
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) h
      · apply Subtype.ext
        exact congrArg (fun q => q.1.2) h
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) h
  map_add' x x' := by
    let E := k4BAggregateCoordEquiv hn hc2
    have h := E.map_add x.1 x'.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) h
      · apply Subtype.ext
        exact congrArg (fun q => q.1.2) h
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) h
  map_smul' r x := by
    let E := k4BAggregateCoordEquiv hn hc2
    have h := E.map_smul r x.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) h
      · apply Subtype.ext
        exact congrArg (fun q => q.1.2) h
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) h

private noncomputable def k4WHalfKernelCoordinateEquiv
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    LinearMap.ker (k4ZAggregateCross (n := n) (c := c)).flip ≃ₗ[F]
      ((K4WFreeHeadRadical n × K4WScalarRadical n) ×
        K4WZTailRadical n c) where
  toFun x := by
    let y := k4WAggregateCoordEquiv hn hc2 x.1
    have h := (k4ZAggregateCross_flip_mem_ker_iff_coordinates
      hn2 hn hc2 x.1).mp x.2
    exact
      ((⟨y.1.1, h.1⟩, ⟨y.1.2, h.2.1⟩),
        ⟨fun t => ⟨y.2.1 t, h.2.2 t⟩, by
          apply LinearMap.mem_ker.mpr
          change (∑ t, (⟨y.2.1 t, h.2.2 t⟩ :
            LinearMap.ker (k4CubeKappaLinear (n := n)).flip)) = 0
          apply Subtype.ext
          simpa only [Submodule.coe_sum, Submodule.coe_zero] using
            pointedValueTailZero_sum y.2⟩)
  invFun z := by
    let yTail : DiamondEvenAxisValueTailZero n c (CyclicCube n) :=
      ⟨fun t => (z.2.1 t).1, by
        apply LinearMap.mem_ker.mpr
        have hz := pointedValueTailZero_sum z.2
        simpa only [Submodule.coe_sum] using congrArg Subtype.val hz⟩
    let y : K4WAggregateCoords n c :=
      ((z.1.1.1, z.1.2.1), yTail)
    let W := (k4WAggregateCoordEquiv hn hc2).symm y
    refine ⟨W, (k4ZAggregateCross_flip_mem_ker_iff_coordinates
      hn2 hn hc2 W).mpr ?_⟩
    have hcoords : k4WAggregateCoordEquiv hn hc2 W = y := by
      exact (k4WAggregateCoordEquiv hn hc2).apply_symm_apply y
    rw [hcoords]
    exact ⟨z.1.1.2, z.1.2.2, fun t => (z.2.1 t).2⟩
  left_inv x := by
    apply Subtype.ext
    let E := k4WAggregateCoordEquiv hn hc2
    apply E.injective
    change E (E.symm (((E x.1).1.1, (E x.1).1.2), (E x.1).2)) = E x.1
    rw [E.apply_symm_apply]
  right_inv z := by
    let E := k4WAggregateCoordEquiv hn hc2
    let yTail : DiamondEvenAxisValueTailZero n c (CyclicCube n) :=
      ⟨fun t => (z.2.1 t).1, by
        apply LinearMap.mem_ker.mpr
        have hz := pointedValueTailZero_sum z.2
        simpa only [Submodule.coe_sum] using congrArg Subtype.val hz⟩
    let y : K4WAggregateCoords n c :=
      ((z.1.1.1, z.1.2.1), yTail)
    have h := E.apply_symm_apply y
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) h
      · apply Subtype.ext
        exact congrArg (fun q => q.1.2) h
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) h
  map_add' x x' := by
    let E := k4WAggregateCoordEquiv hn hc2
    have h := E.map_add x.1 x'.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) h
      · apply Subtype.ext
        exact congrArg (fun q => q.1.2) h
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) h
  map_smul' r x := by
    let E := k4WAggregateCoordEquiv hn hc2
    have h := E.map_smul r x.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) h
      · apply Subtype.ext
        exact congrArg (fun q => q.1.2) h
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) h

/-! ## The frozen six-factor endpoint -/

noncomputable abbrev K4AggregatePolarCoordinateTarget
    (n c : Nat) [NeZero n] :=
  (((Profile n × K4BFreeHeadRadical n) ×
      DiamondEvenAxisValueTailZero n c (MatrixProfile n)) ×
    ((K4WFreeHeadRadical n × Profile n) ×
      DiamondEvenAxisValueTailZero n c (MatrixProfile n)))

private noncomputable def k4BHalfSimplifyEquiv
    {n c : Nat} [NeZero n] :
    ((K4BScalarRadical n × K4BFreeHeadRadical n) ×
        K4BZTailRadical n c) ≃ₗ[F]
      ((Profile n × K4BFreeHeadRadical n) ×
        DiamondEvenAxisValueTailZero n c (MatrixProfile n)) :=
  ((k4PHeadScalarEquiv (n := n)).prodCongr
      (LinearEquiv.refl F (K4BFreeHeadRadical n))).prodCongr
    (k4BZTailRadicalEquivMatrix (n := n) (c := c))

private noncomputable def k4WHalfSimplifyEquiv
    {n c : Nat} [NeZero n] :
    ((K4WFreeHeadRadical n × K4WScalarRadical n) ×
        K4WZTailRadical n c) ≃ₗ[F]
      ((K4WFreeHeadRadical n × Profile n) ×
        DiamondEvenAxisValueTailZero n c (MatrixProfile n)) :=
  ((LinearEquiv.refl F (K4WFreeHeadRadical n)).prodCongr
      (k4RHeadScalarEquiv (n := n))).prodCongr
    (k4WZTailRadicalEquivMatrix (n := n) (c := c))

private noncomputable def k4AggregatePolarKernelCoordinateEquivCore
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    K4AggregatePolarKernel n c ≃ₗ[F]
      K4AggregatePolarCoordinateTarget n c :=
  (k4AggregatePolarKernelEquivHalfKernels (n := n) (c := c)).trans
    (((k4BHalfKernelCoordinateEquiv hn2 hn hc2).prodCongr
      (k4WHalfKernelCoordinateEquiv hn2 hn hc2)).trans
        ((k4BHalfSimplifyEquiv (n := n) (c := c)).prodCongr
          (k4WHalfSimplifyEquiv (n := n) (c := c))))

noncomputable def k4AggregatePolarKernelCoordinateRead
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    K4AggregatePolarKernel n c →ₗ[F]
      K4AggregatePolarCoordinateTarget n c :=
  (k4AggregatePolarKernelCoordinateEquivCore hn2 hn hc2).toLinearMap

noncomputable def k4AggregatePolarKernelCoordinateBuild
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    K4AggregatePolarCoordinateTarget n c →ₗ[F]
      K4AggregatePolarKernel n c :=
  (k4AggregatePolarKernelCoordinateEquivCore hn2 hn hc2).symm.toLinearMap

@[simp] theorem k4AggregatePolarKernelCoordinateRead_build
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarCoordinateTarget n c) :
    k4AggregatePolarKernelCoordinateRead hn2 hn hc2
        (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 x) = x := by
  exact (k4AggregatePolarKernelCoordinateEquivCore
    hn2 hn hc2).apply_symm_apply x

@[simp] theorem k4AggregatePolarKernelCoordinateBuild_read
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarKernel n c) :
    k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
        (k4AggregatePolarKernelCoordinateRead hn2 hn hc2 x) = x := by
  exact (k4AggregatePolarKernelCoordinateEquivCore
    hn2 hn hc2).symm_apply_apply x

noncomputable def k4AggregatePolarKernelCoordinateEquiv
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    K4AggregatePolarKernel n c ≃ₗ[F]
      K4AggregatePolarCoordinateTarget n c where
  toLinearMap := k4AggregatePolarKernelCoordinateRead hn2 hn hc2
  invFun := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
  left_inv := k4AggregatePolarKernelCoordinateBuild_read hn2 hn hc2
  right_inv := k4AggregatePolarKernelCoordinateRead_build hn2 hn hc2

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
