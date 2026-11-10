import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RightReachable

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
-- The frozen completion-first reachable-source certificate uses one file-wide budget.
set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace T37RightP1

private noncomputable def singletonMiddleEquiv
    {n : Nat} [NeZero n]
    (Y W V : Type*) [AddCommGroup V] [Module F V] :
    (Y → PVec n 1 → W → V) ≃ₗ[F] (Y → W → V) where
  toFun f y w := f y zeroVec w
  invFun f y _ w := f y w
  left_inv f := by
    funext y z w
    rw [pVec_one_eq_zeroVec z]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def cubeIKShift
    {n : Nat} [NeZero n] (ui uk : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X (i - ui) j (k - uk)
  invFun X i j k := X (i + ui) j (k + uk)
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem cubeIKShift_apply
    {n : Nat} [NeZero n] (ui uk : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeIKShift ui uk X i j k =
      X (i - ui) j (k - uk) := rfl

private noncomputable def ywGaugeEquiv
    {n b d : Nat} [NeZero n] :
    (PVec n b → PVec n d → CyclicCube n) ≃ₗ[F]
      (PVec n b → PVec n d → CyclicCube n) where
  toFun f yt wt :=
    cubeIKShift (vecSum yt) (vecSum wt) (f yt wt)
  invFun f yt wt :=
    (cubeIKShift (vecSum yt) (vecSum wt)).symm (f yt wt)
  left_inv f := by
    funext yt wt
    exact
      (cubeIKShift (vecSum yt) (vecSum wt)).symm_apply_apply
        (f yt wt)
  right_inv f := by
    funext yt wt
    exact
      (cubeIKShift (vecSum yt) (vecSum wt)).apply_symm_apply
        (f yt wt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def aLiteralGaugeEquiv
    {n b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    AFun4 n b 1 d ≃ₗ[F]
      (PVec n b → PVec n d → CyclicCube n) :=
  (diamondARootCubeEquiv
      (n := n) (b := b) (c := 1) (d := d)
      hb Nat.zero_lt_one hd).trans
    ((singletonMiddleEquiv
      (n := n) (PVec n b) (PVec n d) (CyclicCube n)).trans
        (ywGaugeEquiv (n := n) (b := b) (d := d)))

private noncomputable def cubeKShift
    {n : Nat} [NeZero n] (uk : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n :=
  cubeIKShift 0 uk

private noncomputable def cubeIShift
    {n : Nat} [NeZero n] (ui : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n :=
  cubeIKShift ui 0

private noncomputable def bLiteralGaugeEquiv
    {n d : Nat} [NeZero n]
    (hd : 0 < d) :
    BFun4 n 1 1 d ≃ₗ[F] (PVec n d → CyclicCube n) :=
  (diamondBRootCubeEquiv
      (n := n) (c := 1) (d := d) Nat.zero_lt_one hd).trans
    { toFun := fun f wt => cubeKShift (vecSum wt) (f zeroVec wt)
      invFun := fun f _ wt => (cubeKShift (vecSum wt)).symm (f wt)
      left_inv := by
        intro f
        funext zt wt
        rw [pVec_one_eq_zeroVec zt]
        exact
          (cubeKShift (vecSum wt)).symm_apply_apply (f zeroVec wt)
      right_inv := by
        intro f
        funext wt
        exact
          (cubeKShift (vecSum wt)).apply_symm_apply (f wt)
      map_add' := by intro _ _; rfl
      map_smul' := by intro _ _; rfl }

private noncomputable def wLiteralGaugeEquiv
    {n b : Nat} [NeZero n]
    (hb : 0 < b) :
    WFun4 n 1 b 1 ≃ₗ[F] (PVec n b → CyclicCube n) :=
  (diamondWRootCubeEquiv
      (n := n) (b := b) (c := 1) hb Nat.zero_lt_one).trans
    { toFun := fun f yt => cubeIShift (vecSum yt) (f yt zeroVec)
      invFun := fun f yt _ => (cubeIShift (vecSum yt)).symm (f yt)
      left_inv := by
        intro f
        funext yt zt
        rw [pVec_one_eq_zeroVec zt]
        exact
          (cubeIShift (vecSum yt)).symm_apply_apply (f yt zeroVec)
      right_inv := by
        intro f
        funext yt
        exact
          (cubeIShift (vecSum yt)).apply_symm_apply (f yt)
      map_add' := by intro _ _; rfl
      map_smul' := by intro _ _; rfl }

private noncomputable def t37RightConstraintMap
    {n b d : Nat} [NeZero n] :
    ((PVec n d → CyclicCube n) ×
      (PVec n b → CyclicCube n)) →ₗ[F]
      (PVec n b → PVec n d → CyclicCube n) where
  toFun q yt wt := cubeDiffP (q.1 wt) + cubeDiffR (q.2 yt)
  map_add' q q' := by
    funext yt wt
    simp
    abel
  map_smul' r q := by
    funext yt wt
    simp

@[simp] private theorem vecSum_zero_local
    {n k : Nat} [NeZero n] :
    vecSum (zeroVec : Vec n k) = 0 := by
  unfold vecSum zeroVec
  simp

@[simp] private theorem cubeIKShift_cubeDiffP_apply
    {n : Nat} [NeZero n] (ui uk : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffP (cubeIKShift ui uk X) i j k =
      cubeDiffP X (i - ui) j (k - uk) := by
  rw [EEOEInternal.cubeDiffP_apply, EEOEInternal.cubeDiffP_apply]
  simp only [cubeIKShift_apply]
  congr 2
  abel

@[simp] private theorem cubeIKShift_cubeDiffR_apply
    {n : Nat} [NeZero n] (ui uk : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffR (cubeIKShift ui uk X) i j k =
      cubeDiffR X (i - ui) j (k - uk) := by
  rw [EEOEInternal.cubeDiffR_apply, EEOEInternal.cubeDiffR_apply]
  simp only [cubeIKShift_apply]
  congr 2
  abel

@[simp] private theorem cubeIKShift_cubeDiffJInv_apply
    {n : Nat} [NeZero n] (ui uk : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffJInv (cubeIKShift ui uk X) i j k =
      cubeDiffJInv X (i - ui) j (k - uk) := by
  rw [EEOEInternal.cubeDiffJInv_apply,
    EEOEInternal.cubeDiffJInv_apply]
  simp only [cubeIKShift_apply]

@[simp] private theorem bLiteralGauge_cubeDiffP_apply
    {n d : Nat} [NeZero n] (hd : 0 < d)
    (B : BFun4 n 1 1 d) (wt : PVec n d)
    (i j k : I n) :
    cubeDiffP (bLiteralGaugeEquiv hd B wt) i j k =
      cubeDiffP
        (diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt)
        i j (k - vecSum wt) := by
  change
    cubeDiffP
        (cubeKShift (vecSum wt)
          (diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt))
        i j k = _
  simpa only [cubeKShift, sub_zero] using
    cubeIKShift_cubeDiffP_apply
      (0 : I n) (vecSum wt)
      (diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt)
      i j k

@[simp] private theorem wLiteralGauge_cubeDiffR_apply
    {n b : Nat} [NeZero n] (hb : 0 < b)
    (W : WFun4 n 1 b 1) (yt : PVec n b)
    (i j k : I n) :
    cubeDiffR (wLiteralGaugeEquiv hb W yt) i j k =
      cubeDiffR
        (diamondWRootCubeEquiv hb Nat.zero_lt_one W yt zeroVec)
        (i - vecSum yt) j k := by
  change
    cubeDiffR
        (cubeIShift (vecSum yt)
          (diamondWRootCubeEquiv hb Nat.zero_lt_one W yt zeroVec))
        i j k = _
  simpa only [cubeIShift, sub_zero] using
    cubeIKShift_cubeDiffR_apply
      (vecSum yt) (0 : I n)
      (diamondWRootCubeEquiv hb Nat.zero_lt_one W yt zeroVec)
      i j k

@[simp] private theorem aLiteralGauge_cubeDiffJInv_apply
    {n b d : Nat} [NeZero n] (hb : 0 < b) (hd : 0 < d)
    (A : AFun4 n b 1 d) (yt : PVec n b) (wt : PVec n d)
    (i j k : I n) :
    cubeDiffJInv (aLiteralGaugeEquiv hb hd A yt wt) i j k =
      cubeDiffJInv
        (diamondARootCubeEquiv hb Nat.zero_lt_one hd
          A yt zeroVec wt)
        (i - vecSum yt) j (k - vecSum wt) := by
  change
    cubeDiffJInv
        (cubeIKShift (vecSum yt) (vecSum wt)
          (diamondARootCubeEquiv hb Nat.zero_lt_one hd
            A yt zeroVec wt))
        i j k = _
  exact
    cubeIKShift_cubeDiffJInv_apply
      (vecSum yt) (vecSum wt)
      (diamondARootCubeEquiv hb Nat.zero_lt_one hd
        A yt zeroVec wt)
      i j k

private theorem t37SumPVecOne
    {n : Nat} [NeZero n]
    {V : Type*} [AddCommMonoid V]
    (f : PVec n 1 → V) :
    (∑ z : PVec n 1, f z) = f zeroVec := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro z _ hz
    exact (hz (pVec_one_eq_zeroVec z)).elim
  · simp

theorem literal_reachable_iff_gauged_range
    {n b d : Nat} [NeZero n]
    (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : AFun4 n b 1 d) :
    A ∈ DiamondEvenPReachableA n b 1 d ↔
      (fun yt wt =>
        cubeDiffJInv
          (aLiteralGaugeEquiv
            (by omega : 0 < b) (by omega : 0 < d) A yt wt)) ∈
        LinearMap.range
          (t37RightConstraintMap (n := n) (b := b) (d := d)) := by
  change
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := b) (c := 1) (d := d) A ∈
      LinearMap.range
        (squareCompat
          (n := n) (a := 1) (b := b) (c := 1) (d := d)) ↔ _
  constructor
  · rintro ⟨bw, hbw⟩
    let bg := bLiteralGaugeEquiv (n := n) (d := d) (by omega) bw.1
    let wg := wLiteralGaugeEquiv (n := n) (b := b) (by omega) bw.2
    refine ⟨(bg, wg), ?_⟩
    funext yt wt i j k
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hbw (zeroVec : PVec n 1))
              ((diamondVecHeadTailEquiv (by omega : 0 < b)).symm
                (i - vecSum yt, yt)))
            j)
          ((diamondVecHeadTailEquiv (by omega : 0 < d)).symm
            (k - vecSum wt, wt))
    rw [diamondCubeReindex_squareCompat
      (by omega : 0 < b) Nat.zero_lt_one (by omega : 0 < d)
      bw.1 bw.2 yt wt (i - vecSum yt) j (k - vecSum wt)] at hpoint
    rw [diamondCubeReindex_AConstraint
      (by omega : 0 < b) Nat.zero_lt_one (by omega : 0 < d)
      A yt wt (i - vecSum yt) j (k - vecSum wt)] at hpoint
    simp_rw [t37SumPVecOne] at hpoint
    change
      (cubeDiffP (bg wt) + cubeDiffR (wg yt)) i j k =
        cubeDiffJInv
          (aLiteralGaugeEquiv
            (by omega : 0 < b) (by omega : 0 < d) A yt wt)
          i j k
    simpa only [bg, wg,
      Pi.add_apply,
      bLiteralGauge_cubeDiffP_apply,
      wLiteralGauge_cubeDiffR_apply,
      aLiteralGauge_cubeDiffJInv_apply,
      vecSum_zero_local, sub_zero,
      sub_add_cancel] using hpoint
  · rintro ⟨q, hq⟩
    let B :=
      (bLiteralGaugeEquiv
        (n := n) (d := d) (by omega : 0 < d)).symm q.1
    let W :=
      (wLiteralGaugeEquiv
        (n := n) (b := b) (by omega : 0 < b)).symm q.2
    have hB :
        bLiteralGaugeEquiv
          (n := n) (d := d) (by omega : 0 < d) B = q.1 :=
      (bLiteralGaugeEquiv
        (n := n) (d := d) (by omega : 0 < d)).apply_symm_apply q.1
    have hW :
        wLiteralGaugeEquiv
          (n := n) (b := b) (by omega : 0 < b) W = q.2 :=
      (wLiteralGaugeEquiv
        (n := n) (b := b) (by omega : 0 < b)).apply_symm_apply q.2
    refine ⟨(B, W), ?_⟩
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) (by omega : 0 < b)
    let ew := diamondVecHeadTailEquiv (n := n) (by omega : 0 < d)
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      (by omega : 0 < b) Nat.zero_lt_one (by omega : 0 < d)
      B W (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [diamondCubeReindex_AConstraint
      (by omega : 0 < b) Nat.zero_lt_one (by omega : 0 < d)
      A (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    simp_rw [t37SumPVecOne]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hq (ey y).2)
            (ew w).2)
          ((ey y).1 + vecSum (ey y).2))
        sz
    have hpoint' :=
      congrFun hpoint ((ew w).1 + vecSum (ew w).2)
    change
      (cubeDiffP (q.1 (ew w).2) +
        cubeDiffR (q.2 (ey y).2))
          ((ey y).1 + vecSum (ey y).2) sz
          ((ew w).1 + vecSum (ew w).2) =
        cubeDiffJInv
          (aLiteralGaugeEquiv
            (by omega : 0 < b) (by omega : 0 < d)
            A (ey y).2 (ew w).2)
          ((ey y).1 + vecSum (ey y).2) sz
          ((ew w).1 + vecSum (ew w).2) at hpoint'
    rw [← hB, ← hW] at hpoint'
    simpa only [
      Pi.add_apply,
      bLiteralGauge_cubeDiffP_apply,
      wLiteralGauge_cubeDiffR_apply,
      aLiteralGauge_cubeDiffJInv_apply,
      vecSum_zero_local, sub_zero,
      add_sub_cancel_right] using hpoint'

@[reducible] private noncomputable def
    t37PointedCoordsProdAddCommMonoid
    {n d : Nat} [NeZero n] :
    AddCommMonoid
      (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec ×
        PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec))
    (inferInstance :
      AddCommMonoid
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec))

private local instance {n d : Nat} [NeZero n] :
    AddCommMonoid
      (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec ×
        PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec) :=
  t37PointedCoordsProdAddCommMonoid

noncomputable abbrev T37RightAmbientTarget
    (n b d : Nat) [NeZero n] :=
  DiamondEEOERightAmbient n ×
    (DiamondEvenAxisValueTailZero n b
        (CyclicCube n × CyclicCube n) ×
      (DiamondEvenAxisValueTailZero n d
          (CyclicCube n × CyclicCube n) ×
        DiamondMixedTailZero n b d (CyclicCube n)))

private noncomputable def t37NestedDualRawEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    (PVec n b → PVec n d → CyclicCube n) ≃ₗ[F]
      ((PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec ×
        PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec) ×
        DiamondEvenAxisValueTailZero n b
          (PointedEvenValueCoords
            (PVec n d) (CyclicCube n) zeroVec)) :=
  (diamondEvenAxisDualCoordEquiv
      (n := n) (k := b) (PVec n d → CyclicCube n) hn hb2).trans
    ((TotalEOEEInternal.pointedHeadShear
      (zeroVec : PVec n b)).trans
      ((((diamondEvenAxisDualCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
        (diamondEvenAxisDualCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2)).prodCongr
        (TotalEOEEInternal.tailZeroCongr
          (zeroVec : PVec n b)
          (diamondEvenAxisDualCoordEquiv
            (n := n) (k := d) (CyclicCube n) hn hd2)))))

private noncomputable def t37NestedDualShearEquiv
    {n b d : Nat} [NeZero n] :
    ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec ×
      PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec) ×
      DiamondEvenAxisValueTailZero n b
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec)) ≃ₗ[F]
    ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec ×
      PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec) ×
      DiamondEvenAxisValueTailZero n b
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec)) :=
  (((TotalEOEEInternal.pointedHeadShear
        (zeroVec : PVec n d)).prodCongr
      (TotalEOEEInternal.pointedHeadShear
        (zeroVec : PVec n d))).prodCongr
    (TotalEOEEInternal.tailZeroCongr
      (zeroVec : PVec n b)
      (TotalEOEEInternal.pointedHeadShear
        (zeroVec : PVec n d))))

private noncomputable def t37NestedDualReassocEquiv
    {n b d : Nat} [NeZero n] :
    ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec ×
      PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec) ×
      DiamondEvenAxisValueTailZero n b
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec)) ≃ₗ[F]
      T37RightAmbientTarget n b d where
  toFun x :=
    let wt :=
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec).symm
          (x.1.1.2, x.1.2.2)
    let ym :=
      TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n b)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec x.2
    ((x.1.1.1, x.1.2.1), (ym.1, (wt, ym.2)))
  invFun x :=
    let wt :=
      TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec x.2.2.1
    let ym :=
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n b)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec).symm (x.2.1, x.2.2.2)
    (((x.1.1, wt.1), (x.1.2, wt.2)), ym)
  left_inv x := by
    dsimp only
    have hwt :=
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec).apply_symm_apply
          (x.1.1.2, x.1.2.2)
    have hym :=
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n b)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec).symm_apply_apply x.2
    rw [hwt, hym]
  right_inv x := by
    dsimp only
    have hwt :=
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec).symm_apply_apply x.2.2.1
    have hym :=
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n b)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec).apply_symm_apply (x.2.1, x.2.2.2)
    rw [hwt, hym]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · dsimp only
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · dsimp only
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Prod.ext <;> apply Subtype.ext <;> rfl

noncomputable def t37GaugedRightCoordinateEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    (PVec n b → PVec n d → CyclicCube n) ≃ₗ[F]
      T37RightAmbientTarget n b d :=
  (t37NestedDualRawEquiv hn hb2 hd2).trans
    ((t37NestedDualShearEquiv (n := n) (b := b) (d := d)).trans
      (t37NestedDualReassocEquiv (n := n) (b := b) (d := d)))

noncomputable def t37RightAmbientEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    AFun4 n b 1 d ≃ₗ[F]
      T37RightAmbientTarget n b d :=
  (aLiteralGaugeEquiv
      (n := n) (b := b) (d := d) (by omega) (by omega)).trans
    (t37GaugedRightCoordinateEquiv hn hb2 hd2)

private noncomputable def t37YDual
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b)
    (A : PVec n b → PVec n d → CyclicCube n) :=
  diamondEvenAxisDualCoordEquiv
    (n := n) (k := b) (PVec n d → CyclicCube n) hn hb2 A

private noncomputable def t37GDual
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :=
  diamondEvenAxisDualCoordEquiv
    (n := n) (k := d) (CyclicCube n) hn hd2
      (t37YDual hn hb2 A).1.2

private noncomputable def t37QDual
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :=
  diamondEvenAxisDualCoordEquiv
    (n := n) (k := d) (CyclicCube n) hn hd2
      ((t37YDual hn hb2 A).1.1 + (t37YDual hn hb2 A).1.2)

@[simp] theorem t37GaugedRightCoordinateEquiv_scalar
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2 A).1 =
      (((t37GDual hn hb2 hd2 A).1.2,
        (t37GDual hn hb2 hd2 A).1.1 +
          (t37GDual hn hb2 hd2 A).1.2),
       ((t37QDual hn hb2 hd2 A).1.2,
        (t37QDual hn hb2 hd2 A).1.1 +
          (t37QDual hn hb2 hd2 A).1.2)) := by
  rfl

@[simp] theorem t37GaugedRightCoordinateEquiv_Y
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2 A).2.1.1 yt =
      let z :=
        diamondEvenAxisDualCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2
            ((t37YDual hn hb2 A).2.1 yt)
      (z.1.2, z.1.1 + z.1.2) := by
  rfl

@[simp] theorem t37GaugedRightCoordinateEquiv_W
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (wt : DiamondEvenAxisTailIndex n d) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2 A).2.2.1.1 wt =
      ((t37GDual hn hb2 hd2 A).2.1 wt,
        (t37QDual hn hb2 hd2 A).2.1 wt) := by
  rfl

@[simp] theorem t37GaugedRightCoordinateEquiv_mixed
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((t37GaugedRightCoordinateEquiv hn hb2 hd2 A).2.2.2.1 yt).1 wt) =
      let z :=
        diamondEvenAxisDualCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2
            ((t37YDual hn hb2 A).2.1 yt)
      z.2.1 wt := by
  rfl

private theorem t37SumAtPointTail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommMonoid V] (f : S → V) :
    (∑ s, f s) = f s0 + ∑ t : PointedTail S s0, f t.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset S))
      (p := fun s : S => s = s0) f).symm
  calc
    (∑ s, f s) =
        (∑ s ∈ (Finset.univ : Finset S) with s = s0, f s) +
          ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
            simpa using hpart
    _ = f s0 +
        ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
          congr 1
          rw [Finset.sum_eq_single s0]
          · intro s hs hne
            exact (hne (Finset.mem_filter.mp hs).2).elim
          · simp
    _ = f s0 + ∑ t : PointedTail S s0, f t.1 := by
          congr 1
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset S))
              (p := fun s : S => s ≠ s0) (f := f)).symm

private theorem t37CastOddEqOne
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem t37SumConstOdd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    t37CastOddEqOne hodd, one_smul]

private theorem t37AxisDualK_eq_totalSum
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Even n) (hk2 : 2 ≤ k)
    (g : PVec n k → V) :
    (diamondEvenAxisDualCoordEquiv
        (n := n) (k := k) V hn hk2 g).1.2 =
      ∑ s, g s := by
  change
    (∑ t : DiamondEvenAxisTailIndex n k,
      (g t.1 + g (zeroVec : PVec n k))) =
        ∑ s : PVec n k, g s
  rw [Finset.sum_add_distrib,
    t37SumConstOdd
      (odd_card_diamondEvenAxisTailIndex hn hk2),
    t37SumAtPointTail (zeroVec : PVec n k) g]
  abel

private noncomputable def t37G
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n)
    (wt : PVec n d) : CyclicCube n :=
  ∑ yt, A yt wt

private noncomputable def t37H
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : PVec n b) : CyclicCube n :=
  ∑ wt, A yt wt

private noncomputable def t37D
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n) :
    CyclicCube n :=
  ∑ wt, t37G A wt

private theorem t37YDualK_eq_G
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b)
    (A : PVec n b → PVec n d → CyclicCube n) :
    (t37YDual hn hb2 A).1.2 = t37G A := by
  have h :=
    t37AxisDualK_eq_totalSum
      (PVec n d → CyclicCube n) hn hb2 A
  funext wt
  simpa only [t37YDual, t37G, Finset.sum_apply] using congrFun h wt

private theorem t37YDualTail_eq
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b) :
    (t37YDual hn hb2 A).2.1 yt =
      fun wt => A yt.1 wt + A zeroVec wt + t37G A wt := by
  funext wt
  change
    A yt.1 wt + A zeroVec wt + (t37YDual hn hb2 A).1.2 wt =
      A yt.1 wt + A zeroVec wt + t37G A wt
  rw [t37YDualK_eq_G]

private theorem t37GDualK_eq_D
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :
    (t37GDual hn hb2 hd2 A).1.2 = t37D A := by
  rw [t37GDual, t37YDualK_eq_G]
  exact
    t37AxisDualK_eq_totalSum
      (CyclicCube n) hn hd2 (t37G A)

private theorem t37QDualK_eq_H0_add_D
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :
    (t37QDual hn hb2 hd2 A).1.2 =
      t37H A zeroVec + t37D A := by
  rw [t37QDual, t37YDualK_eq_G]
  rw [t37AxisDualK_eq_totalSum]
  change
    (∑ wt : PVec n d, (A zeroVec wt + t37G A wt)) =
      t37H A zeroVec + t37D A
  rw [Finset.sum_add_distrib]
  rfl

theorem t37RightCoordinate_scalar_explicit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2 A).1 =
      ((t37D A, t37G A zeroVec + t37D A),
       (t37H A zeroVec + t37D A,
        A zeroVec zeroVec + t37G A zeroVec +
          t37H A zeroVec + t37D A)) := by
  rw [t37GaugedRightCoordinateEquiv_scalar,
    t37GDualK_eq_D, t37QDualK_eq_H0_add_D]
  have hg0 :
      (t37GDual hn hb2 hd2 A).1.1 = t37G A zeroVec := by
    change (t37YDual hn hb2 A).1.2 zeroVec = t37G A zeroVec
    rw [t37YDualK_eq_G]
  have hq0 :
      (t37QDual hn hb2 hd2 A).1.1 =
        A zeroVec zeroVec + t37G A zeroVec := by
    change
      (t37YDual hn hb2 A).1.1 zeroVec +
          (t37YDual hn hb2 A).1.2 zeroVec =
        A zeroVec zeroVec + t37G A zeroVec
    rw [t37YDualK_eq_G]
    rfl
  rw [hg0, hq0]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · abel

theorem t37RightCoordinate_Y_explicit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2 A).2.1.1 yt =
      (t37H A yt.1 + t37H A zeroVec + t37D A,
       A yt.1 zeroVec + A zeroVec zeroVec + t37G A zeroVec +
         t37H A yt.1 + t37H A zeroVec + t37D A) := by
  rw [t37GaugedRightCoordinateEquiv_Y]
  dsimp only
  let z :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
        ((t37YDual hn hb2 A).2.1 yt)
  have hzK :
      z.1.2 =
        t37H A yt.1 + t37H A zeroVec + t37D A := by
    dsimp only [z]
    rw [t37AxisDualK_eq_totalSum]
    rw [t37YDualTail_eq]
    change
      (∑ wt : PVec n d,
          (A yt.1 wt + A zeroVec wt + t37G A wt)) =
        t37H A yt.1 + t37H A zeroVec + t37D A
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rfl
  have hz0 :
      z.1.1 =
        A yt.1 zeroVec + A zeroVec zeroVec +
          t37G A zeroVec := by
    dsimp only [z]
    rw [t37YDualTail_eq]
    rfl
  change
    (z.1.2, z.1.1 + z.1.2) =
      (t37H A yt.1 + t37H A zeroVec + t37D A,
       A yt.1 zeroVec + A zeroVec zeroVec + t37G A zeroVec +
         t37H A yt.1 + t37H A zeroVec + t37D A)
  rw [hzK, hz0]
  apply Prod.ext
  · rfl
  · abel

theorem t37RightCoordinate_W_explicit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (wt : DiamondEvenAxisTailIndex n d) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2 A).2.2.1.1 wt =
      (t37G A wt.1 + t37G A zeroVec + t37D A,
       A zeroVec wt.1 + A zeroVec zeroVec +
         t37G A wt.1 + t37G A zeroVec +
         t37H A zeroVec + t37D A) := by
  rw [t37GaugedRightCoordinateEquiv_W]
  have hg :
      (t37GDual hn hb2 hd2 A).2.1 wt =
        t37G A wt.1 + t37G A zeroVec + t37D A := by
    change
      (t37YDual hn hb2 A).1.2 wt.1 +
          (t37YDual hn hb2 A).1.2 zeroVec +
          (t37GDual hn hb2 hd2 A).1.2 = _
    rw [t37YDualK_eq_G, t37GDualK_eq_D]
  have hq :
      (t37QDual hn hb2 hd2 A).2.1 wt =
        A zeroVec wt.1 + A zeroVec zeroVec +
          t37G A wt.1 + t37G A zeroVec +
          t37H A zeroVec + t37D A := by
    change
      ((t37YDual hn hb2 A).1.1 wt.1 +
          (t37YDual hn hb2 A).1.2 wt.1) +
        ((t37YDual hn hb2 A).1.1 zeroVec +
          (t37YDual hn hb2 A).1.2 zeroVec) +
        (t37QDual hn hb2 hd2 A).1.2 = _
    rw [t37YDualK_eq_G, t37QDualK_eq_H0_add_D]
    change
      (A zeroVec wt.1 + t37G A wt.1) +
          (A zeroVec zeroVec + t37G A zeroVec) +
          (t37H A zeroVec + t37D A) = _
    abel
  rw [hg, hq]

theorem t37RightCoordinate_mixed_explicit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((t37GaugedRightCoordinateEquiv hn hb2 hd2 A).2.2.2.1 yt).1 wt) =
      A yt.1 wt.1 + A yt.1 zeroVec +
        A zeroVec wt.1 + A zeroVec zeroVec +
        t37H A yt.1 + t37H A zeroVec +
        t37G A wt.1 + t37G A zeroVec + t37D A := by
  rw [t37GaugedRightCoordinateEquiv_mixed]
  dsimp only
  let z :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
        ((t37YDual hn hb2 A).2.1 yt)
  change z.2.1 wt = _
  have hzK :
      z.1.2 =
        t37H A yt.1 + t37H A zeroVec + t37D A := by
    dsimp only [z]
    rw [t37AxisDualK_eq_totalSum]
    rw [t37YDualTail_eq]
    change
      (∑ x : PVec n d,
        (A yt.1 x + A zeroVec x + t37G A x)) =
          t37H A yt.1 + t37H A zeroVec + t37D A
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rfl
  change
    (t37YDual hn hb2 A).2.1 yt wt.1 +
        (t37YDual hn hb2 A).2.1 yt zeroVec + z.1.2 = _
  rw [t37YDualTail_eq]
  rw [hzK]
  dsimp only
  ac_rfl

private theorem t37CastEvenEqZero
    {m : Nat} (hm : Even m) : (m : F) = 0 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  exact F_add_self (q : F)

private theorem t37SumConstEven
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = 0 := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    t37CastEvenEqZero heven, zero_smul]

private noncomputable def t37USrc
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n) :=
  diamondEvenAxisSrcCoordEquiv
    (n := n) (k := d) (CyclicCube n) hn hd2 U

private noncomputable def t37VSrc
    {n b : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b)
    (V : PVec n b → CyclicCube n) :=
  diamondEvenAxisSrcCoordEquiv
    (n := n) (k := b) (CyclicCube n) hn hb2 V

private theorem t37Src_zero_add_sigma_eq_K
    {n k : Nat} [NeZero n]
    (hn : Even n) (hk2 : 2 ≤ k)
    (f : PVec n k → CyclicCube n) :
    f zeroVec +
        (diamondEvenAxisSrcCoordEquiv
          (n := n) (k := k) (CyclicCube n) hn hk2 f).1.1 =
      (diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) (CyclicCube n) hn hk2 f).1.2 := by
  change
    f zeroVec + (∑ s : PVec n k, f s) =
      ∑ t : DiamondEvenAxisTailIndex n k, f t.1
  rw [t37SumAtPointTail (zeroVec : PVec n k) f]
  calc
    f zeroVec +
        (f zeroVec +
          ∑ t : DiamondEvenAxisTailIndex n k, f t.1) =
      (f zeroVec + f zeroVec) +
        ∑ t : DiamondEvenAxisTailIndex n k, f t.1 := by abel
    _ = _ := by
      rw [(add_eq_zero_iff_eq_of_F_module _ _).2 rfl, zero_add]

private theorem t37Constraint_G
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n)
    (wt : PVec n d) :
    t37G (t37RightConstraintMap (U, V)) wt =
      cubeDiffR (t37VSrc hn hb2 V).1.1 := by
  change
    (∑ yt : PVec n b,
      (cubeDiffP (U wt) + cubeDiffR (V yt))) =
        cubeDiffR (∑ yt : PVec n b, V yt)
  rw [Finset.sum_add_distrib,
    t37SumConstEven (even_card_PVec hn hb2),
    ← map_sum, zero_add]

private theorem t37Constraint_H
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n)
    (yt : PVec n b) :
    t37H (t37RightConstraintMap (U, V)) yt =
      cubeDiffP (t37USrc hn hd2 U).1.1 := by
  change
    (∑ wt : PVec n d,
      (cubeDiffP (U wt) + cubeDiffR (V yt))) =
        cubeDiffP (∑ wt : PVec n d, U wt)
  rw [Finset.sum_add_distrib, ← map_sum,
    t37SumConstEven (even_card_PVec hn hd2), add_zero]

private theorem t37Constraint_D
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n) :
    t37D (t37RightConstraintMap (U, V)) = 0 := by
  change
    (∑ wt : PVec n d,
      t37G (t37RightConstraintMap (U, V)) wt) = 0
  simp_rw [t37Constraint_G hn hb2 U V]
  exact
    t37SumConstEven
      (even_card_PVec hn hd2)
      (cubeDiffR (t37VSrc hn hb2 V).1.1)

private theorem t37AxisSrc_at_point
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Even n) (hk2 : 2 ≤ k)
    (f : PVec n k → V) :
    f zeroVec =
      (diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) V hn hk2 f).1.1 +
      (diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) V hn hk2 f).1.2 := by
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := k) V hn hk2
  have h := congrFun (E.symm_apply_apply f) (zeroVec : PVec n k)
  change
    pointedSrcEvenValueBuild
        (PVec n k) V zeroVec (E f) zeroVec =
      f zeroVec at h
  rw [pointedSrcEvenValueBuild_at_point] at h
  exact h.symm

private theorem t37AxisSrc_at_tail
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Even n) (hk2 : 2 ≤ k)
    (f : PVec n k → V)
    (t : DiamondEvenAxisTailIndex n k) :
    f t.1 =
      (diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) V hn hk2 f).2.1 t +
      (diamondEvenAxisSrcCoordEquiv
        (n := n) (k := k) V hn hk2 f).1.2 := by
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := k) V hn hk2
  have h := congrFun (E.symm_apply_apply f) t.1
  change
    pointedSrcEvenValueBuild
        (PVec n k) V zeroVec (E f) t.1 =
      f t.1 at h
  rw [pointedSrcEvenValueBuild_at_tail] at h
  exact h.symm

theorem t37SeparableCoordinateIdentity
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n) :
    let u := t37USrc hn hd2 U
    let v := t37VSrc hn hb2 V
    let q :=
      t37GaugedRightCoordinateEquiv hn hb2 hd2
        (t37RightConstraintMap (U, V))
    q.1 =
        ((0, cubeDiffR v.1.1),
          (cubeDiffP u.1.1,
            cubeDiffP u.1.2 + cubeDiffR v.1.2)) ∧
      (∀ yt : DiamondEvenAxisTailIndex n b,
        q.2.1.1 yt = (0, cubeDiffR (v.2.1 yt))) ∧
      (∀ wt : DiamondEvenAxisTailIndex n d,
        q.2.2.1.1 wt = (0, cubeDiffP (u.2.1 wt))) ∧
      (∀ yt : DiamondEvenAxisTailIndex n b,
        ∀ wt : DiamondEvenAxisTailIndex n d,
          (q.2.2.2.1 yt).1 wt = 0) := by
  dsimp only
  let u := t37USrc hn hd2 U
  let v := t37VSrc hn hb2 V
  have hG (wt : PVec n d) :
      t37G (t37RightConstraintMap (U, V)) wt =
        cubeDiffR v.1.1 := by
    exact t37Constraint_G hn hb2 U V wt
  have hH (yt : PVec n b) :
      t37H (t37RightConstraintMap (U, V)) yt =
        cubeDiffP u.1.1 := by
    exact t37Constraint_H hn hd2 U V yt
  have hD :
      t37D (t37RightConstraintMap (U, V)) = 0 :=
    t37Constraint_D hn hb2 hd2 U V
  have hU0 : U zeroVec = u.1.1 + u.1.2 :=
    t37AxisSrc_at_point (CyclicCube n) hn hd2 U
  have hV0 : V zeroVec = v.1.1 + v.1.2 :=
    t37AxisSrc_at_point (CyclicCube n) hn hb2 V
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [t37RightCoordinate_scalar_explicit]
    simp_rw [hG, hH, hD, add_zero]
    change
      ((0, cubeDiffR v.1.1),
        (cubeDiffP u.1.1,
          (cubeDiffP (U zeroVec) + cubeDiffR (V zeroVec)) +
            cubeDiffR v.1.1 + cubeDiffP u.1.1)) = _
    rw [hU0, hV0, map_add, map_add]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext i j k
        change
          _ =
            cubeDiffP u.1.2 i j k +
              cubeDiffR v.1.2 i j k
        simp only [Pi.add_apply]
        ring_nf
        simp [show (2 : F) = 0 by decide]
  · intro yt
    rw [t37RightCoordinate_Y_explicit]
    simp_rw [hG, hH, hD, add_zero]
    change
      (cubeDiffP u.1.1 + cubeDiffP u.1.1,
        (cubeDiffP (U zeroVec) + cubeDiffR (V yt.1)) +
          (cubeDiffP (U zeroVec) + cubeDiffR (V zeroVec)) +
          cubeDiffR v.1.1 +
          cubeDiffP u.1.1 + cubeDiffP u.1.1) =
        (0, cubeDiffR (v.2.1 yt))
    have hVyt : V yt.1 = v.2.1 yt + v.1.2 :=
      t37AxisSrc_at_tail (CyclicCube n) hn hb2 V yt
    rw [hV0, hVyt, map_add, map_add]
    apply Prod.ext
    · exact (add_eq_zero_iff_eq_of_F_module _ _).2 rfl
    · funext i j k
      simp only [Pi.add_apply]
      ring_nf
      simp [show (2 : F) = 0 by decide]
  · intro wt
    rw [t37RightCoordinate_W_explicit]
    simp_rw [hG, hH, hD, add_zero]
    change
      (cubeDiffR v.1.1 + cubeDiffR v.1.1,
        (cubeDiffP (U wt.1) + cubeDiffR (V zeroVec)) +
          (cubeDiffP (U zeroVec) + cubeDiffR (V zeroVec)) +
          cubeDiffR v.1.1 + cubeDiffR v.1.1 +
          cubeDiffP u.1.1) =
        (0, cubeDiffP (u.2.1 wt))
    have hUwt : U wt.1 = u.2.1 wt + u.1.2 :=
      t37AxisSrc_at_tail (CyclicCube n) hn hd2 U wt
    rw [hU0, hV0, hUwt, map_add, map_add]
    apply Prod.ext
    · exact (add_eq_zero_iff_eq_of_F_module _ _).2 rfl
    · funext i j k
      simp only [Pi.add_apply]
      ring_nf
      simp [show (2 : F) = 0 by decide,
        show (4 : F) = 0 by decide]
      ring_nf
      simp [show (2 : F) = 0 by decide]
  · intro yt wt
    rw [t37RightCoordinate_mixed_explicit]
    simp_rw [hG, hH, hD, add_zero]
    change
      (cubeDiffP (U wt.1) + cubeDiffR (V yt.1)) +
        (cubeDiffP (U zeroVec) + cubeDiffR (V yt.1)) +
        (cubeDiffP (U wt.1) + cubeDiffR (V zeroVec)) +
        (cubeDiffP (U zeroVec) + cubeDiffR (V zeroVec)) +
        cubeDiffP u.1.1 + cubeDiffP u.1.1 +
        cubeDiffR v.1.1 + cubeDiffR v.1.1 = 0
    funext i j k
    simp only [Pi.add_apply]
    ring_nf
    simp [show (2 : F) = 0 by decide]

theorem t37ConstraintCoordinate_scalar
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2
      (t37RightConstraintMap (U, V))).1 =
      ((0, cubeDiffR (t37VSrc hn hb2 V).1.1),
       (cubeDiffP (t37USrc hn hd2 U).1.1,
        cubeDiffP (t37USrc hn hd2 U).1.2 +
          cubeDiffR (t37VSrc hn hb2 V).1.2)) := by
  exact (t37SeparableCoordinateIdentity hn hb2 hd2 U V).1

theorem t37ConstraintCoordinate_Y
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2
      (t37RightConstraintMap (U, V))).2.1.1 yt =
      (0, cubeDiffR ((t37VSrc hn hb2 V).2.1 yt)) := by
  exact (t37SeparableCoordinateIdentity hn hb2 hd2 U V).2.1 yt

theorem t37ConstraintCoordinate_W
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n)
    (wt : DiamondEvenAxisTailIndex n d) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2
      (t37RightConstraintMap (U, V))).2.2.1.1 wt =
      (0, cubeDiffP ((t37USrc hn hd2 U).2.1 wt)) := by
  exact (t37SeparableCoordinateIdentity hn hb2 hd2 U V).2.2.1 wt

theorem t37ConstraintCoordinate_mixed
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (U : PVec n d → CyclicCube n)
    (V : PVec n b → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((t37GaugedRightCoordinateEquiv hn hb2 hd2
      (t37RightConstraintMap (U, V))).2.2.2.1 yt).1 wt) = 0 := by
  exact (t37SeparableCoordinateIdentity hn hb2 hd2 U V).2.2.2 yt wt

def T37RawRightCoordinateLedger
    {n b d : Nat} [NeZero n]
    (q : T37RightAmbientTarget n b d) : Prop :=
  q.1.1.1 = 0 ∧
    q.1.1.2 ∈ LinearMap.range (cubeDiffR (n := n)) ∧
    q.1.2.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
    q.1.2.2 ∈
      LinearMap.range
        (LinearMap.coprod
          (cubeDiffP (n := n)) (cubeDiffR (n := n))) ∧
    (∀ yt : DiamondEvenAxisTailIndex n b,
      (q.2.1.1 yt).1 = 0 ∧
        (q.2.1.1 yt).2 ∈
          LinearMap.range (cubeDiffR (n := n))) ∧
    (∀ wt : DiamondEvenAxisTailIndex n d,
      (q.2.2.1.1 wt).1 = 0 ∧
        (q.2.2.1.1 wt).2 ∈
          LinearMap.range (cubeDiffP (n := n))) ∧
    (∀ yt : DiamondEvenAxisTailIndex n b,
      ∀ wt : DiamondEvenAxisTailIndex n d,
        (q.2.2.2.1 yt).1 wt = 0)

private theorem t37SumDeltaZero
    {S V : Type*} [Fintype S] [DecidableEq S]
    [AddCommMonoid V] (s0 : S) (v : V) :
    (∑ s : S, if s = s0 then v else 0) = v := by
  rw [Finset.sum_eq_single s0]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

theorem t37GaugedRange_iff_rawCoordinateLedger
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (g : PVec n b → PVec n d → CyclicCube n) :
    g ∈ LinearMap.range
        (t37RightConstraintMap (n := n) (b := b) (d := d)) ↔
      T37RawRightCoordinateLedger
        (t37GaugedRightCoordinateEquiv hn hb2 hd2 g) := by
  classical
  let E :=
    t37GaugedRightCoordinateEquiv
      (n := n) (b := b) (d := d) hn hb2 hd2
  constructor
  · rintro ⟨uv, rfl⟩
    let u := t37USrc hn hd2 uv.1
    let v := t37VSrc hn hb2 uv.2
    have hcoord :=
      t37SeparableCoordinateIdentity hn hb2 hd2 uv.1 uv.2
    dsimp only [T37RawRightCoordinateLedger]
    rw [hcoord.1]
    refine
      ⟨rfl,
       ⟨v.1.1, rfl⟩,
       ⟨u.1.1, rfl⟩,
       ⟨(u.1.2, v.1.2), rfl⟩,
       ?_, ?_, ?_⟩
    · intro yt
      rw [hcoord.2.1 yt]
      exact ⟨rfl, ⟨v.2.1 yt, rfl⟩⟩
    · intro wt
      rw [hcoord.2.2.1 wt]
      exact ⟨rfl, ⟨u.2.1 wt, rfl⟩⟩
    · intro yt wt
      exact hcoord.2.2.2 yt wt
  · intro hledger
    let q := E g
    change T37RawRightCoordinateLedger q at hledger
    rcases hledger with
      ⟨hq00, ⟨vSigma, hvSigma⟩, ⟨uSigma, huSigma⟩,
       ⟨uvK, huvK⟩, hY, hW, hM⟩
    choose vTail hvTail using fun yt => (hY yt).2
    choose uTail huTail using fun wt => (hW wt).2
    let vCorr : CyclicCube n := ∑ yt, vTail yt
    let uCorr : CyclicCube n := ∑ wt, uTail wt
    have hRvCorr : cubeDiffR vCorr = 0 := by
      calc
        cubeDiffR vCorr =
            ∑ yt : DiamondEvenAxisTailIndex n b,
              cubeDiffR (vTail yt) := by rw [map_sum]
        _ = ∑ yt : DiamondEvenAxisTailIndex n b,
              (q.2.1.1 yt).2 := by
            apply Finset.sum_congr rfl
            intro yt _
            exact hvTail yt
        _ = 0 := by
          have hsum := pointedValueTailZero_sum q.2.1
          simpa only [Prod.snd_sum] using congrArg Prod.snd hsum
    have hPuCorr : cubeDiffP uCorr = 0 := by
      calc
        cubeDiffP uCorr =
            ∑ wt : DiamondEvenAxisTailIndex n d,
              cubeDiffP (uTail wt) := by rw [map_sum]
        _ = ∑ wt : DiamondEvenAxisTailIndex n d,
              (q.2.2.1.1 wt).2 := by
            apply Finset.sum_congr rfl
            intro wt _
            exact huTail wt
        _ = 0 := by
          have hsum := pointedValueTailZero_sum q.2.2.1
          simpa only [Prod.snd_sum] using congrArg Prod.snd hsum
    rcases diamondEvenAxisTailIndex_nonempty hn hb2 with ⟨yt0⟩
    rcases diamondEvenAxisTailIndex_nonempty hn hd2 with ⟨wt0⟩
    let vTailCorrected :
        DiamondEvenAxisTailIndex n b → CyclicCube n :=
      fun yt => if yt = yt0 then vTail yt + vCorr else vTail yt
    let uTailCorrected :
        DiamondEvenAxisTailIndex n d → CyclicCube n :=
      fun wt => if wt = wt0 then uTail wt + uCorr else uTail wt
    have hvTailSum : (∑ yt, vTailCorrected yt) = 0 := by
      have hdelta :
          (∑ yt : DiamondEvenAxisTailIndex n b,
            if yt = yt0 then vCorr else 0) = vCorr :=
        t37SumDeltaZero yt0 vCorr
      have hpoint :
          vTailCorrected =
            fun yt => vTail yt + if yt = yt0 then vCorr else 0 := by
        funext yt
        by_cases hyt : yt = yt0 <;> simp [vTailCorrected, hyt]
      rw [hpoint, Finset.sum_add_distrib, hdelta]
      exact (add_eq_zero_iff_eq_of_F_module vCorr vCorr).2 rfl
    have huTailSum : (∑ wt, uTailCorrected wt) = 0 := by
      have hdelta :
          (∑ wt : DiamondEvenAxisTailIndex n d,
            if wt = wt0 then uCorr else 0) = uCorr :=
        t37SumDeltaZero wt0 uCorr
      have hpoint :
          uTailCorrected =
            fun wt => uTail wt + if wt = wt0 then uCorr else 0 := by
        funext wt
        by_cases hwt : wt = wt0 <;> simp [uTailCorrected, hwt]
      rw [hpoint, Finset.sum_add_distrib, hdelta]
      exact (add_eq_zero_iff_eq_of_F_module uCorr uCorr).2 rfl
    have hvTailCorrected (yt : DiamondEvenAxisTailIndex n b) :
        cubeDiffR (vTailCorrected yt) = (q.2.1.1 yt).2 := by
      by_cases hyt : yt = yt0
      · subst yt
        simp only [vTailCorrected, if_pos, map_add, hRvCorr, add_zero]
        exact hvTail yt0
      · simp only [vTailCorrected, hyt]
        exact hvTail yt
    have huTailCorrected (wt : DiamondEvenAxisTailIndex n d) :
        cubeDiffP (uTailCorrected wt) = (q.2.2.1.1 wt).2 := by
      by_cases hwt : wt = wt0
      · subst wt
        simp only [uTailCorrected, if_pos, map_add, hPuCorr, add_zero]
        exact huTail wt0
      · simp only [uTailCorrected, hwt]
        exact huTail wt
    let vCoords :
        PointedEvenValueCoords
          (PVec n b) (CyclicCube n) zeroVec :=
      ((vSigma, uvK.2),
        ⟨vTailCorrected, LinearMap.mem_ker.mpr hvTailSum⟩)
    let uCoords :
        PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec :=
      ((uSigma, uvK.1),
        ⟨uTailCorrected, LinearMap.mem_ker.mpr huTailSum⟩)
    let U := (diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2).symm uCoords
    let V := (diamondEvenAxisSrcCoordEquiv
      (n := n) (k := b) (CyclicCube n) hn hb2).symm vCoords
    refine ⟨(U, V), ?_⟩
    apply E.injective
    have huRead :
        t37USrc hn hd2 U = uCoords := by
      exact
        (diamondEvenAxisSrcCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2).apply_symm_apply
            uCoords
    have hvRead :
        t37VSrc hn hb2 V = vCoords := by
      exact
        (diamondEvenAxisSrcCoordEquiv
          (n := n) (k := b) (CyclicCube n) hn hb2).apply_symm_apply
            vCoords
    have hcoord := t37SeparableCoordinateIdentity hn hb2 hd2 U V
    apply Prod.ext
    · rw [hcoord.1]
      apply Prod.ext
      · apply Prod.ext
        · exact hq00.symm
        · simpa only [hvRead, vCoords] using hvSigma
      · apply Prod.ext
        · simpa only [huRead, uCoords] using huSigma
        · simpa only [huRead, hvRead, uCoords, vCoords] using huvK
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        rw [hcoord.2.1 yt]
        apply Prod.ext
        · exact (hY yt).1.symm
        · simpa only [hvRead, vCoords] using
            hvTailCorrected yt
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          rw [hcoord.2.2.1 wt]
          apply Prod.ext
          · exact (hW wt).1.symm
          · simpa only [huRead, uCoords] using
              huTailCorrected wt
        · apply Subtype.ext
          funext yt
          apply Subtype.ext
          funext wt
          rw [hcoord.2.2.2 yt wt]
          exact (hM yt wt).symm

private theorem t37G_map_J
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n)
    (wt : PVec n d) :
    t37G (fun yt wt => cubeDiffJInv (A yt wt)) wt =
      cubeDiffJInv (t37G A wt) := by
  change
    (∑ yt : PVec n b, cubeDiffJInv (A yt wt)) =
      cubeDiffJInv (∑ yt : PVec n b, A yt wt)
  rw [map_sum]

private theorem t37H_map_J
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : PVec n b) :
    t37H (fun yt wt => cubeDiffJInv (A yt wt)) yt =
      cubeDiffJInv (t37H A yt) := by
  change
    (∑ wt : PVec n d, cubeDiffJInv (A yt wt)) =
      cubeDiffJInv (∑ wt : PVec n d, A yt wt)
  rw [map_sum]

private theorem t37D_map_J
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n) :
    t37D (fun yt wt => cubeDiffJInv (A yt wt)) =
      cubeDiffJInv (t37D A) := by
  change
    (∑ wt : PVec n d,
      t37G (fun yt wt => cubeDiffJInv (A yt wt)) wt) =
      cubeDiffJInv (∑ wt : PVec n d, t37G A wt)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro wt _
  exact t37G_map_J A wt

theorem t37RightCoordinate_J_scalar
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2
      (fun yt wt => cubeDiffJInv (A yt wt))).1 =
      let q := t37GaugedRightCoordinateEquiv hn hb2 hd2 A
      ((cubeDiffJInv q.1.1.1, cubeDiffJInv q.1.1.2),
       (cubeDiffJInv q.1.2.1, cubeDiffJInv q.1.2.2)) := by
  dsimp only
  rw [t37RightCoordinate_scalar_explicit,
    t37RightCoordinate_scalar_explicit]
  simp_rw [t37G_map_J, t37H_map_J, t37D_map_J, map_add]

theorem t37RightCoordinate_J_Y
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2
      (fun yt wt => cubeDiffJInv (A yt wt))).2.1.1 yt =
      let q := t37GaugedRightCoordinateEquiv hn hb2 hd2 A
      (cubeDiffJInv (q.2.1.1 yt).1,
        cubeDiffJInv (q.2.1.1 yt).2) := by
  dsimp only
  rw [t37RightCoordinate_Y_explicit,
    t37RightCoordinate_Y_explicit]
  simp_rw [t37G_map_J, t37H_map_J, t37D_map_J, map_add]

theorem t37RightCoordinate_J_W
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (wt : DiamondEvenAxisTailIndex n d) :
    (t37GaugedRightCoordinateEquiv hn hb2 hd2
      (fun yt wt => cubeDiffJInv (A yt wt))).2.2.1.1 wt =
      let q := t37GaugedRightCoordinateEquiv hn hb2 hd2 A
      (cubeDiffJInv (q.2.2.1.1 wt).1,
        cubeDiffJInv (q.2.2.1.1 wt).2) := by
  dsimp only
  rw [t37RightCoordinate_W_explicit,
    t37RightCoordinate_W_explicit]
  simp_rw [t37G_map_J, t37H_map_J, t37D_map_J, map_add]

theorem t37RightCoordinate_J_mixed
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((t37GaugedRightCoordinateEquiv hn hb2 hd2
      (fun yt wt => cubeDiffJInv (A yt wt))).2.2.2.1 yt).1 wt) =
      cubeDiffJInv
        (((t37GaugedRightCoordinateEquiv hn hb2 hd2 A).2.2.2.1 yt).1 wt) := by
  rw [t37RightCoordinate_mixed_explicit,
    t37RightCoordinate_mixed_explicit]
  simp_rw [t37G_map_J, t37H_map_J, t37D_map_J, map_add]

noncomputable abbrev T37JKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (cubeDiffJInv (n := n))

def T37RightCoordinateLedger
    {n b d : Nat} [NeZero n]
    (q : T37RightAmbientTarget n b d) : Prop :=
  q.1 ∈ DiamondEEOERightSource n ∧
    (∀ yt : DiamondEvenAxisTailIndex n b,
      (q.2.1.1 yt).1 ∈ T37JKernel n ∧
        (q.2.1.1 yt).2 ∈ EEOEInternal.RReachRight n) ∧
    (∀ wt : DiamondEvenAxisTailIndex n d,
      (q.2.2.1.1 wt).1 ∈ T37JKernel n ∧
        (q.2.2.1.1 wt).2 ∈ EEOEInternal.PReachRight n) ∧
    (∀ yt : DiamondEvenAxisTailIndex n b,
      ∀ wt : DiamondEvenAxisTailIndex n d,
        (q.2.2.2.1 yt).1 wt ∈ T37JKernel n)

theorem t37RawLedger_J_iff_coordinateLedger
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :
    T37RawRightCoordinateLedger
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))) ↔
      T37RightCoordinateLedger
        (t37GaugedRightCoordinateEquiv hn hb2 hd2 A) := by
  let q := t37GaugedRightCoordinateEquiv hn hb2 hd2 A
  constructor
  · rintro ⟨h00, h01, h10, h11, hY, hW, hM⟩
    have hJs := t37RightCoordinate_J_scalar hn hb2 hd2 A
    have hJs00 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.1.1 =
            cubeDiffJInv q.1.1.1 := by
      simpa only using congrArg (fun z => z.1.1) hJs
    have hJs01 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.1.2 =
            cubeDiffJInv q.1.1.2 := by
      simpa only using congrArg (fun z => z.1.2) hJs
    have hJs10 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.2.1 =
            cubeDiffJInv q.1.2.1 := by
      simpa only using congrArg (fun z => z.2.1) hJs
    have hJs11 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.2.2 =
            cubeDiffJInv q.1.2.2 := by
      simpa only using congrArg (fun z => z.2.2) hJs
    refine ⟨?_, ?_, ?_, ?_⟩
    · change
        cubeDiffJInv q.1.1.1 = 0 ∧
          cubeDiffJInv q.1.1.2 ∈
            LinearMap.range (cubeDiffR (n := n)) ∧
          cubeDiffJInv q.1.2.1 ∈
            LinearMap.range (cubeDiffP (n := n)) ∧
          cubeDiffJInv q.1.2.2 ∈
            LinearMap.range
              (LinearMap.coprod
                (cubeDiffP (n := n)) (cubeDiffR (n := n)))
      refine ⟨hJs00.symm.trans h00, ?_, ?_, ?_⟩
      · rw [← hJs01]
        exact h01
      · rw [← hJs10]
        exact h10
      · rw [← hJs11]
        exact h11
    · intro yt
      have hJy := t37RightCoordinate_J_Y hn hb2 hd2 A yt
      have hJy0 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.1.1 yt).1 =
              cubeDiffJInv (q.2.1.1 yt).1 := by
        simpa only using congrArg Prod.fst hJy
      have hJy1 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.1.1 yt).2 =
              cubeDiffJInv (q.2.1.1 yt).2 := by
        simpa only using congrArg Prod.snd hJy
      change
        cubeDiffJInv (q.2.1.1 yt).1 = 0 ∧
          cubeDiffJInv (q.2.1.1 yt).2 ∈
            LinearMap.range (cubeDiffR (n := n))
      refine ⟨hJy0.symm.trans (hY yt).1, ?_⟩
      rw [← hJy1]
      exact (hY yt).2
    · intro wt
      have hJw := t37RightCoordinate_J_W hn hb2 hd2 A wt
      have hJw0 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.2.1.1 wt).1 =
              cubeDiffJInv (q.2.2.1.1 wt).1 := by
        simpa only using congrArg Prod.fst hJw
      have hJw1 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.2.1.1 wt).2 =
              cubeDiffJInv (q.2.2.1.1 wt).2 := by
        simpa only using congrArg Prod.snd hJw
      change
        cubeDiffJInv (q.2.2.1.1 wt).1 = 0 ∧
          cubeDiffJInv (q.2.2.1.1 wt).2 ∈
            LinearMap.range (cubeDiffP (n := n))
      refine ⟨hJw0.symm.trans (hW wt).1, ?_⟩
      rw [← hJw1]
      exact (hW wt).2
    · intro yt wt
      change
        cubeDiffJInv ((q.2.2.2.1 yt).1 wt) = 0
      rw [← t37RightCoordinate_J_mixed hn hb2 hd2 A yt wt]
      exact hM yt wt
  · rintro ⟨hs, hY, hW, hM⟩
    have hJs := t37RightCoordinate_J_scalar hn hb2 hd2 A
    have hJs00 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.1.1 =
            cubeDiffJInv q.1.1.1 := by
      simpa only using congrArg (fun z => z.1.1) hJs
    have hJs01 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.1.2 =
            cubeDiffJInv q.1.1.2 := by
      simpa only using congrArg (fun z => z.1.2) hJs
    have hJs10 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.2.1 =
            cubeDiffJInv q.1.2.1 := by
      simpa only using congrArg (fun z => z.2.1) hJs
    have hJs11 :
        (t37GaugedRightCoordinateEquiv hn hb2 hd2
          (fun yt wt => cubeDiffJInv (A yt wt))).1.2.2 =
            cubeDiffJInv q.1.2.2 := by
      simpa only using congrArg (fun z => z.2.2) hJs
    change
      cubeDiffJInv q.1.1.1 = 0 ∧
        cubeDiffJInv q.1.1.2 ∈
          LinearMap.range (cubeDiffR (n := n)) ∧
        cubeDiffJInv q.1.2.1 ∈
          LinearMap.range (cubeDiffP (n := n)) ∧
        cubeDiffJInv q.1.2.2 ∈
          LinearMap.range
            (LinearMap.coprod
              (cubeDiffP (n := n)) (cubeDiffR (n := n))) at hs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hJs00.trans hs.1
    · rw [hJs01]
      exact hs.2.1
    · rw [hJs10]
      exact hs.2.2.1
    · rw [hJs11]
      exact hs.2.2.2
    · intro yt
      have hy := hY yt
      have hJy := t37RightCoordinate_J_Y hn hb2 hd2 A yt
      have hJy0 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.1.1 yt).1 =
              cubeDiffJInv (q.2.1.1 yt).1 := by
        simpa only using congrArg Prod.fst hJy
      have hJy1 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.1.1 yt).2 =
              cubeDiffJInv (q.2.1.1 yt).2 := by
        simpa only using congrArg Prod.snd hJy
      change
        cubeDiffJInv (q.2.1.1 yt).1 = 0 ∧
          cubeDiffJInv (q.2.1.1 yt).2 ∈
            LinearMap.range (cubeDiffR (n := n)) at hy
      refine ⟨hJy0.trans hy.1, ?_⟩
      rw [hJy1]
      exact hy.2
    · intro wt
      have hw := hW wt
      have hJw := t37RightCoordinate_J_W hn hb2 hd2 A wt
      have hJw0 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.2.1.1 wt).1 =
              cubeDiffJInv (q.2.2.1.1 wt).1 := by
        simpa only using congrArg Prod.fst hJw
      have hJw1 :
          ((t37GaugedRightCoordinateEquiv hn hb2 hd2
            (fun yt wt => cubeDiffJInv (A yt wt))).2.2.1.1 wt).2 =
              cubeDiffJInv (q.2.2.1.1 wt).2 := by
        simpa only using congrArg Prod.snd hJw
      change
        cubeDiffJInv (q.2.2.1.1 wt).1 = 0 ∧
          cubeDiffJInv (q.2.2.1.1 wt).2 ∈
            LinearMap.range (cubeDiffP (n := n)) at hw
      refine ⟨hJw0.trans hw.1, ?_⟩
      rw [hJw1]
      exact hw.2
    · intro yt wt
      have hm := hM yt wt
      change cubeDiffJInv ((q.2.2.2.1 yt).1 wt) = 0 at hm
      rw [t37RightCoordinate_J_mixed hn hb2 hd2 A yt wt]
      exact hm

theorem t37LiteralRight_mem_iff_coordinateLedger
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : AFun4 n b 1 d) :
    A ∈ DiamondEvenPReachableA n b 1 d ↔
      T37RightCoordinateLedger
        (t37RightAmbientEquiv hn hb2 hd2 A) := by
  rw [literal_reachable_iff_gauged_range hb2 hd2 A]
  rw [t37GaugedRange_iff_rawCoordinateLedger hn hb2 hd2]
  have hJ :=
    t37RawLedger_J_iff_coordinateLedger hn hb2 hd2
      (aLiteralGaugeEquiv
        (n := n) (b := b) (d := d)
        (by omega : 0 < b) (by omega : 0 < d) A)
  simpa only [t37RightAmbientEquiv, LinearEquiv.trans_apply] using hJ

noncomputable abbrev T37RightReachableTarget
    (n b d : Nat) [NeZero n] :=
  DiamondEEOERightSource n ×
    (DiamondEvenAxisValueTailZero n b
        (T37JKernel n × EEOEInternal.RReachRight n) ×
      (DiamondEvenAxisValueTailZero n d
          (T37JKernel n × EEOEInternal.PReachRight n) ×
        DiamondMixedTailZero n b d (T37JKernel n)))

private noncomputable def t37TailPairPack
    {n k : Nat} [NeZero n]
    (S T : Submodule F (CyclicCube n))
    (u : DiamondEvenAxisValueTailZero n k
      (CyclicCube n × CyclicCube n))
    (huS : ∀ t, (u.1 t).1 ∈ S)
    (huT : ∀ t, (u.1 t).2 ∈ T) :
    DiamondEvenAxisValueTailZero n k (S × T) :=
  ⟨fun t => (⟨(u.1 t).1, huS t⟩, ⟨(u.1 t).2, huT t⟩), by
    apply LinearMap.mem_ker.mpr
    change
      (∑ t,
        ((⟨(u.1 t).1, huS t⟩, ⟨(u.1 t).2, huT t⟩) :
          S × T)) = 0
    have hsum := pointedValueTailZero_sum u
    apply Prod.ext
    · rw [Prod.fst_sum]
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Prod.fst_sum] using
        congrArg Prod.fst hsum
    · rw [Prod.snd_sum]
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Prod.snd_sum] using
        congrArg Prod.snd hsum⟩

private noncomputable def t37TailPairForget
    {n k : Nat} [NeZero n]
    (S T : Submodule F (CyclicCube n)) :
    DiamondEvenAxisValueTailZero n k (S × T) →ₗ[F]
      DiamondEvenAxisValueTailZero n k
        (CyclicCube n × CyclicCube n) where
  toFun u :=
    ⟨fun t => ((u.1 t).1.1, (u.1 t).2.1), by
      apply LinearMap.mem_ker.mpr
      have hsum := pointedValueTailZero_sum u
      change
        (∑ t, (((u.1 t).1.1, (u.1 t).2.1) :
          CyclicCube n × CyclicCube n)) = 0
      apply Prod.ext
      · have hfst := congrArg Prod.fst hsum
        simpa only [Prod.fst_sum, Submodule.coe_sum] using
          congrArg Subtype.val hfst
      · have hsnd := congrArg Prod.snd hsum
        simpa only [Prod.snd_sum, Submodule.coe_sum] using
          congrArg Subtype.val hsnd⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

private noncomputable def t37MixedPack
    {n b d : Nat} [NeZero n]
    (S : Submodule F (CyclicCube n))
    (u : DiamondMixedTailZero n b d (CyclicCube n))
    (huS : ∀ yt wt, (u.1 yt).1 wt ∈ S) :
    DiamondMixedTailZero n b d S :=
  ⟨fun yt =>
      ⟨fun wt => ⟨(u.1 yt).1 wt, huS yt wt⟩, by
        apply LinearMap.mem_ker.mpr
        change
          (∑ wt, (⟨(u.1 yt).1 wt, huS yt wt⟩ : S)) = 0
        apply Subtype.ext
        simpa only [Submodule.coe_sum] using
          pointedValueTailZero_sum (u.1 yt)⟩,
    by
      apply LinearMap.mem_ker.mpr
      change
        (∑ yt,
          (⟨fun wt => ⟨(u.1 yt).1 wt, huS yt wt⟩, by
              apply LinearMap.mem_ker.mpr
              change
                (∑ wt,
                  (⟨(u.1 yt).1 wt, huS yt wt⟩ : S)) = 0
              apply Subtype.ext
              simpa only [Submodule.coe_sum] using
                pointedValueTailZero_sum (u.1 yt)⟩ :
            DiamondEvenAxisValueTailZero n d S)) = 0
      apply Subtype.ext
      funext wt
      apply Subtype.ext
      have hsum := pointedValueTailZero_sum u
      have hsumAt :=
        congrArg
          (fun z :
            DiamondEvenAxisValueTailZero n d (CyclicCube n) =>
              z.1 wt) hsum
      simpa only [Submodule.coe_sum, Finset.sum_apply, Pi.zero_apply] using
        hsumAt⟩

private noncomputable def t37MixedForget
    {n b d : Nat} [NeZero n]
    (S : Submodule F (CyclicCube n)) :
    DiamondMixedTailZero n b d S →ₗ[F]
      DiamondMixedTailZero n b d (CyclicCube n) where
  toFun u := by
    let v :
        DiamondEvenAxisTailIndex n b →
          DiamondEvenAxisValueTailZero n d (CyclicCube n) :=
      fun yt =>
        ⟨fun wt => ((u.1 yt).1 wt).1, by
          apply LinearMap.mem_ker.mpr
          have hsum := pointedValueTailZero_sum (u.1 yt)
          simpa only [Submodule.coe_sum] using
            congrArg Subtype.val hsum⟩
    refine ⟨v, ?_⟩
    apply LinearMap.mem_ker.mpr
    change (∑ yt, v yt) = 0
    apply Subtype.ext
    funext wt
    have hsum := pointedValueTailZero_sum u
    have hsumAt :=
      congrArg
        (fun z : DiamondEvenAxisValueTailZero n d S =>
          (z.1 wt).1) hsum
    simpa only [v, Submodule.coe_sum, Finset.sum_apply, Pi.zero_apply] using
      hsumAt
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

noncomputable def t37RightReachableEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b 1 d ≃ₗ[F]
      T37RightReachableTarget n b d where
  toFun A := by
    let q := t37RightAmbientEquiv hn hb2 hd2 A.1
    have hq :=
      (t37LiteralRight_mem_iff_coordinateLedger
        hn hb2 hd2 A.1).mp A.2
    exact
      (⟨q.1, hq.1⟩,
        (t37TailPairPack
            (T37JKernel n) (EEOEInternal.RReachRight n)
            q.2.1 (fun yt => (hq.2.1 yt).1)
            (fun yt => (hq.2.1 yt).2),
          (t37TailPairPack
              (T37JKernel n) (EEOEInternal.PReachRight n)
              q.2.2.1 (fun wt => (hq.2.2.1 wt).1)
              (fun wt => (hq.2.2.1 wt).2),
            t37MixedPack
              (T37JKernel n) q.2.2.2 hq.2.2.2)))
  invFun q := by
    let raw : T37RightAmbientTarget n b d :=
      (q.1.1,
        (t37TailPairForget
            (T37JKernel n) (EEOEInternal.RReachRight n) q.2.1,
          (t37TailPairForget
              (T37JKernel n) (EEOEInternal.PReachRight n) q.2.2.1,
            t37MixedForget (T37JKernel n) q.2.2.2)))
    let A := (t37RightAmbientEquiv hn hb2 hd2).symm raw
    refine
      ⟨A,
        (t37LiteralRight_mem_iff_coordinateLedger
          hn hb2 hd2 A).mpr ?_⟩
    have hread :
        t37RightAmbientEquiv hn hb2 hd2 A = raw :=
      (t37RightAmbientEquiv hn hb2 hd2).apply_symm_apply raw
    rw [hread]
    refine ⟨q.1.2, ?_, ?_, ?_⟩
    · intro yt
      exact ⟨(q.2.1.1 yt).1.2, (q.2.1.1 yt).2.2⟩
    · intro wt
      exact ⟨(q.2.2.1.1 wt).1.2, (q.2.2.1.1 wt).2.2⟩
    · intro yt wt
      exact ((q.2.2.2.1 yt).1 wt).2
  left_inv A := by
    apply Subtype.ext
    exact (t37RightAmbientEquiv hn hb2 hd2).symm_apply_apply A.1
  right_inv q := by
    have hread :=
      (t37RightAmbientEquiv hn hb2 hd2).apply_symm_apply
        (q.1.1,
          (t37TailPairForget
              (T37JKernel n) (EEOEInternal.RReachRight n) q.2.1,
            (t37TailPairForget
                (T37JKernel n) (EEOEInternal.PReachRight n) q.2.2.1,
              t37MixedForget (T37JKernel n) q.2.2.2)))
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 yt).1) hread
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 yt).2) hread
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun z => (z.2.2.1.1 wt).1) hread
          · apply Subtype.ext
            exact congrArg (fun z => (z.2.2.1.1 wt).2) hread
        · apply Subtype.ext
          funext yt
          apply Subtype.ext
          funext wt
          apply Subtype.ext
          exact
            congrArg
              (fun z => (z.2.2.2.1 yt).1 wt)
              hread
  map_add' A A' := by
    have hmap :=
      (t37RightAmbientEquiv hn hb2 hd2).map_add A.1 A'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 yt).1) hmap
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 yt).2) hmap
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun z => (z.2.2.1.1 wt).1) hmap
          · apply Subtype.ext
            exact congrArg (fun z => (z.2.2.1.1 wt).2) hmap
        · apply Subtype.ext
          funext yt
          apply Subtype.ext
          funext wt
          apply Subtype.ext
          exact
            congrArg
              (fun z => (z.2.2.2.1 yt).1 wt)
              hmap
  map_smul' r A := by
    have hmap :=
      (t37RightAmbientEquiv hn hb2 hd2).map_smul r A.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 yt).1) hmap
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 yt).2) hmap
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun z => (z.2.2.1.1 wt).1) hmap
          · apply Subtype.ext
            exact congrArg (fun z => (z.2.2.1.1 wt).2) hmap
        · apply Subtype.ext
          funext yt
          apply Subtype.ext
          funext wt
          apply Subtype.ext
          exact
            congrArg
              (fun z => (z.2.2.2.1 yt).1 wt)
              hmap

end T37RightP1

end

end Core4loop.SquareDiagonal.EvenP
