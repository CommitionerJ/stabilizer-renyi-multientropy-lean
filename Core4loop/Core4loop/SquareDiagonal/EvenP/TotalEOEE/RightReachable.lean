import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RootGauge

set_option autoImplicit false
set_option warningAsError true
-- This completion-first coordinate certificate uses one file-wide budget.
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

/-! Generic coordinate infrastructure.  No selected linear section occurs. -/

@[reducible] private noncomputable def pointedCoordProdAddCommMonoid
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
  pointedCoordProdAddCommMonoid

noncomputable def tailZeroCongr
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (e : U ≃ₗ[F] V) :
    PointedValueTailZero S U s0 ≃ₗ[F]
      PointedValueTailZero S V s0 where
  toFun x :=
    ⟨fun t => e (x.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, e (x.1 t)) = 0
      rw [← map_sum, pointedValueTailZero_sum x, map_zero]⟩
  invFun x :=
    ⟨fun t => e.symm (x.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, e.symm (x.1 t)) = 0
      rw [← map_sum, pointedValueTailZero_sum x, map_zero]⟩
  left_inv x := by
    apply Subtype.ext
    funext t
    exact e.symm_apply_apply (x.1 t)
  right_inv x := by
    apply Subtype.ext
    funext t
    exact e.apply_symm_apply (x.1 t)
  map_add' x y := by
    apply Subtype.ext
    funext t
    exact e.map_add (x.1 t) (y.1 t)
  map_smul' r x := by
    apply Subtype.ext
    funext t
    exact e.map_smul r (x.1 t)

noncomputable def tailZeroProdEquiv
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] :
    PointedValueTailZero S (U × V) s0 ≃ₗ[F]
      (PointedValueTailZero S U s0 ×
        PointedValueTailZero S V s0) where
  toFun x :=
    (⟨fun t => (x.1 t).1, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (x.1 t).1) = 0
        simpa only [Prod.fst_sum] using
          congrArg Prod.fst (pointedValueTailZero_sum x)⟩,
      ⟨fun t => (x.1 t).2, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (x.1 t).2) = 0
        simpa only [Prod.snd_sum] using
          congrArg Prod.snd (pointedValueTailZero_sum x)⟩)
  invFun x :=
    ⟨fun t => (x.1.1 t, x.2.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, (x.1.1 t, x.2.1 t)) = 0
      apply Prod.ext
      · rw [Prod.fst_sum]
        exact pointedValueTailZero_sum x.1
      · rw [Prod.snd_sum]
        exact pointedValueTailZero_sum x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

noncomputable def pointedHeadShear
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V] :
    PointedEvenValueCoords S V s0 ≃ₗ[F]
      PointedEvenValueCoords S V s0 where
  toFun x := ((x.1.2, x.1.1 + x.1.2), x.2)
  invFun x := ((x.1.1 + x.1.2, x.1.1), x.2)
  left_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · change x.1.2 + (x.1.1 + x.1.2) = x.1.1
        calc
          x.1.2 + (x.1.1 + x.1.2) =
              x.1.1 + (x.1.2 + x.1.2) := by abel
          _ = x.1.1 := by
            rw [(add_eq_zero_iff_eq_of_F_module _ _).2 rfl, add_zero]
      · rfl
    · rfl
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change x.1.1 + x.1.2 + x.1.1 = x.1.2
        calc
          x.1.1 + x.1.2 + x.1.1 =
              (x.1.1 + x.1.1) + x.1.2 := by abel
          _ = x.1.2 := by
            rw [(add_eq_zero_iff_eq_of_F_module _ _).2 rfl, zero_add]
    · rfl
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change
          (x.1.1 + y.1.1) + (x.1.2 + y.1.2) =
            (x.1.1 + x.1.2) + (y.1.1 + y.1.2)
        abel
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact (smul_add r x.1.1 x.1.2).symm
    · rfl

/-! Root-cube gauges. -/

private noncomputable def singletonFamilyEquiv
    {n : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :
    (PVec n 1 → V) ≃ₗ[F] V where
  toFun f := f zeroVec
  invFun v := fun _ => v
  left_inv f := by
    funext p
    rw [pVec_one_eq_zeroVec p]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def cubeJKShift
    {n : Nat} [NeZero n] (uj uk : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X i (j - uj) (k - uk)
  invFun X i j k := X i (j + uj) (k + uk)
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def cubeJShift
    {n : Nat} [NeZero n] (uj : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n :=
  cubeJKShift uj 0

@[simp] private theorem cubeJKShift_apply
    {n : Nat} [NeZero n] (uj uk : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeJKShift uj uk X i j k =
      X i (j - uj) (k - uk) := rfl

private noncomputable def zwGaugeEquiv
    {n c d : Nat} [NeZero n] :
    (PVec n c → PVec n d → CyclicCube n) ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) where
  toFun f z w := cubeJKShift (vecSum z) (vecSum w) (f z w)
  invFun f z w :=
    (cubeJKShift (vecSum z) (vecSum w)).symm (f z w)
  left_inv f := by
    funext z w
    exact
      (cubeJKShift (vecSum z) (vecSum w)).symm_apply_apply (f z w)
  right_inv f := by
    funext z w
    exact
      (cubeJKShift (vecSum z) (vecSum w)).apply_symm_apply (f z w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def zGaugeEquiv
    {n c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) ≃ₗ[F]
      (PVec n c → CyclicCube n) where
  toFun f z := cubeJShift (vecSum z) (f z)
  invFun f z := (cubeJShift (vecSum z)).symm (f z)
  left_inv f := by
    funext z
    exact (cubeJShift (vecSum z)).symm_apply_apply (f z)
  right_inv f := by
    funext z
    exact (cubeJShift (vecSum z)).apply_symm_apply (f z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def aRootGaugedEquiv
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    AFun4 n 1 c d ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) :=
  (diamondARootCubeEquiv
      (n := n) (b := 1) (c := c) (d := d)
      Nat.zero_lt_one hc hd).trans
    ((singletonFamilyEquiv
      (n := n) (PVec n c → PVec n d → CyclicCube n)).trans
        (zwGaugeEquiv (n := n) (c := c) (d := d)))

private noncomputable def bRootGaugedEquiv
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    BFun4 n 1 c d ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) :=
  (diamondBRootCubeEquiv
      (n := n) (c := c) (d := d) hc hd).trans
    (zwGaugeEquiv (n := n) (c := c) (d := d))

private noncomputable def wRootZGaugedEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    WFun4 n 1 1 c ≃ₗ[F] (PVec n c → CyclicCube n) :=
  (diamondWRootCubeEquiv
      (n := n) (b := 1) (c := c) Nat.zero_lt_one hc).trans
    ((singletonFamilyEquiv
      (n := n) (PVec n c → CyclicCube n)).trans
        (zGaugeEquiv (n := n) (c := c)))

@[simp] private theorem aRootGaugedEquiv_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    aRootGaugedEquiv hc hd A zt wt i j k =
      diamondARootCubeEquiv Nat.zero_lt_one hc hd A zeroVec zt wt
        i (j - vecSum zt) (k - vecSum wt) := rfl

@[simp] private theorem bRootGaugedEquiv_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    bRootGaugedEquiv hc hd B zt wt i j k =
      diamondBRootCubeEquiv hc hd B zt wt
        i (j - vecSum zt) (k - vecSum wt) := rfl

@[simp] private theorem wRootZGaugedEquiv_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (W : WFun4 n 1 1 c) (zt : PVec n c)
    (i j k : I n) :
    wRootZGaugedEquiv hc W zt i j k =
      diamondWRootCubeEquiv Nat.zero_lt_one hc W zeroVec zt
        i (j - vecSum zt) k := by
  change
    cubeJShift (vecSum zt)
        ((diamondWRootCubeEquiv Nat.zero_lt_one hc W) zeroVec zt)
        i j k =
      _
  simp [cubeJShift, cubeJKShift]

private theorem aRootGaugedEquiv_eq
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d) :
    aRootGaugedEquiv hc hd A zt wt =
      cubeJKShift (vecSum zt) (vecSum wt)
        (diamondARootCubeEquiv
          Nat.zero_lt_one hc hd A zeroVec zt wt) :=
  rfl

private theorem bRootGaugedEquiv_eq
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d) :
    bRootGaugedEquiv hc hd B zt wt =
      cubeJKShift (vecSum zt) (vecSum wt)
        (diamondBRootCubeEquiv hc hd B zt wt) :=
  rfl

private theorem wRootZGaugedEquiv_eq
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (W : WFun4 n 1 1 c) (zt : PVec n c) :
    wRootZGaugedEquiv hc W zt =
      cubeJShift (vecSum zt)
        (diamondWRootCubeEquiv Nat.zero_lt_one hc W zeroVec zt) := by
  funext i j k
  rw [wRootZGaugedEquiv_apply]
  simp [cubeJShift, cubeJKShift]

@[simp] private theorem vecSum_zero_local
    {n k : Nat} [NeZero n] :
    vecSum (zeroVec : Vec n k) = 0 := by
  unfold vecSum zeroVec
  simp

@[simp] private theorem cubeJKShift_cubeDiffP_apply
    {n : Nat} [NeZero n] (uj uk : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffP (cubeJKShift uj uk X) i j k =
      cubeDiffP X i (j - uj) (k - uk) := by
  rw [EEOEInternal.cubeDiffP_apply, EEOEInternal.cubeDiffP_apply]
  simp only [cubeJKShift_apply]
  congr 2
  abel

@[simp] private theorem cubeJShift_cubeDiffR_apply
    {n : Nat} [NeZero n] (uj : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffR (cubeJShift uj X) i j k =
      cubeDiffR X i (j - uj) k := by
  rw [EEOEInternal.cubeDiffR_apply, EEOEInternal.cubeDiffR_apply]
  simp only [cubeJShift, cubeJKShift_apply, sub_zero]
  congr 2
  abel

@[simp] private theorem cubeJKShift_cubeDiffJInv_apply
    {n : Nat} [NeZero n] (uj uk : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffJInv (cubeJKShift uj uk X) i j k =
      cubeDiffJInv X i (j - uj) (k - uk) := by
  rw [EEOEInternal.cubeDiffJInv_apply,
    EEOEInternal.cubeDiffJInv_apply]
  simp only [cubeJKShift_apply]
  congr 2
  abel

/-! Frozen right ambient target and the nested dual-coordinate equivalence. -/

noncomputable abbrev RightAmbientTarget
    (n c d : Nat) [NeZero n] :=
  DiamondEOEERightAmbient n ×
    (DiamondEvenAxisValueTailZero n d (CyclicCube n × CyclicCube n) ×
      (DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n)))

private noncomputable def nestedDualRawEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    (PVec n c → PVec n d → CyclicCube n) ≃ₗ[F]
      ((PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec ×
        PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec) ×
        DiamondEvenAxisValueTailZero n c
          (PointedEvenValueCoords
            (PVec n d) (CyclicCube n) zeroVec)) :=
  (diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (PVec n d → CyclicCube n) hn hc2).trans
    ((((diamondEvenAxisDualCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
      (diamondEvenAxisDualCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2)).prodCongr
      (tailZeroCongr (zeroVec : PVec n c)
        (diamondEvenAxisDualCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2))))

private noncomputable def nestedDualShearEquiv
    {n c d : Nat} [NeZero n] :
    ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec ×
      PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec) ×
      DiamondEvenAxisValueTailZero n c
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec)) ≃ₗ[F]
    ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec ×
      PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec) ×
      DiamondEvenAxisValueTailZero n c
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec)) :=
  (((pointedHeadShear (zeroVec : PVec n d)).prodCongr
      (pointedHeadShear (zeroVec : PVec n d))).prodCongr
    (tailZeroCongr (zeroVec : PVec n c)
      (pointedHeadShear (zeroVec : PVec n d))))

private noncomputable def nestedDualReassocEquiv
    {n c d : Nat} [NeZero n] :
    ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec ×
      PointedEvenValueCoords
        (PVec n d) (CyclicCube n) zeroVec) ×
      DiamondEvenAxisValueTailZero n c
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec)) ≃ₗ[F]
      RightAmbientTarget n c d where
  toFun x :=
    let wt :=
      (tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec).symm
          (x.1.1.2, x.1.2.2)
    let zm :=
      tailZeroProdEquiv
        (S := PVec n c)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec x.2
    ((x.1.1.1, x.1.2.1), (wt, (zm.1, zm.2)))
  invFun x :=
    let wt :=
      tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec x.2.1
    let zm :=
      (tailZeroProdEquiv
        (S := PVec n c)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec).symm (x.2.2.1, x.2.2.2)
    (((x.1.1, wt.1), (x.1.2, wt.2)), zm)
  left_inv x := by
    dsimp only
    have hw :=
      (tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec).apply_symm_apply
          (x.1.1.2, x.1.2.2)
    have hzm :=
      (tailZeroProdEquiv
        (S := PVec n c)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec).symm_apply_apply x.2
    rw [hw, hzm]
  right_inv x := by
    dsimp only
    have hw :=
      (tailZeroProdEquiv
        (S := PVec n d) (U := CyclicCube n)
        (V := CyclicCube n) zeroVec).symm_apply_apply x.2.1
    have hzm :=
      (tailZeroProdEquiv
        (S := PVec n c)
        (U := CyclicCube n × CyclicCube n)
        (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
        zeroVec).apply_symm_apply (x.2.2.1, x.2.2.2)
    rw [hw, hzm]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact
          (tailZeroProdEquiv
            (S := PVec n d) (U := CyclicCube n)
            (V := CyclicCube n) zeroVec).symm.map_add
              (x.1.1.2, x.1.2.2) (y.1.1.2, y.1.2.2)
      · exact
          (tailZeroProdEquiv
            (S := PVec n c)
            (U := CyclicCube n × CyclicCube n)
            (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
            zeroVec).map_add x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact
          (tailZeroProdEquiv
            (S := PVec n d) (U := CyclicCube n)
            (V := CyclicCube n) zeroVec).symm.map_smul
              r (x.1.1.2, x.1.2.2)
      · exact
          (tailZeroProdEquiv
            (S := PVec n c)
            (U := CyclicCube n × CyclicCube n)
            (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
            zeroVec).map_smul r x.2

noncomputable def rightAmbientEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    AFun4 n 1 c d ≃ₗ[F] RightAmbientTarget n c d :=
  (aRootGaugedEquiv (n := n) (c := c) (d := d)
      (by omega) (by omega)).trans
    ((diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (PVec n d → CyclicCube n) hn hc2).trans
      ((pointedHeadShear (zeroVec : PVec n c)).trans
        (((((diamondEvenAxisDualCoordEquiv
            (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
          (diamondEvenAxisDualCoordEquiv
            (n := n) (k := d) (CyclicCube n) hn hd2)).prodCongr
          (tailZeroCongr (zeroVec : PVec n c)
            (diamondEvenAxisDualCoordEquiv
              (n := n) (k := d) (CyclicCube n) hn hd2))).trans
          (nestedDualShearEquiv (n := n) (c := c) (d := d))).trans
          (nestedDualReassocEquiv (n := n) (c := c) (d := d)))))

private noncomputable def zDualCoords
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    PointedEvenValueCoords
      (PVec n c) (PVec n d → CyclicCube n) zeroVec :=
  diamondEvenAxisDualCoordEquiv
    (n := n) (k := c) (PVec n d → CyclicCube n) hn hc2
      (aRootGaugedEquiv (by omega) (by omega) A)

private noncomputable def dWCoords
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    PointedEvenValueCoords
      (PVec n d) (CyclicCube n) zeroVec :=
  diamondEvenAxisDualCoordEquiv
    (n := n) (k := d) (CyclicCube n) hn hd2
      (zDualCoords hn hc2 hd2 A).1.2

private noncomputable def aWCoords
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    PointedEvenValueCoords
      (PVec n d) (CyclicCube n) zeroVec :=
  diamondEvenAxisDualCoordEquiv
    (n := n) (k := d) (CyclicCube n) hn hd2
      (zDualCoords hn hc2 hd2 A).1.1

@[simp] private theorem rightAmbientEquiv_scalar_constrained
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    (rightAmbientEquiv hn hc2 hd2 A).1.1 =
      ((dWCoords hn hc2 hd2 A).1.2,
        (dWCoords hn hc2 hd2 A).1.1 +
          (dWCoords hn hc2 hd2 A).1.2) := by
  rfl

@[simp] private theorem rightAmbientEquiv_Wtail_constrained
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d)
    (t : DiamondEvenAxisTailIndex n d) :
    ((rightAmbientEquiv hn hc2 hd2 A).2.1.1 t).1 =
      (dWCoords hn hc2 hd2 A).2.1 t := by
  rfl

private theorem rightAmbientEquiv_Wtail_raw_shear
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d)
    (t : DiamondEvenAxisTailIndex n d) :
    (rightAmbientEquiv hn hc2 hd2 A).2.1.1 t =
      ((dWCoords hn hc2 hd2 A).2.1 t,
        (aWCoords hn hc2 hd2 A).2.1 t +
          (dWCoords hn hc2 hd2 A).2.1 t) := by
  apply Prod.ext
  · rfl
  · let E :=
      diamondEvenAxisDualCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    let Z := zDualCoords hn hc2 hd2 A
    have hm := E.map_add Z.1.1 Z.1.2
    exact congrArg (fun q => q.2.1 t) hm

/-! The one-axis uniform range calculation used after summing the Z axis. -/

private noncomputable def uniformConstraintMap
    {n d : Nat} [NeZero n] :
    ((PVec n d → CyclicCube n) × CyclicCube n) →ₗ[F]
      (PVec n d → CyclicCube n) where
  toFun x wt := cubeDiffP (x.1 wt) + cubeDiffR x.2
  map_add' x y := by
    funext wt
    simp
    abel
  map_smul' r x := by
    funext wt
    simp

private theorem sum_at_point_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommMonoid V] (f : S → V) :
    (∑ s, f s) = f s0 + ∑ t : PointedTail S s0, f t.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset S)) (p := fun s : S => s = s0) f).symm
  calc
    (∑ s, f s) =
        (∑ s ∈ (Finset.univ : Finset S) with s = s0, f s) +
          ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
            simpa using hpart
    _ = f s0 + ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
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

private theorem cast_odd_eq_one
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem sum_const_odd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    cast_odd_eq_one hodd, one_smul]

private theorem cast_even_eq_zero
    {m : Nat} (hm : Even m) : (m : F) = 0 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  exact F_add_self (q : F)

private theorem sum_const_even
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = 0 := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    cast_even_eq_zero heven, zero_smul]

private theorem zDual_D_eq_total_sum
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    (zDualCoords hn hc2 hd2 A).1.2 =
      ∑ z, aRootGaugedEquiv (by omega) (by omega) A z := by
  let g := aRootGaugedEquiv (by omega : 0 < c) (by omega : 0 < d) A
  change
    (∑ t : DiamondEvenAxisTailIndex n c,
      (g t.1 + g (zeroVec : PVec n c))) =
        ∑ z : PVec n c, g z
  rw [Finset.sum_add_distrib,
    sum_const_odd
      (odd_card_diamondEvenAxisTailIndex hn hc2),
    sum_at_point_tail (zeroVec : PVec n c) g]
  abel

private theorem src_JInv_coords_from_dual
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (A : PVec n d → CyclicCube n) :
    let D :=
      diamondEvenAxisDualCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2 A
    let S :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
          (fun wt => cubeDiffJInv (A wt))
    S.1.1 = cubeDiffJInv D.1.2 ∧
      S.1.2 = cubeDiffJInv (D.1.1 + D.1.2) ∧
      ∀ t, S.2.1 t = cubeDiffJInv (D.2.1 t) := by
  dsimp only
  let hodd := odd_card_diamondEvenAxisTailIndex hn hd2
  let tailSum :=
    ∑ t : DiamondEvenAxisTailIndex n d, A t.1
  let D :=
    ∑ t : DiamondEvenAxisTailIndex n d,
      (A t.1 + A (zeroVec : PVec n d))
  have hD : D = tailSum + A zeroVec := by
    dsimp only [D, tailSum]
    rw [Finset.sum_add_distrib, sum_const_odd hodd]
  refine ⟨?_, ?_, ?_⟩
  · change
      (∑ s : PVec n d, cubeDiffJInv (A s)) =
        cubeDiffJInv D
    rw [← map_sum]
    rw [sum_at_point_tail (zeroVec : PVec n d) A, hD]
    congr 1
    abel
  · change
      (∑ t : DiamondEvenAxisTailIndex n d,
          cubeDiffJInv (A t.1)) =
        cubeDiffJInv (A zeroVec + D)
    rw [← map_sum, hD]
    congr 1
    calc
      tailSum =
          tailSum + (A zeroVec + A zeroVec) := by
            rw [(add_eq_zero_iff_eq_of_F_module _ _).2 rfl, add_zero]
      _ = A zeroVec + (tailSum + A zeroVec) := by abel
  · intro t
    change
      cubeDiffJInv (A t.1) +
          ∑ u : DiamondEvenAxisTailIndex n d,
            cubeDiffJInv (A u.1) =
        cubeDiffJInv
          (A t.1 + A zeroVec + D)
    rw [← map_sum, ← map_add, hD]
    congr 1
    calc
      A t.1 + tailSum =
          A t.1 + tailSum + (A zeroVec + A zeroVec) := by
            rw [(add_eq_zero_iff_eq_of_F_module _ _).2 rfl, add_zero]
      _ = A t.1 + A zeroVec + (tailSum + A zeroVec) := by abel

private theorem uniformConstraint_coords
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (f : PVec n d → CyclicCube n) (W : CyclicCube n) :
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    let x := E f
    let y := E (uniformConstraintMap (f, W))
    y.1.1 = cubeDiffP x.1.1 ∧
      y.1.2 = cubeDiffP x.1.2 + cubeDiffR W ∧
      ∀ t, y.2.1 t = cubeDiffP (x.2.1 t) := by
  dsimp only
  let heven := even_card_PVec hn hd2
  let hodd := odd_card_diamondEvenAxisTailIndex hn hd2
  refine ⟨?_, ?_, ?_⟩
  · change
      (∑ s : PVec n d, (cubeDiffP (f s) + cubeDiffR W)) =
        cubeDiffP (∑ s : PVec n d, f s)
    rw [Finset.sum_add_distrib, ← map_sum,
      sum_const_even heven, add_zero]
  · change
      (∑ t : DiamondEvenAxisTailIndex n d,
          (cubeDiffP (f t.1) + cubeDiffR W)) =
        cubeDiffP
            (∑ t : DiamondEvenAxisTailIndex n d, f t.1) +
          cubeDiffR W
    rw [Finset.sum_add_distrib, ← map_sum,
      sum_const_odd hodd]
  · intro t
    change
      (cubeDiffP (f t.1) + cubeDiffR W) +
          ∑ u : DiamondEvenAxisTailIndex n d,
            (cubeDiffP (f u.1) + cubeDiffR W) =
        cubeDiffP
          (f t.1 +
            ∑ u : DiamondEvenAxisTailIndex n d, f u.1)
    rw [Finset.sum_add_distrib, ← map_sum,
      sum_const_odd hodd, map_add]
    calc
      (cubeDiffP (f t.1) + cubeDiffR W) +
            (cubeDiffP (∑ u : DiamondEvenAxisTailIndex n d, f u.1) +
              cubeDiffR W) =
          cubeDiffP (f t.1) +
              cubeDiffP (∑ u : DiamondEvenAxisTailIndex n d, f u.1) +
            (cubeDiffR W + cubeDiffR W) := by abel
      _ = _ := by
        rw [show cubeDiffR W + cubeDiffR W = 0 from
          (add_eq_zero_iff_eq_of_F_module _ _).2 rfl, add_zero]

private theorem uniform_range_iff_coords
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (g : PVec n d → CyclicCube n) :
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    let x := E g
    g ∈ LinearMap.range (uniformConstraintMap (n := n) (d := d)) ↔
      x.1.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
      x.1.2 ∈ LinearMap.range
        (LinearMap.coprod
          (cubeDiffP (n := n)) (cubeDiffR (n := n))) ∧
      ∀ t, x.2.1 t ∈ LinearMap.range (cubeDiffP (n := n)) := by
  classical
  dsimp only
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let x := E g
  constructor
  · rintro ⟨fw, rfl⟩
    let y := E fw.1
    have hc := uniformConstraint_coords hn hd2 fw.1 fw.2
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨y.1.1, hc.1.symm⟩
    · refine ⟨(y.1.2, fw.2), ?_⟩
      change cubeDiffP y.1.2 + cubeDiffR fw.2 = _
      exact hc.2.1.symm
    · intro t
      exact ⟨y.2.1 t, (hc.2.2 t).symm⟩
  · rintro ⟨⟨b0, hb0⟩, ⟨⟨b1, W⟩, hb1⟩, htail⟩
    -- This is Prop-level elimination of finitely many range witnesses.
    -- It does not define or export a linear section of `cubeDiffP`.
    choose bt hbt using htail
    let corr : CyclicCube n := ∑ t, bt t
    have hPcorr : cubeDiffP corr = 0 := by
      calc
        cubeDiffP corr =
            ∑ t : DiamondEvenAxisTailIndex n d, cubeDiffP (bt t) := by
              rw [map_sum]
        _ = ∑ t : DiamondEvenAxisTailIndex n d, x.2.1 t := by
              apply Finset.sum_congr rfl
              intro t _
              exact hbt t
        _ = 0 := pointedValueTailZero_sum x.2
    rcases diamondEvenAxisTailIndex_nonempty hn hd2 with ⟨t0⟩
    let tailFun : DiamondEvenAxisTailIndex n d → CyclicCube n :=
      fun t => if t = t0 then bt t + corr else bt t
    have htailSum : (∑ t, tailFun t) = 0 := by
      have hdelta :
          (∑ t : DiamondEvenAxisTailIndex n d,
            if t = t0 then corr else 0) = corr := by
        rw [Finset.sum_eq_single t0]
        · simp
        · intro t _ ht
          simp [ht]
        · simp
      have hpoint :
          tailFun =
            fun t => bt t + if t = t0 then corr else 0 := by
        funext t
        by_cases ht : t = t0 <;> simp [tailFun, ht]
      rw [hpoint, Finset.sum_add_distrib, hdelta]
      exact (add_eq_zero_iff_eq_of_F_module corr corr).2 rfl
    let tail :
        DiamondEvenAxisValueTailZero n d (CyclicCube n) :=
      ⟨tailFun, LinearMap.mem_ker.mpr htailSum⟩
    have hPtail (t : DiamondEvenAxisTailIndex n d) :
        cubeDiffP (tail.1 t) = x.2.1 t := by
      by_cases ht : t = t0
      · subst t
        simp only [tail, tailFun, if_pos]
        rw [map_add, hPcorr, add_zero]
        exact hbt t0
      · simp only [tail, tailFun, ht]
        exact hbt t
    let coords :
        PointedEvenValueCoords
          (PVec n d) (CyclicCube n) zeroVec :=
      ((b0, b1), tail)
    let f := E.symm coords
    refine ⟨(f, W), ?_⟩
    apply E.injective
    have hf : E f = coords := E.apply_symm_apply coords
    have hc := uniformConstraint_coords hn hd2 f W
    apply Prod.ext
    · apply Prod.ext
      · rw [hc.1]
        have hf0 := congrArg (fun z => z.1.1) hf
        calc
          cubeDiffP (E f).1.1 =
              cubeDiffP coords.1.1 := congrArg cubeDiffP hf0
          _ = x.1.1 := hb0
      · rw [hc.2.1]
        have hf1 := congrArg (fun z => z.1.2) hf
        calc
          cubeDiffP (E f).1.2 + cubeDiffR W =
              cubeDiffP coords.1.2 + cubeDiffR W :=
                congrArg
                  (fun z => cubeDiffP z + cubeDiffR W) hf1
          _ = x.1.2 := hb1
    · apply Subtype.ext
      funext t
      rw [hc.2.2 t]
      have hft := congrArg (fun z => z.2.1 t) hf
      calc
        cubeDiffP ((E f).2.1 t) =
            cubeDiffP (coords.2.1 t) :=
              congrArg cubeDiffP hft
        _ = x.2.1 t := hPtail t

/-! Direct comparison of the literal reachable condition with the uniform
W-family constraint after the Z sum. -/

private theorem sum_delta_zero
    {S V : Type*} [Fintype S] [DecidableEq S]
    [AddCommMonoid V] (s0 : S) (v : V) :
    (∑ s : S, if s = s0 then v else 0) = v := by
  rw [Finset.sum_eq_single s0]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

private theorem literal_reachable_iff_uniform_range
    {n c d : Nat} [NeZero n]
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    A ∈ DiamondEvenPReachableA n 1 c d ↔
      (fun wt =>
        cubeDiffJInv
          (∑ zt : PVec n c,
            aRootGaugedEquiv
              (by omega : 0 < c) (by omega : 0 < d) A zt wt)) ∈
        LinearMap.range (uniformConstraintMap (n := n) (d := d)) := by
  change
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := 1) (c := c) (d := d) A ∈
      LinearMap.range
        (squareCompat
          (n := n) (a := 1) (b := 1) (c := c) (d := d)) ↔ _
  constructor
  · rintro ⟨bw, hbw⟩
    let bg :=
      bRootGaugedEquiv
        (n := n) (c := c) (d := d) (by omega) (by omega) bw.1
    let wg :=
      wRootZGaugedEquiv
        (n := n) (c := c) (by omega) bw.2
    refine ⟨(fun wt => ∑ zt, bg zt wt, ∑ zt, wg zt), ?_⟩
    funext wt i j k
    change
      (cubeDiffP (∑ zt, bg zt wt) +
        cubeDiffR (∑ zt, wg zt)) i j k =
      cubeDiffJInv
        (∑ zt,
          aRootGaugedEquiv
            (by omega : 0 < c) (by omega : 0 < d) A zt wt)
        i j k
    rw [map_sum, map_sum, map_sum,
      ← Finset.sum_add_distrib, Finset.sum_apply,
      Finset.sum_apply, Finset.sum_apply]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hbw (zeroVec : PVec n 1))
            ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
              (i, zeroVec)))
          j)
        ((diamondVecHeadTailEquiv (by omega : 0 < d)).symm
          (k - vecSum wt, wt))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one (by omega : 0 < c) (by omega : 0 < d)
      bw.1 bw.2 zeroVec wt i j (k - vecSum wt)] at hpoint
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one (by omega : 0 < c) (by omega : 0 < d)
      A zeroVec wt i j (k - vecSum wt)] at hpoint
    simp only [Pi.add_apply] at hpoint ⊢
    simpa only [bg, wg, vecSum_zero_local, add_zero,
      Finset.sum_apply, bRootGaugedEquiv_eq,
      wRootZGaugedEquiv_eq, aRootGaugedEquiv_eq,
      cubeJKShift_cubeDiffP_apply,
      cubeJShift_cubeDiffR_apply, cubeJKShift_cubeDiffJInv_apply,
      sub_add_cancel] using hpoint
  · rintro ⟨fw, hfw⟩
    classical
    let bf : PVec n c → PVec n d → CyclicCube n :=
      fun zt => if zt = (zeroVec : PVec n c) then fw.1 else 0
    let wf : PVec n c → CyclicCube n :=
      fun zt => if zt = (zeroVec : PVec n c) then fw.2 else 0
    let B :=
      (bRootGaugedEquiv
        (n := n) (c := c) (d := d)
        (by omega : 0 < c) (by omega : 0 < d)).symm bf
    let W :=
      (wRootZGaugedEquiv
        (n := n) (c := c) (by omega : 0 < c)).symm wf
    have hB :
        bRootGaugedEquiv
          (n := n) (c := c) (d := d)
          (by omega : 0 < c) (by omega : 0 < d) B = bf :=
      (bRootGaugedEquiv
        (n := n) (c := c) (d := d)
        (by omega : 0 < c) (by omega : 0 < d)).apply_symm_apply bf
    have hW :
        wRootZGaugedEquiv
          (n := n) (c := c) (by omega : 0 < c) W = wf :=
      (wRootZGaugedEquiv
        (n := n) (c := c)
        (by omega : 0 < c)).apply_symm_apply wf
    have hBsum (wt : PVec n d) :
        (∑ zt, bf zt wt) = fw.1 wt := by
      have hfamily : (∑ zt, bf zt) = fw.1 := by
        simpa only [bf] using
          (sum_delta_zero (zeroVec : PVec n c) fw.1)
      simpa only [Finset.sum_apply] using congrFun hfamily wt
    have hWsum : (∑ zt, wf zt) = fw.2 := by
      exact sum_delta_zero (zeroVec : PVec n c) fw.2
    refine ⟨(B, W), ?_⟩
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew :=
      diamondVecHeadTailEquiv (n := n) (by omega : 0 < d)
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one (by omega : 0 < c) (by omega : 0 < d)
      B W (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one (by omega : 0 < c) (by omega : 0 < d)
      A (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hfw (ew w).2)
            (ey y).1)
          sz)
        ((ew w).1 + vecSum (ew w).2)
    change
      (cubeDiffP (fw.1 (ew w).2) + cubeDiffR fw.2)
          (ey y).1 sz ((ew w).1 + vecSum (ew w).2) =
        cubeDiffJInv
          (∑ zt : PVec n c,
            aRootGaugedEquiv
              (by omega : 0 < c) (by omega : 0 < d)
              A zt (ew w).2)
          (ey y).1 sz ((ew w).1 + vecSum (ew w).2) at hpoint
    rw [← hBsum (ew w).2, ← hWsum] at hpoint
    rw [← hB, ← hW] at hpoint
    rw [map_sum, map_sum, map_sum,
      ← Finset.sum_add_distrib, Finset.sum_apply,
      Finset.sum_apply, Finset.sum_apply] at hpoint
    simp only [Pi.add_apply] at hpoint ⊢
    simpa only [vecSum_zero_local, add_zero, Finset.sum_apply,
      bRootGaugedEquiv_eq, wRootZGaugedEquiv_eq,
      aRootGaugedEquiv_eq,
      cubeJKShift_cubeDiffP_apply,
      cubeJShift_cubeDiffR_apply, cubeJKShift_cubeDiffJInv_apply,
      add_sub_cancel_right] using hpoint

theorem right_mem_iff
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    A ∈ DiamondEvenPReachableA n 1 c d ↔
      (rightAmbientEquiv hn hc2 hd2 A).1 ∈
          DiamondEOEERightSource n ∧
        ∀ t : DiamondEvenAxisTailIndex n d,
          ((rightAmbientEquiv hn hc2 hd2 A).2.1.1 t).1 ∈
            EEOEInternal.PReachRight n := by
  let gA :=
    aRootGaugedEquiv
      (n := n) (c := c) (d := d)
      (by omega : 0 < c) (by omega : 0 < d) A
  let Z :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (PVec n d → CyclicCube n) hn hc2 gA
  let D :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 Z.1.2
  let g : PVec n d → CyclicCube n :=
    fun wt => cubeDiffJInv (Z.1.2 wt)
  let S :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 g
  have hZ :
      Z.1.2 = ∑ zt : PVec n c, gA zt := by
    simpa only [Z, gA, zDualCoords] using
      zDual_D_eq_total_sum hn hc2 hd2 A
  have hJ :
      S.1.1 = cubeDiffJInv D.1.2 ∧
        S.1.2 = cubeDiffJInv (D.1.1 + D.1.2) ∧
        ∀ t, S.2.1 t = cubeDiffJInv (D.2.1 t) := by
    simpa only [S, g, D] using
      src_JInv_coords_from_dual hn hd2 Z.1.2
  have hrange :
      g ∈ LinearMap.range (uniformConstraintMap (n := n) (d := d)) ↔
        S.1.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
        S.1.2 ∈ LinearMap.range
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n))) ∧
        ∀ t, S.2.1 t ∈
          LinearMap.range (cubeDiffP (n := n)) := by
    simpa only [S, g] using uniform_range_iff_coords hn hd2 g
  have hg :
      (fun wt =>
        cubeDiffJInv
          (∑ zt : PVec n c,
            aRootGaugedEquiv
              (by omega : 0 < c) (by omega : 0 < d) A zt wt)) =
        g := by
    funext wt
    dsimp only [g]
    simpa only [Finset.sum_apply, gA] using
      congrArg
        (fun h : PVec n d → CyclicCube n =>
          cubeDiffJInv (h wt))
        hZ.symm
  constructor
  · intro hA
    have hraw :=
      (literal_reachable_iff_uniform_range hc2 hd2 A).mp hA
    rw [hg] at hraw
    have hc := hrange.mp hraw
    have h0 :
        cubeDiffJInv D.1.2 ∈
          LinearMap.range (cubeDiffP (n := n)) := by
      exact hJ.1 ▸ hc.1
    have h1 :
        cubeDiffJInv (D.1.1 + D.1.2) ∈
          LinearMap.range
            (LinearMap.coprod
              (cubeDiffP (n := n)) (cubeDiffR (n := n))) := by
      exact hJ.2.1 ▸ hc.2.1
    refine ⟨?_, ?_⟩
    · change
        cubeDiffJInv
              (rightAmbientEquiv hn hc2 hd2 A).1.1.1 ∈
            LinearMap.range (cubeDiffP (n := n)) ∧
          cubeDiffJInv
              (rightAmbientEquiv hn hc2 hd2 A).1.1.2 ∈
            LinearMap.range
              (LinearMap.coprod
                (cubeDiffP (n := n)) (cubeDiffR (n := n)))
      rw [rightAmbientEquiv_scalar_constrained]
      exact ⟨h0, h1⟩
    · intro t
      change
        cubeDiffJInv
            ((rightAmbientEquiv hn hc2 hd2 A).2.1.1 t).1 ∈
          LinearMap.range (cubeDiffP (n := n))
      rw [rightAmbientEquiv_Wtail_constrained]
      exact hJ.2.2 t ▸ hc.2.2 t
  · rintro ⟨hs, ht⟩
    have h0 :
        cubeDiffJInv D.1.2 ∈
          LinearMap.range (cubeDiffP (n := n)) := by
      have hs0 := hs.1
      change
        cubeDiffJInv
            (rightAmbientEquiv hn hc2 hd2 A).1.1.1 ∈
          LinearMap.range (cubeDiffP (n := n)) at hs0
      rw [rightAmbientEquiv_scalar_constrained] at hs0
      exact hs0
    have h1 :
        cubeDiffJInv (D.1.1 + D.1.2) ∈
          LinearMap.range
            (LinearMap.coprod
              (cubeDiffP (n := n)) (cubeDiffR (n := n))) := by
      have hs1 := hs.2
      change
        cubeDiffJInv
            (rightAmbientEquiv hn hc2 hd2 A).1.1.2 ∈
          LinearMap.range
            (LinearMap.coprod
              (cubeDiffP (n := n)) (cubeDiffR (n := n))) at hs1
      rw [rightAmbientEquiv_scalar_constrained] at hs1
      exact hs1
    have hc :
        S.1.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
          S.1.2 ∈ LinearMap.range
            (LinearMap.coprod
              (cubeDiffP (n := n)) (cubeDiffR (n := n))) ∧
          ∀ t, S.2.1 t ∈
            LinearMap.range (cubeDiffP (n := n)) := by
      refine ⟨hJ.1.symm ▸ h0, hJ.2.1.symm ▸ h1, ?_⟩
      intro t
      have htt := ht t
      change
        cubeDiffJInv
            ((rightAmbientEquiv hn hc2 hd2 A).2.1.1 t).1 ∈
          LinearMap.range (cubeDiffP (n := n)) at htt
      rw [rightAmbientEquiv_Wtail_constrained] at htt
      exact (hJ.2.2 t).symm ▸ htt
    have hraw : g ∈
        LinearMap.range (uniformConstraintMap (n := n) (d := d)) :=
      hrange.mpr hc
    rw [← hg] at hraw
    exact (literal_reachable_iff_uniform_range hc2 hd2 A).mpr hraw

noncomputable abbrev RightReachableTarget
    (n c d : Nat) [NeZero n] :=
  DiamondEOEERightSource n ×
    (DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n) ×
      (DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n)))

private noncomputable def wTailPack
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d
      (CyclicCube n × CyclicCube n))
    (hu : ∀ t, (u.1 t).1 ∈ EEOEInternal.PReachRight n) :
    DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n) :=
  ⟨fun t => (⟨(u.1 t).1, hu t⟩, (u.1 t).2), by
    apply LinearMap.mem_ker.mpr
    change
      (∑ t,
        ((⟨(u.1 t).1, hu t⟩ : EEOEInternal.PReachRight n),
          (u.1 t).2)) = 0
    have hsum := pointedValueTailZero_sum u
    apply Prod.ext
    · apply Subtype.ext
      simpa only [Submodule.coe_sum, Prod.fst_sum] using
        congrArg Prod.fst hsum
    · simpa only [Prod.snd_sum] using congrArg Prod.snd hsum⟩

private noncomputable def wTailForget
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d
        (DiamondEOEEWRightSource n) →ₗ[F]
      DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n) where
  toFun u :=
    ⟨fun t => ((u.1 t).1.1, (u.1 t).2), by
      apply LinearMap.mem_ker.mpr
      have hu := pointedValueTailZero_sum u
      change
        (∑ t, (((u.1 t).1.1, (u.1 t).2) :
          CyclicCube n × CyclicCube n)) = 0
      apply Prod.ext
      · have hfst := congrArg Prod.fst hu
        simpa only [Prod.fst_sum, Submodule.coe_sum] using
          congrArg Subtype.val hfst
      · simpa only [Prod.snd_sum] using congrArg Prod.snd hu⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

noncomputable def rightReachableEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n 1 c d ≃ₗ[F]
      RightReachableTarget n c d where
  toFun A := by
    let q := rightAmbientEquiv hn hc2 hd2 A.1
    have hq := (right_mem_iff hn hc2 hd2 A.1).mp A.2
    exact
      (⟨q.1, hq.1⟩,
        (wTailPack q.2.1 hq.2, (q.2.2.1, q.2.2.2)))
  invFun q := by
    let raw : RightAmbientTarget n c d :=
      (q.1.1,
        (wTailForget q.2.1, (q.2.2.1, q.2.2.2)))
    let A := (rightAmbientEquiv hn hc2 hd2).symm raw
    refine ⟨A, (right_mem_iff hn hc2 hd2 A).mpr ?_⟩
    have hread : rightAmbientEquiv hn hc2 hd2 A = raw :=
      (rightAmbientEquiv hn hc2 hd2).apply_symm_apply raw
    refine ⟨?_, ?_⟩
    · have hfst := congrArg Prod.fst hread
      rw [hfst]
      exact q.1.2
    · intro t
      have ht := (q.2.1.1 t).1.2
      have htail := congrArg (fun z => z.2.1.1 t) hread
      change
        ((rightAmbientEquiv hn hc2 hd2 A).2.1.1 t).1 ∈
          EEOEInternal.PReachRight n
      change
        ((raw.2.1.1 t).1 : CyclicCube n) ∈
          EEOEInternal.PReachRight n at ht
      have htailFst := congrArg Prod.fst htail
      rw [htailFst]
      exact ht
  left_inv A := by
    apply Subtype.ext
    exact (rightAmbientEquiv hn hc2 hd2).symm_apply_apply A.1
  right_inv q := by
    have hread :=
      (rightAmbientEquiv hn hc2 hd2).apply_symm_apply
        (q.1.1,
          (wTailForget q.2.1, (q.2.2.1, q.2.2.2)))
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · apply Prod.ext
      · apply Subtype.ext
        funext t
        apply Prod.ext
        · apply Subtype.ext
          exact
            congrArg
              (fun z => (z.2.1.1 t).1)
              hread
        · exact
            congrArg
              (fun z => (z.2.1.1 t).2)
              hread
      · apply Prod.ext
        · exact congrArg (fun z => z.2.2.1) hread
        · exact congrArg (fun z => z.2.2.2) hread
  map_add' A A' := by
    have hmap :=
      (rightAmbientEquiv hn hc2 hd2).map_add A.1 A'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext t
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 t).1) hmap
        · exact congrArg (fun z => (z.2.1.1 t).2) hmap
      · apply Prod.ext
        · exact congrArg (fun z => z.2.2.1) hmap
        · exact congrArg (fun z => z.2.2.2) hmap
  map_smul' r A := by
    have hmap :=
      (rightAmbientEquiv hn hc2 hd2).map_smul r A.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext t
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 t).1) hmap
        · exact congrArg (fun z => (z.2.1.1 t).2) hmap
      · apply Prod.ext
        · exact congrArg (fun z => z.2.2.1) hmap
        · exact congrArg (fun z => z.2.2.2) hmap

theorem rightReachableEquiv_Wtail_is_pointwise_shear
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n 1 c d)
    (t : DiamondEvenAxisTailIndex n d) :
    (rightReachableEquiv hn hc2 hd2 A).2.1.1 t =
      diamondEOEEWRightShear
        ((aWCoords hn hc2 hd2 A.1).2.1 t,
          ⟨(dWCoords hn hc2 hd2 A.1).2.1 t, by
            have h :=
              (right_mem_iff hn hc2 hd2 A.1).mp A.2 |>.2 t
            change
              cubeDiffJInv
                  ((rightAmbientEquiv hn hc2 hd2 A.1).2.1.1 t).1 ∈
                LinearMap.range (cubeDiffP (n := n)) at h
            rw [rightAmbientEquiv_Wtail_constrained] at h
            exact h⟩) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · change
      ((rightAmbientEquiv hn hc2 hd2 A.1).2.1.1 t).2 =
        (aWCoords hn hc2 hd2 A.1).2.1 t +
          (dWCoords hn hc2 hd2 A.1).2.1 t
    exact congrArg Prod.snd
      (rightAmbientEquiv_Wtail_raw_shear hn hc2 hd2 A.1 t)


end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP
