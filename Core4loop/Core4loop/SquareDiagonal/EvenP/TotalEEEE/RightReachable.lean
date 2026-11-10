import Core4loop.SquareDiagonal.EvenP.TotalEEEE.LeftSource
import Core4loop.SquareDiagonal.EvenP.TotalEEOE.RightReachable
import Core4loop.SquareDiagonal.EvenP.EEEE.Definitions

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 2000000
set_option maxSynthPendingDepth 2048

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEEEERightInternal

/-! ## Literal three-axis gauge and the complete-`Z` reachable equation -/

noncomputable def cubeIJKShiftEquiv
    {n : Nat} [NeZero n] (u v w : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X (i - u) (j - v) (k - w)
  invFun X i j k := X (i + u) (j + v) (k + w)
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cubeIJKShiftEquiv_apply
    {n : Nat} [NeZero n] (u v w : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeIJKShiftEquiv u v w X i j k =
      X (i - u) (j - v) (k - w) :=
  rfl

noncomputable def yzwGaugeEquiv
    {n b c d : Nat} [NeZero n] :
    (PVec n b → PVec n c → PVec n d → CyclicCube n) ≃ₗ[F]
      (PVec n b → PVec n c → PVec n d → CyclicCube n) where
  toFun f yt zt wt :=
    cubeIJKShiftEquiv (vecSum yt) (vecSum zt) (vecSum wt)
      (f yt zt wt)
  invFun f yt zt wt :=
    (cubeIJKShiftEquiv (vecSum yt) (vecSum zt) (vecSum wt)).symm
      (f yt zt wt)
  left_inv f := by
    funext yt zt wt
    exact
      (cubeIJKShiftEquiv
        (vecSum yt) (vecSum zt) (vecSum wt)).symm_apply_apply
          (f yt zt wt)
  right_inv f := by
    funext yt zt wt
    exact
      (cubeIJKShiftEquiv
        (vecSum yt) (vecSum zt) (vecSum wt)).apply_symm_apply
          (f yt zt wt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def aLiteralGaugeEquiv
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    AFun4 n b c d ≃ₗ[F]
      (PVec n b → PVec n c → PVec n d → CyclicCube n) :=
  (diamondARootCubeEquiv hb hc hd).trans
    (yzwGaugeEquiv (n := n) (b := b) (c := c) (d := d))

@[simp] theorem aLiteralGaugeEquiv_apply
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    aLiteralGaugeEquiv hb hc hd A yt zt wt i j k =
      diamondARootCubeEquiv hb hc hd A yt zt wt
        (i - vecSum yt) (j - vecSum zt) (k - vecSum wt) :=
  rfl

@[simp] theorem cubeIJKShift_cubeDiffJInv_apply
    {n : Nat} [NeZero n] (u v w : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffJInv (cubeIJKShiftEquiv u v w X) i j k =
      cubeDiffJInv X (i - u) (j - v) (k - w) := by
  rw [EEOEInternal.cubeDiffJInv_apply,
    EEOEInternal.cubeDiffJInv_apply]
  simp only [cubeIJKShiftEquiv_apply]
  congr 2
  abel

@[simp] theorem aLiteralGauge_cubeDiffJInv_apply
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    cubeDiffJInv (aLiteralGaugeEquiv hb hc hd A yt zt wt) i j k =
      cubeDiffJInv
        (diamondARootCubeEquiv hb hc hd A yt zt wt)
        (i - vecSum yt) (j - vecSum zt) (k - vecSum wt) := by
  exact
    cubeIJKShift_cubeDiffJInv_apply
      (vecSum yt) (vecSum zt) (vecSum wt)
      (diamondARootCubeEquiv hb hc hd A yt zt wt) i j k

noncomputable def totalEEEET37ConstraintMap
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

theorem literal_reachable_iff_Ztotal_t37_range
    {n b c d : Nat} [NeZero n]
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n b c d) :
    A ∈ DiamondEvenPReachableA n b c d ↔
      (fun yt wt =>
        cubeDiffJInv
          (∑ zt : PVec n c,
            aLiteralGaugeEquiv
              (by omega : 0 < b) (by omega : 0 < c)
              (by omega : 0 < d) A yt zt wt)) ∈
        LinearMap.range
          (totalEEEET37ConstraintMap
            (n := n) (b := b) (d := d)) := by
  classical
  change
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := b) (c := c) (d := d) A ∈
      LinearMap.range
        (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)) ↔ _
  constructor
  · rintro ⟨bw, hbw⟩
    let g :=
      TotalEEEEInternal.literalGaugeEquiv
        (n := n) (b := b) (c := c) (d := d)
        (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) bw
    refine
      ⟨((fun wt => ∑ zt : PVec n c, g.1 zt wt),
          fun yt => ∑ zt : PVec n c, g.2 yt zt), ?_⟩
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
      (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d)
      bw.1 bw.2 yt wt (i - vecSum yt) j (k - vecSum wt)] at hpoint
    rw [diamondCubeReindex_AConstraint
      (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d)
      A yt wt (i - vecSum yt) j (k - vecSum wt)] at hpoint
    change
      (cubeDiffP (∑ zt : PVec n c, g.1 zt wt) +
        cubeDiffR (∑ zt : PVec n c, g.2 yt zt)) i j k =
        cubeDiffJInv
          (∑ zt : PVec n c,
            aLiteralGaugeEquiv
              (by omega : 0 < b) (by omega : 0 < c)
              (by omega : 0 < d) A yt zt wt) i j k
    simp only [map_sum, Pi.add_apply, Finset.sum_apply]
    rw [← Finset.sum_add_distrib]
    simpa only [g, TotalEEEEInternal.literalGaugeEquiv,
      LinearEquiv.prodCongr_apply, Pi.add_apply,
      TotalEEEEInternal.bGauged_cubeDiffP_apply,
      TotalEEEEInternal.wGauged_cubeDiffR_apply,
      aLiteralGauge_cubeDiffJInv_apply,
      sub_add_cancel] using hpoint
  · rintro ⟨q, hq⟩
    let bf : PVec n c → PVec n d → CyclicCube n :=
      fun zt wt => if zt = zeroVec then q.1 wt else 0
    let wf : PVec n b → PVec n c → CyclicCube n :=
      fun yt zt => if zt = zeroVec then q.2 yt else 0
    let bw :=
      (TotalEEEEInternal.literalGaugeEquiv
        (n := n) (b := b) (c := c) (d := d)
        (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d)).symm (bf, wf)
    have hbw :
        TotalEEEEInternal.literalGaugeEquiv
            (n := n) (b := b) (c := c) (d := d)
            (by omega : 0 < b) (by omega : 0 < c)
            (by omega : 0 < d) bw =
          (bf, wf) :=
      (TotalEEEEInternal.literalGaugeEquiv
        (n := n) (b := b) (c := c) (d := d)
        (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d)).apply_symm_apply (bf, wf)
    have hBsum (wt : PVec n d) :
        (∑ zt : PVec n c, bf zt wt) = q.1 wt := by
      rw [Finset.sum_eq_single (zeroVec : PVec n c)]
      · simp [bf]
      · intro zt _ hzt
        simp [bf, hzt]
      · simp
    have hWsum (yt : PVec n b) :
        (∑ zt : PVec n c, wf yt zt) = q.2 yt := by
      rw [Finset.sum_eq_single (zeroVec : PVec n c)]
      · simp [wf]
      · intro zt _ hzt
        simp [wf, hzt]
      · simp
    refine ⟨bw, ?_⟩
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) (by omega : 0 < b)
    let ew := diamondVecHeadTailEquiv (n := n) (by omega : 0 < d)
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d)
      bw.1 bw.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [diamondCubeReindex_AConstraint
      (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d)
      A (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
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
          (∑ zt : PVec n c,
            aLiteralGaugeEquiv
              (by omega : 0 < b) (by omega : 0 < c)
              (by omega : 0 < d)
              A (ey y).2 zt (ew w).2)
          ((ey y).1 + vecSum (ey y).2) sz
          ((ew w).1 + vecSum (ew w).2) at hpoint'
    rw [← hBsum (ew w).2, ← hWsum (ey y).2] at hpoint'
    have hB := congrArg Prod.fst hbw
    have hW := congrArg Prod.snd hbw
    change
      (TotalEEEEInternal.literalGaugeEquiv
        (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d) bw).1 = bf at hB
    change
      (TotalEEEEInternal.literalGaugeEquiv
        (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d) bw).2 = wf at hW
    rw [← hB, ← hW] at hpoint'
    simp only [map_sum, Pi.add_apply, Finset.sum_apply] at hpoint'
    rw [← Finset.sum_add_distrib] at hpoint'
    simpa only [
      TotalEEEEInternal.literalGaugeEquiv,
      LinearEquiv.prodCongr_apply,
      TotalEEEEInternal.bGauged_cubeDiffP_apply,
      TotalEEEEInternal.wGauged_cubeDiffR_apply,
      aLiteralGauge_cubeDiffJInv_apply,
      add_sub_cancel_right] using hpoint'

/-! ## Ambient dual coordinates in frozen eight-sector order -/

noncomputable def zOuterEquiv
    {n b c d : Nat} [NeZero n] :
    (PVec n b → PVec n c → PVec n d → CyclicCube n) ≃ₗ[F]
      (PVec n c → PVec n b → PVec n d → CyclicCube n) where
  toFun f zt yt wt := f yt zt wt
  invFun f yt zt wt := f zt yt wt
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by
    funext zt yt wt i j k
    rfl

noncomputable def aZOuterGaugeEquiv
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    AFun4 n b c d ≃ₗ[F]
      (PVec n c → PVec n b → PVec n d → CyclicCube n) :=
  (aLiteralGaugeEquiv hb hc hd).trans
    (zOuterEquiv (n := n) (b := b) (c := c) (d := d))

noncomputable abbrev TotalEEEERawRightCoords
    (n b c d : Nat) [NeZero n] :=
  (T37RightP1.T37RightAmbientTarget n b d ×
      T37RightP1.T37RightAmbientTarget n b d) ×
    DiamondEvenAxisValueTailZero n c
      (T37RightP1.T37RightAmbientTarget n b d)

private local instance t37RightAmbientTargetAddCommMonoid
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (T37RightP1.T37RightAmbientTarget n b d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (DiamondEEOERightAmbient n))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
            (CyclicCube n × CyclicCube n) ×
          (DiamondEvenAxisValueTailZero n d
              (CyclicCube n × CyclicCube n) ×
            DiamondMixedTailZero n b d (CyclicCube n))))

private local instance t37RightAmbientTargetModule
    {n b d : Nat} [NeZero n] :
    Module F (T37RightP1.T37RightAmbientTarget n b d) :=
  @Prod.instModule F
    (DiamondEEOERightAmbient n)
    (DiamondEvenAxisValueTailZero n b
        (CyclicCube n × CyclicCube n) ×
      (DiamondEvenAxisValueTailZero n d
          (CyclicCube n × CyclicCube n) ×
        DiamondMixedTailZero n b d (CyclicCube n)))
    inferInstance
    (inferInstance : AddCommMonoid (DiamondEEOERightAmbient n))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
            (CyclicCube n × CyclicCube n) ×
          (DiamondEvenAxisValueTailZero n d
              (CyclicCube n × CyclicCube n) ×
            DiamondMixedTailZero n b d (CyclicCube n))))
    (inferInstance : Module F (DiamondEEOERightAmbient n))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n b
            (CyclicCube n × CyclicCube n) ×
          (DiamondEvenAxisValueTailZero n d
              (CyclicCube n × CyclicCube n) ×
            DiamondMixedTailZero n b d (CyclicCube n))))

private local instance rawRightCoordsAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEERawRightCoords n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (T37RightP1.T37RightAmbientTarget n b d ×
          T37RightP1.T37RightAmbientTarget n b d))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n c
          (T37RightP1.T37RightAmbientTarget n b d)))

private local instance rawRightCoordsModule
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEERawRightCoords n b c d) :=
  @Prod.instModule F
    (T37RightP1.T37RightAmbientTarget n b d ×
      T37RightP1.T37RightAmbientTarget n b d)
    (DiamondEvenAxisValueTailZero n c
      (T37RightP1.T37RightAmbientTarget n b d))
    inferInstance
    (inferInstance :
      AddCommMonoid
        (T37RightP1.T37RightAmbientTarget n b d ×
          T37RightP1.T37RightAmbientTarget n b d))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n c
          (T37RightP1.T37RightAmbientTarget n b d)))
    (inferInstance :
      Module F
        (T37RightP1.T37RightAmbientTarget n b d ×
          T37RightP1.T37RightAmbientTarget n b d))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n c
          (T37RightP1.T37RightAmbientTarget n b d)))

noncomputable def rawRightCoordinateEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    AFun4 n b c d ≃ₗ[F]
      TotalEEEERawRightCoords n b c d :=
  (aZOuterGaugeEquiv
      (n := n) (b := b) (c := c) (d := d)
      (by omega) (by omega) (by omega)).trans
    ((diamondEvenAxisDualCoordEquiv
        (n := n) (k := c)
        (PVec n b → PVec n d → CyclicCube n) hn hc2).trans
      ((TotalEOEEInternal.pointedHeadShear
          (zeroVec : PVec n c)).trans
        (((T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2).prodCongr
            (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2)).prodCongr
          (TotalEOEEInternal.tailZeroCongr
            (zeroVec : PVec n c)
            (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2)))))

private theorem cast_odd_eq_one
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, hq⟩
  rw [hq]
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

private theorem sum_at_point_add_tail
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

theorem axisDualHead_eq_totalSum
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
    sum_const_odd
      (odd_card_diamondEvenAxisTailIndex hn hk2)
      (g (zeroVec : PVec n k)),
    sum_at_point_add_tail (zeroVec : PVec n k) g]
  abel

theorem zDualHead_eq_totalSum
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (g : PVec n c → PVec n b → PVec n d → CyclicCube n) :
    ((TotalEOEEInternal.pointedHeadShear
      (zeroVec : PVec n c))
      (diamondEvenAxisDualCoordEquiv
        (n := n) (k := c)
        (PVec n b → PVec n d → CyclicCube n) hn hc2 g)).1.1 =
      ∑ zt : PVec n c, g zt := by
  exact
    axisDualHead_eq_totalSum
      (PVec n b → PVec n d → CyclicCube n) hn hc2 g

noncomputable def tailSwapEquiv
    (S T V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup V] [Module F V] :
    PointedValueTailZero S
        (PointedValueTailZero T V t0) s0 ≃ₗ[F]
      PointedValueTailZero T
        (PointedValueTailZero S V s0) t0 where
  toFun x :=
    ⟨fun tt =>
      ⟨fun ss => (x.1 ss).1 tt, by
        apply LinearMap.mem_ker.mpr
        change (∑ ss, (x.1 ss).1 tt) = 0
        have hx := pointedValueTailZero_sum x
        have hxv :
            (∑ ss, (x.1 ss).1) = 0 := by
          simpa only [Submodule.coe_sum] using
            congrArg Subtype.val hx
        have hxt := congrFun hxv tt
        simpa only [Finset.sum_apply, Pi.zero_apply] using hxt⟩,
      by
        apply LinearMap.mem_ker.mpr
        apply Subtype.ext
        simp only [fintypeSumLinearMap, LinearMap.coe_mk,
          AddHom.coe_mk]
        rw [Submodule.coe_sum]
        funext ss
        simpa only [Finset.sum_apply, Pi.zero_apply] using
          pointedValueTailZero_sum (x.1 ss)⟩
  invFun x :=
    ⟨fun ss =>
      ⟨fun tt => (x.1 tt).1 ss, by
        apply LinearMap.mem_ker.mpr
        change (∑ tt, (x.1 tt).1 ss) = 0
        have hx := pointedValueTailZero_sum x
        have hxv :
            (∑ tt, (x.1 tt).1) = 0 := by
          simpa only [Submodule.coe_sum] using
            congrArg Subtype.val hx
        have hxs := congrFun hxv ss
        simpa only [Finset.sum_apply, Pi.zero_apply] using hxs⟩,
      by
        apply LinearMap.mem_ker.mpr
        apply Subtype.ext
        simp only [fintypeSumLinearMap, LinearMap.coe_mk,
          AddHom.coe_mk]
        rw [Submodule.coe_sum]
        funext tt
        simpa only [Finset.sum_apply, Pi.zero_apply] using
          pointedValueTailZero_sum (x.1 tt)⟩
  left_inv x := by
    apply Subtype.ext
    funext ss
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    funext tt
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    funext tt
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    funext tt
    apply Subtype.ext
    rfl

noncomputable def scalarInterleaveEquiv
    {n : Nat} [NeZero n] :
    (DiamondEEOERightAmbient n × DiamondEEOERightAmbient n) ≃ₗ[F]
      DiamondEEEERightAmbient n where
  toFun q :=
    (((q.1.1.1, q.1.1.2), (q.2.1.1, q.2.1.2)),
      ((q.1.2.1, q.1.2.2), (q.2.2.1, q.2.2.2)))
  invFun q :=
    ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by
    ext <;> rfl

noncomputable def wInterleaveEquiv
    {n : Nat} [NeZero n] :
    ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)) where
  toFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def yPairEquiv
    {n b : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n b
        (CyclicCube n × CyclicCube n) ×
      DiamondEvenAxisValueTailZero n b
        (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      DiamondEvenAxisValueTailZero n b
        ((CyclicCube n × CyclicCube n) ×
          (CyclicCube n × CyclicCube n)) :=
  (TotalEOEEInternal.tailZeroProdEquiv
    (S := PVec n b)
    (U := CyclicCube n × CyclicCube n)
    (V := CyclicCube n × CyclicCube n)
    (zeroVec : PVec n b)).symm

noncomputable def wPairEquiv
    {n d : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n) ×
      DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      DiamondEvenAxisValueTailZero n d
        ((CyclicCube n × CyclicCube n) ×
          (CyclicCube n × CyclicCube n)) :=
  (TotalEOEEInternal.tailZeroProdEquiv
      (S := PVec n d)
      (U := CyclicCube n × CyclicCube n)
      (V := CyclicCube n × CyclicCube n)
      (zeroVec : PVec n d)).symm.trans
    (TotalEOEEInternal.tailZeroCongr
      (zeroVec : PVec n d)
      (wInterleaveEquiv (n := n)))

noncomputable def ywPairEquiv
    {n b d : Nat} [NeZero n] :
    (DiamondMixedTailZero n b d (CyclicCube n) ×
      DiamondMixedTailZero n b d (CyclicCube n)) ≃ₗ[F]
      DiamondMixedTailZero n b d
        (CyclicCube n × CyclicCube n) :=
  (TotalEOEEInternal.tailZeroProdEquiv
      (S := PVec n b)
      (U := DiamondEvenAxisValueTailZero n d (CyclicCube n))
      (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
      (zeroVec : PVec n b)).symm.trans
    (TotalEOEEInternal.tailZeroCongr
      (zeroVec : PVec n b)
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n d)
        (U := CyclicCube n) (V := CyclicCube n)
        (zeroVec : PVec n d)).symm)

noncomputable abbrev TotalEEEEHeadAmbientTarget
    (n b d : Nat) [NeZero n] :=
  DiamondEEEERightAmbient n ×
    (DiamondEvenAxisValueTailZero n b
        ((CyclicCube n × CyclicCube n) ×
          (CyclicCube n × CyclicCube n)) ×
      (DiamondEvenAxisValueTailZero n d
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n)) ×
        DiamondMixedTailZero n b d
          (CyclicCube n × CyclicCube n)))

private local instance headAmbientTargetAddCommMonoid
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEEHeadAmbientTarget n b d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (DiamondEEEERightAmbient n))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
            ((CyclicCube n × CyclicCube n) ×
              (CyclicCube n × CyclicCube n)) ×
          (DiamondEvenAxisValueTailZero n d
              ((CyclicCube n × CyclicCube n) ×
                (CyclicCube n × CyclicCube n)) ×
            DiamondMixedTailZero n b d
              (CyclicCube n × CyclicCube n))))

private local instance headAmbientTargetModule
    {n b d : Nat} [NeZero n] :
    Module F (TotalEEEEHeadAmbientTarget n b d) :=
  @Prod.instModule F
    (DiamondEEEERightAmbient n)
    (DiamondEvenAxisValueTailZero n b
        ((CyclicCube n × CyclicCube n) ×
          (CyclicCube n × CyclicCube n)) ×
      (DiamondEvenAxisValueTailZero n d
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n)) ×
        DiamondMixedTailZero n b d
          (CyclicCube n × CyclicCube n)))
    inferInstance
    (inferInstance : AddCommMonoid (DiamondEEEERightAmbient n))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
            ((CyclicCube n × CyclicCube n) ×
              (CyclicCube n × CyclicCube n)) ×
          (DiamondEvenAxisValueTailZero n d
              ((CyclicCube n × CyclicCube n) ×
                (CyclicCube n × CyclicCube n)) ×
            DiamondMixedTailZero n b d
              (CyclicCube n × CyclicCube n))))
    (inferInstance : Module F (DiamondEEEERightAmbient n))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n b
            ((CyclicCube n × CyclicCube n) ×
              (CyclicCube n × CyclicCube n)) ×
          (DiamondEvenAxisValueTailZero n d
              ((CyclicCube n × CyclicCube n) ×
                (CyclicCube n × CyclicCube n)) ×
            DiamondMixedTailZero n b d
              (CyclicCube n × CyclicCube n))))
noncomputable def headPairReassocEquiv
    {n b d : Nat} [NeZero n] :
    (T37RightP1.T37RightAmbientTarget n b d ×
      T37RightP1.T37RightAmbientTarget n b d) ≃ₗ[F]
      TotalEEEEHeadAmbientTarget n b d where
  toFun q :=
    (scalarInterleaveEquiv (q.1.1, q.2.1),
      (yPairEquiv (q.1.2.1, q.2.2.1),
        (wPairEquiv (q.1.2.2.1, q.2.2.2.1),
          ywPairEquiv (q.1.2.2.2, q.2.2.2.2))))
  invFun q :=
    let s := scalarInterleaveEquiv.symm q.1
    let y := yPairEquiv.symm q.2.1
    let w := wPairEquiv.symm q.2.2.1
    let yw := ywPairEquiv.symm q.2.2.2
    ((s.1, (y.1, (w.1, yw.1))),
      (s.2, (y.2, (w.2, yw.2))))
  left_inv q := by
    dsimp only
    rw [scalarInterleaveEquiv.symm_apply_apply,
      yPairEquiv.symm_apply_apply,
      wPairEquiv.symm_apply_apply,
      ywPairEquiv.symm_apply_apply]
  right_inv q := by
    dsimp only
    rw [scalarInterleaveEquiv.apply_symm_apply,
      yPairEquiv.apply_symm_apply,
      wPairEquiv.apply_symm_apply,
      ywPairEquiv.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable abbrev TotalEEEETailAmbientTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c
      (DiamondEEOERightAmbient n) ×
    (DiamondMixedTailZero n b c
        (CyclicCube n × CyclicCube n) ×
      (DiamondMixedTailZero n c d
          (CyclicCube n × CyclicCube n) ×
        DiamondEvenAxisValueTailZero n b
          (DiamondEvenAxisValueTailZero n c
            (DiamondEvenAxisValueTailZero n d
              (CyclicCube n)))))

private local instance tailAmbientTargetAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEETailAmbientTarget n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n)))
    (inferInstance :
      AddCommMonoid
        (DiamondMixedTailZero n b c
            (CyclicCube n × CyclicCube n) ×
          (DiamondMixedTailZero n c d
              (CyclicCube n × CyclicCube n) ×
            DiamondEvenAxisValueTailZero n b
              (DiamondEvenAxisValueTailZero n c
                (DiamondEvenAxisValueTailZero n d
                  (CyclicCube n))))))

private local instance tailAmbientTargetModule
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEETailAmbientTarget n b c d) :=
  @Prod.instModule F
    (DiamondEvenAxisValueTailZero n c
      (DiamondEEOERightAmbient n))
    (DiamondMixedTailZero n b c
        (CyclicCube n × CyclicCube n) ×
      (DiamondMixedTailZero n c d
          (CyclicCube n × CyclicCube n) ×
        DiamondEvenAxisValueTailZero n b
          (DiamondEvenAxisValueTailZero n c
            (DiamondEvenAxisValueTailZero n d
              (CyclicCube n)))))
    inferInstance
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n)))
    (inferInstance :
      AddCommMonoid
        (DiamondMixedTailZero n b c
            (CyclicCube n × CyclicCube n) ×
          (DiamondMixedTailZero n c d
              (CyclicCube n × CyclicCube n) ×
            DiamondEvenAxisValueTailZero n b
              (DiamondEvenAxisValueTailZero n c
                (DiamondEvenAxisValueTailZero n d
                  (CyclicCube n))))))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n)))
    (inferInstance :
      Module F
        (DiamondMixedTailZero n b c
            (CyclicCube n × CyclicCube n) ×
          (DiamondMixedTailZero n c d
              (CyclicCube n × CyclicCube n) ×
            DiamondEvenAxisValueTailZero n b
              (DiamondEvenAxisValueTailZero n c
                (DiamondEvenAxisValueTailZero n d
                  (CyclicCube n))))))
noncomputable abbrev TotalEEEETailSplitTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c
      (DiamondEEOERightAmbient n) ×
    (DiamondEvenAxisValueTailZero n c
        (DiamondEvenAxisValueTailZero n b
          (CyclicCube n × CyclicCube n)) ×
      (DiamondEvenAxisValueTailZero n c
          (DiamondEvenAxisValueTailZero n d
            (CyclicCube n × CyclicCube n)) ×
        DiamondEvenAxisValueTailZero n c
          (DiamondMixedTailZero n b d (CyclicCube n))))

noncomputable def tailT37SplitEquiv
    {n b c d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n c
        (T37RightP1.T37RightAmbientTarget n b d) ≃ₗ[F]
      TotalEEEETailSplitTarget n b c d :=
  (TotalEOEEInternal.tailZeroProdEquiv
      (S := PVec n c)
      (U := DiamondEEOERightAmbient n)
      (V :=
        DiamondEvenAxisValueTailZero n b
            (CyclicCube n × CyclicCube n) ×
          (DiamondEvenAxisValueTailZero n d
              (CyclicCube n × CyclicCube n) ×
            DiamondMixedTailZero n b d (CyclicCube n)))
      (zeroVec : PVec n c)).trans
    ((LinearEquiv.refl F
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n))).prodCongr
      ((TotalEOEEInternal.tailZeroProdEquiv
          (S := PVec n c)
          (U := DiamondEvenAxisValueTailZero n b
            (CyclicCube n × CyclicCube n))
          (V :=
            DiamondEvenAxisValueTailZero n d
                (CyclicCube n × CyclicCube n) ×
              DiamondMixedTailZero n b d (CyclicCube n))
          (zeroVec : PVec n c)).trans
        ((LinearEquiv.refl F
            (DiamondEvenAxisValueTailZero n c
              (DiamondEvenAxisValueTailZero n b
                (CyclicCube n × CyclicCube n)))).prodCongr
          (TotalEOEEInternal.tailZeroProdEquiv
            (S := PVec n c)
            (U := DiamondEvenAxisValueTailZero n d
              (CyclicCube n × CyclicCube n))
            (V := DiamondMixedTailZero n b d (CyclicCube n))
            (zeroVec : PVec n c)))))

noncomputable def tailT37ReassocEquiv
    {n b c d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n c
        (T37RightP1.T37RightAmbientTarget n b d) ≃ₗ[F]
      TotalEEEETailAmbientTarget n b c d :=
  (tailT37SplitEquiv
      (n := n) (b := b) (c := c) (d := d)).trans
    ((LinearEquiv.refl F
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n))).prodCongr
      ((tailSwapEquiv
          (PVec n c) (PVec n b)
          (CyclicCube n × CyclicCube n)
          (zeroVec : PVec n c)
          (zeroVec : PVec n b)).prodCongr
        ((LinearEquiv.refl F
            (DiamondMixedTailZero n c d
              (CyclicCube n × CyclicCube n))).prodCongr
          (tailSwapEquiv
            (PVec n c) (PVec n b)
            (DiamondEvenAxisValueTailZero n d (CyclicCube n))
            (zeroVec : PVec n c)
            (zeroVec : PVec n b)))))

noncomputable abbrev TotalEEEERightAmbientTailRest2Target
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c
      (DiamondEEOERightAmbient n) ×
    (DiamondMixedTailZero n b c
        (CyclicCube n × CyclicCube n) ×
      (DiamondMixedTailZero n c d
          (CyclicCube n × CyclicCube n) ×
        (DiamondMixedTailZero n b d
            (CyclicCube n × CyclicCube n) ×
          DiamondEvenAxisValueTailZero n b
            (DiamondEvenAxisValueTailZero n c
              (DiamondEvenAxisValueTailZero n d
                (CyclicCube n))))))

noncomputable abbrev TotalEEEERightAmbientTailRestTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n d
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)) ×
    TotalEEEERightAmbientTailRest2Target n b c d

noncomputable abbrev TotalEEEERightAmbientTailTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n b
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)) ×
    TotalEEEERightAmbientTailRestTarget n b c d

private local instance rightAmbientTailRestTargetAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEERightAmbientTailRestTarget n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n d
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n))))
    (inferInstance :
      AddCommMonoid
        (TotalEEEERightAmbientTailRest2Target n b c d))

private local instance rightAmbientTailRestTargetModule
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEERightAmbientTailRestTarget n b c d) :=
  @Prod.instModule F
    (DiamondEvenAxisValueTailZero n d
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)))
    (TotalEEEERightAmbientTailRest2Target n b c d)
    inferInstance
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n d
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n))))
    (inferInstance :
      AddCommMonoid
        (TotalEEEERightAmbientTailRest2Target n b c d))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n d
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n))))
    (inferInstance :
      Module F
        (TotalEEEERightAmbientTailRest2Target n b c d))

private local instance rightAmbientTailTargetAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEERightAmbientTailTarget n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n))))
    (inferInstance :
      AddCommMonoid
        (TotalEEEERightAmbientTailRestTarget n b c d))

private local instance rightAmbientTailTargetModule
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEERightAmbientTailTarget n b c d) :=
  @Prod.instModule F
    (DiamondEvenAxisValueTailZero n b
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n)))
    (TotalEEEERightAmbientTailRestTarget n b c d)
    inferInstance
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n))))
    (inferInstance :
      AddCommMonoid
        (TotalEEEERightAmbientTailRestTarget n b c d))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n b
          ((CyclicCube n × CyclicCube n) ×
            (CyclicCube n × CyclicCube n))))
    (inferInstance :
      Module F
        (TotalEEEERightAmbientTailRestTarget n b c d))

noncomputable abbrev TotalEEEERightAmbientTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEEEERightAmbient n ×
    TotalEEEERightAmbientTailTarget n b c d

private local instance rightAmbientTargetAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEERightAmbientTarget n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (DiamondEEEERightAmbient n))
    (inferInstance :
      AddCommMonoid (TotalEEEERightAmbientTailTarget n b c d))

private local instance rightAmbientTargetModule
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEERightAmbientTarget n b c d) :=
  @Prod.instModule F
    (DiamondEEEERightAmbient n)
    (TotalEEEERightAmbientTailTarget n b c d)
    inferInstance
    (inferInstance : AddCommMonoid (DiamondEEEERightAmbient n))
    (inferInstance :
      AddCommMonoid (TotalEEEERightAmbientTailTarget n b c d))
    (inferInstance : Module F (DiamondEEEERightAmbient n))
    (inferInstance :
      Module F (TotalEEEERightAmbientTailTarget n b c d))

noncomputable def branchReassocEquiv
    {n b c d : Nat} [NeZero n] :
    (TotalEEEEHeadAmbientTarget n b d ×
      TotalEEEETailAmbientTarget n b c d) ≃ₗ[F]
      TotalEEEERightAmbientTarget n b c d where
  toFun q :=
    (q.1.1,
      (q.1.2.1,
        (q.1.2.2.1,
          (q.2.1,
            (q.2.2.1,
              (q.2.2.2.1, (q.1.2.2.2, q.2.2.2.2)))))))
  invFun q :=
    ((q.1, (q.2.1, (q.2.2.1, q.2.2.2.2.2.2.1))),
      (q.2.2.2.1,
        (q.2.2.2.2.1,
          (q.2.2.2.2.2.1, q.2.2.2.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := by
    ext <;> rfl

noncomputable def rightAmbientEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    AFun4 n b c d ≃ₗ[F]
      TotalEEEERightAmbientTarget n b c d :=
  (rawRightCoordinateEquiv hn hb2 hc2 hd2).trans
    (((headPairReassocEquiv
        (n := n) (b := b) (d := d)).prodCongr
      (tailT37ReassocEquiv
        (n := n) (b := b) (c := c) (d := d))).trans
      (branchReassocEquiv
        (n := n) (b := b) (c := c) (d := d)))

theorem t37Range_iff_coordinateLedger
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (D : PVec n b → PVec n d → CyclicCube n) :
    (fun yt wt => cubeDiffJInv (D yt wt)) ∈
        LinearMap.range
          (totalEEEET37ConstraintMap
            (n := n) (b := b) (d := d)) ↔
      T37RightP1.T37RightCoordinateLedger
        (T37RightP1.t37GaugedRightCoordinateEquiv
          hn hb2 hd2 D) := by
  exact
    (T37RightP1.t37GaugedRange_iff_rawCoordinateLedger
      hn hb2 hd2 (fun yt wt => cubeDiffJInv (D yt wt))).trans
      (T37RightP1.t37RawLedger_J_iff_coordinateLedger
        hn hb2 hd2 D)

@[simp] theorem rawRightCoordinateEquiv_D
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n b c d) :
    (rawRightCoordinateEquiv hn hb2 hc2 hd2 A).1.1 =
      T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2
        ((TotalEOEEInternal.pointedHeadShear
          (zeroVec : PVec n c))
          (diamondEvenAxisDualCoordEquiv
            (n := n) (k := c)
            (PVec n b → PVec n d → CyclicCube n) hn hc2
            (aZOuterGaugeEquiv
              (n := n) (b := b) (c := c) (d := d)
              (by omega : 0 < b) (by omega : 0 < c)
      (by omega : 0 < d) A))).1.1 :=
  rfl

theorem rawRightCoordinateHead_eq_literal_sum
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (hb0 : 0 < b) (hd0 : 0 < d)
    (A : AFun4 n b c d) :
    ((TotalEOEEInternal.pointedHeadShear
      (zeroVec : PVec n c))
      (diamondEvenAxisDualCoordEquiv
        (n := n) (k := c)
        (PVec n b → PVec n d → CyclicCube n) hn hc2
        (aZOuterGaugeEquiv
          (n := n) (b := b) (c := c) (d := d)
          hb0 (by omega : 0 < c) hd0 A))).1.1 =
      fun yt wt =>
        ∑ zt : PVec n c,
          aLiteralGaugeEquiv hb0 (by omega : 0 < c) hd0 A yt zt wt := by
  rw [zDualHead_eq_totalSum]
  funext yt wt
  simp only [Finset.sum_apply]
  rfl

theorem literal_reachable_iff_raw_D_ledger
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n b c d) :
    A ∈ DiamondEvenPReachableA n b c d ↔
      T37RightP1.T37RightCoordinateLedger
        (rawRightCoordinateEquiv hn hb2 hc2 hd2 A).1.1 := by
  rw [literal_reachable_iff_Ztotal_t37_range hb2 hc2 hd2 A]
  rw [rawRightCoordinateEquiv_D]
  rw [← t37Range_iff_coordinateLedger hn hb2 hd2]
  rw [rawRightCoordinateHead_eq_literal_sum
    hn hc2 (by omega : 0 < b) (by omega : 0 < d) A]

/-! ## Restrict the unique complete-`Z` coordinate -/

noncomputable def t37RightLedgerSubmodule
    (n b d : Nat) [NeZero n] :
    Submodule F (T37RightP1.T37RightAmbientTarget n b d) where
  carrier := {q | T37RightP1.T37RightCoordinateLedger q}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_, ?_, ?_⟩
    · intro yt
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    · intro wt
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    · intro yt wt
      exact Submodule.zero_mem _
  add_mem' := by
    rintro q r ⟨hq0, hqY, hqW, hqYW⟩
      ⟨hr0, hrY, hrW, hrYW⟩
    refine ⟨Submodule.add_mem _ hq0 hr0, ?_, ?_, ?_⟩
    · intro yt
      exact
        ⟨Submodule.add_mem _ (hqY yt).1 (hrY yt).1,
          Submodule.add_mem _ (hqY yt).2 (hrY yt).2⟩
    · intro wt
      exact
        ⟨Submodule.add_mem _ (hqW wt).1 (hrW wt).1,
          Submodule.add_mem _ (hqW wt).2 (hrW wt).2⟩
    · intro yt wt
      exact Submodule.add_mem _ (hqYW yt wt) (hrYW yt wt)
  smul_mem' := by
    rintro r q ⟨hq0, hqY, hqW, hqYW⟩
    refine ⟨Submodule.smul_mem _ r hq0, ?_, ?_, ?_⟩
    · intro yt
      exact
        ⟨Submodule.smul_mem _ r (hqY yt).1,
          Submodule.smul_mem _ r (hqY yt).2⟩
    · intro wt
      exact
        ⟨Submodule.smul_mem _ r (hqW wt).1,
          Submodule.smul_mem _ r (hqW wt).2⟩
    · intro yt wt
      exact Submodule.smul_mem _ r (hqYW yt wt)

noncomputable def t37LedgerAmbientToReachableSourceEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    t37RightLedgerSubmodule n b d ≃ₗ[F]
      DiamondEvenPReachableA n b 1 d where
  toFun q :=
    ⟨(T37RightP1.t37RightAmbientEquiv hn hb2 hd2).symm q.1,
      (T37RightP1.t37LiteralRight_mem_iff_coordinateLedger
        hn hb2 hd2
        ((T37RightP1.t37RightAmbientEquiv
          hn hb2 hd2).symm q.1)).mpr (by
          rw [(T37RightP1.t37RightAmbientEquiv
            hn hb2 hd2).apply_symm_apply]
          exact q.2)⟩
  invFun A :=
    ⟨T37RightP1.t37RightAmbientEquiv hn hb2 hd2 A.1,
      (T37RightP1.t37LiteralRight_mem_iff_coordinateLedger
        hn hb2 hd2 A.1).mp A.2⟩
  left_inv q := by
    apply Subtype.ext
    exact
      (T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).apply_symm_apply q.1
  right_inv A := by
    apply Subtype.ext
    exact
      (T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).symm_apply_apply A.1
  map_add' q r := by
    apply Subtype.ext
    exact
      (T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).symm.map_add q.1 r.1
  map_smul' r q := by
    apply Subtype.ext
    exact
      (T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).symm.map_smul r q.1

noncomputable def t37LedgerAmbientToReachableTargetEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    t37RightLedgerSubmodule n b d ≃ₗ[F]
      T37RightP1.T37RightReachableTarget n b d :=
  (t37LedgerAmbientToReachableSourceEquiv hn hb2 hd2).trans
    (T37RightP1.t37RightReachableEquiv hn hb2 hd2)

noncomputable abbrev TotalEEEERestrictedRawTarget
    (n b c d : Nat) [NeZero n] :=
  (t37RightLedgerSubmodule n b d ×
      T37RightP1.T37RightAmbientTarget n b d) ×
    DiamondEvenAxisValueTailZero n c
      (T37RightP1.T37RightAmbientTarget n b d)

noncomputable def rawRightRestrictedEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b c d ≃ₗ[F]
      TotalEEEERestrictedRawTarget n b c d where
  toFun A :=
    let raw := rawRightCoordinateEquiv hn hb2 hc2 hd2 A.1
    ((⟨raw.1.1,
        (literal_reachable_iff_raw_D_ledger
          hn hb2 hc2 hd2 A.1).mp A.2⟩,
      raw.1.2), raw.2)
  invFun q :=
    let raw : TotalEEEERawRightCoords n b c d :=
      ((q.1.1.1, q.1.2), q.2)
    let A := (rawRightCoordinateEquiv hn hb2 hc2 hd2).symm raw
    ⟨A, (literal_reachable_iff_raw_D_ledger
      hn hb2 hc2 hd2 A).mpr (by
        have hread :
            rawRightCoordinateEquiv hn hb2 hc2 hd2 A = raw :=
          (rawRightCoordinateEquiv
            hn hb2 hc2 hd2).apply_symm_apply raw
        rw [hread]
        exact q.1.1.2)⟩
  left_inv A := by
    apply Subtype.ext
    exact
      (rawRightCoordinateEquiv
        hn hb2 hc2 hd2).symm_apply_apply A.1
  right_inv q := by
    have hread :=
      (rawRightCoordinateEquiv
        hn hb2 hc2 hd2).apply_symm_apply
          (((q.1.1.1, q.1.2), q.2) :
            TotalEEEERawRightCoords n b c d)
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun raw => raw.1.1) hread
      · exact congrArg (fun raw => raw.1.2) hread
    · change
        (rawRightCoordinateEquiv hn hb2 hc2 hd2
          ((rawRightCoordinateEquiv hn hb2 hc2 hd2).symm
            (((q.1.1.1, q.1.2), q.2) :
              TotalEEEERawRightCoords n b c d))).2 = q.2
      exact congrArg Prod.snd hread
  map_add' A A' := by
    have hread :=
      (rawRightCoordinateEquiv
        hn hb2 hc2 hd2).map_add A.1 A'.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun raw => raw.1.1) hread
      · exact congrArg (fun raw => raw.1.2) hread
    · change
        (rawRightCoordinateEquiv hn hb2 hc2 hd2
          (A.1 + A'.1)).2 =
          (rawRightCoordinateEquiv hn hb2 hc2 hd2 A.1).2 +
            (rawRightCoordinateEquiv hn hb2 hc2 hd2 A'.1).2
      exact congrArg Prod.snd hread
  map_smul' r A := by
    have hread :=
      (rawRightCoordinateEquiv
        hn hb2 hc2 hd2).map_smul r A.1
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun raw => raw.1.1) hread
      · exact congrArg (fun raw => raw.1.2) hread
    · change
        (rawRightCoordinateEquiv hn hb2 hc2 hd2
          (r • A.1)).2 =
          r • (rawRightCoordinateEquiv hn hb2 hc2 hd2 A.1).2
      exact congrArg Prod.snd hread

/-! ## Constrained complete-`Z` coordinate plus free complement -/

noncomputable abbrev YRightBase
    (n : Nat) [NeZero n] :=
  (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
    (CyclicCube n × CyclicCube n)

noncomputable abbrev WRightBase
    (n : Nat) [NeZero n] :=
  (T37RightP1.T37JKernel n × CyclicCube n) ×
    (EEOEInternal.PReachRight n × CyclicCube n)

noncomputable abbrev YWRightBase
    (n : Nat) [NeZero n] :=
  T37RightP1.T37JKernel n × CyclicCube n

noncomputable def scalarConstrainedFreeEquiv
    {n : Nat} [NeZero n] :
    (DiamondEEOERightSource n × DiamondEEOERightAmbient n) ≃ₗ[F]
      DiamondEEEERightSource n where
  toFun q :=
    ⟨(((q.1.1.1.1, q.1.1.1.2), (q.2.1.1, q.2.1.2)),
       ((q.1.1.2.1, q.1.1.2.2), (q.2.2.1, q.2.2.2))),
      q.1.2⟩
  invFun q :=
    (⟨(q.1.1.1, q.1.2.1), q.2⟩,
      (q.1.1.2, q.1.2.2))
  left_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv q := by
    apply Subtype.ext
    rfl
  map_add' q r := by
    apply Subtype.ext
    rfl
  map_smul' r q := by
    apply Subtype.ext
    rfl

noncomputable def wRestrictedInterleaveEquiv
    {n : Nat} [NeZero n] :
    ((T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
      (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      WRightBase n where
  toFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def yConstrainedFreeEquiv
    {n b : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n b
        (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
      DiamondEvenAxisValueTailZero n b
        (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      DiamondEvenAxisValueTailZero n b (YRightBase n) :=
  (TotalEOEEInternal.tailZeroProdEquiv
    (S := PVec n b)
    (U := T37RightP1.T37JKernel n × EEOEInternal.RReachRight n)
    (V := CyclicCube n × CyclicCube n)
    (zeroVec : PVec n b)).symm

noncomputable def wConstrainedFreeEquiv
    {n d : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n d
        (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
      DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      DiamondEvenAxisValueTailZero n d (WRightBase n) :=
  (TotalEOEEInternal.tailZeroProdEquiv
      (S := PVec n d)
      (U := T37RightP1.T37JKernel n × EEOEInternal.PReachRight n)
      (V := CyclicCube n × CyclicCube n)
      (zeroVec : PVec n d)).symm.trans
    (TotalEOEEInternal.tailZeroCongr
      (zeroVec : PVec n d)
      (wRestrictedInterleaveEquiv (n := n)))

noncomputable def ywConstrainedFreeEquiv
    {n b d : Nat} [NeZero n] :
    (DiamondMixedTailZero n b d (T37RightP1.T37JKernel n) ×
      DiamondMixedTailZero n b d (CyclicCube n)) ≃ₗ[F]
      DiamondMixedTailZero n b d (YWRightBase n) :=
  (TotalEOEEInternal.tailZeroProdEquiv
      (S := PVec n b)
      (U :=
        DiamondEvenAxisValueTailZero n d
          (T37RightP1.T37JKernel n))
      (V := DiamondEvenAxisValueTailZero n d (CyclicCube n))
      (zeroVec : PVec n b)).symm.trans
    (TotalEOEEInternal.tailZeroCongr
      (zeroVec : PVec n b)
      (TotalEOEEInternal.tailZeroProdEquiv
        (S := PVec n d)
        (U := T37RightP1.T37JKernel n)
        (V := CyclicCube n)
        (zeroVec : PVec n d)).symm)

noncomputable abbrev TotalEEEEHeadReachableTarget
    (n b d : Nat) [NeZero n] :=
  DiamondEEEERightSource n ×
    (DiamondEvenAxisValueTailZero n b (YRightBase n) ×
      (DiamondEvenAxisValueTailZero n d (WRightBase n) ×
        DiamondMixedTailZero n b d (YWRightBase n)))

@[reducible] private noncomputable def
    t37ReachableTargetAddCommMonoid
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (T37RightP1.T37RightReachableTarget n b d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (DiamondEEOERightSource n))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
            (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
          (DiamondEvenAxisValueTailZero n d
              (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
            DiamondMixedTailZero n b d (T37RightP1.T37JKernel n))))

private local instance
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (T37RightP1.T37RightReachableTarget n b d) :=
  t37ReachableTargetAddCommMonoid

private local instance
    {n b d : Nat} [NeZero n] :
    Module F (T37RightP1.T37RightReachableTarget n b d) :=
  @Prod.instModule F
    (DiamondEEOERightSource n)
    (DiamondEvenAxisValueTailZero n b
        (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
      (DiamondEvenAxisValueTailZero n d
          (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
        DiamondMixedTailZero n b d (T37RightP1.T37JKernel n)))
    inferInstance
    (inferInstance : AddCommMonoid (DiamondEEOERightSource n))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
            (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
          (DiamondEvenAxisValueTailZero n d
              (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
            DiamondMixedTailZero n b d (T37RightP1.T37JKernel n))))
    (inferInstance : Module F (DiamondEEOERightSource n))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n b
            (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
          (DiamondEvenAxisValueTailZero n d
              (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
            DiamondMixedTailZero n b d (T37RightP1.T37JKernel n))))

noncomputable abbrev ConstrainedFreeHeadInput
    (n b d : Nat) [NeZero n] :=
  T37RightP1.T37RightReachableTarget n b d ×
    T37RightP1.T37RightAmbientTarget n b d

@[reducible] private noncomputable def
    constrainedFreeHeadInputAddCommMonoid
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (ConstrainedFreeHeadInput n b d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid (T37RightP1.T37RightReachableTarget n b d))
    (inferInstance :
      AddCommMonoid (T37RightP1.T37RightAmbientTarget n b d))

private local instance
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (ConstrainedFreeHeadInput n b d) :=
  constrainedFreeHeadInputAddCommMonoid

private local instance
    {n b d : Nat} [NeZero n] :
    Module F (ConstrainedFreeHeadInput n b d) :=
  @Prod.instModule F
    (T37RightP1.T37RightReachableTarget n b d)
    (T37RightP1.T37RightAmbientTarget n b d)
    inferInstance
    (inferInstance :
      AddCommMonoid (T37RightP1.T37RightReachableTarget n b d))
    (inferInstance :
      AddCommMonoid (T37RightP1.T37RightAmbientTarget n b d))
    (inferInstance :
      Module F (T37RightP1.T37RightReachableTarget n b d))
    (inferInstance :
      Module F (T37RightP1.T37RightAmbientTarget n b d))

noncomputable def headConstrainedFreeEquiv
    {n b d : Nat} [NeZero n] :
    ConstrainedFreeHeadInput n b d ≃ₗ[F]
      TotalEEEEHeadReachableTarget n b d where
  toFun q :=
    (scalarConstrainedFreeEquiv (q.1.1, q.2.1),
      (yConstrainedFreeEquiv (q.1.2.1, q.2.2.1),
        (wConstrainedFreeEquiv (q.1.2.2.1, q.2.2.2.1),
          ywConstrainedFreeEquiv (q.1.2.2.2, q.2.2.2.2))))
  invFun q :=
    let s := scalarConstrainedFreeEquiv.symm q.1
    let y := yConstrainedFreeEquiv.symm q.2.1
    let w := wConstrainedFreeEquiv.symm q.2.2.1
    let yw := ywConstrainedFreeEquiv.symm q.2.2.2
    ((s.1, (y.1, (w.1, yw.1))),
      (s.2, (y.2, (w.2, yw.2))))
  left_inv q := by
    dsimp only
    rw [scalarConstrainedFreeEquiv.symm_apply_apply,
      yConstrainedFreeEquiv.symm_apply_apply,
      wConstrainedFreeEquiv.symm_apply_apply,
      ywConstrainedFreeEquiv.symm_apply_apply]
  right_inv q := by
    dsimp only
    rw [scalarConstrainedFreeEquiv.apply_symm_apply,
      yConstrainedFreeEquiv.apply_symm_apply,
      wConstrainedFreeEquiv.apply_symm_apply,
      ywConstrainedFreeEquiv.apply_symm_apply]
  map_add' q r := by
    apply Prod.ext
    · exact
        (scalarConstrainedFreeEquiv (n := n)).map_add
          (q.1.1, q.2.1) (r.1.1, r.2.1)
    · apply Prod.ext
      · exact
          (yConstrainedFreeEquiv (n := n) (b := b)).map_add
            (q.1.2.1, q.2.2.1) (r.1.2.1, r.2.2.1)
      · apply Prod.ext
        · exact
            (wConstrainedFreeEquiv (n := n) (d := d)).map_add
              (q.1.2.2.1, q.2.2.2.1)
              (r.1.2.2.1, r.2.2.2.1)
        · exact
            (ywConstrainedFreeEquiv
              (n := n) (b := b) (d := d)).map_add
                (q.1.2.2.2, q.2.2.2.2)
                (r.1.2.2.2, r.2.2.2.2)
  map_smul' r q := by
    apply Prod.ext
    · exact
        (scalarConstrainedFreeEquiv (n := n)).map_smul
          r (q.1.1, q.2.1)
    · apply Prod.ext
      · exact
          (yConstrainedFreeEquiv (n := n) (b := b)).map_smul
            r (q.1.2.1, q.2.2.1)
      · apply Prod.ext
        · exact
            (wConstrainedFreeEquiv (n := n) (d := d)).map_smul
              r (q.1.2.2.1, q.2.2.2.1)
        · exact
            (ywConstrainedFreeEquiv
              (n := n) (b := b) (d := d)).map_smul
                r (q.1.2.2.2, q.2.2.2.2)

end TotalEEEERightInternal

noncomputable abbrev TotalEEEERightReachableTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEEEERightSource n ×
    (DiamondEvenAxisValueTailZero n b
        (TotalEEEERightInternal.YRightBase n) ×
      (DiamondEvenAxisValueTailZero n d
          (TotalEEEERightInternal.WRightBase n) ×
        (DiamondEvenAxisValueTailZero n c
            (DiamondEEOERightAmbient n) ×
          (DiamondMixedTailZero n b c
              (CyclicCube n × CyclicCube n) ×
            (DiamondMixedTailZero n c d
                (CyclicCube n × CyclicCube n) ×
              (DiamondMixedTailZero n b d
                  (TotalEEEERightInternal.YWRightBase n) ×
                DiamondEvenAxisValueTailZero n b
                  (DiamondEvenAxisValueTailZero n c
                    (DiamondEvenAxisValueTailZero n d
                      (CyclicCube n)))))))))

namespace TotalEEEERightInternal

private local instance
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (T37RightP1.T37RightAmbientTarget n b d) :=
  t37RightAmbientTargetAddCommMonoid

private local instance
    {n b d : Nat} [NeZero n] :
    Module F (T37RightP1.T37RightAmbientTarget n b d) :=
  t37RightAmbientTargetModule

private local instance
    {n b d : Nat} [NeZero n] :
    AddCommMonoid (T37RightP1.T37RightReachableTarget n b d) :=
  t37ReachableTargetAddCommMonoid

private local instance
    {n b d : Nat} [NeZero n] :
    Module F (T37RightP1.T37RightReachableTarget n b d) :=
  @Prod.instModule F
    (DiamondEEOERightSource n)
    (DiamondEvenAxisValueTailZero n b
        (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
      (DiamondEvenAxisValueTailZero n d
          (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
        DiamondMixedTailZero n b d (T37RightP1.T37JKernel n)))
    inferInstance
    (inferInstance : AddCommMonoid (DiamondEEOERightSource n))
    (inferInstance :
      AddCommMonoid
        (DiamondEvenAxisValueTailZero n b
            (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
          (DiamondEvenAxisValueTailZero n d
              (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
            DiamondMixedTailZero n b d (T37RightP1.T37JKernel n))))
    (inferInstance : Module F (DiamondEEOERightSource n))
    (inferInstance :
      Module F
        (DiamondEvenAxisValueTailZero n b
            (T37RightP1.T37JKernel n × EEOEInternal.RReachRight n) ×
          (DiamondEvenAxisValueTailZero n d
              (T37RightP1.T37JKernel n × EEOEInternal.PReachRight n) ×
            DiamondMixedTailZero n b d (T37RightP1.T37JKernel n))))

noncomputable abbrev ConstrainedZTotalFreeInput
    (n b c d : Nat) [NeZero n] :=
  ConstrainedFreeHeadInput n b d ×
    TotalEEEETailAmbientTarget n b c d

noncomputable def branchRestrictedReassocEquiv
    {n b c d : Nat} [NeZero n] :
    (TotalEEEEHeadReachableTarget n b d ×
      TotalEEEETailAmbientTarget n b c d) ≃ₗ[F]
      TotalEEEERightReachableTarget n b c d where
  toFun q :=
    (q.1.1,
      (q.1.2.1,
        (q.1.2.2.1,
          (q.2.1,
            (q.2.2.1,
              (q.2.2.2.1, (q.1.2.2.2, q.2.2.2.2)))))))
  invFun q :=
    ((q.1, (q.2.1, (q.2.2.1, q.2.2.2.2.2.2.1))),
      (q.2.2.2.1,
        (q.2.2.2.2.1,
          (q.2.2.2.2.2.1, q.2.2.2.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def restrictedCoordinateToConstrainedFreeEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    TotalEEEERestrictedRawTarget n b c d ≃ₗ[F]
      ConstrainedZTotalFreeInput n b c d :=
  (((t37LedgerAmbientToReachableTargetEquiv
      hn hb2 hd2).prodCongr
    (LinearEquiv.refl F
      (T37RightP1.T37RightAmbientTarget n b d))).prodCongr
    (tailT37ReassocEquiv
      (n := n) (b := b) (c := c) (d := d)))

noncomputable def constrainedZTotalFreeEquiv
    {n b c d : Nat} [NeZero n] :
    ConstrainedZTotalFreeInput n b c d ≃ₗ[F]
      TotalEEEERightReachableTarget n b c d :=
  ((headConstrainedFreeEquiv
      (n := n) (b := b) (d := d)).prodCongr
    (LinearEquiv.refl F
      (TotalEEEETailAmbientTarget n b c d))).trans
    (branchRestrictedReassocEquiv
      (n := n) (b := b) (c := c) (d := d))

theorem constrainedZTotalFree_forget_pack
    {n b c d : Nat} [NeZero n]
    (q : ConstrainedZTotalFreeInput n b c d) :
    (constrainedZTotalFreeEquiv
        (n := n) (b := b) (c := c) (d := d)).symm
        (constrainedZTotalFreeEquiv
          (n := n) (b := b) (c := c) (d := d) q) = q :=
  (constrainedZTotalFreeEquiv
    (n := n) (b := b) (c := c) (d := d)).symm_apply_apply q

theorem constrainedZTotalFree_pack_forget
    {n b c d : Nat} [NeZero n]
    (q : TotalEEEERightReachableTarget n b c d) :
    constrainedZTotalFreeEquiv
        (n := n) (b := b) (c := c) (d := d)
        ((constrainedZTotalFreeEquiv
          (n := n) (b := b) (c := c) (d := d)).symm q) = q :=
  (constrainedZTotalFreeEquiv
    (n := n) (b := b) (c := c) (d := d)).apply_symm_apply q

end TotalEEEERightInternal

theorem totalEEEERight_mem_iff_coordinateLedger
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n b c d) :
    A ∈ DiamondEvenPReachableA n b c d ↔
      T37RightP1.T37RightCoordinateLedger
        (TotalEEEERightInternal.rawRightCoordinateEquiv
          hn hb2 hc2 hd2 A).1.1 :=
  TotalEEEERightInternal.literal_reachable_iff_raw_D_ledger
    hn hb2 hc2 hd2 A

noncomputable def diamondEvenPReachableAEEEEEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b c d ≃ₗ[F]
      TotalEEEERightReachableTarget n b c d :=
  ((TotalEEEERightInternal.rawRightRestrictedEquiv
      hn hb2 hc2 hd2).trans
    (TotalEEEERightInternal.restrictedCoordinateToConstrainedFreeEquiv
      hn hb2 hd2)).trans
    (TotalEEEERightInternal.constrainedZTotalFreeEquiv
      (n := n) (b := b) (c := c) (d := d))

end

end Core4loop.SquareDiagonal.EvenP
