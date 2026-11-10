import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RootGauge
import Core4loop.SquareDiagonal.EvenP.TotalEEOE.LeftSource
import Core4loop.SquareDiagonal.EvenP.EEEE.Definitions

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEEEEInternal

/-!
# The literal all-even left source

This file is the P0 source-coordinate layer only.  It keeps the complete
literal `Z` sum and all passive cube coordinates.  It contains no right
source, phase, range, or rank theorem.
-/

noncomputable def cubeIJShiftEquiv
    {n : Nat} [NeZero n] (u v : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X (i - u) (j - v) k
  invFun X i j k := X (i + u) (j + v) k
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def ijGaugeBiFamilyEquiv
    {n b c : Nat} [NeZero n] :
    (PVec n b → PVec n c → CyclicCube n) ≃ₗ[F]
      (PVec n b → PVec n c → CyclicCube n) where
  toFun f yt zt :=
    cubeIJShiftEquiv (vecSum yt) (vecSum zt) (f yt zt)
  invFun f yt zt :=
    (cubeIJShiftEquiv (vecSum yt) (vecSum zt)).symm (f yt zt)
  left_inv f := by
    funext yt zt
    exact
      (cubeIJShiftEquiv
        (vecSum yt) (vecSum zt)).symm_apply_apply (f yt zt)
  right_inv f := by
    funext yt zt
    exact
      (cubeIJShiftEquiv
        (vecSum yt) (vecSum zt)).apply_symm_apply (f yt zt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def wGaugedYZFamilyEquiv
    {n b c : Nat} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    WFun4 n 1 b c ≃ₗ[F]
      (PVec n b → PVec n c → CyclicCube n) :=
  (diamondWRootCubeEquiv hb hc).trans
    (ijGaugeBiFamilyEquiv (n := n) (b := b) (c := c))

@[simp] theorem wGaugedYZFamilyEquiv_apply
    {n b c : Nat} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n 1 b c) (yt : PVec n b) (zt : PVec n c)
    (i j k : I n) :
    wGaugedYZFamilyEquiv hb hc W yt zt i j k =
      diamondWRootCubeEquiv hb hc W yt zt
        (i - vecSum yt) (j - vecSum zt) k :=
  rfl

@[simp] theorem cubeJKShift_cubeDiffP_apply
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffP (TotalEOEEInternal.cubeJKShiftEquiv u v X) i j k =
      cubeDiffP X i (j - u) (k - v) := by
  rw [EEOEInternal.cubeDiffP_apply, EEOEInternal.cubeDiffP_apply]
  simp only [TotalEOEEInternal.cubeJKShiftEquiv_apply]
  congr 2
  abel

@[simp] theorem cubeIJShift_cubeDiffR_apply
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffR (cubeIJShiftEquiv u v X) i j k =
      cubeDiffR X (i - u) (j - v) k := by
  rw [EEOEInternal.cubeDiffR_apply, EEOEInternal.cubeDiffR_apply]
  change
    X (i - u) (j - v) k +
        X (i - u) ((j - 1) - v) (k + 1) =
      X (i - u) (j - v) k +
        X (i - u) ((j - v) - 1) (k + 1)
  congr 2
  abel

@[simp] theorem bGauged_cubeDiffP_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    cubeDiffP
        (TotalEOEEInternal.bGaugedRootFamilyEquiv hc hd B zt wt)
        i j k =
      cubeDiffP
        (diamondBRootCubeEquiv hc hd B zt wt)
        i (j - vecSum zt) (k - vecSum wt) := by
  exact
    cubeJKShift_cubeDiffP_apply
      (vecSum zt) (vecSum wt)
      (diamondBRootCubeEquiv hc hd B zt wt) i j k

@[simp] theorem wGauged_cubeDiffR_apply
    {n b c : Nat} [NeZero n] (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n 1 b c) (yt : PVec n b) (zt : PVec n c)
    (i j k : I n) :
    cubeDiffR
        (wGaugedYZFamilyEquiv hb hc W yt zt)
        i j k =
      cubeDiffR
        (diamondWRootCubeEquiv hb hc W yt zt)
        (i - vecSum yt) (j - vecSum zt) k := by
  exact
    cubeIJShift_cubeDiffR_apply
      (vecSum yt) (vecSum zt)
      (diamondWRootCubeEquiv hb hc W yt zt) i j k

/-- The exact literal gauge.  The `B` family is `Z` outer and `W` inner;
the `W` family is `Y` outer and `Z` inner. -/
noncomputable def literalGaugeEquiv
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (BFun4 n 1 c d × WFun4 n 1 b c) ≃ₗ[F]
      ((PVec n c → PVec n d → CyclicCube n) ×
        (PVec n b → PVec n c → CyclicCube n)) :=
  (TotalEOEEInternal.bGaugedRootFamilyEquiv hc hd).prodCongr
    (wGaugedYZFamilyEquiv hb hc)

/-- Literal source membership after the root gauge.  The constraint is a
sum over the complete `Z` field, not a pointwise-`Z` equation. -/
theorem literal_mem_iff_uniform
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    x ∈ DiamondEvenPLeft n b c d ↔
      ∀ yt : PVec n b, ∀ wt : PVec n d,
        cubeDiffP
            (∑ zt : PVec n c,
              (literalGaugeEquiv hb hc hd x).1 zt wt) +
          cubeDiffR
            (∑ zt : PVec n c,
              (literalGaugeEquiv hb hc hd x).2 yt zt) = 0 := by
  simp only [DiamondEvenPLeft, LinearMap.mem_ker]
  constructor
  · intro hx yt wt
    funext i j k
    rw [map_sum, map_sum, ← Finset.sum_add_distrib,
      Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hx (zeroVec : PVec n 1))
            ((diamondVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt)))
          j)
        ((diamondVecHeadTailEquiv hd).symm
          (k - vecSum wt, wt))
    rw [diamondCubeReindex_squareCompat
      hb hc hd x.1 x.2 yt wt
      (i - vecSum yt) j (k - vecSum wt)] at hpoint
    simpa only [literalGaugeEquiv, LinearEquiv.prodCongr_apply,
      Pi.add_apply, bGauged_cubeDiffP_apply,
      wGauged_cubeDiffR_apply, Pi.zero_apply,
      sub_add_cancel] using hpoint
  · intro h
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) hb
    let ew := diamondVecHeadTailEquiv (n := n) hd
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      hb hc hd x.1 x.2
      (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (h (ey y).2 (ew w).2)
            ((ey y).1 + vecSum (ey y).2))
          sz)
        ((ew w).1 + vecSum (ew w).2)
    rw [map_sum, map_sum, ← Finset.sum_add_distrib,
      Finset.sum_apply, Finset.sum_apply, Finset.sum_apply] at hpoint
    simpa only [literalGaugeEquiv, LinearEquiv.prodCongr_apply,
      Pi.add_apply, bGauged_cubeDiffP_apply,
      wGauged_cubeDiffR_apply, Pi.zero_apply,
      add_sub_cancel_right] using hpoint

noncomputable abbrev NestedCoords
    (n s t : Nat) [NeZero n] :=
  TotalEOEEInternal.TailCoordHelpers.NestedSrcEvenTarget
    (PVec n s) (PVec n t) (CyclicCube n)
    (zeroVec : PVec n s) (zeroVec : PVec n t)

/-! A transparent local presentation of the production nested coordinate
equivalence.  It uses the public `TailCoordHelpers` maps verbatim; keeping
the two reassociation steps visible supplies the projection equations needed
below without relying on generated private declaration names. -/
private noncomputable def totalEEEENestedSrcRawEquiv
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (hS : Even (Fintype.card S))
    (hT : Even (Fintype.card T)) :
    (S → T → U) ≃ₗ[F]
      ((PointedEvenValueCoords T U t0 ×
          PointedEvenValueCoords T U t0) ×
        PointedValueTailZero S
          (PointedEvenValueCoords T U t0) s0) :=
  (pointedSrcEvenValueEquiv S (T → U) s0 hS).trans
    (((pointedSrcEvenValueEquiv T U t0 hT).prodCongr
        (pointedSrcEvenValueEquiv T U t0 hT)).prodCongr
      (TotalEOEEInternal.TailCoordHelpers.tailZeroCongr s0
        (pointedSrcEvenValueEquiv T U t0 hT)))

private noncomputable def totalEEEENestedSrcReassocEquiv
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U] :
    ((PointedEvenValueCoords T U t0 ×
        PointedEvenValueCoords T U t0) ×
      PointedValueTailZero S
        (PointedEvenValueCoords T U t0) s0) ≃ₗ[F]
      TotalEOEEInternal.TailCoordHelpers.NestedSrcEvenTarget
        S T U s0 t0 where
  toFun x :=
    let tTail :=
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := T) (U := U) (V := U) t0).symm
          (x.1.1.2, x.1.2.2)
    let sTail :=
      TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0 x.2
    ((x.1.1.1, x.1.2.1), (tTail, (sTail.1, sTail.2)))
  invFun x :=
    let tTail :=
      TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := T) (U := U) (V := U) t0 x.2.1
    let sTail :=
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0).symm
          (x.2.2.1, x.2.2.2)
    (((x.1.1, tTail.1), (x.1.2, tTail.2)), sTail)
  left_inv x := by
    dsimp only
    have ht :=
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := T) (U := U) (V := U) t0).apply_symm_apply
          (x.1.1.2, x.1.2.2)
    have hs :=
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0).symm_apply_apply x.2
    rw [ht, hs]
  right_inv x := by
    dsimp only
    have ht :=
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := T) (U := U) (V := U) t0).symm_apply_apply x.2.1
    have hs :=
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0).apply_symm_apply
          (x.2.2.1, x.2.2.2)
    rw [ht, hs]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact
          (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
            (S := T) (U := U) (V := U) t0).symm.map_add
              (x.1.1.2, x.1.2.2) (y.1.1.2, y.1.2.2)
      · exact
          (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
            (S := S) (U := U × U)
            (V := PointedValueTailZero T U t0) s0).map_add x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact
          (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
            (S := T) (U := U) (V := U) t0).symm.map_smul
              r (x.1.1.2, x.1.2.2)
      · exact
          (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
            (S := S) (U := U × U)
            (V := PointedValueTailZero T U t0) s0).map_smul r x.2

@[simp] private theorem totalEEEENestedSrcReassocEquiv_scalar
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (x :
      (PointedEvenValueCoords T U t0 ×
          PointedEvenValueCoords T U t0) ×
        PointedValueTailZero S
          (PointedEvenValueCoords T U t0) s0) :
    (totalEEEENestedSrcReassocEquiv S T U s0 t0 x).1 =
      (x.1.1.1, x.1.2.1) :=
  rfl

@[simp] private theorem totalEEEENestedSrcReassocEquiv_TTail
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (x :
      (PointedEvenValueCoords T U t0 ×
          PointedEvenValueCoords T U t0) ×
        PointedValueTailZero S
          (PointedEvenValueCoords T U t0) s0) :
    (totalEEEENestedSrcReassocEquiv S T U s0 t0 x).2.1 =
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := T) (U := U) (V := U) t0).symm
          (x.1.1.2, x.1.2.2) :=
  rfl

@[simp] private theorem totalEEEENestedSrcReassocEquiv_STail
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (x :
      (PointedEvenValueCoords T U t0 ×
          PointedEvenValueCoords T U t0) ×
        PointedValueTailZero S
          (PointedEvenValueCoords T U t0) s0) :
    (totalEEEENestedSrcReassocEquiv S T U s0 t0 x).2.2 =
      TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0 x.2 :=
  rfl

@[simp] private theorem totalEEEETailZeroProdEquiv_symm_apply
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (x : PointedValueTailZero S U s0)
    (y : PointedValueTailZero S V s0)
    (t : PointedTail S s0) :
    ((TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := S) (U := U) (V := V) s0).symm (x, y)).1 t =
      (x.1 t, y.1 t) :=
  rfl

@[simp] private theorem totalEEEETailZeroProdEquiv_apply_fst
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (x : PointedValueTailZero S (U × V) s0)
    (t : PointedTail S s0) :
    ((TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := S) (U := U) (V := V) s0) x).1.1 t =
      (x.1 t).1 :=
  rfl

@[simp] private theorem totalEEEETailZeroCongr_apply
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (e : U ≃ₗ[F] V)
    (x : PointedValueTailZero S U s0)
    (t : PointedTail S s0) :
    (TotalEOEEInternal.TailCoordHelpers.tailZeroCongr s0 e x).1 t =
      e (x.1 t) :=
  rfl

private noncomputable def totalEEEENestedSrcEvenValueEquiv
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (hS : Even (Fintype.card S))
    (hT : Even (Fintype.card T)) :
    (S → T → U) ≃ₗ[F]
      TotalEOEEInternal.TailCoordHelpers.NestedSrcEvenTarget
        S T U s0 t0 :=
  (totalEEEENestedSrcRawEquiv S T U s0 t0 hS hT).trans
    (totalEEEENestedSrcReassocEquiv S T U s0 t0)

noncomputable def bNestedCoords
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    BFun4 n 1 c d ≃ₗ[F] NestedCoords n c d :=
  (TotalEOEEInternal.bGaugedRootFamilyEquiv
      (by omega) (by omega)).trans
    (totalEEEENestedSrcEvenValueEquiv
      (PVec n c) (PVec n d) (CyclicCube n)
      (zeroVec : PVec n c) (zeroVec : PVec n d)
      (even_card_PVec hn hc2) (even_card_PVec hn hd2))

noncomputable def wNestedCoords
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    WFun4 n 1 b c ≃ₗ[F] NestedCoords n b c :=
  (wGaugedYZFamilyEquiv (by omega) (by omega)).trans
    (totalEEEENestedSrcEvenValueEquiv
      (PVec n b) (PVec n c) (CyclicCube n)
      (zeroVec : PVec n b) (zeroVec : PVec n c)
      (even_card_PVec hn hb2) (even_card_PVec hn hc2))

/-- The five exact active coordinate equations.  In each `Y`/`W` pair only
the first cube is constrained; the second cube is passive. -/
theorem literal_mem_iff_active_coords
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    x ∈ DiamondEvenPLeft n b c d ↔
      let g := literalGaugeEquiv
        (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) x
      let Bs : PVec n d → CyclicCube n :=
        fun wt => ∑ zt : PVec n c, g.1 zt wt
      let Ws : PVec n b → CyclicCube n :=
        fun yt => ∑ zt : PVec n c, g.2 yt zt
      let Bc :=
        diamondEvenAxisSrcCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2 Bs
      let Wc :=
        diamondEvenAxisSrcCoordEquiv
          (n := n) (k := b) (CyclicCube n) hn hb2 Ws
      cubeDiffP Bc.1.1 = 0 ∧
      cubeDiffR Wc.1.1 = 0 ∧
      cubeDiffP Bc.1.2 + cubeDiffR Wc.1.2 = 0 ∧
      (∀ wt : DiamondEvenAxisTailIndex n d,
        cubeDiffP (Bc.2.1 wt) = 0) ∧
      (∀ yt : DiamondEvenAxisTailIndex n b,
        cubeDiffR (Wc.2.1 yt) = 0) := by
  rw [literal_mem_iff_uniform
    (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d)]
  exact
    T37LeftP0.totalEEOE_gauged_source_iff
      (n := n) (b := b) (d := d) hn hb2 hd2
      (fun wt => ∑ zt : PVec n c,
        (literalGaugeEquiv
          (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) x).1
          zt wt)
      (fun yt => ∑ zt : PVec n c,
        (literalGaugeEquiv
          (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) x).2
          yt zt)

noncomputable abbrev TotalEEEEYLeftBase
    (n : Nat) [NeZero n] :=
  EEOEInternal.RBlockLeft n × CyclicCube n

noncomputable abbrev TotalEEEEWLeftBase
    (n : Nat) [NeZero n] :=
  EEOEInternal.PBlockLeft n × CyclicCube n

noncomputable abbrev TotalEEEEYTailLeft
    (n b : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n b (TotalEEEEYLeftBase n)

noncomputable abbrev TotalEEEEWTailLeft
    (n d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n d (TotalEEEEWLeftBase n)

noncomputable abbrev TotalEEEEZTailLeft
    (n c : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c (DiamondEEOELeftAmbient n)

noncomputable abbrev TotalEEEEYZTailLeft
    (n b c : Nat) [NeZero n] :=
  DiamondMixedTailZero n b c (CyclicCube n)

noncomputable abbrev TotalEEEEWZTailLeft
    (n c d : Nat) [NeZero n] :=
  DiamondMixedTailZero n c d (CyclicCube n)

noncomputable abbrev TotalEEEEYWLeftZero
    (n b d : Nat) [NeZero n] :=
  DiamondMixedTailZero n b d
    (⊥ : Submodule F (CyclicCube n))

noncomputable abbrev TotalEEEEWBottomTail
    (n d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n d
    (⊥ : Submodule F (CyclicCube n))

noncomputable abbrev TotalEEEEZWBottomTail
    (n c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c
    (TotalEEEEWBottomTail n d)

set_option maxHeartbeats 12000000 in
-- The outer bottom-tail abbreviation needs a larger elaboration budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested subtype instances need a larger typeclass budget.
set_option maxSynthPendingDepth 2048 in
-- The three nested tail layers need a larger pending-synthesis depth.
/-- The frozen literal field order `Y-Z-W`, with an actual bottom cube at
the innermost level.  The two preceding abbreviations only make typeclass
elaboration incremental; this unfolds to the exact frozen carrier. -/
noncomputable abbrev TotalEEEEYWZLeftZero
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n b
    (TotalEEEEZWBottomTail n c d)

noncomputable abbrev TotalEEEELeftAmbientTailTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n b
      (CyclicCube n × CyclicCube n) ×
    (DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n) ×
      (TotalEEEEZTailLeft n c ×
        (TotalEEEEYZTailLeft n b c ×
          TotalEEEEWZTailLeft n c d)))

noncomputable abbrev TotalEEEELeftAmbientTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEEEELeftAmbient n ×
    TotalEEEELeftAmbientTailTarget n b c d

noncomputable abbrev TotalEEEELeftSourceTailRestTarget
    (n b c d : Nat) [NeZero n] :=
  TotalEEEEWTailLeft n d ×
    (TotalEEEEZTailLeft n c ×
      (TotalEEEEYZTailLeft n b c ×
        (TotalEEEEWZTailLeft n c d ×
          (TotalEEEEYWLeftZero n b d ×
            TotalEEEEYWZLeftZero n b c d))))

noncomputable abbrev TotalEEEELeftSourceTailTarget
    (n b c d : Nat) [NeZero n] :=
  TotalEEEEYTailLeft n b ×
    TotalEEEELeftSourceTailRestTarget n b c d

/-! Frozen addition-first association:
`scalar × (Y × (W × (Z × (YZ × (WZ × (YW × YWZ))))))`. -/
noncomputable abbrev TotalEEEELeftSourceTarget
    (n b c d : Nat) [NeZero n] :=
  DiamondEEEELeftSource n ×
    TotalEEEELeftSourceTailTarget n b c d

@[reducible] private noncomputable def
    totalEEEELeftAmbientTargetAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEELeftAmbientTarget n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (DiamondEEEELeftAmbient n))
    (inferInstance :
      AddCommMonoid (TotalEEEELeftAmbientTailTarget n b c d))

private local instance
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEELeftAmbientTarget n b c d) :=
  totalEEEELeftAmbientTargetAddCommMonoid

private local instance
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEELeftAmbientTarget n b c d) :=
  @Prod.instModule F
    (DiamondEEEELeftAmbient n)
    (TotalEEEELeftAmbientTailTarget n b c d)
    inferInstance
    (inferInstance : AddCommMonoid (DiamondEEEELeftAmbient n))
    (inferInstance :
      AddCommMonoid (TotalEEEELeftAmbientTailTarget n b c d))
    (inferInstance : Module F (DiamondEEEELeftAmbient n))
    (inferInstance :
      Module F (TotalEEEELeftAmbientTailTarget n b c d))

@[reducible] private noncomputable def
    totalEEEELeftSourceTailTargetAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEELeftSourceTailTarget n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (TotalEEEEYTailLeft n b))
    (inferInstance :
      AddCommMonoid (TotalEEEELeftSourceTailRestTarget n b c d))

private local instance
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEELeftSourceTailTarget n b c d) :=
  totalEEEELeftSourceTailTargetAddCommMonoid

set_option maxHeartbeats 12000000 in
-- The exact eight-slot source product needs a larger elaboration budget.
set_option synthInstance.maxHeartbeats 2000000 in
-- The nested bottom carriers need a larger typeclass budget.
set_option maxSynthPendingDepth 2048 in
-- The nested source product needs a larger pending-synthesis depth.
private local instance
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEELeftSourceTailTarget n b c d) :=
  @Prod.instModule F
    (TotalEEEEYTailLeft n b)
    (TotalEEEELeftSourceTailRestTarget n b c d)
    inferInstance
    (inferInstance : AddCommMonoid (TotalEEEEYTailLeft n b))
    (inferInstance :
      AddCommMonoid (TotalEEEELeftSourceTailRestTarget n b c d))
    (inferInstance : Module F (TotalEEEEYTailLeft n b))
    (inferInstance :
      Module F (TotalEEEELeftSourceTailRestTarget n b c d))

@[reducible] private noncomputable def
    totalEEEELeftSourceTargetAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEELeftSourceTarget n b c d) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (DiamondEEEELeftSource n))
    (inferInstance :
      AddCommMonoid (TotalEEEELeftSourceTailTarget n b c d))

noncomputable instance totalEEEELeftSourceTargetAddCommMonoidInstance
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (TotalEEEELeftSourceTarget n b c d) :=
  totalEEEELeftSourceTargetAddCommMonoid

noncomputable instance totalEEEELeftSourceTargetModule
    {n b c d : Nat} [NeZero n] :
    Module F (TotalEEEELeftSourceTarget n b c d) :=
  @Prod.instModule F
    (DiamondEEEELeftSource n)
    (TotalEEEELeftSourceTailTarget n b c d)
    inferInstance
    (inferInstance : AddCommMonoid (DiamondEEEELeftSource n))
    (inferInstance :
      AddCommMonoid (TotalEEEELeftSourceTailTarget n b c d))
    (inferInstance : Module F (DiamondEEEELeftSource n))
    (inferInstance :
      Module F (TotalEEEELeftSourceTailTarget n b c d))

/-- Recombine the two independent `Z` tails into the literal EEOE four-cube
ambient. -/
private noncomputable def totalEEEEZTailEquiv
    {n c : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n c
        (CyclicCube n × CyclicCube n) ×
      DiamondEvenAxisValueTailZero n c
        (CyclicCube n × CyclicCube n)) ≃ₗ[F]
      TotalEEEEZTailLeft n c :=
  (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
    (S := PVec n c)
    (U := CyclicCube n × CyclicCube n)
    (V := CyclicCube n × CyclicCube n)
    (zeroVec : PVec n c)).symm

@[reducible] private noncomputable def
    totalEEEENestedCoordsProdAddCommMonoid
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (NestedCoords n c d × NestedCoords n b c) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance : AddCommMonoid (NestedCoords n c d))
    (inferInstance : AddCommMonoid (NestedCoords n b c))

private local instance
    {n b c d : Nat} [NeZero n] :
    AddCommMonoid (NestedCoords n c d × NestedCoords n b c) :=
  totalEEEENestedCoordsProdAddCommMonoid

private local instance
    {n b c d : Nat} [NeZero n] :
    Module F (NestedCoords n c d × NestedCoords n b c) :=
  @Prod.instModule F
    (NestedCoords n c d)
    (NestedCoords n b c)
    inferInstance
    (inferInstance : AddCommMonoid (NestedCoords n c d))
    (inferInstance : AddCommMonoid (NestedCoords n b c))
    (inferInstance : Module F (NestedCoords n c d))
    (inferInstance : Module F (NestedCoords n b c))

/-- Exact reassociation of the full nested coordinates.  No coordinate is
discarded: the passive `Z-K` cubes remain in the `Y` and `W` tails. -/
private noncomputable def totalEEEELeftAmbientReassoc
    {n b c d : Nat} [NeZero n] :
    (NestedCoords n c d × NestedCoords n b c) ≃ₗ[F]
      TotalEEEELeftAmbientTarget n b c d where
  toFun q :=
    ((q.1.1, q.2.1),
      (q.2.2.2.1,
        (q.1.2.1,
          (totalEEEEZTailEquiv (q.1.2.2.1, q.2.2.1),
            (q.2.2.2.2, q.1.2.2.2)))))
  invFun q :=
    let z := totalEEEEZTailEquiv.symm q.2.2.2.1
    ((q.1.1, (q.2.2.1, (z.1, q.2.2.2.2.2))),
      (q.1.2, (z.2, (q.2.1, q.2.2.2.2.1))))
  left_inv q := by
    dsimp only
    have hz :=
      totalEEEEZTailEquiv.symm_apply_apply
        (q.1.2.2.1, q.2.2.1)
    rw [hz]
  right_inv q := by
    dsimp only
    have hz :=
      totalEEEEZTailEquiv.apply_symm_apply q.2.2.2.1
    rw [hz]
  map_add' q r := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact
              totalEEEEZTailEquiv.map_add
                (q.1.2.2.1, q.2.2.1)
                (r.1.2.2.1, r.2.2.1)
          · rfl
  map_smul' a q := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact
              totalEEEEZTailEquiv.map_smul
                a (q.1.2.2.1, q.2.2.1)
          · rfl

/-- Complete ambient coordinates, before imposing any source equation. -/
noncomputable def totalEEEELeftAmbientCoords
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    (BFun4 n 1 c d × WFun4 n 1 b c) ≃ₗ[F]
      TotalEEEELeftAmbientTarget n b c d :=
  ((bNestedCoords hn hc2 hd2).prodCongr
      (wNestedCoords hn hb2 hc2)).trans
    totalEEEELeftAmbientReassoc

@[simp] theorem totalEEEELeftAmbientCoords_scalar
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    (totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).1 =
      ((bNestedCoords hn hc2 hd2 x.1).1,
        (wNestedCoords hn hb2 hc2 x.2).1) :=
  rfl

@[simp] theorem totalEEEELeftAmbientCoords_YTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    (totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).2.1 =
      (wNestedCoords hn hb2 hc2 x.2).2.2.1 :=
  rfl

@[simp] theorem totalEEEELeftAmbientCoords_WTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    (totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).2.2.1 =
      (bNestedCoords hn hc2 hd2 x.1).2.1 :=
  rfl

@[simp] theorem totalEEEELeftAmbientCoords_ZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    (totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).2.2.2.1 =
      totalEEEEZTailEquiv
        ((bNestedCoords hn hc2 hd2 x.1).2.2.1,
          (wNestedCoords hn hb2 hc2 x.2).2.1) :=
  rfl

@[simp] theorem totalEEEELeftAmbientCoords_YZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    (totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).2.2.2.2.1 =
      (wNestedCoords hn hb2 hc2 x.2).2.2.2 :=
  rfl

@[simp] theorem totalEEEELeftAmbientCoords_WZTail
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    (totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).2.2.2.2.2 =
      (bNestedCoords hn hc2 hd2 x.1).2.2.2 :=
  rfl

private theorem bNestedCoords_sigma
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (B : BFun4 n 1 c d) :
    let g :=
      TotalEOEEInternal.bGaugedRootFamilyEquiv
        (by omega : 0 < c) (by omega : 0 < d) B
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (bNestedCoords hn hc2 hd2 B).1.1 =
      (E (fun wt => ∑ zt : PVec n c, g zt wt)).1 := by
  dsimp only
  simp only [bNestedCoords, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply,
    totalEEEENestedSrcEvenValueEquiv,
    totalEEEENestedSrcRawEquiv,
    totalEEEENestedSrcReassocEquiv_scalar,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K]
  apply Prod.ext
  · simp only [diamondEvenAxisSrcCoordEquiv,
      pointedSrcEvenValueEquiv_apply_sigma, Finset.sum_apply]
  · simp only [diamondEvenAxisSrcCoordEquiv,
      pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]

private theorem bNestedCoords_WTail_fst
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (B : BFun4 n 1 c d)
    (wt : DiamondEvenAxisTailIndex n d) :
    let g :=
      TotalEOEEInternal.bGaugedRootFamilyEquiv
        (by omega : 0 < c) (by omega : 0 < d) B
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    ((bNestedCoords hn hc2 hd2 B).2.1.1 wt).1 =
      (E (fun w => ∑ zt : PVec n c, g zt w)).2.1 wt := by
  dsimp only
  simp only [bNestedCoords, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply,
    totalEEEENestedSrcEvenValueEquiv,
    totalEEEENestedSrcRawEquiv,
    totalEEEENestedSrcReassocEquiv_TTail,
    totalEEEETailZeroProdEquiv_symm_apply,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K]
  simp only [diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv_apply_tail, Finset.sum_apply]

private theorem wNestedCoords_sigma
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (W : WFun4 n 1 b c) :
    let g :=
      wGaugedYZFamilyEquiv
        (by omega : 0 < b) (by omega : 0 < c) W
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := b) (CyclicCube n) hn hb2
    ((wNestedCoords hn hb2 hc2 W).1.1.1,
        (wNestedCoords hn hb2 hc2 W).1.2.1) =
      (E (fun yt => ∑ zt : PVec n c, g yt zt)).1 := by
  dsimp only
  simp only [wNestedCoords, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply,
    totalEEEENestedSrcEvenValueEquiv,
    totalEEEENestedSrcRawEquiv,
    totalEEEENestedSrcReassocEquiv_scalar,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K]
  apply Prod.ext
  · simp only [diamondEvenAxisSrcCoordEquiv,
      pointedSrcEvenValueEquiv_apply_sigma, Finset.sum_apply]
    exact Finset.sum_comm
  · simp only [diamondEvenAxisSrcCoordEquiv,
      pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
    exact Finset.sum_comm

private theorem wNestedCoords_YTail_fst
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (W : WFun4 n 1 b c)
    (yt : DiamondEvenAxisTailIndex n b) :
    let g :=
      wGaugedYZFamilyEquiv
        (by omega : 0 < b) (by omega : 0 < c) W
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := b) (CyclicCube n) hn hb2
    ((wNestedCoords hn hb2 hc2 W).2.2.1.1 yt).1 =
      (E (fun y => ∑ zt : PVec n c, g y zt)).2.1 yt := by
  dsimp only
  simp only [wNestedCoords, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply,
    totalEEEENestedSrcEvenValueEquiv,
    totalEEEENestedSrcRawEquiv,
    totalEEEENestedSrcReassocEquiv_STail,
    totalEEEETailZeroProdEquiv_apply_fst,
    totalEEEETailZeroCongr_apply,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K]
  simp only [diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv_apply_tail]
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/-- Source membership in the complete ambient coordinates.  This is the
literal five-equation ledger: scalar EEEE plus one oriented condition on
each `Y` and `W` tail. -/
theorem totalEEEELeft_mem_iff_coords
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    x ∈ DiamondEvenPLeft n b c d ↔
      (totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).1 ∈
          DiamondEEEELeftSource n ∧
      (∀ yt : DiamondEvenAxisTailIndex n b,
        cubeDiffR
          (((totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).2.1.1 yt).1) =
            0) ∧
      (∀ wt : DiamondEvenAxisTailIndex n d,
        cubeDiffP
          (((totalEEEELeftAmbientCoords hn hb2 hc2 hd2 x).2.2.1.1 wt).1) =
            0) := by
  rw [literal_mem_iff_active_coords hn hb2 hc2 hd2]
  dsimp only
  let g :=
    literalGaugeEquiv
      (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) x
  let Bc :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
      (fun wt => ∑ zt : PVec n c, g.1 zt wt)
  let Wc :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := b) (CyclicCube n) hn hb2
      (fun yt => ∑ zt : PVec n c, g.2 yt zt)
  let bn := bNestedCoords hn hc2 hd2 x.1
  let wn := wNestedCoords hn hb2 hc2 x.2
  have hB : bn.1.1 = Bc.1 := by
    exact bNestedCoords_sigma hn hc2 hd2 x.1
  have hW : (wn.1.1.1, wn.1.2.1) = Wc.1 := by
    exact wNestedCoords_sigma hn hb2 hc2 x.2
  have hBt :
      ∀ wt : DiamondEvenAxisTailIndex n d,
        (bn.2.1.1 wt).1 = Bc.2.1 wt := by
    intro wt
    exact bNestedCoords_WTail_fst hn hc2 hd2 x.1 wt
  have hWt :
      ∀ yt : DiamondEvenAxisTailIndex n b,
        (wn.2.2.1.1 yt).1 = Wc.2.1 yt := by
    intro yt
    exact wNestedCoords_YTail_fst hn hb2 hc2 x.2 yt
  simp only [totalEEEELeftAmbientCoords_scalar,
    totalEEEELeftAmbientCoords_YTail,
    totalEEEELeftAmbientCoords_WTail]
  change
    cubeDiffP Bc.1.1 = 0 ∧
        cubeDiffR Wc.1.1 = 0 ∧
        cubeDiffP Bc.1.2 + cubeDiffR Wc.1.2 = 0 ∧
        (∀ wt, cubeDiffP (Bc.2.1 wt) = 0) ∧
        (∀ yt, cubeDiffR (Wc.2.1 yt) = 0) ↔
      (bn.1, wn.1) ∈ DiamondEEEELeftSource n ∧
        (∀ yt, cubeDiffR ((wn.2.2.1.1 yt).1) = 0) ∧
        (∀ wt, cubeDiffP ((bn.2.1.1 wt).1) = 0)
  constructor
  · rintro ⟨hP, hR, hK, hTailB, hTailW⟩
    refine ⟨?_, ?_, ?_⟩
    · apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · apply Prod.ext
        · calc
            cubeDiffP bn.1.1.1 = cubeDiffP Bc.1.1 :=
              congrArg (fun z => cubeDiffP z.1) hB
            _ = 0 := hP
        · calc
            cubeDiffR wn.1.1.1 = cubeDiffR Wc.1.1 :=
              congrArg (fun z => cubeDiffR z.1) hW
            _ = 0 := hR
      · calc
          cubeDiffP bn.1.1.2 + cubeDiffR wn.1.2.1 =
              cubeDiffP Bc.1.2 + cubeDiffR Wc.1.2 := by
                rw [show bn.1.1.2 = Bc.1.2 from
                    congrArg Prod.snd hB,
                  show wn.1.2.1 = Wc.1.2 from
                    congrArg Prod.snd hW]
          _ = 0 := hK
    · intro yt
      calc
        cubeDiffR ((wn.2.2.1.1 yt).1) =
            cubeDiffR (Wc.2.1 yt) := congrArg cubeDiffR (hWt yt)
        _ = 0 := hTailW yt
    · intro wt
      calc
        cubeDiffP ((bn.2.1.1 wt).1) =
            cubeDiffP (Bc.2.1 wt) := congrArg cubeDiffP (hBt wt)
        _ = 0 := hTailB wt
  · rintro ⟨hScalar, hTailW, hTailB⟩
    have hs := LinearMap.mem_ker.mp hScalar
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · calc
        cubeDiffP Bc.1.1 = cubeDiffP bn.1.1.1 :=
          congrArg (fun z => cubeDiffP z.1) hB.symm
        _ = 0 := congrArg (fun z => z.1.1) hs
    · calc
        cubeDiffR Wc.1.1 = cubeDiffR wn.1.1.1 :=
          congrArg (fun z => cubeDiffR z.1) hW.symm
        _ = 0 := congrArg (fun z => z.1.2) hs
    · calc
        cubeDiffP Bc.1.2 + cubeDiffR Wc.1.2 =
            cubeDiffP bn.1.1.2 + cubeDiffR wn.1.2.1 := by
              rw [show Bc.1.2 = bn.1.1.2 from
                  congrArg Prod.snd hB.symm,
                show Wc.1.2 = wn.1.2.1 from
                  congrArg Prod.snd hW.symm]
        _ = 0 := congrArg Prod.snd hs
    · intro wt
      calc
        cubeDiffP (Bc.2.1 wt) =
            cubeDiffP ((bn.2.1.1 wt).1) :=
              congrArg cubeDiffP (hBt wt).symm
        _ = 0 := hTailB wt
    · intro yt
      calc
        cubeDiffR (Wc.2.1 yt) =
            cubeDiffR ((wn.2.2.1.1 yt).1) :=
              congrArg cubeDiffR (hWt yt).symm
        _ = 0 := hTailW yt

private noncomputable def totalEEEEYTailPack
    {n b : Nat} [NeZero n]
    (u :
      DiamondEvenAxisValueTailZero n b
        (CyclicCube n × CyclicCube n))
    (hu : ∀ yt : DiamondEvenAxisTailIndex n b,
      cubeDiffR ((u.1 yt).1) = 0) :
    TotalEEEEYTailLeft n b :=
  ⟨fun yt =>
      (⟨(u.1 yt).1, LinearMap.mem_ker.mpr (hu yt)⟩,
        (u.1 yt).2),
    by
      apply LinearMap.mem_ker.mpr
      change
        (∑ yt,
          ((⟨(u.1 yt).1, LinearMap.mem_ker.mpr (hu yt)⟩ :
              EEOEInternal.RBlockLeft n),
            (u.1 yt).2)) = 0
      apply Prod.ext
      · apply Subtype.ext
        have h := pointedValueTailZero_sum u
        simpa only [Prod.fst_sum, Submodule.coe_sum] using
          congrArg Prod.fst h
      · have h := pointedValueTailZero_sum u
        simpa only [Prod.snd_sum] using congrArg Prod.snd h⟩

private noncomputable def totalEEEEYTailForget
    {n b : Nat} [NeZero n] :
    TotalEEEEYTailLeft n b →ₗ[F]
      DiamondEvenAxisValueTailZero n b
        (CyclicCube n × CyclicCube n) where
  toFun u :=
    ⟨fun yt => ((u.1 yt).1.1, (u.1 yt).2), by
      apply LinearMap.mem_ker.mpr
      change (∑ yt, ((u.1 yt).1.1, (u.1 yt).2)) = 0
      apply Prod.ext
      · have h := congrArg Prod.fst (pointedValueTailZero_sum u)
        simpa only [Prod.fst_sum, Submodule.coe_sum] using
          congrArg Subtype.val h
      · have h := pointedValueTailZero_sum u
        simpa only [Prod.snd_sum] using congrArg Prod.snd h⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

private noncomputable def totalEEEEWTailPack
    {n d : Nat} [NeZero n]
    (u :
      DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n))
    (hu : ∀ wt : DiamondEvenAxisTailIndex n d,
      cubeDiffP ((u.1 wt).1) = 0) :
    TotalEEEEWTailLeft n d :=
  ⟨fun wt =>
      (⟨(u.1 wt).1, LinearMap.mem_ker.mpr (hu wt)⟩,
        (u.1 wt).2),
    by
      apply LinearMap.mem_ker.mpr
      change
        (∑ wt,
          ((⟨(u.1 wt).1, LinearMap.mem_ker.mpr (hu wt)⟩ :
              EEOEInternal.PBlockLeft n),
            (u.1 wt).2)) = 0
      apply Prod.ext
      · apply Subtype.ext
        have h := pointedValueTailZero_sum u
        simpa only [Prod.fst_sum, Submodule.coe_sum] using
          congrArg Prod.fst h
      · have h := pointedValueTailZero_sum u
        simpa only [Prod.snd_sum] using congrArg Prod.snd h⟩

private noncomputable def totalEEEEWTailForget
    {n d : Nat} [NeZero n] :
    TotalEEEEWTailLeft n d →ₗ[F]
      DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n) where
  toFun u :=
    ⟨fun wt => ((u.1 wt).1.1, (u.1 wt).2), by
      apply LinearMap.mem_ker.mpr
      change (∑ wt, ((u.1 wt).1.1, (u.1 wt).2)) = 0
      apply Prod.ext
      · have h := congrArg Prod.fst (pointedValueTailZero_sum u)
        simpa only [Prod.fst_sum, Submodule.coe_sum] using
          congrArg Subtype.val h
      · have h := pointedValueTailZero_sum u
        simpa only [Prod.snd_sum] using congrArg Prod.snd h⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

private theorem totalEEEEYWLeftZero_eq_zero
    {n b d : Nat} [NeZero n]
    (q : TotalEEEEYWLeftZero n b d) :
    q = 0 := by
  apply Subtype.ext
  funext yt
  apply Subtype.ext
  funext wt
  exact Subsingleton.elim _ _

private theorem totalEEEEYWZLeftZero_eq_zero
    {n b c d : Nat} [NeZero n]
    (q : TotalEEEEYWZLeftZero n b c d) :
    q = 0 := by
  apply Subtype.ext
  funext yt
  apply Subtype.ext
  funext zt
  apply Subtype.ext
  funext wt
  exact Subsingleton.elim _ _

/-- The complete literal all-even left-source equivalence. -/
noncomputable def leftSourceEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPLeft n b c d ≃ₗ[F]
      TotalEEEELeftSourceTarget n b c d where
  toFun l := by
    let q := totalEEEELeftAmbientCoords hn hb2 hc2 hd2 l.1
    have hq :=
      (totalEEEELeft_mem_iff_coords hn hb2 hc2 hd2 l.1).mp l.2
    exact
      (⟨q.1, hq.1⟩,
        (totalEEEEYTailPack q.2.1 hq.2.1,
          (totalEEEEWTailPack q.2.2.1 hq.2.2,
            (q.2.2.2.1,
              (q.2.2.2.2.1,
                (q.2.2.2.2.2, (0, 0)))))))
  invFun q := by
    let raw : TotalEEEELeftAmbientTarget n b c d :=
      (q.1.1,
        (totalEEEEYTailForget q.2.1,
          (totalEEEEWTailForget q.2.2.1,
            (q.2.2.2.1,
              (q.2.2.2.2.1, q.2.2.2.2.2.1)))))
    let l := (totalEEEELeftAmbientCoords hn hb2 hc2 hd2).symm raw
    refine
      ⟨l, (totalEEEELeft_mem_iff_coords hn hb2 hc2 hd2 l).mpr ?_⟩
    have hread :
        totalEEEELeftAmbientCoords hn hb2 hc2 hd2 l = raw :=
      (totalEEEELeftAmbientCoords hn hb2 hc2 hd2).apply_symm_apply raw
    refine ⟨?_, ?_, ?_⟩
    · have hs := congrArg Prod.fst hread
      rw [hs]
      exact q.1.2
    · intro yt
      have ht :=
        LinearMap.mem_ker.mp (q.2.1.1 yt).1.2
      calc
        cubeDiffR
            (((totalEEEELeftAmbientCoords
              hn hb2 hc2 hd2 l).2.1.1 yt).1) =
          cubeDiffR ((raw.2.1.1 yt).1) :=
            congrArg
              (fun z => cubeDiffR ((z.2.1.1 yt).1)) hread
        _ = 0 := by
          simpa only [raw, totalEEEEYTailForget] using ht
    · intro wt
      have ht :=
        LinearMap.mem_ker.mp (q.2.2.1.1 wt).1.2
      calc
        cubeDiffP
            (((totalEEEELeftAmbientCoords
              hn hb2 hc2 hd2 l).2.2.1.1 wt).1) =
          cubeDiffP ((raw.2.2.1.1 wt).1) :=
            congrArg
              (fun z => cubeDiffP ((z.2.2.1.1 wt).1)) hread
        _ = 0 := by
          simpa only [raw, totalEEEEWTailForget] using ht
  left_inv l := by
    apply Subtype.ext
    exact
      (totalEEEELeftAmbientCoords
        hn hb2 hc2 hd2).symm_apply_apply l.1
  right_inv q := by
    let raw : TotalEEEELeftAmbientTarget n b c d :=
      (q.1.1,
        (totalEEEEYTailForget q.2.1,
          (totalEEEEWTailForget q.2.2.1,
            (q.2.2.2.1,
              (q.2.2.2.2.1, q.2.2.2.2.2.1)))))
    have hread :=
      (totalEEEELeftAmbientCoords hn hb2 hc2 hd2).apply_symm_apply raw
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => ((z.2.1.1 yt).1)) hread
        · exact congrArg (fun z => ((z.2.1.1 yt).2)) hread
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun z => ((z.2.2.1.1 wt).1)) hread
          · exact congrArg (fun z => ((z.2.2.1.1 wt).2)) hread
        · apply Prod.ext
          · exact congrArg (fun z => z.2.2.2.1) hread
          · apply Prod.ext
            · exact congrArg (fun z => z.2.2.2.2.1) hread
            · apply Prod.ext
              · exact congrArg (fun z => z.2.2.2.2.2) hread
              · apply Prod.ext
                · exact
                    (totalEEEEYWLeftZero_eq_zero
                      q.2.2.2.2.2.2.1).symm
                · exact
                    (totalEEEEYWZLeftZero_eq_zero
                      q.2.2.2.2.2.2.2).symm
  map_add' l l' := by
    have hmap :=
      (totalEEEELeftAmbientCoords hn hb2 hc2 hd2).map_add l.1 l'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => ((z.2.1.1 yt).1)) hmap
        · exact congrArg (fun z => ((z.2.1.1 yt).2)) hmap
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun z => ((z.2.2.1.1 wt).1)) hmap
          · exact congrArg (fun z => ((z.2.2.1.1 wt).2)) hmap
        · apply Prod.ext
          · exact congrArg (fun z => z.2.2.2.1) hmap
          · apply Prod.ext
            · exact congrArg (fun z => z.2.2.2.2.1) hmap
            · apply Prod.ext
              · exact congrArg (fun z => z.2.2.2.2.2) hmap
              · rfl
  map_smul' r l := by
    have hmap :=
      (totalEEEELeftAmbientCoords hn hb2 hc2 hd2).map_smul r l.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => ((z.2.1.1 yt).1)) hmap
        · exact congrArg (fun z => ((z.2.1.1 yt).2)) hmap
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Prod.ext
          · apply Subtype.ext
            exact congrArg (fun z => ((z.2.2.1.1 wt).1)) hmap
          · exact congrArg (fun z => ((z.2.2.1.1 wt).2)) hmap
        · apply Prod.ext
          · exact congrArg (fun z => z.2.2.2.1) hmap
          · apply Prod.ext
            · exact congrArg (fun z => z.2.2.2.2.1) hmap
            · apply Prod.ext
              · exact congrArg (fun z => z.2.2.2.2.2) hmap
              · rfl

end TotalEEEEInternal

/-! Public P0 carrier and endpoint. -/
noncomputable abbrev TotalEEEELeftSourceTarget
    (n b c d : Nat) [NeZero n] :=
  TotalEEEEInternal.TotalEEEELeftSourceTarget n b c d

noncomputable def diamondEvenPLeftEEEEEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPLeft n b c d ≃ₗ[F]
      TotalEEEELeftSourceTarget n b c d :=
  TotalEEEEInternal.leftSourceEquiv hn hb2 hc2 hd2

end

end Core4loop.SquareDiagonal.EvenP
