import Core4loop.SquareDiagonal.EvenP.TotalEOEE.LeftSource
import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RightReachable
import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RawPhase

set_option autoImplicit false
set_option warningAsError true
-- The exact block alignment deliberately keeps the compiled scratch budgets.
set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

def scalarAmbientPhase
    {n : Nat} [NeZero n]
    (R A : DiamondEOEERightAmbient n) : F :=
  cubeDot R.1.1 A.1.1 + cubeDot R.1.2 A.1.2 +
    cubeDot R.2.1 A.2.1 + cubeDot R.2.2 A.2.2

/-- Scalar component order:
`((ZΣWΣ,ZΣWK),(ZKWΣ,ZKWK)),(WZΣ,WZK)`, paired with
`((D₀,D₀+A₀),(D₁,D₁+A₁))`. -/
theorem scalar_alignment_to_production_cross
    {n : Nat} [NeZero n]
    (l : DiamondEOEELeftSource n)
    (A : DiamondEOEERightSource n) :
    scalarAmbientPhase (diamondEOEECoeffMap l.1) A.1 =
      diamondEOEECross l A := by
  rfl

/-- The literal natural W phase is equal to the production post-shear cross.
This theorem fixes both orders: left `(u,v)=(BΣ-tail,BK-tail)` and right
natural `(a,d)`, with production right coordinate `(d,a+d)`. -/
theorem w_natural_to_post_shear_alignment
    {n : Nat} [NeZero n]
    (x : DiamondEOEEWLeftSource n)
    (y : DiamondEOEEWRightNatural n) :
    cubeDot (cubeDiffI x.1.1) y.1 +
        cubeDot (cubeDiffI x.2) y.2.1 =
      diamondEOEEWCross x (diamondEOEEWRightShear y) := by
  rw [diamondEOEEWCross_apply, diamondEOEEWRightShear_apply]
  simp only [map_add, EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  abel_nf
  simp only [two_smul, F_add_self, add_zero]

/-- The one-even Z local phase is definitionally the production
`diamondTailOneEvenZCross`; the right order is `(D,A₀+D)`. -/
theorem z_one_even_shear_alignment
    {n : Nat} [NeZero n]
    (x : DiamondEOOELeftAmbient n)
    (y : DiamondEOOERightAmbient n) :
    cubeDot
          (cubeDiffI (x.1.1 + x.1.2) + cubeDiffK x.2) y.1 +
        cubeDot (cubeDiffI x.1.1) y.2 =
      diamondTailOneEvenZCross x y := by
  rfl

/-- The mixed block is exactly one `I` difference, with Z-tail outer and
W-tail inner. -/
theorem mixed_zw_singleI_alignment
    {n : Nat} [NeZero n]
    (x y : CyclicCube n) :
    cubeDot (cubeDiffI x) y =
      diamondTailSingleICross x y := by
  rfl

theorem mixed_amplification_is_Z_outer_W_inner
    {n c d : Nat} [NeZero n]
    (x y : DiamondMixedTailZero n c d (CyclicCube n)) :
    diamondMixedTailAmplify
        (n := n) (k := c) (l := d)
        (diamondTailSingleICross (n := n)) x y =
      ∑ zt : DiamondEvenAxisTailIndex n c,
        ∑ wt : DiamondEvenAxisTailIndex n d,
          cubeDot
            (cubeDiffI (n := n) ((x.1 zt).1 wt))
            ((y.1 zt).1 wt) := by
  simp only [diamondMixedTailAmplify, diamondTailAmplify_apply,
    mixed_zw_singleI_alignment]


end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP


set_option autoImplicit false
set_option warningAsError true
set_option pp.universes false

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal


def eoeeAmbientPhase
    {n : Nat} [NeZero n]
    (R A : DiamondEOEERightAmbient n) : F :=
  cubeDot R.1.1 A.1.1 + cubeDot R.1.2 A.1.2 +
    cubeDot R.2.1 A.2.1 + cubeDot R.2.2 A.2.2

noncomputable def expectedLeftScalar
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d) :
    DiamondEOEELeftAmbient n :=
  let Z :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (RawOuterLeft n d) hn hc2 f
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  ((((E Z.1.1.1).1.1, (E Z.1.1.1).1.2),
      ((E Z.1.2.1).1.1, (E Z.1.2.1).1.2)),
    (Z.1.1.2, Z.1.2.2))

noncomputable def expectedRightScalar
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (g : PVec n c → RawOuterRight n d) :
    DiamondEOEERightAmbient n :=
  let Z :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (RawOuterRight n d) hn hc2 g
  let E :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let D0 := E Z.1.2
  let D1 := E (Z.1.1 + Z.1.2)
  ((D0.1.2, D0.1.1 + D0.1.2),
    (D1.1.2, D1.1.1 + D1.1.2))

noncomputable def expectedLeftWAt
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (t : DiamondEvenAxisTailIndex n d) :
    CyclicCube n × CyclicCube n :=
  let Z :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (RawOuterLeft n d) hn hc2 f
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  ((E Z.1.1.1).2.1 t, (E Z.1.2.1).2.1 t)

noncomputable def expectedRightWNaturalAt
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (g : PVec n c → RawOuterRight n d)
    (t : DiamondEvenAxisTailIndex n d) :
    CyclicCube n × CyclicCube n :=
  let Z :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (RawOuterRight n d) hn hc2 g
  let E :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  ((E Z.1.1).2.1 t, (E Z.1.2).2.1 t)

noncomputable def expectedLeftZLocal
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (u : RawOuterLeft n d) :
    DiamondEOOELeftAmbient n :=
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  (((E u.1).1.1, (E u.1).1.2), u.2)

noncomputable def expectedRightZLocal
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (v : RawOuterRight n d) :
    DiamondEOOERightAmbient n :=
  let E :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  ((E v).1.2, (E v).1.1 + (E v).1.2)

set_option maxHeartbeats 4000000 in
theorem left_scalar_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c) :
    (totalEOEELeftAmbientCoords hn hc2 hd2 x).1 =
      expectedLeftScalar hn hc2 hd2
        (fun zt =>
          (fun wt => bGaugedRootFamilyEquiv
            (by omega : 0 < c) (by omega : 0 < d) x.1 zt wt,
          wGaugedRootFamilyEquiv
            (by omega : 0 < c) x.2 zt)) := by
  rw [totalEOEELeftAmbientCoords_scalar hn hc2 hd2 x]
  ext i j k <;>
    simp only [expectedLeftScalar, diamondEvenAxisSrcCoordEquiv,
      pointedSrcEvenValueEquiv_apply_sigma,
      pointedSrcEvenValueEquiv_apply_K,
      Prod.fst_sum, Prod.snd_sum, Finset.sum_apply,
      bGaugedRootFamilyEquiv_apply,
      wGaugedRootFamilyEquiv_apply]

set_option maxHeartbeats 4000000 in
theorem right_scalar_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 c d) :
    (TotalEOEEInternal.rightAmbientEquiv hn hc2 hd2 A).1 =
      expectedRightScalar hn hc2 hd2
        (fun zt wt =>
          aGaugedRootFamilyEquiv
            (by omega : 0 < c) (by omega : 0 < d) A zt wt) := by
  rfl

set_option maxHeartbeats 4000000 in
theorem left_w_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (t : DiamondEvenAxisTailIndex n d) :
    ((((leftSourceEquiv hn hc2 hd2 l).2.1.1 t).1.1,
        ((leftSourceEquiv hn hc2 hd2 l).2.1.1 t).2) :
        CyclicCube n × CyclicCube n) =
      expectedLeftWAt hn hc2 hd2
        (literalOuterLeftFamily
          (by omega : 0 < c) (by omega : 0 < d) l) t := by
  change
    ((((totalEOEELeftAmbientCoords hn hc2 hd2 l.1).2.1.1 t).1,
        ((totalEOEELeftAmbientCoords hn hc2 hd2 l.1).2.1.1 t).2) :
        CyclicCube n × CyclicCube n) =
      expectedLeftWAt hn hc2 hd2
        (literalOuterLeftFamily
          (by omega : 0 < c) (by omega : 0 < d) l) t
  rw [totalEOEELeftAmbientCoords_WTail]
  rfl

set_option maxHeartbeats 4000000 in
theorem right_w_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n 1 c d)
    (t : DiamondEvenAxisTailIndex n d) :
    ((((TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.1.1 t).1.1,
        ((TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.1.1 t).2) :
        CyclicCube n × CyclicCube n) =
      (let q :=
        expectedRightWNaturalAt hn hc2 hd2
          (literalOuterRightFamily
            (by omega : 0 < c) (by omega : 0 < d) A) t
       (q.2, q.1 + q.2)) := by
  have h :=
    congrArg
      (fun p : DiamondEOEEWRightSource n => ((p.1.1, p.2) :
        CyclicCube n × CyclicCube n))
      (TotalEOEEInternal.rightReachableEquiv_Wtail_is_pointwise_shear
        hn hc2 hd2 A t)
  simpa only [diamondEOEEWRightShear_apply] using h

set_option maxHeartbeats 4000000 in
theorem raw_outer_w_eq_sum_expected
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) :
    rawOuterWBlock hn hc2 hd2 f g =
      ∑ t : DiamondEvenAxisTailIndex n d,
        let x := expectedLeftWAt hn hc2 hd2 f t
        let y := expectedRightWNaturalAt hn hc2 hd2 g t
        cubeDot (cubeDiffI x.1) y.1 +
          cubeDot (cubeDiffI x.2) y.2 := by
  simp only [rawOuterWBlock, rawInnerTailPhase,
    expectedLeftWAt, expectedRightWNaturalAt,
    Finset.sum_add_distrib]

set_option maxHeartbeats 4000000 in
theorem raw_inner_scalar_eq_z_cross
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (u : RawOuterLeft n d) (v : RawOuterRight n d) :
    rawInnerScalarPhase hn hd2 u v =
      diamondTailOneEvenZCross
        (expectedLeftZLocal hn hd2 u)
        (expectedRightZLocal hn hd2 v) := by
  simpa only [rawInnerScalarPhase, expectedLeftZLocal,
    expectedRightZLocal] using
      (TotalEOEEInternal.z_one_even_shear_alignment
        (expectedLeftZLocal hn hd2 u)
        (expectedRightZLocal hn hd2 v))

set_option maxHeartbeats 4000000 in
theorem raw_outer_z_eq_sum_expected
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) :
    rawOuterZBlock hn hc2 hd2 f g =
      ∑ t : DiamondEvenAxisTailIndex n c,
        diamondTailOneEvenZCross
          (expectedLeftZLocal hn hd2
            ((diamondEvenAxisSrcCoordEquiv
              (RawOuterLeft n d) hn hc2 f).2.1 t))
          (expectedRightZLocal hn hd2
            ((diamondEvenAxisDualCoordEquiv
              (RawOuterRight n d) hn hc2 g).2.1 t)) := by
  simp only [rawOuterZBlock]
  apply Finset.sum_congr rfl
  intro t _
  exact raw_inner_scalar_eq_z_cross hn hd2 _ _

set_option maxHeartbeats 4000000 in
theorem raw_outer_zw_eq_double_sum_expected
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) :
    rawOuterZWBlock hn hc2 hd2 f g =
      ∑ zt : DiamondEvenAxisTailIndex n c,
        ∑ wt : DiamondEvenAxisTailIndex n d,
          diamondTailSingleICross
            ((diamondEvenAxisSrcCoordEquiv
              (CyclicCube n) hn hd2
              ((diamondEvenAxisSrcCoordEquiv
                (RawOuterLeft n d) hn hc2 f).2.1 zt).1).2.1 wt)
            ((diamondEvenAxisDualCoordEquiv
              (CyclicCube n) hn hd2
              ((diamondEvenAxisDualCoordEquiv
                (RawOuterRight n d) hn hc2 g).2.1 zt)).2.1 wt) := by
  simp only [rawOuterZWBlock, rawInnerTailPhase]
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  exact
    TotalEOEEInternal.mixed_zw_singleI_alignment _ _

set_option maxHeartbeats 4000000 in
theorem left_z_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (t : DiamondEvenAxisTailIndex n c) :
    (leftSourceEquiv hn hc2 hd2 l).2.2.1.1 t =
      expectedLeftZLocal hn hd2
        ((diamondEvenAxisSrcCoordEquiv
          (RawOuterLeft n d) hn hc2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)).2.1 t) := by
  change
    (totalEOEELeftAmbientCoords hn hc2 hd2 l.1).2.2.1.1 t =
      expectedLeftZLocal hn hd2
        ((diamondEvenAxisSrcCoordEquiv
          (RawOuterLeft n d) hn hc2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)).2.1 t)
  rw [totalEOEELeftAmbientCoords_ZTail]
  rfl

set_option maxHeartbeats 4000000 in
theorem right_z_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n 1 c d)
    (t : DiamondEvenAxisTailIndex n c) :
    (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.2.1.1 t =
      expectedRightZLocal hn hd2
        ((diamondEvenAxisDualCoordEquiv
          (RawOuterRight n d) hn hc2
          (literalOuterRightFamily
            (by omega : 0 < c) (by omega : 0 < d) A)).2.1 t) := by
  rfl

set_option maxHeartbeats 4000000 in
theorem left_zw_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (zt : DiamondEvenAxisTailIndex n c)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((leftSourceEquiv hn hc2 hd2 l).2.2.2.1 zt).1 wt) =
      ((diamondEvenAxisSrcCoordEquiv
        (CyclicCube n) hn hd2
        ((diamondEvenAxisSrcCoordEquiv
          (RawOuterLeft n d) hn hc2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)).2.1 zt).1).2.1 wt) := by
  change
    (((totalEOEELeftAmbientCoords hn hc2 hd2 l.1).2.2.2.1 zt).1 wt) =
      ((diamondEvenAxisSrcCoordEquiv
        (CyclicCube n) hn hd2
        ((diamondEvenAxisSrcCoordEquiv
          (RawOuterLeft n d) hn hc2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)).2.1 zt).1).2.1 wt)
  rw [totalEOEELeftAmbientCoords_ZWTail]
  rfl

set_option maxHeartbeats 4000000 in
theorem right_zw_coordinate_bridge
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n 1 c d)
    (zt : DiamondEvenAxisTailIndex n c)
    (wt : DiamondEvenAxisTailIndex n d) :
    (((TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.2.2.1 zt).1 wt) =
      ((diamondEvenAxisDualCoordEquiv
        (CyclicCube n) hn hd2
        ((diamondEvenAxisDualCoordEquiv
          (RawOuterRight n d) hn hc2
          (literalOuterRightFamily
            (by omega : 0 < c) (by omega : 0 < d) A)).2.1 zt)).2.1 wt) := by
  rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem scalar_block_eq_expected_ambient
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (A : AFun4 n 1 c d) :
    rawOuterScalarBlock hn hc2 hd2
        (fun zt =>
          (fun wt => bGaugedRootFamilyEquiv
            (by omega : 0 < c) (by omega : 0 < d) x.1 zt wt,
          wGaugedRootFamilyEquiv
            (by omega : 0 < c) x.2 zt))
        (fun zt wt =>
          aGaugedRootFamilyEquiv
            (by omega : 0 < c) (by omega : 0 < d) A zt wt) =
      eoeeAmbientPhase
        (diamondEOEECoeffMap
          (expectedLeftScalar hn hc2 hd2
            (fun zt =>
              (fun wt => bGaugedRootFamilyEquiv
                (by omega : 0 < c) (by omega : 0 < d) x.1 zt wt,
              wGaugedRootFamilyEquiv
                (by omega : 0 < c) x.2 zt))))
        (expectedRightScalar hn hc2 hd2
          (fun zt wt =>
            aGaugedRootFamilyEquiv
              (by omega : 0 < c) (by omega : 0 < d) A zt wt)) := by
  simp only [rawOuterScalarBlock, rawInnerScalarPhase,
    eoeeAmbientPhase, diamondEOEECoeffMap, expectedLeftScalar,
    expectedRightScalar, map_add,
    EEOEInternal.cubeDot_add_left, EEOEInternal.cubeDot_add_right,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [LinearEquiv.map_add]
  simp only [Prod.fst_add, Prod.snd_add,
    EEOEInternal.cubeDot_add_right]
  ring_nf
  rw [show (2 : F) = 0 by decide, show (4 : F) = 0 by decide]
  simp

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem scalar_block_eq_production_ambient
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (A : AFun4 n 1 c d) :
    rawOuterScalarBlock hn hc2 hd2
        (fun zt =>
          (fun wt => bGaugedRootFamilyEquiv
            (by omega : 0 < c) (by omega : 0 < d) x.1 zt wt,
          wGaugedRootFamilyEquiv
            (by omega : 0 < c) x.2 zt))
        (fun zt wt =>
          aGaugedRootFamilyEquiv
            (by omega : 0 < c) (by omega : 0 < d) A zt wt) =
      eoeeAmbientPhase
        (diamondEOEECoeffMap
          (totalEOEELeftAmbientCoords hn hc2 hd2 x).1)
        (TotalEOEEInternal.rightAmbientEquiv hn hc2 hd2 A).1 := by
  rw [left_scalar_coordinate_bridge hn hc2 hd2 x,
    right_scalar_coordinate_bridge hn hc2 hd2 A]
  exact scalar_block_eq_expected_ambient hn hc2 hd2 x A

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem scalar_block_eq_production_cross
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    rawOuterScalarBlock hn hc2 hd2
        (literalOuterLeftFamily
          (by omega : 0 < c) (by omega : 0 < d) l)
        (literalOuterRightFamily
          (by omega : 0 < c) (by omega : 0 < d) A) =
      diamondEOEECross
        (leftSourceEquiv hn hc2 hd2 l).1
        (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).1 := by
  calc
    _ = eoeeAmbientPhase
          (diamondEOEECoeffMap
            (totalEOEELeftAmbientCoords hn hc2 hd2 l.1).1)
          (TotalEOEEInternal.rightAmbientEquiv hn hc2 hd2 A.1).1 :=
      scalar_block_eq_production_ambient hn hc2 hd2 l.1 A.1
    _ = _ := by rfl

set_option maxHeartbeats 4000000 in
theorem w_block_eq_production_cross
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    rawOuterWBlock hn hc2 hd2
        (literalOuterLeftFamily
          (by omega : 0 < c) (by omega : 0 < d) l)
        (literalOuterRightFamily
          (by omega : 0 < c) (by omega : 0 < d) A) =
      diamondTailAmplify (diamondEOEEWCross (n := n))
        (leftSourceEquiv hn hc2 hd2 l).2.1
        (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.1 := by
  rw [raw_outer_w_eq_sum_expected, diamondTailAmplify_apply]
  apply Finset.sum_congr rfl
  intro t _
  let p := (leftSourceEquiv hn hc2 hd2 l).2.1.1 t
  let q := (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.1.1 t
  let x :=
    expectedLeftWAt hn hc2 hd2
      (literalOuterLeftFamily
        (by omega : 0 < c) (by omega : 0 < d) l) t
  let y :=
    expectedRightWNaturalAt hn hc2 hd2
      (literalOuterRightFamily
        (by omega : 0 < c) (by omega : 0 < d) A) t
  have hl := left_w_coordinate_bridge hn hc2 hd2 l t
  have hr := right_w_coordinate_bridge hn hc2 hd2 A t
  have hl1 : p.1.1 = x.1 := congrArg Prod.fst hl
  have hl2 : p.2 = x.2 := congrArg Prod.snd hl
  have hr1 : q.1.1 = y.2 := congrArg Prod.fst hr
  have hr2 : q.2 = y.1 + y.2 := congrArg Prod.snd hr
  change
    cubeDot (cubeDiffI x.1) y.1 +
        cubeDot (cubeDiffI x.2) y.2 =
      diamondEOEEWCross p q
  rw [diamondEOEEWCross_apply, hl1, hl2, hr1, hr2]
  simp only [map_add, EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  abel_nf
  simp only [two_smul, F_add_self, add_zero]

set_option maxHeartbeats 4000000 in
theorem z_block_eq_production_cross
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    rawOuterZBlock hn hc2 hd2
        (literalOuterLeftFamily
          (by omega : 0 < c) (by omega : 0 < d) l)
        (literalOuterRightFamily
          (by omega : 0 < c) (by omega : 0 < d) A) =
      diamondTailAmplify (diamondTailOneEvenZCross (n := n))
        (leftSourceEquiv hn hc2 hd2 l).2.2.1
        (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.2.1 := by
  rw [raw_outer_z_eq_sum_expected, diamondTailAmplify_apply]
  apply Finset.sum_congr rfl
  intro t _
  rw [← left_z_coordinate_bridge hn hc2 hd2 l t,
    ← right_z_coordinate_bridge hn hc2 hd2 A t]

set_option maxHeartbeats 4000000 in
theorem zw_block_eq_production_cross
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    rawOuterZWBlock hn hc2 hd2
        (literalOuterLeftFamily
          (by omega : 0 < c) (by omega : 0 < d) l)
        (literalOuterRightFamily
          (by omega : 0 < c) (by omega : 0 < d) A) =
      diamondMixedTailAmplify
          (n := n) (k := c) (l := d)
          (diamondTailSingleICross (n := n))
        (leftSourceEquiv hn hc2 hd2 l).2.2.2
        (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.2.2 := by
  rw [raw_outer_zw_eq_double_sum_expected]
  simp only [diamondMixedTailAmplify, diamondTailAmplify_apply]
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  rw [← left_zw_coordinate_bridge hn hc2 hd2 l zt wt,
    ← right_zw_coordinate_bridge hn hc2 hd2 A zt wt]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
noncomputable def totalEOEEWAmplifiedCross
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n)) :=
  diamondTailAmplify
    (n := n) (k := d) (diamondEOEEWCross (n := n))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
noncomputable def totalEOEEZAmplifiedCross
    {n c : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n)) :=
  diamondTailAmplify
    (n := n) (k := c) (diamondTailOneEvenZCross (n := n))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
noncomputable def totalEOEEZWAmplifiedCross
    {n c d : Nat} [NeZero n] :
    DiamondMixedTailZero n c d (CyclicCube n) →ₗ[F]
      Module.Dual F (DiamondMixedTailZero n c d (CyclicCube n)) :=
  diamondMixedTailAmplify
    (n := n) (k := c) (l := d)
    (diamondTailSingleICross (n := n))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
noncomputable def totalEOEEZAndZWCross
    {n c d : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
      DiamondMixedTailZero n c d (CyclicCube n)) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
          DiamondMixedTailZero n c d (CyclicCube n)) :=
  diamondCrossProd
    (U₁ := DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n))
    (U₂ := DiamondMixedTailZero n c d (CyclicCube n))
    (V₁ := DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n))
    (V₂ := DiamondMixedTailZero n c d (CyclicCube n))
    (totalEOEEZAmplifiedCross (n := n) (c := c))
    (totalEOEEZWAmplifiedCross (n := n) (c := c) (d := d))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
noncomputable def totalEOEEWZAndZWCross
    {n c d : Nat} [NeZero n] :
    (DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) ×
      (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n))) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n) ×
          (DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
            DiamondMixedTailZero n c d (CyclicCube n))) :=
  diamondCrossProd
    (U₁ := DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n))
    (U₂ :=
      DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n))
    (V₁ := DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n))
    (V₂ :=
      DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n))
    (totalEOEEWAmplifiedCross (n := n) (d := d))
    (totalEOEEZAndZWCross (n := n) (c := c) (d := d))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
noncomputable def totalEOEEBlockCross
    {n c d : Nat} [NeZero n] :
    TotalEOEELeftSourceTarget n c d →ₗ[F]
      Module.Dual F (TotalEOEEInternal.RightReachableTarget n c d) :=
  diamondCrossProd
    (U₁ := DiamondEOEELeftSource n)
    (U₂ :=
      DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) ×
        (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
          DiamondMixedTailZero n c d (CyclicCube n)))
    (V₁ := DiamondEOEERightSource n)
    (V₂ :=
      DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n) ×
        (DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
          DiamondMixedTailZero n c d (CyclicCube n)))
    (diamondEOEECross (n := n))
    (totalEOEEWZAndZWCross (n := n) (c := c) (d := d))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem literal_phase_eq_totalEOEEBlockCross
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    diamondEvenPCross l A =
      totalEOEEBlockCross
        (leftSourceEquiv hn hc2 hd2 l)
        (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A) := by
  unfold totalEOEEBlockCross totalEOEEWZAndZWCross
    totalEOEEZAndZWCross totalEOEEWAmplifiedCross
    totalEOEEZAmplifiedCross totalEOEEZWAmplifiedCross
  change
    diamondEvenPCross l A =
      diamondEOEECross
          (leftSourceEquiv hn hc2 hd2 l).1
          (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).1 +
        (diamondTailAmplify (diamondEOEEWCross (n := n))
            (leftSourceEquiv hn hc2 hd2 l).2.1
            (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.1 +
          (diamondTailAmplify (diamondTailOneEvenZCross (n := n))
              (leftSourceEquiv hn hc2 hd2 l).2.2.1
              (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.2.1 +
            diamondMixedTailAmplify
                (n := n) (k := c) (l := d)
                (diamondTailSingleICross (n := n))
              (leftSourceEquiv hn hc2 hd2 l).2.2.2
              (TotalEOEEInternal.rightReachableEquiv hn hc2 hd2 A).2.2.2))
  rw [literal_phase_four_raw_blocks hn hc2 hd2 l A,
    scalar_block_eq_production_cross hn hc2 hd2 l A,
    w_block_eq_production_cross hn hc2 hd2 l A,
    z_block_eq_production_cross hn hc2 hd2 l A,
    zw_block_eq_production_cross hn hc2 hd2 l A]
  abel


end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP
