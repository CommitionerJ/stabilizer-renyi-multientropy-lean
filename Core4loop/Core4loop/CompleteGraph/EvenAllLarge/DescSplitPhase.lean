import Core4loop.CompleteGraph.EvenAllLarge.MixedOverlapSectors

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

set_option linter.style.setOption false in
section

set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

theorem k4AggregateKernel_BAggregateRaw_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (k : K4AggregateKernel n b c d hn hb2 hc2 hd2) :
    k4BaseBAggregateRaw (by omega : 0 < c) (by omega : 0 < d)
        k.1.1.1 = 0 := by
  have h := congrArg (fun q => q.1.1) (LinearMap.mem_ker.mp k.2)
  change
    k4BaseBAggregateRaw (by omega : 0 < c) (by omega : 0 < d)
        k.1.1.1 = 0 at h
  exact h

theorem k4AggregateKernel_WAggregateRaw_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (k : K4AggregateKernel n b c d hn hb2 hc2 hd2) :
    k4BaseWAggregateRaw (by omega : 0 < b) (by omega : 0 < c)
        k.1.1.2 = 0 := by
  have h := congrArg (fun q => q.2.1) (LinearMap.mem_ker.mp k.2)
  change
    k4BaseWAggregateRaw (by omega : 0 < b) (by omega : 0 < c)
        k.1.1.2 = 0 at h
  exact h

private theorem k4AggregateKappaScalar_zero_left
    {n c : Nat} [NeZero n]
    (W : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar (0 : PVec n c → CyclicCube n) W = 0 := by
  change k4AggregateKappaLinear (0 : PVec n c → CyclicCube n) W = 0
  rw [map_zero]
  rfl

private theorem k4AggregateKappaScalar_zero_right
    {n c : Nat} [NeZero n]
    (B : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar B (0 : PVec n c → CyclicCube n) = 0 := by
  change k4AggregateKappaLinear B (0 : PVec n c → CyclicCube n) = 0
  rw [map_zero]

theorem k4EvenPSlicePolar_aggregateKernel_add_lift
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (k : K4AggregateKernel n b c d hn hb2 hc2 hd2)
    (u : K4AggregatePolarKernel n c)
    (K : K4EvenPSlice n b c d) :
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    let BKbar :=
      k4BaseBAggregateRaw (by omega : 0 < c) (by omega : 0 < d) K.1
    let WKbar :=
      k4BaseWAggregateRaw (by omega : 0 < b) (by omega : 0 < c) K.2
    k4EvenPSlicePolar (k.1 + lift).1 K =
      k4AggregateKappaScalar u.1.1.1 WKbar +
        k4AggregateKappaScalar BKbar u.1.2.1 := by
  dsimp only
  have hBk := k4AggregateKernel_BAggregateRaw_eq_zero
    hn hb2 hc2 hd2 k
  have hWk := k4AggregateKernel_WAggregateRaw_eq_zero
    hn hb2 hc2 hd2 k
  have hBlift := k4EvenPBAggregateRaw_lift
    (n := n) (b := b) (c := c) (d := d)
    (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) u.1
  have hWlift := k4EvenPWAggregateRaw_lift
    (n := n) (b := b) (c := c) (d := d)
    (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d) u.1
  change
    k4BaseBAggregateRaw (by omega : 0 < c) (by omega : 0 < d)
        (k4AggregateLift (n := n) (b := b) (c := c) (d := d)
          (by omega) (by omega) (by omega) u.1).1.1 =
      u.1.1.1 at hBlift
  change
    k4BaseWAggregateRaw (by omega : 0 < b) (by omega : 0 < c)
        (k4AggregateLift (n := n) (b := b) (c := c) (d := d)
          (by omega) (by omega) (by omega) u.1).1.2 =
      u.1.2.1 at hWlift
  unfold k4EvenPSlicePolar
  simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
  rw [k4BWSlice_add_left, k4BWSlice_add_right]
  simp_rw [k4BWSlice_eq_aggregate_kappa
    (by omega : 0 < b) (by omega : 0 < c) (by omega : 0 < d)]
  rw [hBk, hWk, hBlift, hWlift]
  rw [k4AggregateKappaScalar_zero_left,
    k4AggregateKappaScalar_zero_right]
  simp

theorem k4BaseDescendedMixedOverlapCross_split_phase
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (k : K4AggregateKernel n b c d hn hb2 hc2 hd2)
    (x : K4AggregatePolarCoordinateTarget n c)
    (r : K4EvenPBaseRight n b c d) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 x
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    let BKbar :=
      k4BaseBAggregateRaw (by omega : 0 < c) (by omega : 0 < d) r.1.2.1
    let WKbar :=
      k4BaseWAggregateRaw (by omega : 0 < b) (by omega : 0 < c) r.1.2.2
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2 (k, x)
        (k4BaseRightToDiamondReachable r) =
      diamondEvenPCross k.1 (k4BaseRightToDiamondReachable r) +
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 +
        k4AggregateKappaScalar u.1.1.1 WKbar +
        k4AggregateKappaScalar BKbar u.1.2.1 := by
  dsimp only
  rw [k4BaseDescendedMixedOverlapCross_literal]
  have hslice := k4EvenPSlicePolar_aggregateKernel_add_lift
    hn hb2 hc2 hd2 k
      (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 x) r.1.2
  dsimp only at hslice
  rw [hslice]
  have hdiamond :
      diamondEvenPCross k.1 (k4BaseRightToDiamondReachable r) =
        coeffApplyA (KBMap k.1.1.1 + KWMap k.1.1.2) r.1.1 := by
    rfl
  rw [hdiamond]
  simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, map_add]
  simp only [coeffApplyA_eq_sum, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  abel

theorem k4BaseDescendedMixedOverlapSectorCross_split_phase
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedOverlapSectorSource n b c d)
    (r : K4EvenPBaseRight n b c d) :
    let z := k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    let BKbar :=
      k4BaseBAggregateRaw (by omega : 0 < c) (by omega : 0 < d) r.1.2.1
    let WKbar :=
      k4BaseWAggregateRaw (by omega : 0 < b) (by omega : 0 < c) r.1.2.2
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2 z
        (k4BaseRightToDiamondReachable r) =
      diamondEvenPCross z.1.1 (k4BaseRightToDiamondReachable r) +
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 +
        k4AggregateKappaScalar u.1.1.1 WKbar +
        k4AggregateKappaScalar BKbar u.1.2.1 := by
  dsimp only
  exact k4BaseDescendedMixedOverlapCross_split_phase
    hn2 hn hb2 hc2 hd2
    (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 s).1
    (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 s).2 r


end


end


end Core4loop.CompleteGraph.EvenP.BaseKKT
