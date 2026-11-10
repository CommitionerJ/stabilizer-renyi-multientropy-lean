import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.Build

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

private theorem mixedOverlap_fst
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : TotalEEEEYTailLeft n b) :
    (mixedOverlap hn hb2 hc2 hd2 y).1 =
      aggregateKernel hn hb2 hc2 hd2 y :=
  rfl

private theorem mixedOverlap_snd
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : TotalEEEEYTailLeft n b) :
    (mixedOverlap hn hb2 hc2 hd2 y).2 = 0 :=
  rfl

private theorem coeffApplyA_zero_local
    {n b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) :
    coeffApplyA (0 : AFun4 n b c d) A = 0 := by
  rw [coeffApplyA_eq_sum]
  simp

private theorem kappa_zero_left_local
    {n c : Nat} [NeZero n]
    (W : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar (0 : PVec n c → CyclicCube n) W = 0 := by
  change k4AggregateKappaLinear (0 : PVec n c → CyclicCube n) W = 0
  rw [map_zero]
  rfl

private theorem kappa_zero_right_local
    {n c : Nat} [NeZero n]
    (B : PVec n c → CyclicCube n) :
    k4AggregateKappaScalar B (0 : PVec n c → CyclicCube n) = 0 := by
  change k4AggregateKappaLinear B (0 : PVec n c → CyclicCube n) = 0
  rw [map_zero]

theorem addedPhaseVanishesOnProjection
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : TotalEEEEYTailLeft n b)
    (r : K4EvenPBaseRight n b c d) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (mixedOverlap hn hb2 hc2 hd2 y)
        (k4BaseRightToDiamondReachable r) =
      diamondEvenPCross (aggregateKernel hn hb2 hc2 hd2 y).1
        (k4BaseRightToDiamondReachable r) := by
  have hu :
      k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
          (0 : K4AggregatePolarCoordinateTarget n c) = 0 :=
    (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2).map_zero
  rw [k4BaseDescendedMixedOverlapCross_split_phase]
  rw [mixedOverlap_fst, mixedOverlap_snd]
  rw [hu]
  simp only [Submodule.coe_zero]
  rw [(k4AggregateLift
    (n := n) (b := b) (c := c) (d := d)
    (by omega) (by omega) (by omega)).map_zero]
  simp only [Submodule.coe_zero, Prod.fst_zero, Prod.snd_zero]
  rw [(KBMap (n := n) (a := 1) (b := b) (c := c) (d := d)).map_zero]
  rw [(KWMap (n := n) (a := 1) (b := b) (c := c) (d := d)).map_zero]
  simp only [zero_add]
  rw [coeffApplyA_zero_local, kappa_zero_left_local,
    kappa_zero_right_local]
  simp only [add_zero]

theorem addedPhaseVanishes
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (y : TotalEEEEYTailLeft n b)
    (A : DiamondEvenPReachableA n b c d) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (mixedOverlap hn hb2 hc2 hd2 y) A =
      diamondEvenPCross (aggregateKernel hn hb2 hc2 hd2 y).1 A := by
  rcases k4BaseRightToDiamondReachable_surjective A with ⟨r, rfl⟩
  exact addedPhaseVanishesOnProjection hn2 hn hb2 hc2 hd2 y r

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY
