import Core4loop.CompleteGraph.EvenAllLarge.PassiveWZ.Intertwine

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

noncomputable def tailCross
    {n c d : Nat} [NeZero n] :
    TotalEEEEWZTailLeft n c d →ₗ[F]
      Module.Dual F
        (DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n)) :=
  diamondMixedTailAmplify
    (TotalEEEEBlockP2.totalEEEEWZBaseCross (n := n))

noncomputable def rightRead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b c d →ₗ[F]
      DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n) :=
  (LinearMap.fst F _ _).comp
    ((LinearMap.snd F _ _).comp
      ((LinearMap.snd F _ _).comp
        ((LinearMap.snd F _ _).comp
          ((LinearMap.snd F _ _).comp
            ((LinearMap.snd F _ _).comp
              (diamondEvenPReachableAEEEEEquiv
                hn hb2 hc2 hd2).toLinearMap)))))

noncomputable def rightSection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n) →ₗ[F]
      DiamondEvenPReachableA n b c d :=
  (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2).symm.toLinearMap.comp
    (rightCoordinate (n := n) (b := b) (c := c) (d := d))

@[simp] theorem rightRead_rightSection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : DiamondMixedTailZero n c d (CyclicCube n × CyclicCube n)) :
    rightRead hn hb2 hc2 hd2 (rightSection hn hb2 hc2 hd2 q) = q := by
  simp only [rightRead, rightSection, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
    LinearMap.fst_apply, LinearMap.snd_apply,
    rightCoordinate, LinearMap.coe_mk, AddHom.coe_mk]

theorem rightRead_surjective
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Function.Surjective (rightRead hn hb2 hc2 hd2) := by
  intro q
  exact ⟨rightSection hn hb2 hc2 hd2 q,
    rightRead_rightSection hn hb2 hc2 hd2 q⟩

noncomputable def descendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEWZTailLeft n c d →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2).comp
    (mixedOverlap hn hb2 hc2 hd2)

theorem coordinatePhase_rightRead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (wz : TotalEEEEWZTailLeft n c d)
    (A : DiamondEvenPReachableA n b c d) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate
          (n := n) (b := b) (c := c) (d := d) wz)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      tailCross (n := n) (c := c) (d := d) wz
        (rightRead hn hb2 hc2 hd2 A) := by
  simp only [TotalEEEEPhase.totalEEEECoordinatePhase,
    leftCoordinate, rightRead, tailCross,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    diamondMixedTailAmplify, diamondTailAmplify_apply,
    TotalEEEEBlockP2.totalEEEEWZBaseCross,
    TotalEEEEPhase.totalEEEEYBasePhase,
    TotalEEEEPhase.totalEEEEWBasePhase,
    TotalEEEEPhase.totalEEEEYZBasePhase,
    TotalEEEEPhase.totalEEEEYWBasePhase,
    TotalEEEEPhase.totalEEEEYWZBasePhase, cubeDot,
    map_zero, LinearMap.zero_apply, LinearMap.mk₂_apply,
    Finset.sum_const_zero, zero_add, add_zero, zero_mul,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap,
    Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, Pi.zero_apply]

theorem descendedCross_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (wz : TotalEEEEWZTailLeft n c d)
    (A : DiamondEvenPReachableA n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 wz A =
      tailCross (n := n) (c := c) (d := d) wz
        (rightRead hn hb2 hc2 hd2 A) := by
  change
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (mixedOverlap hn hb2 hc2 hd2 wz) A = _
  rw [addedPhaseVanishes]
  exact @PassiveY.diamondCross_eq_of_coordinates n b c d _
    hn hb2 hc2 hd2
    (aggregateKernel hn hb2 hc2 hd2 wz).1
    A
    (leftCoordinate (n := n) (b := b) (c := c) (d := d) wz)
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A)
    (tailCross (n := n) (c := c) (d := d) wz
      (rightRead hn hb2 hc2 hd2 A))
    (aggregateKernel_leftCoordinate hn hb2 hc2 hd2 wz)
    rfl
    (coordinatePhase_rightRead hn hb2 hc2 hd2 wz A)

theorem descendedCross_eq
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    descendedCross hn2 hn hb2 hc2 hd2 =
      (rightRead hn hb2 hc2 hd2).dualMap.comp
        (tailCross (n := n) (c := c) (d := d)) := by
  ext wz A
  exact descendedCross_apply hn2 hn hb2 hc2 hd2 wz A

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveWZ
