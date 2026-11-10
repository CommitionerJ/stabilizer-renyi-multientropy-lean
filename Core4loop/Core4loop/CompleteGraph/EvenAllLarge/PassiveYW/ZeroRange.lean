import Core4loop.CompleteGraph.EvenAllLarge.DescSplitPhase

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYW

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal

noncomputable section

/-! The seventh EEEE row has a bottom-valued left source.  Its right YW
carrier is nevertheless retained exactly; it is the phase and the resulting
source-first cross that vanish. -/

theorem source_eq_zero
    {n b d : Nat} [NeZero n]
    (yw : TotalEEEEYWLeftZero n b d) : yw = 0 :=
  Subsingleton.elim _ _

noncomputable def aggregateSource
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYWLeftZero n b d →ₗ[F]
      K4AggregateKernelEEEESource n b c d where
  toFun yw := (0, (0, (0, (0, (0, (0, (yw, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def leftCoordinate
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYWLeftZero n b d →ₗ[F]
      SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d where
  toFun yw := (0, (0, (0, (0, (0, (0, (yw, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightCoordinate
    {n b c d : Nat} [NeZero n] :
    DiamondMixedTailZero n b d (YWRightBase n) →ₗ[F]
      TotalEEEERightReachableTarget n b c d where
  toFun q := (0, (0, (0, (0, (0, (0, (q, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embed_aggregateSource
    {n b c d : Nat} [NeZero n]
    (yw : TotalEEEEYWLeftZero n b d) :
    k4AggregateKernelEEEESourceEmbed
        (n := n) (b := b) (c := c) (d := d)
        (aggregateSource
          (n := n) (b := b) (c := c) (d := d) yw) =
      leftCoordinate
        (n := n) (b := b) (c := c) (d := d) yw := by
  rfl

theorem aggregateSource_eq_zero
    {n b c d : Nat} [NeZero n]
    (yw : TotalEEEEYWLeftZero n b d) :
    aggregateSource (n := n) (b := b) (c := c) (d := d) yw = 0 := by
  rw [source_eq_zero yw]
  exact (aggregateSource (n := n) (b := b) (c := c) (d := d)).map_zero

theorem leftCoordinate_eq_zero
    {n b c d : Nat} [NeZero n]
    (yw : TotalEEEEYWLeftZero n b d) :
    leftCoordinate (n := n) (b := b) (c := c) (d := d) yw = 0 := by
  rw [source_eq_zero yw]
  exact (leftCoordinate (n := n) (b := b) (c := c) (d := d)).map_zero

theorem coordinatePhase_zero
    {n b c d : Nat} [NeZero n]
    (yw : TotalEEEEYWLeftZero n b d)
    (q : DiamondMixedTailZero n b d (YWRightBase n)) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate
          (n := n) (b := b) (c := c) (d := d) yw)
        (rightCoordinate
          (n := n) (b := b) (c := c) (d := d) q) = 0 := by
  rw [leftCoordinate_eq_zero]
  simp only [TotalEEEEPhase.totalEEEECoordinatePhase,
    TotalEEEEPhase.totalEEEEYBasePhase,
    TotalEEEEPhase.totalEEEEWBasePhase,
    TotalEEEEPhase.totalEEEEYZBasePhase,
    TotalEEEEPhase.totalEEEEWZBasePhase,
    TotalEEEEPhase.totalEEEEYWBasePhase,
    TotalEEEEPhase.totalEEEEYWZBasePhase, cubeDot,
    map_zero, LinearMap.zero_apply, Finset.sum_const_zero, add_zero, zero_mul,
    Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, Pi.zero_apply]

theorem coordinatePhase_arbitraryRight
    {n b c d : Nat} [NeZero n]
    (yw : TotalEEEEYWLeftZero n b d)
    (q : TotalEEEERightReachableTarget n b c d) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate
          (n := n) (b := b) (c := c) (d := d) yw) q = 0 := by
  rw [leftCoordinate_eq_zero]
  simp only [TotalEEEEPhase.totalEEEECoordinatePhase,
    TotalEEEEPhase.totalEEEEYBasePhase,
    TotalEEEEPhase.totalEEEEWBasePhase,
    TotalEEEEPhase.totalEEEEYZBasePhase,
    TotalEEEEPhase.totalEEEEWZBasePhase,
    TotalEEEEPhase.totalEEEEYWBasePhase,
    TotalEEEEPhase.totalEEEEYWZBasePhase, cubeDot,
    map_zero, LinearMap.zero_apply, Finset.sum_const_zero, add_zero, zero_mul,
    Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, Pi.zero_apply]

noncomputable def sectorSource
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYWLeftZero n b d →ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d where
  toFun yw := (0, (0, (0, (0, (0, (0, (yw, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def aggregateKernel
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWLeftZero n b d →ₗ[F]
      K4AggregateKernel n b c d hn hb2 hc2 hd2 :=
  (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2).comp aggregateSource

noncomputable def mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWLeftZero n b d →ₗ[F]
      K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 :=
  (LinearMap.inl F
      (K4AggregateKernel n b c d hn hb2 hc2 hd2)
      (K4AggregatePolarCoordinateTarget n c)).comp
    (aggregateKernel hn hb2 hc2 hd2)

theorem sectorBuild_eq_mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yw : TotalEEEEYWLeftZero n b d) :
    k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
        (sectorSource (n := n) (b := b) (c := c) (d := d) yw) =
      mixedOverlap hn hb2 hc2 hd2 yw := by
  rfl

theorem aggregateKernel_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yw : TotalEEEEYWLeftZero n b d) :
    aggregateKernel hn hb2 hc2 hd2 yw = 0 := by
  rw [source_eq_zero yw]
  exact (aggregateKernel hn hb2 hc2 hd2).map_zero

theorem mixedOverlap_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yw : TotalEEEEYWLeftZero n b d) :
    mixedOverlap hn hb2 hc2 hd2 yw = 0 := by
  rw [source_eq_zero yw]
  exact (mixedOverlap hn hb2 hc2 hd2).map_zero

noncomputable def aggregateDescCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWLeftZero n b d →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (k4BaseDescendedAggregateKernelCross hn2 hn hb2 hc2 hd2).comp
    (aggregateKernel hn hb2 hc2 hd2)

noncomputable def descendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWLeftZero n b d →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2).comp
    (mixedOverlap hn hb2 hc2 hd2)

theorem descendedCross_eq_aggregateDescCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    descendedCross hn2 hn hb2 hc2 hd2 =
      aggregateDescCross hn2 hn hb2 hc2 hd2 := by
  rfl

theorem aggregateDescCross_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    aggregateDescCross hn2 hn hb2 hc2 hd2 = 0 := by
  apply LinearMap.ext
  intro yw
  rw [source_eq_zero yw]
  exact (aggregateDescCross hn2 hn hb2 hc2 hd2).map_zero

theorem descendedCross_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    descendedCross hn2 hn hb2 hc2 hd2 = 0 := by
  apply LinearMap.ext
  intro yw
  rw [source_eq_zero yw]
  exact (descendedCross hn2 hn hb2 hc2 hd2).map_zero

theorem sourceFirstCross_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yw : TotalEEEEYWLeftZero n b d)
    (A : DiamondEvenPReachableA n b c d) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
          (sectorSource (n := n) (b := b) (c := c) (d := d) yw)) A = 0 := by
  rw [sectorBuild_eq_mixedOverlap, mixedOverlap_eq_zero]
  rw [(k4BaseDescendedMixedOverlapCross
    hn2 hn hb2 hc2 hd2).map_zero]
  exact LinearMap.zero_apply A

noncomputable def rightRead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b c d →ₗ[F]
      DiamondMixedTailZero n b d (YWRightBase n) :=
  (LinearMap.fst F _ _).comp
    ((LinearMap.snd F _ _).comp
      ((LinearMap.snd F _ _).comp
        ((LinearMap.snd F _ _).comp
          ((LinearMap.snd F _ _).comp
            ((LinearMap.snd F _ _).comp
              ((LinearMap.snd F _ _).comp
                (diamondEvenPReachableAEEEEEquiv
                  hn hb2 hc2 hd2).toLinearMap))))))

theorem rightRead_apply
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    rightRead hn hb2 hc2 hd2 A =
      (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.2.2.2.2.2.1 :=
  rfl

theorem coordinatePhase_rightRead_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yw : TotalEEEEYWLeftZero n b d)
    (A : DiamondEvenPReachableA n b c d) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate
          (n := n) (b := b) (c := c) (d := d) yw)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) = 0 :=
  coordinatePhase_arbitraryRight yw _

theorem descendedCross_apply_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (yw : TotalEEEEYWLeftZero n b d)
    (A : DiamondEvenPReachableA n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 yw A = 0 := by
  have h := congrArg (fun f => f yw A)
    (descendedCross_eq_zero hn2 hn hb2 hc2 hd2)
  simpa only [LinearMap.zero_apply] using h

theorem range_descendedCross_eq_bot
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.range (descendedCross hn2 hn hb2 hc2 hd2) = ⊥ := by
  rw [descendedCross_eq_zero, LinearMap.range_zero]

theorem finrank_range_descendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range (descendedCross hn2 hn hb2 hc2 hd2)) = 0 := by
  rw [range_descendedCross_eq_bot]
  exact finrank_bot F _

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYW
