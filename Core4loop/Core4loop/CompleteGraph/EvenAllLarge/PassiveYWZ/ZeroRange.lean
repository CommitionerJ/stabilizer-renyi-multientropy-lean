import Core4loop.CompleteGraph.EvenAllLarge.DescSplitPhase

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option maxSynthPendingDepth 2048

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYWZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

theorem source_eq_zero
    {n b c d : Nat} [NeZero n]
    (ywz : TotalEEEEYWZLeftZero n b c d) : ywz = 0 := by
  apply Subtype.ext
  funext yt
  apply Subtype.ext
  funext zt
  apply Subtype.ext
  funext wt
  exact Subsingleton.elim _ _

noncomputable def aggregateSource
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYWZLeftZero n b c d →ₗ[F]
      CompleteGraph.EvenP.BaseKKT.K4AggregateKernelEEEESource n b c d where
  toFun ywz := (0, (0, (0, (0, (0, (0, (0, ywz)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def leftCoordinate
    {n b c d : Nat} [NeZero n] :
    TotalEEEEYWZLeftZero n b c d →ₗ[F]
      SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d where
  toFun ywz := (0, (0, (0, (0, (0, (0, (0, ywz)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightCoordinate
    {n b c d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n b
        (DiamondEvenAxisValueTailZero n c
          (DiamondEvenAxisValueTailZero n d (CyclicCube n))) →ₗ[F]
      TotalEEEERightReachableTarget n b c d where
  toFun q := (0, (0, (0, (0, (0, (0, (0, q)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embed_aggregateSource
    {n b c d : Nat} [NeZero n]
    (ywz : TotalEEEEYWZLeftZero n b c d) :
    CompleteGraph.EvenP.BaseKKT.k4AggregateKernelEEEESourceEmbed
        (aggregateSource ywz) = leftCoordinate ywz := by
  rfl

theorem aggregateSource_eq_zero
    {n b c d : Nat} [NeZero n]
    (ywz : TotalEEEEYWZLeftZero n b c d) :
    aggregateSource ywz = 0 := by
  rw [source_eq_zero ywz]
  exact (aggregateSource
    (n := n) (b := b) (c := c) (d := d)).map_zero

theorem leftCoordinate_eq_zero
    {n b c d : Nat} [NeZero n]
    (ywz : TotalEEEEYWZLeftZero n b c d) :
    leftCoordinate ywz = 0 := by
  rw [source_eq_zero ywz]
  exact (leftCoordinate
    (n := n) (b := b) (c := c) (d := d)).map_zero

theorem coordinatePhase_zero
    {n b c d : Nat} [NeZero n]
    (ywz : TotalEEEEYWZLeftZero n b c d)
    (q : DiamondEvenAxisValueTailZero n b
      (DiamondEvenAxisValueTailZero n c
        (DiamondEvenAxisValueTailZero n d (CyclicCube n)))) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate ywz) (rightCoordinate q) = 0 := by
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
    (ywz : TotalEEEEYWZLeftZero n b c d)
    (q : TotalEEEERightReachableTarget n b c d) :
    TotalEEEEPhase.totalEEEECoordinatePhase (leftCoordinate ywz) q = 0 := by
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
    TotalEEEEYWZLeftZero n b c d →ₗ[F]
      CompleteGraph.EvenP.BaseKKT.K4BaseMixedOverlapSectorSource n b c d where
  toFun ywz := (0, (0, (0, (0, (0, (0, (0, ywz)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def aggregateKernel
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWZLeftZero n b c d →ₗ[F]
      CompleteGraph.EvenP.BaseKKT.K4AggregateKernel n b c d hn hb2 hc2 hd2 :=
  (CompleteGraph.EvenP.BaseKKT.k4AggregateKernelEEEEBuild
    hn hb2 hc2 hd2).comp aggregateSource

noncomputable def mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWZLeftZero n b c d →ₗ[F]
      CompleteGraph.EvenP.BaseKKT.K4BaseMixedOverlapSource
        n b c d hn hb2 hc2 hd2 :=
  (LinearMap.inl F
      (CompleteGraph.EvenP.BaseKKT.K4AggregateKernel n b c d hn hb2 hc2 hd2)
      (CompleteGraph.EvenP.BaseKKT.K4AggregatePolarCoordinateTarget n c)).comp
    (aggregateKernel hn hb2 hc2 hd2)

theorem sectorBuild_eq_mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (ywz : TotalEEEEYWZLeftZero n b c d) :
    CompleteGraph.EvenP.BaseKKT.k4BaseMixedOverlapSectorBuild
        hn hb2 hc2 hd2 (sectorSource ywz) =
      mixedOverlap hn hb2 hc2 hd2 ywz := by
  rfl

theorem aggregateKernel_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (ywz : TotalEEEEYWZLeftZero n b c d) :
    aggregateKernel hn hb2 hc2 hd2 ywz = 0 := by
  rw [source_eq_zero ywz]
  exact (aggregateKernel hn hb2 hc2 hd2).map_zero

theorem mixedOverlap_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (ywz : TotalEEEEYWZLeftZero n b c d) :
    mixedOverlap hn hb2 hc2 hd2 ywz = 0 := by
  rw [source_eq_zero ywz]
  exact (mixedOverlap hn hb2 hc2 hd2).map_zero

noncomputable def aggregateDescCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWZLeftZero n b c d →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (CompleteGraph.EvenP.BaseKKT.k4BaseDescendedAggregateKernelCross
    hn2 hn hb2 hc2 hd2).comp (aggregateKernel hn hb2 hc2 hd2)

noncomputable def descendedCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    TotalEEEEYWZLeftZero n b c d →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (CompleteGraph.EvenP.BaseKKT.k4BaseDescendedMixedOverlapCross
    hn2 hn hb2 hc2 hd2).comp (mixedOverlap hn hb2 hc2 hd2)

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
  intro ywz
  rw [source_eq_zero ywz]
  exact (aggregateDescCross hn2 hn hb2 hc2 hd2).map_zero

theorem descendedCross_eq_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    descendedCross hn2 hn hb2 hc2 hd2 = 0 := by
  apply LinearMap.ext
  intro ywz
  rw [source_eq_zero ywz]
  exact (descendedCross hn2 hn hb2 hc2 hd2).map_zero

theorem sourceFirstCross_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (ywz : TotalEEEEYWZLeftZero n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    CompleteGraph.EvenP.BaseKKT.k4BaseDescendedMixedOverlapCross
        hn2 hn hb2 hc2 hd2
        (CompleteGraph.EvenP.BaseKKT.k4BaseMixedOverlapSectorBuild
          hn hb2 hc2 hd2 (sectorSource ywz)) A = 0 := by
  rw [sectorBuild_eq_mixedOverlap, mixedOverlap_eq_zero]
  rw [(CompleteGraph.EvenP.BaseKKT.k4BaseDescendedMixedOverlapCross
    hn2 hn hb2 hc2 hd2).map_zero]
  exact LinearMap.zero_apply A

noncomputable def rightRead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b c d →ₗ[F]
      DiamondEvenAxisValueTailZero n b
        (DiamondEvenAxisValueTailZero n c
          (DiamondEvenAxisValueTailZero n d (CyclicCube n))) :=
  (LinearMap.snd F _ _).comp
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
      (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.2.2.2.2.2.2 :=
  rfl

theorem coordinatePhase_rightRead_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (ywz : TotalEEEEYWZLeftZero n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    TotalEEEEPhase.totalEEEECoordinatePhase
        (leftCoordinate ywz)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) = 0 :=
  coordinatePhase_arbitraryRight ywz _

theorem descendedCross_apply_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (ywz : TotalEEEEYWZLeftZero n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 ywz A = 0 := by
  have h := congrArg (fun f => f ywz A)
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

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveYWZ
