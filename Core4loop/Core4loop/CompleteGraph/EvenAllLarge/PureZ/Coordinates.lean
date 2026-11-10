import Core4loop.CompleteGraph.EvenAllLarge.DescSplitPhase

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

noncomputable def aggregateSource
    {n b c d : Nat} [NeZero n] :
    K4AggregateEEEEZKernelTail n c →ₗ[F]
      K4AggregateKernelEEEESource n b c d where
  toFun z := (0, (0, (0, (z, (0, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def polarSource
    {n c : Nat} [NeZero n] :
    K4AggregatePolarZCoordinates n c →ₗ[F]
      K4AggregatePolarCoordinateTarget n c where
  toFun z := ((0, z.1), (0, z.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def sectorSource
    {n b c d : Nat} [NeZero n] :
    K4BaseMixedZSector n c →ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d where
  toFun z := (0, (0, (0, (z, (0, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def aggregateKernel
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregateEEEEZKernelTail n c →ₗ[F]
      K4AggregateKernel n b c d hn hb2 hc2 hd2 :=
  (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2).comp aggregateSource

noncomputable def mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedZSector n c →ₗ[F]
      K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 :=
  LinearMap.prod
    ((aggregateKernel hn hb2 hc2 hd2).comp
      (LinearMap.fst F _ _))
    ((polarSource (n := n) (c := c)).comp
      (LinearMap.snd F _ _))

theorem sectorBuild_eq_mixedOverlap
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c) :
    k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 (sectorSource z) =
      mixedOverlap hn hb2 hc2 hd2 z := by
  rw [k4BaseMixedOverlapSectorBuild_coordinates]
  rfl

noncomputable def gPolarSource
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedZSector n c →ₗ[F] K4GPolarKernel n b c d :=
  (k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2).comp
    (mixedOverlap hn hb2 hc2 hd2)

noncomputable def fullLeftCoordinate
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedZSector n c →ₗ[F]
      SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d :=
  (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).toLinearMap.comp
    ((K4GPolarKernel n b c d).subtype.comp
      (gPolarSource hn2 hn hb2 hc2 hd2))

private noncomputable def zLeftProjection
    {n b c d : Nat} [NeZero n] :
    SquareDiagonal.EvenP.TotalEEEELeftSourceTarget n b c d →ₗ[F]
      TotalEEEEZTailLeft n c where
  toFun z := z.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def zLeftCoordinate
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedZSector n c →ₗ[F] TotalEEEEZTailLeft n c :=
  zLeftProjection.comp (fullLeftCoordinate hn2 hn hb2 hc2 hd2)

noncomputable def rightCoordinate
    {n b c d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n c (DiamondEEOERightAmbient n) →ₗ[F]
      TotalEEEERightReachableTarget n b c d where
  toFun q := (0, (0, (0, (q, (0, (0, (0, 0)))))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def rightProjection
    {n b c d : Nat} [NeZero n] :
    TotalEEEERightReachableTarget n b c d →ₗ[F]
      DiamondEvenAxisValueTailZero n c (DiamondEEOERightAmbient n) where
  toFun q := q.2.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rightRead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b c d →ₗ[F]
      DiamondEvenAxisValueTailZero n c (DiamondEEOERightAmbient n) :=
  rightProjection.comp
    (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2).toLinearMap

noncomputable def rightSection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenAxisValueTailZero n c (DiamondEEOERightAmbient n) →ₗ[F]
      DiamondEvenPReachableA n b c d :=
  (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2).symm.toLinearMap.comp
    rightCoordinate

theorem rightRead_apply
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (A : DiamondEvenPReachableA n b c d) :
    rightRead hn hb2 hc2 hd2 A =
      (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).2.2.2.1 := by
  rfl

theorem rightRead_rightSection
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : DiamondEvenAxisValueTailZero n c (DiamondEEOERightAmbient n)) :
    rightRead hn hb2 hc2 hd2 (rightSection hn hb2 hc2 hd2 q) = q := by
  simp only [rightRead, rightProjection, rightSection, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
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
    K4BaseMixedZSector n c →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2).comp
    (mixedOverlap hn hb2 hc2 hd2)

theorem descendedCross_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c)
    (A : DiamondEvenPReachableA n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 z A =
      k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2
        (mixedOverlap hn hb2 hc2 hd2 z) A := by
  rfl

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ
