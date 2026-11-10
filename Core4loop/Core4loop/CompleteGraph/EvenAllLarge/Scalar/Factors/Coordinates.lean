import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Multiplier

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar.ShallowProjectionProbe

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

theorem scalarLeftCoordinate_B00_eq_fullRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 =
      (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).1.1.1.1 := by
  rfl

theorem fullLeftCoordinate_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    fullLeftCoordinate hn2 hn hb2 hc2 hd2 s =
      diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
        (gPolarSource hn2 hn hb2 hc2 hd2 s).1 := by
  rfl

theorem fullRead_B00_eq_polar_Bcoord
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).1.1.1.1 =
      (k4BAggregateCoordEquiv hn hc2 u.1.1).1.1.1 := by
  dsimp only
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift := by
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 z
  have hAgg :
      k4EvenPAggregate hn hb2 (by omega) hd2 z.1.1 = 0 := by
    exact LinearMap.mem_ker.mp z.1.2
  have hsigma :
      k4EvenPAggregate hn hb2 (by omega) hd2
          (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = u.1 := by
    rw [hval, map_add, hAgg, zero_add]
    exact k4EvenPAggregate_lift hn hb2 (by omega) hd2 u.1
  have hB00 := congrArg (fun q => q.1.1.1.1)
    (k4AggregateEEEERead_intertwines
      hn hb2 hc2 hd2 (gPolarSource hn2 hn hb2 hc2 hd2 s).1)
  rw [← fullLeftCoordinate_apply hn2 hn hb2 hc2 hd2 s] at hB00
  rw [hsigma] at hB00
  exact hB00

theorem polar_Bcoord_eq_profile_build
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource (c := c) x)
    (k4BAggregateCoordEquiv hn hc2 u.1.1).1.1.1 =
      (k4PHeadScalarBuild x.1.1).1.1 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource (c := c) x)
  let Bc := k4BAggregateCoordEquiv hn hc2 u.1.1
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  let X : K4BScalarRadical n :=
    ⟨Bc.1.1, LinearMap.mem_ker.mpr hu.1⟩
  have hp0 := congrArg (fun q => q.1.1.1)
    (k4AggregatePolarKernelCoordinateRead_build
      hn2 hn hc2 (polarSource (c := c) x))
  have hp : k4PHeadScalarRead X = x.1.1 := by
    exact hp0
  have hread := k4PHeadScalarBuild_read X
  have hval := congrArg (fun q => q.1.1) hread
  change Bc.1.1.1 = (k4PHeadScalarBuild x.1.1).1.1
  calc
    Bc.1.1.1 = X.1 := rfl
    _ = (k4PHeadScalarBuild (k4PHeadScalarRead X)).1.1 := hval.symm
    _ = (k4PHeadScalarBuild x.1.1).1.1 := by rw [hp]

theorem scalarLeftCoordinate_B00
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 =
      (k4PHeadScalarBuild s.2.1.1).1.1 := by
  rw [scalarLeftCoordinate_B00_eq_fullRead]
  rw [fullRead_B00_eq_polar_Bcoord]
  exact polar_Bcoord_eq_profile_build hn2 hn hc2 s.2

theorem scalarCoeffMap_row011
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 =
      cubeDiffI
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 := by
  rw [scalarCoeffMap]
  change
    cubeDiffI
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1 + 0 =
      cubeDiffI
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1
  simp

theorem rest_row011_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : K4AggregateEEEEScalarKernel n)
    (bf : K4BFreeHeadRadical n)
    (wf : K4WFreeHeadRadical n) (pw : Profile n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2
      (q, ((0, bf), (wf, pw)))).1.2.2 = 0 := by
  rw [scalarCoeffMap_row011]
  rw [scalarLeftCoordinate_B00]
  exact map_zero cubeDiffI

theorem scalarCoeffMap_row011_depends_only_on_B_profile
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2
        (0, ((s.2.1.1, 0), (0, 0)))).1.2.2 := by
  rw [scalarCoeffMap_row011, scalarLeftCoordinate_B00]
  rw [scalarCoeffMap_row011, scalarLeftCoordinate_B00]

theorem scalarLeftCoordinate_W00_eq_fullRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 =
      (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).2.1.2.1 := by
  rfl

theorem fullRead_W00_eq_polar_Wcoord
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).2.1.2.1 =
      (k4WAggregateCoordEquiv hn hc2 u.1.2).1.2.1 := by
  dsimp only
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift := by
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 z
  have hAgg :
      k4EvenPAggregate hn hb2 (by omega) hd2 z.1.1 = 0 := by
    exact LinearMap.mem_ker.mp z.1.2
  have hsigma :
      k4EvenPAggregate hn hb2 (by omega) hd2
          (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = u.1 := by
    rw [hval, map_add, hAgg, zero_add]
    exact k4EvenPAggregate_lift hn hb2 (by omega) hd2 u.1
  have hW00 := congrArg (fun q => q.2.1.2.1)
    (k4AggregateEEEERead_intertwines
      hn hb2 hc2 hd2 (gPolarSource hn2 hn hb2 hc2 hd2 s).1)
  rw [← fullLeftCoordinate_apply hn2 hn hb2 hc2 hd2 s] at hW00
  rw [hsigma] at hW00
  exact hW00

theorem polar_Wcoord_eq_profile_build
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource (c := c) x)
    (k4WAggregateCoordEquiv hn hc2 u.1.2).1.2.1 =
      (k4RHeadScalarBuild x.2.2).1.1 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource (c := c) x)
  let Wc := k4WAggregateCoordEquiv hn hc2 u.1.2
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  let X : K4WScalarRadical n :=
    ⟨Wc.1.2, LinearMap.mem_ker.mpr hu.2.2.2.2.1⟩
  have hp0 := congrArg (fun q => q.2.1.2)
    (k4AggregatePolarKernelCoordinateRead_build
      hn2 hn hc2 (polarSource (c := c) x))
  have hp : k4RHeadScalarRead X = x.2.2 := by
    exact hp0
  have hread := k4RHeadScalarBuild_read X
  have hval := congrArg (fun q => q.1.1) hread
  change Wc.1.2.1 = (k4RHeadScalarBuild x.2.2).1.1
  calc
    Wc.1.2.1 = X.1.1 := rfl
    _ = (k4RHeadScalarBuild (k4RHeadScalarRead X)).1.1 := hval.symm
    _ = (k4RHeadScalarBuild x.2.2).1.1 := by rw [hp]

theorem scalarLeftCoordinate_W00
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 =
      (k4RHeadScalarBuild s.2.2.2).1.1 := by
  rw [scalarLeftCoordinate_W00_eq_fullRead]
  rw [fullRead_W00_eq_polar_Wcoord]
  exact polar_Wcoord_eq_profile_build hn2 hn hc2 s.2

theorem scalarCoeffMap_row110
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.2.1 =
      cubeDiffK
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 := by
  rw [scalarCoeffMap]
  change
    cubeDiffK
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 + 0 =
      cubeDiffK
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1
  simp

theorem scalarCoeffMap_row110_depends_only_on_W_profile
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.2.1 =
      (scalarCoeffMap hn2 hn hb2 hc2 hd2
        (0, ((0, 0), (0, s.2.2.2)))).2.2.1 := by
  rw [scalarCoeffMap_row110, scalarLeftCoordinate_W00]
  rw [scalarCoeffMap_row110, scalarLeftCoordinate_W00]

theorem scalarLeftCoordinate_B10_eq_fullRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.1 =
      (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).1.1.2 := by
  rfl

theorem fullRead_B10_eq_polar_Bcoord
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).1.1.2 =
      (k4BAggregateCoordEquiv hn hc2 u.1.1).1.2 := by
  dsimp only
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift := by
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 z
  have hAgg :
      k4EvenPAggregate hn hb2 (by omega) hd2 z.1.1 = 0 := by
    exact LinearMap.mem_ker.mp z.1.2
  have hsigma :
      k4EvenPAggregate hn hb2 (by omega) hd2
          (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = u.1 := by
    rw [hval, map_add, hAgg, zero_add]
    exact k4EvenPAggregate_lift hn hb2 (by omega) hd2 u.1
  have hB10 := congrArg (fun q => q.1.1.2)
    (k4AggregateEEEERead_intertwines
      hn hb2 hc2 hd2 (gPolarSource hn2 hn hb2 hc2 hd2 s).1)
  rw [← fullLeftCoordinate_apply hn2 hn hb2 hc2 hd2 s] at hB10
  rw [hsigma] at hB10
  exact hB10

theorem polar_Bfree_coord
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource (c := c) x)
    (k4BAggregateCoordEquiv hn hc2 u.1.1).1.2 = x.1.2.1 := by
  dsimp only
  have h := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource (c := c) x)
  exact congrArg (fun q => q.1.1.2.1) h

theorem scalarLeftCoordinate_B10
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.1 =
      s.2.1.2.1 := by
  rw [scalarLeftCoordinate_B10_eq_fullRead]
  rw [fullRead_B10_eq_polar_Bcoord]
  exact polar_Bfree_coord hn2 hn hc2 s.2

theorem scalarLeftCoordinate_Wsum_eq_fullRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 =
      (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).2.1.1 := by
  rfl

theorem fullRead_Wsum_eq_polar_Wcoord
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    (k4AggregateEEEERead
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)).2.1.1 =
      (k4WAggregateCoordEquiv hn hc2 u.1.2).1.1 := by
  dsimp only
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift := by
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 z
  have hAgg :
      k4EvenPAggregate hn hb2 (by omega) hd2 z.1.1 = 0 := by
    exact LinearMap.mem_ker.mp z.1.2
  have hsigma :
      k4EvenPAggregate hn hb2 (by omega) hd2
          (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = u.1 := by
    rw [hval, map_add, hAgg, zero_add]
    exact k4EvenPAggregate_lift hn hb2 (by omega) hd2 u.1
  have hWsum := congrArg (fun q => q.2.1.1)
    (k4AggregateEEEERead_intertwines
      hn hb2 hc2 hd2 (gPolarSource hn2 hn hb2 hc2 hd2 s).1)
  rw [← fullLeftCoordinate_apply hn2 hn hb2 hc2 hd2 s] at hWsum
  rw [hsigma] at hWsum
  exact hWsum

theorem polar_Wfree_coord
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource (c := c) x)
    (k4WAggregateCoordEquiv hn hc2 u.1.2).1.1 = x.2.1.1 := by
  dsimp only
  have h := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource (c := c) x)
  exact congrArg (fun q => q.2.1.1.1) h

theorem scalarLeftCoordinate_Wsum
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 =
      s.2.2.1.1 := by
  rw [scalarLeftCoordinate_Wsum_eq_fullRead]
  rw [fullRead_Wsum_eq_polar_Wcoord]
  exact polar_Wfree_coord hn2 hn hc2 s.2

theorem scalarLeftCoordinate_W01
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 =
      s.2.2.1.1 +
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 := by
  have h := scalarLeftCoordinate_Wsum hn2 hn hb2 hc2 hd2 s
  have hself :
      (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 = 0 := by
    exact EEEEInternal.module_add_self _
  calc
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 =
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 + 0 := by
          simp
    _ = (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2 +
        ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
          (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1) := by
            rw [hself]
    _ = ((scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 +
          (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.2) +
          (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 := by abel
    _ = s.2.2.1.1 +
        (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.1.1 := by rw [h]

end
end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar.ShallowProjectionProbe

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar.NestedOneTailProbe

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

private noncomputable def nestedRead
    {n s t : Nat} [NeZero n]
    (hn : Even n) (hs2 : 2 ≤ s) (ht2 : 2 ≤ t)
    (f : PVec n s → PVec n t → CyclicCube n) :
    NestedCoords n s t :=
  let inner := pointedSrcEvenValueEquiv
    (PVec n t) (CyclicCube n) (zeroVec : PVec n t)
      (even_card_PVec hn ht2)
  let outer := pointedSrcEvenValueEquiv
    (PVec n s) (PVec n t → CyclicCube n) (zeroVec : PVec n s)
      (even_card_PVec hn hs2) f
  let x :=
    ((inner outer.1.1, inner outer.1.2),
      TotalEOEEInternal.TailCoordHelpers.tailZeroCongr
        (zeroVec : PVec n s) inner outer.2)
  let tTail :=
    (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := PVec n t) (U := CyclicCube n) (V := CyclicCube n)
      (zeroVec : PVec n t)).symm (x.1.1.2, x.1.2.2)
  let sTail :=
    TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := PVec n s) (U := CyclicCube n × CyclicCube n)
      (V := PointedValueTailZero (PVec n t) (CyclicCube n)
        (zeroVec : PVec n t)) (zeroVec : PVec n s) x.2
  ((x.1.1.1, x.1.2.1), (tTail, (sTail.1, sTail.2)))

theorem nestedRead_second_one_tail_scalar
    {n s t : Nat} [NeZero n]
    (hn : Even n) (hs2 : 2 ≤ s) (ht2 : 2 ≤ t)
    (g : PVec n s → CyclicCube n) :
    (nestedRead hn hs2 ht2
      (fun x y => if y = zeroVec then g x else 0)).1 =
      (((∑ x, g x), 0),
        ((∑ x : PointedTail (PVec n s) zeroVec, g x.1), 0)) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma]
      simp
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K]
      apply Fintype.sum_eq_zero
      intro x
      simp [x.2]
  · apply Prod.ext
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K]
      simp
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K]
      apply Fintype.sum_eq_zero
      intro x
      simp [x.2]

theorem nestedRead_first_one_tail_scalar
    {n s t : Nat} [NeZero n]
    (hn : Even n) (hs2 : 2 ≤ s) (ht2 : 2 ≤ t)
    (g : PVec n t → CyclicCube n) :
    (nestedRead hn hs2 ht2
      (fun x y => if x = zeroVec then g y else 0)).1 =
      (((∑ y, g y),
          (∑ y : PointedTail (PVec n t) zeroVec, g y.1)),
        (0, 0)) := by
  apply Prod.ext
  · apply Prod.ext
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma]
      simp
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K]
      simp
  · apply Prod.ext
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K]
      simp only [Finset.sum_apply]
      apply Fintype.sum_eq_zero
      intro y
      apply Fintype.sum_eq_zero
      intro x
      simp [x.2]
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K]
      simp only [Finset.sum_apply]
      apply Fintype.sum_eq_zero
      intro y
      apply Fintype.sum_eq_zero
      intro x
      simp [x.2]

private theorem bNestedCoords_eq_nestedRead
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (B : BFun4 n 1 c d) :
    bNestedCoords hn hc2 hd2 B =
      nestedRead hn hc2 hd2
        (TotalEOEEInternal.bGaugedRootFamilyEquiv
          (by omega) (by omega) B) := by
  rfl

private theorem wNestedCoords_eq_nestedRead
    {n b c : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c)
    (W : WFun4 n 1 b c) :
    wNestedCoords hn hb2 hc2 W =
      nestedRead hn hb2 hc2
        (wGaugedYZFamilyEquiv (by omega) (by omega) W) := by
  rfl

theorem aggregateLift_B_scalar
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
      (k4AggregateLift (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d) x)).1.1.1 =
      (((∑ zt, x.1.1 zt), 0),
        ((∑ zt : PointedTail (PVec n c) zeroVec, x.1.1 zt.1), 0)) := by
  change (bNestedCoords hn hc2 hd2
      (k4AggregateLift (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d) x).1.1).1 = _
  rw [bNestedCoords_eq_nestedRead]
  have hGauge := k4AggregateLiftRaw_gauge
    (n := n) (b := b) (c := c) (d := d)
    (by omega) (by omega) (by omega) x
  have hB := congrArg Prod.fst hGauge
  change
    TotalEOEEInternal.bGaugedRootFamilyEquiv (by omega) (by omega)
        (k4AggregateLift (by omega : 0 < b) (by omega : 0 < c)
          (by omega : 0 < d) x).1.1 =
      k4BOneTailFamily x.1.1 at hB
  rw [hB]
  exact nestedRead_second_one_tail_scalar hn hc2 hd2 x.1.1

theorem aggregateLift_W_scalar
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
      (k4AggregateLift (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d) x)).1.1.2 =
      (((∑ zt, x.2.1 zt),
          (∑ zt : PointedTail (PVec n c) zeroVec, x.2.1 zt.1)),
        (0, 0)) := by
  change (wNestedCoords hn hb2 hc2
      (k4AggregateLift (by omega : 0 < b) (by omega : 0 < c)
        (by omega : 0 < d) x).1.2).1 = _
  rw [wNestedCoords_eq_nestedRead]
  have hGauge := k4AggregateLiftRaw_gauge
    (n := n) (b := b) (c := c) (d := d)
    (by omega) (by omega) (by omega) x
  have hW := congrArg Prod.snd hGauge
  change
    wGaugedYZFamilyEquiv (by omega) (by omega)
        (k4AggregateLift (by omega : 0 < b) (by omega : 0 < c)
          (by omega : 0 < d) x).1.2 =
      k4WOneTailFamily x.2.1 at hW
  rw [hW]
  exact nestedRead_first_one_tail_scalar hn hb2 hc2 x.2.1

end
end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar.NestedOneTailProbe

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar.AllCoordinatesProbe

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

private theorem aggregateLift_B01_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
      (k4AggregateLift (by omega) (by omega) (by omega) x)).1.1.1.1.2 = 0 := by
  have h := congrArg (fun q => q.1.2)
    (NestedOneTailProbe.aggregateLift_B_scalar hn hb2 hc2 hd2 x)
  exact h

private theorem aggregateLift_B11_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
      (k4AggregateLift (by omega) (by omega) (by omega) x)).1.1.1.2.2 = 0 := by
  have h := congrArg (fun q => q.2.2)
    (NestedOneTailProbe.aggregateLift_B_scalar hn hb2 hc2 hd2 x)
  exact h

private theorem aggregateLift_W10_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
      (k4AggregateLift (by omega) (by omega) (by omega) x)).1.1.2.2.1 = 0 := by
  have h := congrArg (fun q => q.2.1)
    (NestedOneTailProbe.aggregateLift_W_scalar hn hb2 hc2 hd2 x)
  exact h

private theorem aggregateLift_W11_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BAggregateLeft n c × K4WAggregateLeft n c) :
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
      (k4AggregateLift (by omega) (by omega) (by omega) x)).1.1.2.2.2 = 0 := by
  have h := congrArg (fun q => q.2.2)
    (NestedOneTailProbe.aggregateLift_W_scalar hn hb2 hc2 hd2 x)
  exact h

theorem scalarLeftCoordinate_B01
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.2 =
      s.1.1.1.1.1.2 := by
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift :=
    k4GPolarKernelMixedOverlapBuild_val hn2 hn hb2 hc2 hd2 z
  have hmap :=
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).map_add z.1.1 lift
  have hz : z.1 =
      k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 (aggregateSource s.1) := rfl
  have hagg :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.1.1.2 =
        s.1.1.1.1.1.2 := by
    rw [hz, k4AggregateKernelEEEEBuild_coordinates]
    rfl
  have hlift :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.1.1.2 = 0 :=
    aggregateLift_B01_zero hn hb2 hc2 hd2 u.1
  change (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.1.2 = _
  rw [ShallowProjectionProbe.fullLeftCoordinate_apply, hval, hmap]
  change
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.1.1.2 +
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.1.1.2 = _
  rw [hagg, hlift, add_zero]

theorem scalarLeftCoordinate_B11
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.2 =
      s.1.1.1.1.2.2 := by
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift :=
    k4GPolarKernelMixedOverlapBuild_val hn2 hn hb2 hc2 hd2 z
  have hmap :=
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).map_add z.1.1 lift
  have hz : z.1 =
      k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 (aggregateSource s.1) := rfl
  have hagg :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.1.2.2 =
        s.1.1.1.1.2.2 := by
    rw [hz, k4AggregateKernelEEEEBuild_coordinates]
    rfl
  have hlift :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.1.2.2 = 0 :=
    aggregateLift_B11_zero hn hb2 hc2 hd2 u.1
  change (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.1.2.2 = _
  rw [ShallowProjectionProbe.fullLeftCoordinate_apply, hval, hmap]
  change
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.1.2.2 +
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.1.2.2 = _
  rw [hagg, hlift, add_zero]

theorem scalarLeftCoordinate_W10
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.1 =
      s.1.1.1.2.2.1 := by
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift :=
    k4GPolarKernelMixedOverlapBuild_val hn2 hn hb2 hc2 hd2 z
  have hmap :=
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).map_add z.1.1 lift
  have hz : z.1 =
      k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 (aggregateSource s.1) := rfl
  have hagg :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.2.2.1 =
        s.1.1.1.2.2.1 := by
    rw [hz, k4AggregateKernelEEEEBuild_coordinates]
    rfl
  have hlift :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.2.2.1 = 0 :=
    aggregateLift_W10_zero hn hb2 hc2 hd2 u.1
  change (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.2.1 = _
  rw [ShallowProjectionProbe.fullLeftCoordinate_apply, hval, hmap]
  change
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.2.2.1 +
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.2.2.1 = _
  rw [hagg, hlift, add_zero]

theorem scalarLeftCoordinate_W11
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.2.2.2 =
      s.1.1.1.2.2.2 := by
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift :=
    k4GPolarKernelMixedOverlapBuild_val hn2 hn hb2 hc2 hd2 z
  have hmap :=
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2).map_add z.1.1 lift
  have hz : z.1 =
      k4AggregateKernelEEEEBuild hn hb2 hc2 hd2 (aggregateSource s.1) := rfl
  have hagg :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.2.2.2 =
        s.1.1.1.2.2.2 := by
    rw [hz, k4AggregateKernelEEEEBuild_coordinates]
    rfl
  have hlift :
      (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.2.2.2 = 0 :=
    aggregateLift_W11_zero hn hb2 hc2 hd2 u.1
  change (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s).1.1.2.2.2 = _
  rw [ShallowProjectionProbe.fullLeftCoordinate_apply, hval, hmap]
  change
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).1.1.2.2.2 +
        (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1.1.2.2.2 = _
  rw [hagg, hlift, add_zero]

end
end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar.AllCoordinatesProbe
