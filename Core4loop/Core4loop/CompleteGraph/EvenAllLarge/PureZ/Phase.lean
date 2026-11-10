import Core4loop.CompleteGraph.EvenAllLarge.PureZ.Coordinates

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ

open scoped BigOperators

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEEPhase
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

attribute [local instance] Fintype.ofFinite

noncomputable abbrev LocalSource
    (n : Nat) [NeZero n] :=
  K4AggregateEEEEZKernel n × (MatrixProfile n × MatrixProfile n)

noncomputable abbrev LocalTailSource
    (n c : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c (LocalSource n)

private noncomputable def localTailSplitEquiv
    {n c : Nat} [NeZero n] :
    LocalTailSource n c ≃ₗ[F] K4BaseMixedZSector n c :=
  (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := PVec n c)
      (U := K4AggregateEEEEZKernel n)
      (V := MatrixProfile n × MatrixProfile n)
      (zeroVec : PVec n c)).trans
    ((LinearEquiv.refl F (K4AggregateEEEEZKernelTail n c)).prodCongr
      (TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
        (S := PVec n c)
        (U := MatrixProfile n)
        (V := MatrixProfile n)
        (zeroVec : PVec n c)))

noncomputable def localTailEquiv
    {n c : Nat} [NeZero n] :
    K4BaseMixedZSector n c ≃ₗ[F] LocalTailSource n c :=
  (localTailSplitEquiv (n := n) (c := c)).symm

theorem localTailEquiv_apply
    {n c : Nat} [NeZero n]
    (z : K4BaseMixedZSector n c)
    (t : PointedTail (PVec n c) zeroVec) :
    (localTailEquiv z).1 t =
      (z.1.1 t, (z.2.1.1 t, z.2.2.1 t)) := by
  rfl

noncomputable def localLeft
    {n : Nat} [NeZero n] :
    LocalSource n →ₗ[F] DiamondEEOELeftAmbient n where
  toFun x :=
    (((k4KappaKernelBuild x.2.1).1, x.1.1.1.2),
      ((k4KappaFlipKernelBuild x.2.2).1, x.1.1.2.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def localLeftTail
    {n c : Nat} [NeZero n] :
    LocalTailSource n c →ₗ[F] TotalEEEEZTailLeft n c where
  toFun x :=
    ⟨fun t => localLeft (x.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, (localLeft (n := n)) (x.1 t)) = 0
      have hmap (s : Finset (PointedTail (PVec n c) zeroVec)) :
          (∑ t ∈ s, (localLeft (n := n)) (x.1 t)) =
            (localLeft (n := n)) (∑ t ∈ s, x.1 t) := by
        classical
        induction s using Finset.induction_on with
        | empty =>
            rw [Finset.sum_empty, Finset.sum_empty]
            rfl
        | @insert t s ht ih =>
            rw [Finset.sum_insert ht, Finset.sum_insert ht, ih]
            rfl
      rw [hmap, pointedValueTailZero_sum]
      rfl⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    rfl
  map_smul' r x := by
    apply Subtype.ext
    funext t
    rfl

noncomputable def zLeftModel
    {n c : Nat} [NeZero n] :
    K4BaseMixedZSector n c →ₗ[F] TotalEEEEZTailLeft n c :=
  localLeftTail.comp (localTailEquiv (n := n) (c := c)).toLinearMap

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

@[simp] private theorem tailZeroCongr_apply
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (e : U ≃ₗ[F] V) (q : PointedValueTailZero S U s0)
    (t : PointedTail S s0) :
    (TotalEOEEInternal.TailCoordHelpers.tailZeroCongr s0 e q).1 t =
      e (q.1 t) := by
  rfl

@[simp] private theorem tailZeroProdEquiv_apply_fst
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (q : PointedValueTailZero S (U × V) s0)
    (t : PointedTail S s0) :
    ((TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := S) (U := U) (V := V) s0) q).1.1 t = (q.1 t).1 := by
  rfl

@[simp] private theorem tailZeroProdEquiv_apply_snd
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (q : PointedValueTailZero S (U × V) s0)
    (t : PointedTail S s0) :
    ((TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := S) (U := U) (V := V) s0) q).2.1 t = (q.1 t).2 := by
  rfl

@[simp] private theorem tailZeroProdEquiv_symm_apply
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (q : PointedValueTailZero S U s0)
    (r : PointedValueTailZero S V s0)
    (t : PointedTail S s0) :
    ((TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := S) (U := U) (V := V) s0).symm (q, r)).1 t =
      (q.1 t, r.1 t) := by
  rfl

private theorem nestedRead_second_one_tail_scalar
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

private theorem nestedRead_first_one_tail_scalar
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
        pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
      apply Fintype.sum_eq_zero
      intro y
      apply Fintype.sum_eq_zero
      intro x
      simp [x.2]
    · simp only [nestedRead, pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K, Finset.sum_apply]
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

private theorem pureZ_polar_B_head_zero
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (z : K4AggregatePolarZCoordinates n c) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    let B := k4BAggregateCoordEquiv hn hc2 u.1.1
    B.1 = 0 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let B := k4BAggregateCoordEquiv hn hc2 u.1.1
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  let X : K4BScalarRadical n :=
    ⟨B.1.1, LinearMap.mem_ker.mpr hu.1⟩
  have hread := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource z)
  have hp : k4PHeadScalarRead X = 0 := by
    exact congrArg (fun q => q.1.1.1) hread
  have hfree : B.1.2 = 0 := by
    exact congrArg (fun q => q.1.1.2.1) hread
  have hscalar : B.1.1 = 0 := by
    apply Subtype.ext
    have hbuild := congrArg (fun q => q.1.1) (k4PHeadScalarBuild_read X)
    calc
      B.1.1.1 = X.1 := rfl
      _ = (k4PHeadScalarBuild (k4PHeadScalarRead X)).1.1 := hbuild.symm
      _ = 0 := by rw [hp]; rfl
  exact Prod.ext hscalar hfree

private theorem pureZ_polar_W_head_zero
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (z : K4AggregatePolarZCoordinates n c) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    let W := k4WAggregateCoordEquiv hn hc2 u.1.2
    W.1 = 0 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let W := k4WAggregateCoordEquiv hn hc2 u.1.2
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  let X : K4WScalarRadical n :=
    ⟨W.1.2, LinearMap.mem_ker.mpr hu.2.2.2.2.1⟩
  have hread := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource z)
  have hfree : W.1.1 = 0 := by
    exact congrArg (fun q => q.2.1.1.1) hread
  have hp : k4RHeadScalarRead X = 0 := by
    exact congrArg (fun q => q.2.1.2) hread
  have hscalar : W.1.2 = 0 := by
    apply Subtype.ext
    have hbuild := congrArg (fun q => q.1.1) (k4RHeadScalarBuild_read X)
    calc
      W.1.2.1 = X.1 := rfl
      _ = (k4RHeadScalarBuild (k4RHeadScalarRead X)).1.1 := hbuild.symm
      _ = 0 := by rw [hp]; rfl
  exact Prod.ext hfree hscalar

private theorem pureZ_polar_B_tail
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (z : K4AggregatePolarZCoordinates n c)
    (t : PointedTail (PVec n c) zeroVec) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    let B := k4BAggregateCoordEquiv hn hc2 u.1.1
    B.2.1 t = (k4KappaKernelBuild (z.1.1 t)).1 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let B := k4BAggregateCoordEquiv hn hc2 u.1.1
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  let X : LinearMap.ker (k4CubeKappaLinear (n := n)) :=
    ⟨B.2.1 t, LinearMap.mem_ker.mpr (hu.2.2.1 t)⟩
  have hread := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource z)
  have ht : k4KappaKernelRead X = z.1.1 t := by
    exact congrArg (fun q => q.1.2.1 t) hread
  have hbuild := congrArg Subtype.val (k4KappaKernelBuild_read X)
  calc
    B.2.1 t = X.1 := rfl
    _ = (k4KappaKernelBuild (k4KappaKernelRead X)).1 := hbuild.symm
    _ = (k4KappaKernelBuild (z.1.1 t)).1 := by rw [ht]

private theorem pureZ_polar_W_tail
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (z : K4AggregatePolarZCoordinates n c)
    (t : PointedTail (PVec n c) zeroVec) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    let W := k4WAggregateCoordEquiv hn hc2 u.1.2
    W.2.1 t = (k4KappaFlipKernelBuild (z.2.1 t)).1 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let W := k4WAggregateCoordEquiv hn hc2 u.1.2
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  let X : LinearMap.ker (k4CubeKappaLinear (n := n)).flip :=
    ⟨W.2.1 t, LinearMap.mem_ker.mpr (hu.2.2.2.2.2 t)⟩
  have hread := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource z)
  have ht : k4KappaFlipKernelRead X = z.2.1 t := by
    exact congrArg (fun q => q.2.2.1 t) hread
  have hbuild := congrArg Subtype.val (k4KappaFlipKernelBuild_read X)
  calc
    W.2.1 t = X.1 := rfl
    _ = (k4KappaFlipKernelBuild (k4KappaFlipKernelRead X)).1 := hbuild.symm
    _ = (k4KappaFlipKernelBuild (z.2.1 t)).1 := by rw [ht]

theorem zLeftCoordinate_eq_zLeftModel
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (zsrc : K4BaseMixedZSector n c) :
    zLeftCoordinate hn2 hn hb2 hc2 hd2 zsrc = zLeftModel zsrc := by
  apply Subtype.ext
  funext t
  change
    ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
      (gPolarSource hn2 hn hb2 hc2 hd2 zsrc).1).2.2.2.1.1 t) =
      (((k4KappaKernelBuild (zsrc.2.1.1 t)).1,
          (zsrc.1.1 t).1.1.2),
        ((k4KappaFlipKernelBuild (zsrc.2.2.1 t)).1,
          (zsrc.1.1 t).1.2.2))
  let z := mixedOverlap hn hb2 hc2 hd2 zsrc
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  let B := k4BAggregateCoordEquiv hn hc2 u.1.1
  let W := k4WAggregateCoordEquiv hn hc2 u.1.2
  have hzAgg : z.1 =
      k4AggregateKernelEEEEBuild hn hb2 hc2 hd2
        (aggregateSource zsrc.1) := by
    rfl
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 zsrc).1 = z.1.1 + lift := by
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 z
  have hAggCoordinate :
      ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).2.2.2.1.1 t) =
        (zsrc.1.1 t).1 := by
    rw [hzAgg, k4AggregateKernelEEEEBuild_coordinates]
    rfl
  have hGauge :
      literalGaugeEquiv (by omega) (by omega) (by omega) lift.1 =
        k4AggregateOneTailFamily u.1 := by
    exact k4AggregateLiftRaw_gauge
      (by omega) (by omega) (by omega) u.1
  have hBgauge :
      TotalEOEEInternal.bGaugedRootFamilyEquiv
          (by omega) (by omega) lift.1.1 =
        k4BOneTailFamily u.1.1 := by
    exact congrArg Prod.fst hGauge
  have hWgauge :
      wGaugedYZFamilyEquiv (by omega) (by omega) lift.1.2 =
        k4WOneTailFamily u.1.2 := by
    exact congrArg Prod.snd hGauge
  have hBGauged
      (wt : PointedTail (PVec n d) zeroVec) (zu : PVec n c) :
      TotalEOEEInternal.bGaugedRootFamilyEquiv (by omega) (by omega)
          lift.1.1 zu wt.1 = 0 := by
    rw [hBgauge]
    simp [k4BOneTailFamily, wt.2]
  have hWGauged
      (yt : PointedTail (PVec n b) zeroVec) (zu : PVec n c) :
      wGaugedYZFamilyEquiv (by omega) (by omega)
          lift.1.2 yt.1 zu = 0 := by
    rw [hWgauge]
    simp [k4WOneTailFamily, yt.2]
  have hBtailBuild :
      B.2.1 t = (k4KappaKernelBuild (zsrc.2.1.1 t)).1 := by
    exact pureZ_polar_B_tail hn2 hn hc2 zsrc.2 t
  have hWtailBuild :
      W.2.1 t = (k4KappaFlipKernelBuild (zsrc.2.2.1 t)).1 := by
    exact pureZ_polar_W_tail hn2 hn hc2 zsrc.2 t
  have hAggregateRead :
      k4AggregateEEEERead
          ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2) lift) =
        (B, W) := by
    rw [k4AggregateEEEERead_intertwines]
    rw [k4EvenPAggregate_lift]
  have hLiftBFirst :
      (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
        lift).2.2.2.1.1 t).1.1 =
        (k4KappaKernelBuild (zsrc.2.1.1 t)).1 := by
    have h := congrArg (fun q => q.1.2.1 t) hAggregateRead
    change
      (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
        lift).2.2.2.1.1 t).1.1 = B.2.1 t at h
    exact h.trans hBtailBuild
  have hLiftWFirst :
      (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
        lift).2.2.2.1.1 t).2.1 =
        (k4KappaFlipKernelBuild (zsrc.2.2.1 t)).1 := by
    have h := congrArg (fun q => q.2.2.1 t) hAggregateRead
    change
      (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
        lift).2.2.2.1.1 t).2.1 = W.2.1 t at h
    exact h.trans hWtailBuild
  have hLiftBSecond :
      (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
        lift).2.2.2.1.1 t).1.2 = 0 := by
    change ((bNestedCoords hn hc2 hd2 lift.1.1).2.2.1.1 t).2 = 0
    rw [bNestedCoords_eq_nestedRead]
    simp only [nestedRead, tailZeroProdEquiv_apply_fst,
      tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
      pointedSrcEvenValueEquiv_apply_sigma,
      pointedSrcEvenValueEquiv_apply_K,
      pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
      Finset.sum_apply]
    simp_rw [hBGauged]
    simp
  have hLiftWSecond :
      (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
        lift).2.2.2.1.1 t).2.2 = 0 := by
    change ((wNestedCoords hn hb2 hc2 lift.1.2).2.1.1 t).2 = 0
    rw [wNestedCoords_eq_nestedRead]
    simp only [nestedRead, tailZeroProdEquiv_apply_fst,
      tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
      pointedSrcEvenValueEquiv_apply_sigma,
      pointedSrcEvenValueEquiv_apply_K,
      pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
      Finset.sum_apply]
    simp_rw [hWGauged]
    simp
  have hzSigma := LinearMap.mem_ker.mp (zsrc.1.1 t).2
  have hzB := congrArg Prod.fst hzSigma
  have hzW := congrArg Prod.snd hzSigma
  change (zsrc.1.1 t).1.1.1 = 0 at hzB
  change (zsrc.1.1 t).1.2.1 = 0 at hzW
  rw [hval, LinearEquiv.map_add]
  change
    ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1).2.2.2.1.1 t) +
        ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).2.2.2.1.1 t) =
      (((k4KappaKernelBuild (zsrc.2.1.1 t)).1,
          (zsrc.1.1 t).1.1.2),
        ((k4KappaFlipKernelBuild (zsrc.2.2.1 t)).1,
          (zsrc.1.1 t).1.2.2))
  rw [hAggCoordinate]
  apply Prod.ext
  · apply Prod.ext
    · change
        (zsrc.1.1 t).1.1.1 +
            (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
              lift).2.2.2.1.1 t).1.1 =
          (k4KappaKernelBuild (zsrc.2.1.1 t)).1
      rw [hzB, hLiftBFirst, zero_add]
    · change
        (zsrc.1.1 t).1.1.2 +
            (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
              lift).2.2.2.1.1 t).1.2 =
          (zsrc.1.1 t).1.1.2
      rw [hLiftBSecond, add_zero]
  · apply Prod.ext
    · change
        (zsrc.1.1 t).1.2.1 +
            (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
              lift).2.2.2.1.1 t).2.1 =
          (k4KappaFlipKernelBuild (zsrc.2.2.1 t)).1
      rw [hzW, hLiftWFirst, zero_add]
    · change
        (zsrc.1.1 t).1.2.2 +
            (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
              lift).2.2.2.1.1 t).2.2 =
          (zsrc.1.1 t).1.2.2
      rw [hLiftWSecond, add_zero]

noncomputable def localCoeffMap
    {n : Nat} [NeZero n] :
    LocalSource n →ₗ[F] DiamondEEOERightAmbient n :=
  diamondEEOECoeffMap.comp localLeft

theorem localCoeffMap_apply
    {n : Nat} [NeZero n] (x : LocalSource n) :
    localCoeffMap x =
      ((cubeDiffI ((k4KappaKernelBuild x.2.1).1 + x.1.1.1.2) +
          cubeDiffK ((k4KappaFlipKernelBuild x.2.2).1 + x.1.1.2.2),
        cubeDiffI (k4KappaKernelBuild x.2.1).1),
        (cubeDiffK (k4KappaFlipKernelBuild x.2.2).1, 0)) := by
  rfl

noncomputable def localCross
    {n : Nat} [NeZero n] :
    LocalSource n →ₗ[F] Module.Dual F (DiamondEEOERightAmbient n) :=
  EEOEInternal.ambientPairing.comp localCoeffMap

theorem localCross_apply
    {n : Nat} [NeZero n]
    (x : LocalSource n) (q : DiamondEEOERightAmbient n) :
    localCross x q =
      cubeDot
          (cubeDiffI ((k4KappaKernelBuild x.2.1).1 + x.1.1.1.2) +
            cubeDiffK ((k4KappaFlipKernelBuild x.2.2).1 + x.1.1.2.2))
          q.1.1 +
        cubeDot (cubeDiffI (k4KappaKernelBuild x.2.1).1) q.1.2 +
        cubeDot (cubeDiffK (k4KappaFlipKernelBuild x.2.2).1) q.2.1 := by
  simp [localCross, localCoeffMap, localLeft,
    EEOEInternal.ambientPairing, EEOEInternal.ambientPhase,
    diamondEEOECoeffMap, cubeDot]

noncomputable def tailCross
    {n c : Nat} [NeZero n] :
    K4BaseMixedZSector n c →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n c
          (DiamondEEOERightAmbient n)) :=
  (diamondTailAmplify (localCross (n := n))).comp
    (localTailEquiv (n := n) (c := c)).toLinearMap

theorem tailCross_apply
    {n c : Nat} [NeZero n]
    (z : K4BaseMixedZSector n c)
    (q : DiamondEvenAxisValueTailZero n c
      (DiamondEEOERightAmbient n)) :
    tailCross z q =
      ∑ t, localCross ((localTailEquiv z).1 t) (q.1 t) := by
  rfl

private theorem pureZ_lift_scalar_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4AggregatePolarZCoordinates n c) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    (diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift).1 = 0 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  let B := k4BAggregateCoordEquiv hn hc2 u.1.1
  let W := k4WAggregateCoordEquiv hn hc2 u.1.2
  have hBhead : B.1 = 0 :=
    pureZ_polar_B_head_zero hn2 hn hc2 z
  have hWhead : W.1 = 0 :=
    pureZ_polar_W_head_zero hn2 hn hc2 z
  have hGauge :
      literalGaugeEquiv (by omega) (by omega) (by omega) lift.1 =
        k4AggregateOneTailFamily u.1 := by
    exact k4AggregateLiftRaw_gauge
      (by omega) (by omega) (by omega) u.1
  have hBgauge :
      TotalEOEEInternal.bGaugedRootFamilyEquiv
          (by omega) (by omega) lift.1.1 =
        k4BOneTailFamily u.1.1 := by
    exact congrArg Prod.fst hGauge
  have hWgauge :
      wGaugedYZFamilyEquiv (by omega) (by omega) lift.1.2 =
        k4WOneTailFamily u.1.2 := by
    exact congrArg Prod.snd hGauge
  apply Subtype.ext
  apply Prod.ext
  · change (bNestedCoords hn hc2 hd2 lift.1.1).1 = 0
    rw [bNestedCoords_eq_nestedRead, hBgauge]
    change
      (nestedRead hn hc2 hd2
        (fun x y => if y = zeroVec then u.1.1.1 x else 0)).1 = 0
    rw [nestedRead_second_one_tail_scalar]
    change ((B.1.1.1, 0), (B.1.2, 0)) = 0
    rw [hBhead]
    rfl
  · change (wNestedCoords hn hb2 hc2 lift.1.2).1 = 0
    rw [wNestedCoords_eq_nestedRead, hWgauge]
    change
      (nestedRead hn hb2 hc2
        (fun x y => if x = zeroVec then u.1.2.1 y else 0)).1 = 0
    rw [nestedRead_first_one_tail_scalar]
    have hsum := TotalEEEERightInternal.axisDualHead_eq_totalSum
      (CyclicCube n) hn hc2 u.1.2.1
    change W.1.2.1 = (∑ zt, u.1.2.1 zt) at hsum
    have hpoint : u.1.2.1 (zeroVec : PVec n c) = 0 := by
      have h := congrArg Prod.fst hWhead
      change u.1.2.1 (zeroVec : PVec n c) = 0 at h
      exact h
    have htail :
        (∑ zt : PointedTail (PVec n c) zeroVec, u.1.2.1 zt.1) = 0 := by
      have h := congrArg (fun q => q.1) (congrArg Prod.snd hWhead)
      change
        (∑ zt : PointedTail (PVec n c) zeroVec,
          (u.1.2.1 zt.1 + u.1.2.1 (zeroVec : PVec n c))) = 0 at h
      simpa only [hpoint, add_zero] using h
    have hall : (∑ zt, u.1.2.1 zt) = 0 := by
      rw [← hsum]
      exact congrArg (fun q => q.1) (congrArg Prod.snd hWhead)
    rw [hall, htail]
    rfl

private theorem pureZ_lift_only_Z
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4AggregatePolarZCoordinates n c) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    let q := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift
    q = (0, (0, (0, (q.2.2.2.1, (0, (0, (0, 0))))))) := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hScalar := pureZ_lift_scalar_zero
    hn2 hn hb2 hc2 hd2 z
  have hGauge :
      literalGaugeEquiv (by omega) (by omega) (by omega) lift.1 =
        k4AggregateOneTailFamily u.1 := by
    exact k4AggregateLiftRaw_gauge
      (by omega) (by omega) (by omega) u.1
  have hBgauge :
      TotalEOEEInternal.bGaugedRootFamilyEquiv
          (by omega) (by omega) lift.1.1 =
        k4BOneTailFamily u.1.1 := by
    exact congrArg Prod.fst hGauge
  have hWgauge :
      wGaugedYZFamilyEquiv (by omega) (by omega) lift.1.2 =
        k4WOneTailFamily u.1.2 := by
    exact congrArg Prod.snd hGauge
  have hBGauged
      (wt : PointedTail (PVec n d) zeroVec) (zu : PVec n c) :
      TotalEOEEInternal.bGaugedRootFamilyEquiv (by omega) (by omega)
          lift.1.1 zu wt.1 = 0 := by
    rw [hBgauge]
    simp [k4BOneTailFamily, wt.2]
  have hWGauged
      (yt : PointedTail (PVec n b) zeroVec) (zu : PVec n c) :
      wGaugedYZFamilyEquiv (by omega) (by omega)
          lift.1.2 yt.1 zu = 0 := by
    rw [hWgauge]
    simp [k4WOneTailFamily, yt.2]
  have hWFamily
      (yt : PointedTail (PVec n b) zeroVec) :
      wGaugedYZFamilyEquiv (by omega) (by omega)
          lift.1.2 yt.1 = 0 := by
    funext zu
    exact hWGauged yt zu
  have hY :
      ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2) lift).2.1 = 0 := by
    apply Subtype.ext
    funext yt
    apply Prod.ext
    · apply Subtype.ext
      change ((wNestedCoords hn hb2 hc2 lift.1.2).2.2.1.1 yt).1 = 0
      rw [wNestedCoords_eq_nestedRead]
      simp only [nestedRead, tailZeroProdEquiv_apply_fst,
        tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
        pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K,
        pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
        Finset.sum_apply]
      simp_rw [hWFamily]
      simp
    · change ((wNestedCoords hn hb2 hc2 lift.1.2).2.2.1.1 yt).2 = 0
      rw [wNestedCoords_eq_nestedRead]
      simp only [nestedRead, tailZeroProdEquiv_apply_fst,
        tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
        pointedSrcEvenValueEquiv_apply_sigma,
        pointedSrcEvenValueEquiv_apply_K,
        pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
        Finset.sum_apply]
      simp_rw [hWGauged]
      simp
  apply Prod.ext
  · exact hScalar
  · apply Prod.ext
    · exact hY
    · apply Prod.ext
      · apply Subtype.ext
        funext wt
        apply Prod.ext
        · apply Subtype.ext
          change ((bNestedCoords hn hc2 hd2 lift.1.1).2.1.1 wt).1 = 0
          rw [bNestedCoords_eq_nestedRead]
          simp only [nestedRead, tailZeroProdEquiv_apply_fst,
            tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
            pointedSrcEvenValueEquiv_apply_sigma,
            pointedSrcEvenValueEquiv_apply_K,
            pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
            Finset.sum_apply]
          have hfirst :
              (∑ zu : PVec n c,
                TotalEOEEInternal.bGaugedRootFamilyEquiv
                  (by omega) (by omega) lift.1.1 zu wt.1) = 0 := by
            apply Fintype.sum_eq_zero
            intro zu
            exact hBGauged wt zu
          have hsecond :
              (∑ x : PointedTail (PVec n d) zeroVec,
                ∑ zu : PVec n c,
                  TotalEOEEInternal.bGaugedRootFamilyEquiv
                    (by omega) (by omega) lift.1.1 zu x.1) = 0 := by
            apply Fintype.sum_eq_zero
            intro x
            apply Fintype.sum_eq_zero
            intro zu
            exact hBGauged x zu
          rw [hfirst, hsecond, zero_add]
        · change ((bNestedCoords hn hc2 hd2 lift.1.1).2.1.1 wt).2 = 0
          rw [bNestedCoords_eq_nestedRead]
          simp only [nestedRead, tailZeroProdEquiv_apply_fst,
            tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
            pointedSrcEvenValueEquiv_apply_sigma,
            pointedSrcEvenValueEquiv_apply_K,
            pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
            Finset.sum_apply]
          simp_rw [hBGauged]
          simp
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · apply Subtype.ext
            funext yt
            apply Subtype.ext
            funext zt
            change
              (((wNestedCoords hn hb2 hc2 lift.1.2).2.2.2.1 yt).1 zt) = 0
            rw [wNestedCoords_eq_nestedRead]
            simp only [nestedRead, tailZeroProdEquiv_apply_fst,
              tailZeroProdEquiv_apply_snd,
              tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
              pointedSrcEvenValueEquiv_apply_sigma,
              pointedSrcEvenValueEquiv_apply_K,
              pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
              Finset.sum_apply]
            simp_rw [hWGauged]
            simp
          · apply Prod.ext
            · apply Subtype.ext
              funext zt
              apply Subtype.ext
              funext wt
              change
                (((bNestedCoords hn hc2 hd2 lift.1.1).2.2.2.1 zt).1 wt) = 0
              rw [bNestedCoords_eq_nestedRead]
              simp only [nestedRead, tailZeroProdEquiv_apply_fst,
                tailZeroProdEquiv_apply_snd,
                tailZeroProdEquiv_symm_apply, tailZeroCongr_apply,
                pointedSrcEvenValueEquiv_apply_sigma,
                pointedSrcEvenValueEquiv_apply_K,
                pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
                Finset.sum_apply]
              simp_rw [hBGauged]
              simp
            · apply Prod.ext
              · rfl
              · rfl

private theorem fullLeftCoordinate_eq_pureZ_injection
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (zsrc : K4BaseMixedZSector n c) :
    fullLeftCoordinate hn2 hn hb2 hc2 hd2 zsrc =
      (0, (0, (0,
        (zLeftCoordinate hn2 hn hb2 hc2 hd2 zsrc,
          (0, (0, (0, 0))))))) := by
  let z := mixedOverlap hn hb2 hc2 hd2 zsrc
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  let qAgg := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 z.1.1
  let qLift := diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 lift
  have hzAgg : z.1 =
      k4AggregateKernelEEEEBuild hn hb2 hc2 hd2
        (aggregateSource zsrc.1) := by
    rfl
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 zsrc).1 = z.1.1 + lift := by
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 z
  have hAggSupport :
      qAgg =
        (0, (0, (0, (qAgg.2.2.2.1, (0, (0, (0, 0))))))) := by
    dsimp only [qAgg]
    rw [hzAgg, k4AggregateKernelEEEEBuild_coordinates]
    rfl
  have hLiftSupport :
      qLift =
        (0, (0, (0, (qLift.2.2.2.1, (0, (0, (0, 0))))))) := by
    exact pureZ_lift_only_Z hn2 hn hb2 hc2 hd2 zsrc.2
  change
    diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
        (gPolarSource hn2 hn hb2 hc2 hd2 zsrc).1 =
      (0, (0, (0,
        ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2
          (gPolarSource hn2 hn hb2 hc2 hd2 zsrc).1).2.2.2.1,
          (0, (0, (0, 0)))))))
  rw [hval, LinearEquiv.map_add]
  change qAgg + qLift =
    (0, (0, (0, ((qAgg + qLift).2.2.2.1, (0, (0, (0, 0)))))))
  rw [hAggSupport, hLiftSupport]
  simp

private theorem coordinatePhase_rightRead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c)
    (A : DiamondEvenPReachableA n b c d) :
    totalEEEECoordinatePhase
        (0, (0, (0, (zLeftModel z, (0, (0, (0, 0)))))))
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      tailCross z (rightRead hn hb2 hc2 hd2 A) := by
  simp only [totalEEEECoordinatePhase,
    tailCross, zLeftModel, localLeftTail,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    diamondTailAmplify_apply,
    totalEEEEYBasePhase,
    totalEEEEWBasePhase,
    totalEEEEYZBasePhase,
    totalEEEEWZBasePhase,
    totalEEEEYWBasePhase,
    totalEEEEYWZBasePhase,
    map_zero, LinearMap.zero_apply, LinearMap.mk₂_apply,
    Finset.sum_const_zero, zero_add, add_zero, zero_mul,
    Prod.fst_zero, Prod.snd_zero, Submodule.coe_zero, Pi.zero_apply,
    rightRead_apply]
  simp [cubeDot, diamondTailAllEvenZCross, localCross, localCoeffMap]

private theorem aggregateKappa_left_pureZ
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (z : K4AggregatePolarZCoordinates n c)
    (WK : PVec n c → CyclicCube n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    k4AggregateKappaScalar u.1.1.1 WK = 0 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let Bc := k4BAggregateCoordEquiv hn hc2 u.1.1
  let yw := pointedDualEvenValueEquiv
    (PVec n c) (CyclicCube n) (zeroVec : PVec n c)
      (even_card_PVec hn hc2) WK
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  have hpair := pointedEvenValue_pairing
    (zeroVec : PVec n c) (even_card_PVec hn hc2)
    (k4CubeKappaLinear (n := n)) u.1.1.1 WK
  simp only [k4CubeKappaLinear_apply] at hpair
  change k4AggregateKappaScalar u.1.1.1 WK = 0
  rw [k4AggregateKappaScalar, hpair]
  change
    k4CubeKappa Bc.1.1.1 yw.1.1 +
        k4CubeKappa Bc.1.2 yw.1.2 +
        (∑ t, k4CubeKappa (Bc.2.1 t) (yw.2.1 t)) = 0
  have hhead := LinearMap.congr_fun
    (LinearMap.mem_ker.mp hu.1) yw.1.1
  change k4CubeKappa Bc.1.1.1 yw.1.1 = 0 at hhead
  have htail :
      (∑ t, k4CubeKappa (Bc.2.1 t) (yw.2.1 t)) = 0 := by
    apply Fintype.sum_eq_zero
    intro t
    exact LinearMap.congr_fun (hu.2.2.1 t) (yw.2.1 t)
  have hread := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource z)
  have hfree : Bc.1.2 = 0 := by
    exact congrArg (fun q => q.1.1.2.1) hread
  rw [hhead, zero_add, htail, add_zero, hfree]
  simp [k4CubeKappa]

private theorem aggregateKappa_right_pureZ
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (z : K4AggregatePolarZCoordinates n c)
    (BK : PVec n c → CyclicCube n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    k4AggregateKappaScalar BK u.1.2.1 = 0 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (polarSource z)
  let xb := pointedSrcEvenValueEquiv
    (PVec n c) (CyclicCube n) (zeroVec : PVec n c)
      (even_card_PVec hn hc2) BK
  let Wc := k4WAggregateCoordEquiv hn hc2 u.1.2
  have hu := (k4AggregatePolar_mem_ker_iff_coordinates
    hn2 hn hc2 u.1).mp u.2
  have hpair := pointedEvenValue_pairing
    (zeroVec : PVec n c) (even_card_PVec hn hc2)
    (k4CubeKappaLinear (n := n)) BK u.1.2.1
  simp only [k4CubeKappaLinear_apply] at hpair
  change k4AggregateKappaScalar BK u.1.2.1 = 0
  rw [k4AggregateKappaScalar, hpair]
  change
    k4CubeKappa xb.1.1 Wc.1.1 +
        k4CubeKappa xb.1.2 Wc.1.2.1 +
        (∑ t, k4CubeKappa (xb.2.1 t) (Wc.2.1 t)) = 0
  have hhead := LinearMap.congr_fun
    (LinearMap.mem_ker.mp hu.2.2.2.2.1) xb.1.2
  change k4CubeKappa xb.1.2 Wc.1.2.1 = 0 at hhead
  have htail :
      (∑ t, k4CubeKappa (xb.2.1 t) (Wc.2.1 t)) = 0 := by
    apply Fintype.sum_eq_zero
    intro t
    have ht := LinearMap.congr_fun (hu.2.2.2.2.2 t) (xb.2.1 t)
    change k4CubeKappa (xb.2.1 t) (Wc.2.1 t) = 0 at ht
    exact ht
  have hread := k4AggregatePolarKernelCoordinateRead_build
    hn2 hn hc2 (polarSource z)
  have hfree : Wc.1.1 = 0 := by
    exact congrArg (fun q => q.2.1.1.1) hread
  rw [hhead, add_zero, htail, add_zero, hfree]
  simp [k4CubeKappa]

private theorem aggregateKappa_pair_pureZ
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (z : K4AggregatePolarZCoordinates n c)
    (BK WK : PVec n c → CyclicCube n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (polarSource z)
    k4AggregateKappaScalar u.1.1.1 WK +
      k4AggregateKappaScalar BK u.1.2.1 = 0 := by
  dsimp only
  rw [aggregateKappa_left_pureZ hn2 hn hc2 z,
    aggregateKappa_right_pureZ hn2 hn hc2 z, add_zero]

private theorem coordinatePhase_eq_tailCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c)
    (A : DiamondEvenPReachableA n b c d) :
    totalEEEECoordinatePhase
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 z)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
      tailCross z (rightRead hn hb2 hc2 hd2 A) := by
  rw [fullLeftCoordinate_eq_pureZ_injection,
    zLeftCoordinate_eq_zLeftModel]
  exact coordinatePhase_rightRead hn hb2 hc2 hd2 z A

private theorem diamondRoot_eq_tailCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c)
    (r : K4EvenPBaseRight n b c d) :
    let m := mixedOverlap hn hb2 hc2 hd2 z
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 m.2
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    diamondEvenPCross m.1.1 (k4BaseRightToDiamondReachable r) +
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 =
      tailCross z
        (rightRead hn hb2 hc2 hd2
          (k4BaseRightToDiamondReachable r)) := by
  dsimp only
  let m := mixedOverlap hn hb2 hc2 hd2 z
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 m.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  have hfull :
      diamondEvenPCross
          (gPolarSource hn2 hn hb2 hc2 hd2 z).1
          (k4BaseRightToDiamondReachable r) =
        tailCross z
          (rightRead hn hb2 hc2 hd2
            (k4BaseRightToDiamondReachable r)) := by
    rw [totalEEEELiteralPhaseCoordinateSplit]
    exact coordinatePhase_eq_tailCross hn2 hn hb2 hc2 hd2 z _
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 z).1 =
        m.1.1 + lift := by
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 m
  have hlift :
      diamondEvenPCross lift (k4BaseRightToDiamondReachable r) =
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 := by
    rfl
  rw [hval, map_add, LinearMap.add_apply, hlift] at hfull
  exact hfull

private theorem descendedCross_eq_tailCross_on_baseRight
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c)
    (r : K4EvenPBaseRight n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 z
        (k4BaseRightToDiamondReachable r) =
      tailCross z
        (rightRead hn hb2 hc2 hd2
          (k4BaseRightToDiamondReachable r)) := by
  rw [descendedCross_apply]
  rw [k4BaseDescendedMixedOverlapCross_split_phase
    (n := n) (b := b) (c := c) (d := d)
    hn2 hn hb2 hc2 hd2
    (mixedOverlap hn hb2 hc2 hd2 z).1
    (mixedOverlap hn hb2 hc2 hd2 z).2 r]
  have hroot := diamondRoot_eq_tailCross
    hn2 hn hb2 hc2 hd2 z r
  have hm2 :
      (mixedOverlap hn hb2 hc2 hd2 z).2 =
        polarSource z.2 := by
    rfl
  have hkappaL := aggregateKappa_left_pureZ
    hn2 hn hc2 z.2
    (k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2)
  have hkappaR := aggregateKappa_right_pureZ
    hn2 hn hc2 z.2
    (k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1)
  dsimp only at hroot hkappaL hkappaR ⊢
  rw [hm2] at hroot ⊢
  rw [hkappaL, hkappaR, add_zero, add_zero]
  exact hroot

private theorem descendedCross_eq_tailCross_pointwise
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c)
    (A : DiamondEvenPReachableA n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 z A =
      tailCross z (rightRead hn hb2 hc2 hd2 A) := by
  obtain ⟨r, rfl⟩ := k4BaseRightToDiamondReachable_surjective A
  exact descendedCross_eq_tailCross_on_baseRight
    hn2 hn hb2 hc2 hd2 z r

theorem descendedCross_ker_rightRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c) :
    LinearMap.ker (rightRead hn hb2 hc2 hd2) ≤
      LinearMap.ker (descendedCross hn2 hn hb2 hc2 hd2 z) := by
  intro A hA
  apply LinearMap.mem_ker.mpr
  rw [descendedCross_eq_tailCross_pointwise,
    LinearMap.mem_ker.mp hA]
  exact map_zero _

theorem pureZPhaseFullSupport
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedZSector n c)
    (A : DiamondEvenPReachableA n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 z A =
      descendedCross hn2 hn hb2 hc2 hd2 z
        (rightSection hn hb2 hc2 hd2
          (rightRead hn hb2 hc2 hd2 A)) := by
  rw [descendedCross_eq_tailCross_pointwise,
    descendedCross_eq_tailCross_pointwise]
  rw [rightRead_rightSection]

theorem descendedCross_eq_rightRead_dual_tailCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    descendedCross hn2 hn hb2 hc2 hd2 =
      (rightRead hn hb2 hc2 hd2).dualMap.comp
        (tailCross (n := n) (c := c)) := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro A
  exact descendedCross_eq_tailCross_pointwise
    hn2 hn hb2 hc2 hd2 z A

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PureZ
