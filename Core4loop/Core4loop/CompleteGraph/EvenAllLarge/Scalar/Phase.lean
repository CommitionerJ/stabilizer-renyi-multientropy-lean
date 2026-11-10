import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Coordinates

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEEPhase
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

attribute [local instance] Fintype.ofFinite

@[simp] private theorem pointedSrcDelta_K_eq_zero
    {S V : Type*} [Fintype S] [DecidableEq S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (v : V) :
    (pointedSrcEvenValueEquiv S V s0 heven
      (fun s => if s = s0 then v else 0)).1.2 = 0 := by
  simp only [pointedSrcEvenValueEquiv_apply_K]
  apply Fintype.sum_eq_zero
  intro t
  simp [t.2]

@[simp] private theorem pointedSrcDelta_tail_eq_zero
    {S V : Type*} [Fintype S] [DecidableEq S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (v : V) :
    (pointedSrcEvenValueEquiv S V s0 heven
      (fun s => if s = s0 then v else 0)).2 = 0 := by
  apply Subtype.ext
  funext t
  simp only [pointedSrcEvenValueEquiv_apply_tail,
    Submodule.coe_zero, Pi.zero_apply]
  have hsum :
      (∑ u : PointedTail S s0,
        if u.1 = s0 then v else 0) = 0 := by
    apply Fintype.sum_eq_zero
    intro u
    simp [u.2]
  rw [hsum]
  simp [t.2]

private theorem cast_odd_eq_one
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, hq⟩
  rw [hq]
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem sum_const_odd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    cast_odd_eq_one hodd, one_smul]

private theorem module_add_self
    {V : Type*} [AddCommGroup V] [Module F V] (v : V) :
    v + v = 0 := by
  calc
    v + v = (1 : F) • v + (1 : F) • v := by simp
    _ = ((1 : F) + (1 : F)) • v := by rw [add_smul]
    _ = 0 := by rw [F_add_self, zero_smul]

private theorem src_tail_zero_of_dual_tail_zero
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S))
    (hodd : Odd (Fintype.card (PointedTail S s0)))
    (g : S → V)
    (hdual : (pointedDualEvenValueEquiv S V s0 heven g).2 = 0) :
    (pointedSrcEvenValueEquiv S V s0 heven g).2 = 0 := by
  apply Subtype.ext
  funext t
  have ht := congrArg (fun q => q.1 t) hdual
  simp only [pointedDualEvenValueEquiv_apply_tail,
    Submodule.coe_zero, Pi.zero_apply] at ht
  rw [Finset.sum_add_distrib, sum_const_odd hodd] at ht
  simp only [pointedSrcEvenValueEquiv_apply_tail,
    Submodule.coe_zero, Pi.zero_apply]
  calc
    g t.1 + ∑ u : PointedTail S s0, g u.1 =
        (g t.1 + ∑ u : PointedTail S s0, g u.1) +
          (g s0 + g s0) := by rw [module_add_self, add_zero]
    _ = g t.1 + g s0 +
          ((∑ u : PointedTail S s0, g u.1) + g s0) := by abel
    _ = 0 := ht

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

@[simp] private theorem tailZeroProdEquiv_apply
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (q : PointedValueTailZero S (U × V) s0)
    (t : PointedTail S s0) :
    (((TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := S) (U := U) (V := V) s0) q).1.1 t,
      ((TotalEOEEInternal.TailCoordHelpers.tailZeroProdEquiv
      (S := S) (U := U) (V := V) s0) q).2.1 t) = q.1 t := by
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

private theorem fullLeftCoordinate_eq_scalar_injection
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    fullLeftCoordinate hn2 hn hb2 hc2 hd2 s =
      (scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s,
        (0, (0, (0, (0, (0, (0, 0))))))) := by
  apply Prod.ext
  · rfl
  · let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      z.2
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    have hAgg :
        ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
          (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2
            (aggregateSource s.1)).1).2 = 0 := by
      rw [k4AggregateKernelEEEEBuild_coordinates]
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · rfl
        · apply Prod.ext
          · apply Subtype.ext
            funext zt
            rfl
          · rfl
    have hzAgg : z.1 =
        k4AggregateKernelEEEEBuild hn hb2 hc2 hd2
          (aggregateSource s.1) := by
      rfl
    have hval :
        (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift := by
      exact k4GPolarKernelMixedOverlapBuild_val
        hn2 hn hb2 hc2 hd2 z
    change
      ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
        (gPolarSource hn2 hn hb2 hc2 hd2 s).1).2 = 0
    rw [hval, LinearEquiv.map_add, Prod.snd_add, hzAgg, hAgg, zero_add]
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
    have huRead := k4AggregatePolarKernelCoordinateRead_build
      hn2 hn hc2 (polarSource s.2)
    have hBTail := congrArg (fun q => q.1.2) huRead
    have hWTail := congrArg (fun q => q.2.2) huRead
    dsimp at hBTail hWTail
    let B := k4BAggregateCoordEquiv hn hc2 u.1.1
    let W := k4WAggregateCoordEquiv hn hc2 u.1.2
    have hu := (k4AggregatePolar_mem_ker_iff_coordinates
      hn2 hn hc2 u.1).mp u.2
    let Bt : K4BZTailRadical n c :=
      ⟨fun t => ⟨B.2.1 t, LinearMap.mem_ker.mpr (hu.2.2.1 t)⟩, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (⟨B.2.1 t, LinearMap.mem_ker.mpr
          (hu.2.2.1 t)⟩ : LinearMap.ker
            (k4CubeKappaLinear (n := n)))) = 0
        apply Subtype.ext
        simpa only [Submodule.coe_sum, Submodule.coe_zero] using
          pointedValueTailZero_sum B.2⟩
    let Wt : K4WZTailRadical n c :=
      ⟨fun t => ⟨W.2.1 t, LinearMap.mem_ker.mpr (hu.2.2.2.2.2 t)⟩, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (⟨W.2.1 t, LinearMap.mem_ker.mpr
          (hu.2.2.2.2.2 t)⟩ : LinearMap.ker
            (k4CubeKappaLinear (n := n)).flip)) = 0
        apply Subtype.ext
        simpa only [Submodule.coe_sum, Submodule.coe_zero] using
          pointedValueTailZero_sum W.2⟩
    change k4BZTailRadicalEquivMatrix Bt = 0 at hBTail
    change k4WZTailRadicalEquivMatrix Wt = 0 at hWTail
    have hBt : Bt = 0 := by
      apply (k4BZTailRadicalEquivMatrix (n := n) (c := c)).injective
      simpa using hBTail
    have hWt : Wt = 0 := by
      apply (k4WZTailRadicalEquivMatrix (n := n) (c := c)).injective
      simpa using hWTail
    have hB : B.2 = 0 := by
      apply Subtype.ext
      funext t
      have ht := congrArg (fun q => (q.1 t).1) hBt
      simpa only [Bt, Submodule.coe_zero, Pi.zero_apply] using ht
    have hW : W.2 = 0 := by
      apply Subtype.ext
      funext t
      have ht := congrArg (fun q => (q.1 t).1) hWt
      simpa only [Wt, Submodule.coe_zero, Pi.zero_apply] using ht
    have hBsrc :
        (pointedSrcEvenValueEquiv
          (PVec n c) (CyclicCube n) (zeroVec : PVec n c)
          (even_card_PVec hn hc2) u.1.1.1).2 = 0 := by
      change B.2 = 0
      exact hB
    have hWdual :
        (pointedDualEvenValueEquiv
          (PVec n c) (CyclicCube n) (zeroVec : PVec n c)
          (even_card_PVec hn hc2) u.1.2.1).2 = 0 := by
      change W.2 = 0
      exact hW
    have hWsrc :
        (pointedSrcEvenValueEquiv
          (PVec n c) (CyclicCube n) (zeroVec : PVec n c)
          (even_card_PVec hn hc2) u.1.2.1).2 = 0 := by
      exact src_tail_zero_of_dual_tail_zero
        (zeroVec : PVec n c) (even_card_PVec hn hc2)
        (odd_card_diamondEvenAxisTailIndex hn hc2) u.1.2.1 hWdual
    have hAggregateRead :
        k4AggregateEEEERead
            ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2) lift) =
          (B, W) := by
      rw [k4AggregateEEEERead_intertwines]
      rw [k4EvenPAggregate_lift]
    have hReadB :
        (k4AggregateEEEERead
          ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2) lift)).1.2 = 0 := by
      rw [hAggregateRead, hB]
    have hReadW :
        (k4AggregateEEEERead
          ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2) lift)).2.2 = 0 := by
      rw [hAggregateRead, hW]
    have hY :
        ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2) lift).2.1 = 0 := by
      apply Subtype.ext
      funext yt
      apply Prod.ext
      · apply Subtype.ext
        change ((wNestedCoords hn hb2 hc2 lift.1.2).2.2.1.1 yt).1 = 0
        rw [wNestedCoords_eq_nestedRead]
        simp only [nestedRead, tailZeroProdEquiv_apply,
          tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_apply_snd,
          tailZeroProdEquiv_symm_apply,
          tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
          pointedSrcEvenValueEquiv_apply_K,
          pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
          Finset.sum_apply]
        simp_rw [hWFamily]
        simp
      · change ((wNestedCoords hn hb2 hc2 lift.1.2).2.2.1.1 yt).2 = 0
        rw [wNestedCoords_eq_nestedRead]
        simp only [nestedRead, tailZeroProdEquiv_apply,
          tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_symm_apply,
          tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
          pointedSrcEvenValueEquiv_apply_K,
          pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
          Finset.sum_apply]
        simp_rw [hWGauged]
        simp
    change
      ((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2) lift).2 =
        (0, (0, (0, (0, (0, (0, 0))))))
    apply Prod.ext
    · exact hY
    · apply Prod.ext
      · apply Subtype.ext
        funext wt
        apply Prod.ext
        · apply Subtype.ext
          change ((bNestedCoords hn hc2 hd2 lift.1.1).2.1.1 wt).1 = 0
          rw [bNestedCoords_eq_nestedRead]
          simp only [nestedRead, tailZeroProdEquiv_apply,
            tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_apply_snd,
            tailZeroProdEquiv_symm_apply,
            tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
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
          simp only [nestedRead, tailZeroProdEquiv_apply,
            tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_symm_apply,
            tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
            pointedSrcEvenValueEquiv_apply_K,
            pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
            Finset.sum_apply]
          simp_rw [hBGauged]
          simp
      · apply Prod.ext
        · apply Subtype.ext
          funext zt
          apply Prod.ext
          · apply Prod.ext
            · have h := congrArg (fun q => q.1 zt) hReadB
              change
                (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
                  lift).2.2.2.1.1 zt).1.1 = 0 at h
              exact h
            · change
                ((bNestedCoords hn hc2 hd2 lift.1.1).2.2.1.1 zt).2 = 0
              rw [bNestedCoords_eq_nestedRead]
              simp only [nestedRead, tailZeroProdEquiv_apply,
                tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_symm_apply,
                tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
                pointedSrcEvenValueEquiv_apply_K,
                pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
                Finset.sum_apply]
              simp_rw [hBGauged]
              simp
          · apply Prod.ext
            · have h := congrArg (fun q => q.1 zt) hReadW
              change
                (((diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2)
                  lift).2.2.2.1.1 zt).2.1 = 0 at h
              exact h
            · change
                ((wNestedCoords hn hb2 hc2 lift.1.2).2.1.1 zt).2 = 0
              rw [wNestedCoords_eq_nestedRead]
              simp only [nestedRead, tailZeroProdEquiv_apply,
                tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_symm_apply,
                tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
                pointedSrcEvenValueEquiv_apply_K,
                pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
                Finset.sum_apply]
              simp_rw [hWGauged]
              simp
        · apply Prod.ext
          · apply Subtype.ext
            funext yt
            apply Subtype.ext
            funext zt
            change
              ((wNestedCoords hn hb2 hc2 lift.1.2).2.2.2.1 yt).1 zt = 0
            rw [wNestedCoords_eq_nestedRead]
            simp only [nestedRead, tailZeroProdEquiv_apply,
              tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_apply_snd,
              tailZeroProdEquiv_symm_apply,
              tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
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
                ((bNestedCoords hn hc2 hd2 lift.1.1).2.2.2.1 zt).1 wt = 0
              rw [bNestedCoords_eq_nestedRead]
              simp only [nestedRead, tailZeroProdEquiv_apply,
                tailZeroProdEquiv_apply_fst, tailZeroProdEquiv_apply_snd,
                tailZeroProdEquiv_symm_apply,
                tailZeroCongr_apply, pointedSrcEvenValueEquiv_apply_sigma,
                pointedSrcEvenValueEquiv_apply_K,
                pointedSrcEvenValueEquiv_apply_tail, Pi.add_apply,
                Finset.sum_apply]
              simp_rw [hBGauged]
              simp
            · apply Prod.ext
              · rfl
              · rfl

private theorem diamond_root_pair_zero_of_rightRead_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (s : K4BaseMixedScalarSector n)
    (r : K4EvenPBaseRight n b c d)
    (hread : rightRead hn hb2 hc2 hd2
      (k4BaseRightToDiamondReachable r) = 0) :
    let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    diamondEvenPCross z.1.1 (k4BaseRightToDiamondReachable r) +
      coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 = 0 := by
  dsimp only
  let z := mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  let A : DiamondEvenPReachableA n b c d :=
    k4BaseRightToDiamondReachable r
  have hright :
      (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).1 = 0 := by
    rw [← rightRead_apply]
    exact hread
  have hfull :
      diamondEvenPCross (gPolarSource hn2 hn hb2 hc2 hd2 s).1 A = 0 := by
    rw [totalEEEELiteralPhaseCoordinateSplit]
    change
      totalEEEECoordinatePhase
        (fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)
        (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) = 0
    rw [fullLeftCoordinate_eq_scalar_injection]
    simp only [totalEEEECoordinatePhase, hright, map_zero,
      totalEEEEYWBasePhase, totalEEEEYWZBasePhase,
      Finset.sum_const_zero, add_zero, zero_add]
    simp [totalEEEEYBasePhase, totalEEEEWBasePhase,
      totalEEEEYZBasePhase, totalEEEEWZBasePhase,
      diamondTailAllEvenZCross]
  have hval :
      (gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift := by
    change
      (k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2 z).1 =
        z.1.1 + lift
    exact k4GPolarKernelMixedOverlapBuild_val
      hn2 hn hb2 hc2 hd2 z
  have hlift :
      diamondEvenPCross lift A =
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 := by
    rfl
  change
    diamondEvenPCross z.1.1 A +
      coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 = 0
  rw [← hlift]
  rw [← LinearMap.add_apply, ← map_add]
  rw [← hval]
  exact hfull

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

attribute [local instance] Fintype.ofFinite

private theorem g2_t37_A001
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hd2 : 2 <= d)
    (D : PVec n b -> PVec n d -> CyclicCube n) :
    (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 D).1.1.2 =
      (∑ yt : PVec n b, D yt (zeroVec : PVec n d)) +
        ∑ yt : PVec n b, ∑ wt : PVec n d, D yt wt := by
  rw [T37RightP1.t37RightCoordinate_scalar_explicit]
  change
    (∑ yt : PVec n b, D yt zeroVec) +
      (∑ wt : PVec n d, ∑ yt : PVec n b, D yt wt) = _
  rw [Finset.sum_comm]

private theorem g2_t37_A100
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hd2 : 2 <= d)
    (D : PVec n b -> PVec n d -> CyclicCube n) :
    (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 D).1.2.1 =
      (∑ wt : PVec n d, D (zeroVec : PVec n b) wt) +
        ∑ yt : PVec n b, ∑ wt : PVec n d, D yt wt := by
  rw [T37RightP1.t37RightCoordinate_scalar_explicit]
  change
    (∑ wt : PVec n d, D zeroVec wt) +
      (∑ wt : PVec n d, ∑ yt : PVec n b, D yt wt) = _
  rw [Finset.sum_comm]

private theorem g2_sum_const_even
    {n : Nat} [NeZero n]
    {S : Type*} [Fintype S]
    (hS : Even (Fintype.card S)) (X : CyclicCube n) :
    (∑ _s : S, X) = 0 := by
  funext i j k
  simp only [Finset.sum_apply, Finset.sum_const, nsmul_eq_mul]
  change (Fintype.card S : F) * X i j k = 0
  rw [natCast_even_eq_zero_F hS, zero_mul]

private theorem g2_joint_total_zero
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hd2 : 2 <= d)
    (P : PVec n d -> CyclicCube n)
    (R : PVec n b -> CyclicCube n)
    (E : PVec n b -> PVec n d -> CyclicCube n)
    (hsource : forall yt wt, E yt wt + P wt + R yt = 0) :
    (∑ yt : PVec n b, ∑ wt : PVec n d, E yt wt) = 0 := by
  have heq (yt : PVec n b) (wt : PVec n d) :
      E yt wt = P wt + R yt := by
    apply (add_eq_zero_iff_eq_of_F_module _ _).mp
    simpa only [add_assoc] using hsource yt wt
  calc
    (∑ yt : PVec n b, ∑ wt : PVec n d, E yt wt) =
        ∑ yt : PVec n b, ∑ wt : PVec n d, (P wt + R yt) := by
          apply Finset.sum_congr rfl
          intro yt _
          apply Finset.sum_congr rfl
          intro wt _
          exact heq yt wt
    _ = ∑ yt : PVec n b,
          ((∑ wt : PVec n d, P wt) +
            ∑ _wt : PVec n d, R yt) := by
          apply Finset.sum_congr rfl
          intro yt _
          rw [Finset.sum_add_distrib]
    _ = ∑ _yt : PVec n b, (∑ wt : PVec n d, P wt) := by
          apply Finset.sum_congr rfl
          intro yt _
          rw [g2_sum_const_even (even_card_PVec hn hd2), add_zero]
    _ = 0 := g2_sum_const_even (even_card_PVec hn hb2) _

private theorem g2_B_joint_identity
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hd2 : 2 <= d)
    (P : PVec n d -> CyclicCube n)
    (R : PVec n b -> CyclicCube n)
    (E : PVec n b -> PVec n d -> CyclicCube n)
    (hsource : forall yt wt, E yt wt + P wt + R yt = 0) :
    (∑ wt : PVec n d, P wt) =
      (∑ wt : PVec n d, E (zeroVec : PVec n b) wt) +
        ∑ yt : PVec n b, ∑ wt : PVec n d, E yt wt := by
  have heq (yt : PVec n b) (wt : PVec n d) :
      E yt wt = P wt + R yt := by
    apply (add_eq_zero_iff_eq_of_F_module _ _).mp
    simpa only [add_assoc] using hsource yt wt
  rw [g2_joint_total_zero hn hb2 hd2 P R E hsource, add_zero]
  calc
    (∑ wt : PVec n d, P wt) =
        (∑ wt : PVec n d, P wt) + 0 := by rw [add_zero]
    _ = (∑ wt : PVec n d, P wt) +
        ∑ _wt : PVec n d, R (zeroVec : PVec n b) := by
          rw [g2_sum_const_even (even_card_PVec hn hd2)]
    _ = ∑ wt : PVec n d,
        (P wt + R (zeroVec : PVec n b)) :=
          Finset.sum_add_distrib.symm
    _ = ∑ wt : PVec n d,
        E (zeroVec : PVec n b) wt := by
          apply Finset.sum_congr rfl
          intro wt _
          exact (heq zeroVec wt).symm

private theorem g2_W_joint_identity
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hd2 : 2 <= d)
    (P : PVec n d -> CyclicCube n)
    (R : PVec n b -> CyclicCube n)
    (E : PVec n b -> PVec n d -> CyclicCube n)
    (hsource : forall yt wt, E yt wt + P wt + R yt = 0) :
    (∑ yt : PVec n b, R yt) =
      (∑ yt : PVec n b, E yt (zeroVec : PVec n d)) +
        ∑ yt : PVec n b, ∑ wt : PVec n d, E yt wt := by
  have heq (yt : PVec n b) (wt : PVec n d) :
      E yt wt = P wt + R yt := by
    apply (add_eq_zero_iff_eq_of_F_module _ _).mp
    simpa only [add_assoc] using hsource yt wt
  rw [g2_joint_total_zero hn hb2 hd2 P R E hsource, add_zero]
  calc
    (∑ yt : PVec n b, R yt) =
        0 + (∑ yt : PVec n b, R yt) := by rw [zero_add]
    _ = (∑ _yt : PVec n b, P (zeroVec : PVec n d)) +
        ∑ yt : PVec n b, R yt := by
          rw [g2_sum_const_even (even_card_PVec hn hb2)]
    _ = ∑ yt : PVec n b,
        (P (zeroVec : PVec n d) + R yt) :=
          Finset.sum_add_distrib.symm
    _ = ∑ yt : PVec n b,
        E yt (zeroVec : PVec n d) := by
          apply Finset.sum_congr rfl
          intro yt _
          exact (heq yt zeroVec).symm

private theorem g2_oddVecHeadTail_eq_evenVecHeadTail
    {n k : Nat} [NeZero n] (hk : 0 < k) :
    diamondOddVecHeadTailEquiv (n := n) (k := k) hk =
      diamondVecHeadTailEquiv (n := n) (k := k) hk := by
  cases k with
  | zero => omega
  | succ k => rfl

private theorem g2_k4BaseBCell_eq_bGauged
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d) :
    k4BaseBCell hc hd B zt wt =
      TotalEOEEInternal.bGaugedRootFamilyEquiv hc hd B zt wt := by
  funext i j k
  simp only [k4BaseBCell,
    diamondOddBGaugeEquiv_apply,
    diamondOddBPassiveCubeEquiv_apply,
    TotalEOEEInternal.bGaugedRootFamilyEquiv_apply,
    diamondBRootCubeEquiv_apply]
  rw [g2_oddVecHeadTail_eq_evenVecHeadTail (n := n) hc,
    g2_oddVecHeadTail_eq_evenVecHeadTail (n := n) hd]

private theorem g2_k4BaseWCell_eq_wGauged
    {n b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n 1 b c) (yt : PVec n b) (zt : PVec n c) :
    k4BaseWCell hb hc W yt zt =
      wGaugedYZFamilyEquiv hb hc W yt zt := by
  funext i j k
  simp only [k4BaseWCell,
    diamondOddWGaugeEquiv_apply,
    diamondOddWPassiveCubeEquiv_apply,
    wGaugedYZFamilyEquiv_apply,
    diamondWRootCubeEquiv_apply]
  rw [g2_oddVecHeadTail_eq_evenVecHeadTail (n := n) hb,
    g2_oddVecHeadTail_eq_evenVecHeadTail (n := n) hc]

private theorem g2_baseRight_literal_source
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (r : K4EvenPBaseRight n b c d)
    (yt : PVec n b) (wt : PVec n d) :
    cubeDiffJInv
        (∑ zt : PVec n c,
          aLiteralGaugeEquiv hb hc hd r.1.1 yt zt wt) +
      (∑ zt : PVec n c,
        cubeDiffP (k4BaseBCell hc hd r.1.2.1 zt wt)) +
      (∑ zt : PVec n c,
        cubeDiffR (k4BaseWCell hb hc r.1.2.2 yt zt)) = 0 := by
  funext i j k
  have hbase := LinearMap.mem_ker.mp r.2
  rw [k4EvenPBaseRightMap_apply] at hbase
  have hp := congrFun
    (congrFun
      (congrFun
        (congrFun hbase (zeroVec : PVec n 1))
        ((diamondVecHeadTailEquiv hb).symm
          (i - vecSum yt, yt)))
      j)
    ((diamondVecHeadTailEquiv hd).symm
      (k - vecSum wt, wt))
  simp only [Pi.add_apply, Pi.zero_apply] at hp
  rw [diamondCubeReindex_AConstraint hb hc hd,
    diamondCubeReindex_squareCompat hb hc hd] at hp
  simp only [map_sum, Pi.add_apply, Finset.sum_apply,
    g2_k4BaseBCell_eq_bGauged,
    g2_k4BaseWCell_eq_wGauged,
    TotalEEEEInternal.bGauged_cubeDiffP_apply,
    TotalEEEEInternal.wGauged_cubeDiffR_apply,
    aLiteralGauge_cubeDiffJInv_apply,
    sub_add_cancel, Finset.sum_add_distrib] at hp ⊢
  simpa only [add_assoc] using hp

private theorem g2_reachableEEEEEquiv_eq_pack_raw
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (A : DiamondEvenPReachableA n b c d) :
    let raw :=
      TotalEEEERightInternal.rawRightCoordinateEquiv
        hn hb2 hc2 hd2 A.1
    let D :
        TotalEEEERightInternal.t37RightLedgerSubmodule n b d :=
      ⟨raw.1.1,
        (TotalEEEERightInternal.literal_reachable_iff_raw_D_ledger
          hn hb2 hc2 hd2 A.1).mp A.2⟩
    let packedD :=
      TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
        hn hb2 hd2 D
    let packedZTail :=
      TotalEEEERightInternal.tailT37ReassocEquiv
        (n := n) (b := b) (c := c) (d := d) raw.2
    diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A =
      TotalEEEERightInternal.constrainedZTotalFreeEquiv
        (n := n) (b := b) (c := c) (d := d)
        ((packedD, raw.1.2), packedZTail) := by
  rfl

private theorem g2_packedT37_scalar_value
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hd2 : 2 <= d)
    (q : TotalEEEERightInternal.t37RightLedgerSubmodule n b d) :
    ((TotalEEEERightInternal.t37LedgerAmbientToReachableTargetEquiv
      hn hb2 hd2 q).1).1 = q.1.1 := by
  change
    (T37RightP1.t37RightAmbientEquiv hn hb2 hd2
      ((T37RightP1.t37RightAmbientEquiv
        hn hb2 hd2).symm q.1)).1 = q.1.1
  exact congrArg Prod.fst
    ((T37RightP1.t37RightAmbientEquiv
      hn hb2 hd2).apply_symm_apply q.1)

private theorem g2_constrainedZTotalFreeEquiv_fields
    {n b c d : Nat} [NeZero n]
    (q : TotalEEEERightInternal.ConstrainedZTotalFreeInput n b c d) :
    TotalEEEERightInternal.constrainedZTotalFreeEquiv
        (n := n) (b := b) (c := c) (d := d) q =
      (TotalEEEERightInternal.scalarConstrainedFreeEquiv
          (q.1.1.1, q.1.2.1),
        (TotalEEEERightInternal.yConstrainedFreeEquiv
            (q.1.1.2.1, q.1.2.2.1),
          (TotalEEEERightInternal.wConstrainedFreeEquiv
              (q.1.1.2.2.1, q.1.2.2.2.1),
            (q.2.1,
              (q.2.2.1,
                (q.2.2.2.1,
                  (TotalEEEERightInternal.ywConstrainedFreeEquiv
                      (q.1.1.2.2.2, q.1.2.2.2.2),
                    q.2.2.2.2))))))) := by
  rfl

private theorem g2_right_A100_eq_raw
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (A : DiamondEvenPReachableA n b c d) :
    (rightRead hn hb2 hc2 hd2 A).1.2.1.1 =
      (TotalEEEERightInternal.rawRightCoordinateEquiv
        hn hb2 hc2 hd2 A.1).1.1.1.2.1 := by
  rw [rightRead_apply]
  rw [g2_reachableEEEEEquiv_eq_pack_raw]
  rw [g2_constrainedZTotalFreeEquiv_fields]
  let raw := TotalEEEERightInternal.rawRightCoordinateEquiv
    hn hb2 hc2 hd2 A.1
  let D : TotalEEEERightInternal.t37RightLedgerSubmodule n b d :=
    ⟨raw.1.1,
      (TotalEEEERightInternal.literal_reachable_iff_raw_D_ledger
        hn hb2 hc2 hd2 A.1).mp A.2⟩
  have h := g2_packedT37_scalar_value hn hb2 hd2 D
  exact congrArg (fun q => q.2.1) h

private theorem g2_right_A001_eq_raw
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (A : DiamondEvenPReachableA n b c d) :
    (rightRead hn hb2 hc2 hd2 A).1.1.1.2 =
      (TotalEEEERightInternal.rawRightCoordinateEquiv
        hn hb2 hc2 hd2 A.1).1.1.1.1.2 := by
  rw [rightRead_apply]
  rw [g2_reachableEEEEEquiv_eq_pack_raw]
  rw [g2_constrainedZTotalFreeEquiv_fields]
  let raw := TotalEEEERightInternal.rawRightCoordinateEquiv
    hn hb2 hc2 hd2 A.1
  let D : TotalEEEERightInternal.t37RightLedgerSubmodule n b d :=
    ⟨raw.1.1,
      (TotalEEEERightInternal.literal_reachable_iff_raw_D_ledger
        hn hb2 hc2 hd2 A.1).mp A.2⟩
  have h := g2_packedT37_scalar_value hn hb2 hd2 D
  exact congrArg (fun q => q.1.2) h

private theorem g2_baseRight_BAggregateConstraint_eq_right_A100
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (r : K4EvenPBaseRight n b c d) :
    k4BAggregateConstraint
        (k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1) =
      cubeDiffJInv
        (rightRead hn hb2 hc2 hd2
          (k4BaseRightToDiamondReachable r)).1.2.1.1 := by
  let D : PVec n b -> PVec n d -> CyclicCube n := fun yt wt =>
    ∑ zt : PVec n c,
      aLiteralGaugeEquiv (by omega) (by omega) (by omega) r.1.1 yt zt wt
  let P : PVec n d -> CyclicCube n := fun wt =>
    ∑ zt : PVec n c,
      cubeDiffP (k4BaseBCell (by omega) (by omega) r.1.2.1 zt wt)
  let R : PVec n b -> CyclicCube n := fun yt =>
    ∑ zt : PVec n c,
      cubeDiffR (k4BaseWCell (by omega) (by omega) r.1.2.2 yt zt)
  let E : PVec n b -> PVec n d -> CyclicCube n := fun yt wt =>
    cubeDiffJInv (D yt wt)
  have hsource : forall yt wt, E yt wt + P wt + R yt = 0 := by
    intro yt wt
    exact g2_baseRight_literal_source (by omega) (by omega) (by omega) r yt wt
  have hB := g2_B_joint_identity hn hb2 hd2 P R E hsource
  have hA := g2_t37_A100 hn hb2 hd2 D
  rw [k4BAggregateConstraint_apply]
  change cubeDiffP (∑ zt : PVec n c,
    ∑ wt : PVec n d, k4BaseBCell (by omega) (by omega) r.1.2.1 zt wt) = _
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  change (∑ wt : PVec n d, P wt) = _
  calc
    (∑ wt : PVec n d, P wt) =
        (∑ wt : PVec n d, E zeroVec wt) +
          ∑ yt : PVec n b, ∑ wt : PVec n d, E yt wt := hB
    _ = cubeDiffJInv
        ((∑ wt : PVec n d, D zeroVec wt) +
          ∑ yt : PVec n b, ∑ wt : PVec n d, D yt wt) := by
          simp only [E, map_add, map_sum]
    _ = cubeDiffJInv
        (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 D).1.2.1 := by
          rw [hA]
    _ = cubeDiffJInv
        (rightRead hn hb2 hc2 hd2
          (k4BaseRightToDiamondReachable r)).1.2.1.1 := by
          rw [g2_right_A100_eq_raw]
          rw [TotalEEEERightInternal.rawRightCoordinateEquiv_D]
          have hHead :=
            TotalEEEERightInternal.rawRightCoordinateHead_eq_literal_sum
              hn hc2 (by omega) (by omega) r.1.1
          have hCoord := congrArg
            (fun G =>
              (T37RightP1.t37GaugedRightCoordinateEquiv
                hn hb2 hd2 G).1.2.1) hHead
          exact congrArg (cubeDiffJInv (n := n)) hCoord.symm

private theorem g2_baseRight_WAggregateConstraint_eq_right_A001
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (r : K4EvenPBaseRight n b c d) :
    k4WAggregateConstraint
        (k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2) =
      cubeDiffJInv
        (rightRead hn hb2 hc2 hd2
          (k4BaseRightToDiamondReachable r)).1.1.1.2 := by
  let D : PVec n b -> PVec n d -> CyclicCube n := fun yt wt =>
    ∑ zt : PVec n c,
      aLiteralGaugeEquiv (by omega) (by omega) (by omega) r.1.1 yt zt wt
  let P : PVec n d -> CyclicCube n := fun wt =>
    ∑ zt : PVec n c,
      cubeDiffP (k4BaseBCell (by omega) (by omega) r.1.2.1 zt wt)
  let R : PVec n b -> CyclicCube n := fun yt =>
    ∑ zt : PVec n c,
      cubeDiffR (k4BaseWCell (by omega) (by omega) r.1.2.2 yt zt)
  let E : PVec n b -> PVec n d -> CyclicCube n := fun yt wt =>
    cubeDiffJInv (D yt wt)
  have hsource : forall yt wt, E yt wt + P wt + R yt = 0 := by
    intro yt wt
    exact g2_baseRight_literal_source (by omega) (by omega) (by omega) r yt wt
  have hW := g2_W_joint_identity hn hb2 hd2 P R E hsource
  have hA := g2_t37_A001 hn hb2 hd2 D
  rw [k4WAggregateConstraint_apply]
  change cubeDiffR (∑ zt : PVec n c,
    ∑ yt : PVec n b, k4BaseWCell (by omega) (by omega) r.1.2.2 yt zt) = _
  simp_rw [map_sum]
  rw [Finset.sum_comm]
  change (∑ yt : PVec n b, R yt) = _
  calc
    (∑ yt : PVec n b, R yt) =
        (∑ yt : PVec n b, E yt zeroVec) +
          ∑ yt : PVec n b, ∑ wt : PVec n d, E yt wt := hW
    _ = cubeDiffJInv
        ((∑ yt : PVec n b, D yt zeroVec) +
          ∑ yt : PVec n b, ∑ wt : PVec n d, D yt wt) := by
          simp only [E, map_add, map_sum]
    _ = cubeDiffJInv
        (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 D).1.1.2 := by
          rw [hA]
    _ = cubeDiffJInv
        (rightRead hn hb2 hc2 hd2
          (k4BaseRightToDiamondReachable r)).1.1.1.2 := by
          rw [g2_right_A001_eq_raw]
          rw [TotalEEEERightInternal.rawRightCoordinateEquiv_D]
          have hHead :=
            TotalEEEERightInternal.rawRightCoordinateHead_eq_literal_sum
              hn hc2 (by omega) (by omega) r.1.1
          have hCoord := congrArg
            (fun G =>
              (T37RightP1.t37GaugedRightCoordinateEquiv
                hn hb2 hd2 G).1.1.2) hHead
          exact congrArg (cubeDiffJInv (n := n)) hCoord.symm

private theorem g2_baseRight_BAggregate_mem_of_rightRead_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (r : K4EvenPBaseRight n b c d)
    (hread : rightRead hn hb2 hc2 hd2
      (k4BaseRightToDiamondReachable r) = 0) :
    k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1 ∈
      K4BAggregateLeft n c := by
  apply LinearMap.mem_ker.mpr
  rw [g2_baseRight_BAggregateConstraint_eq_right_A100
    hn hb2 hc2 hd2 r]
  have hA := congrArg
    (fun q : DiamondEEEERightSource n => q.1.2.1.1) hread
  have hDiff := congrArg (cubeDiffJInv (n := n)) hA
  simpa only [map_zero] using hDiff

private theorem g2_baseRight_WAggregate_mem_of_rightRead_zero
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (r : K4EvenPBaseRight n b c d)
    (hread : rightRead hn hb2 hc2 hd2
      (k4BaseRightToDiamondReachable r) = 0) :
    k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2 ∈
      K4WAggregateLeft n c := by
  apply LinearMap.mem_ker.mpr
  rw [g2_baseRight_WAggregateConstraint_eq_right_A001
    hn hb2 hc2 hd2 r]
  have hA := congrArg
    (fun q : DiamondEEEERightSource n => q.1.1.1.2) hread
  have hDiff := congrArg (cubeDiffJInv (n := n)) hA
  simpa only [map_zero] using hDiff

private theorem g2_kappa_pair_zero_of_rightRead_zero
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (s : K4BaseMixedScalarSector n)
    (r : K4EvenPBaseRight n b c d)
    (hread : rightRead hn hb2 hc2 hd2
      (k4BaseRightToDiamondReachable r) = 0) :
    let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    let BK := k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1
    let WK := k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2
    k4AggregateKappaScalar u.1.1.1 WK +
      k4AggregateKappaScalar BK u.1.2.1 = 0 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (mixedOverlap hn hb2 hc2 hd2 s).2
  let BK := k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1
  let WK := k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2
  let vB : K4BAggregateLeft n c :=
    ⟨BK, g2_baseRight_BAggregate_mem_of_rightRead_zero
      hn hb2 hc2 hd2 r hread⟩
  let vW : K4WAggregateLeft n c :=
    ⟨WK, g2_baseRight_WAggregate_mem_of_rightRead_zero
      hn hb2 hc2 hd2 r hread⟩
  have hker := LinearMap.mem_ker.mp u.2
  have h := LinearMap.congr_fun hker (vB, vW)
  change
    k4AggregateKappaScalar u.1.1.1 WK +
      k4AggregateKappaScalar BK u.1.2.1 = 0 at h
  exact h


private theorem descendedCross_zero_on_baseRight_scalarKernel
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (s : K4BaseMixedScalarSector n)
    (r : K4EvenPBaseRight n b c d)
    (hread : rightRead hn hb2 hc2 hd2
      (k4BaseRightToDiamondReachable r) = 0) :
    descendedCross hn2 hn hb2 hc2 hd2 s
      (k4BaseRightToDiamondReachable r) = 0 := by
  rw [descendedCross_apply]
  rw [k4BaseDescendedMixedOverlapCross_split_phase
    (n := n) (b := b) (c := c) (d := d)
    hn2 hn hb2 hc2 hd2
    (mixedOverlap hn hb2 hc2 hd2 s).1
    (mixedOverlap hn hb2 hc2 hd2 s).2 r]
  have hRoot := diamond_root_pair_zero_of_rightRead_zero
    hn2 hn hb2 hc2 hd2 s r hread
  have hKappa := g2_kappa_pair_zero_of_rightRead_zero
    hn2 hn hb2 hc2 hd2 s r hread
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hd : 0 < d := by omega
  dsimp only at hRoot hKappa ⊢
  calc
    _ = (diamondEvenPCross
          (mixedOverlap hn hb2 hc2 hd2 s).1.1
          (k4BaseRightToDiamondReachable r) +
        coeffApplyA
          (KBMap
              (k4AggregateLift hb hc hd
                (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
                  (mixedOverlap hn hb2 hc2 hd2 s).2).1).1.1 +
            KWMap
              (k4AggregateLift hb hc hd
                (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
                  (mixedOverlap hn hb2 hc2 hd2 s).2).1).1.2)
          r.1.1) +
        (k4AggregateKappaScalar
            (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
              (mixedOverlap hn hb2 hc2 hd2 s).2).1.1.1
            (k4BaseWAggregateRaw hb hc r.1.2.2) +
          k4AggregateKappaScalar
            (k4BaseBAggregateRaw hc hd r.1.2.1
            )
            (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
              (mixedOverlap hn hb2 hc2 hd2 s).2).1.2.1) := by
          abel_nf
    _ = 0 := by rw [hRoot, hKappa, add_zero]

/-! The exact six frozen public declarations. -/

noncomputable def localScalarCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d) :
    K4BaseMixedScalarSector n →ₗ[F]
      Module.Dual F (DiamondEEEERightSource n) :=
  (rightSection hn hb2 hc2 hd2).dualMap.comp
    (descendedCross hn2 hn hb2 hc2 hd2)

theorem localScalarCross_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (s : K4BaseMixedScalarSector n)
    (q : DiamondEEEERightSource n) :
    localScalarCross hn2 hn hb2 hc2 hd2 s q =
      descendedCross hn2 hn hb2 hc2 hd2 s
        (rightSection hn hb2 hc2 hd2 q) := by
  rfl

theorem localScalarCross_four_terms
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (s : K4BaseMixedScalarSector n)
    (q : DiamondEEEERightSource n)
    (r : K4EvenPBaseRight n b c d)
    (hr : k4BaseRightToDiamondReachable r =
      rightSection hn hb2 hc2 hd2 q) :
    let z := mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    let BKbar :=
      k4BaseBAggregateRaw (by omega : 0 < c) (by omega : 0 < d) r.1.2.1
    let WKbar :=
      k4BaseWAggregateRaw (by omega : 0 < b) (by omega : 0 < c) r.1.2.2
    localScalarCross hn2 hn hb2 hc2 hd2 s q =
      diamondEvenPCross z.1.1 (k4BaseRightToDiamondReachable r) +
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 +
        k4AggregateKappaScalar u.1.1.1 WKbar +
        k4AggregateKappaScalar BKbar u.1.2.1 := by
  dsimp only
  rw [localScalarCross_apply, <- hr, descendedCross_apply]
  exact k4BaseDescendedMixedOverlapCross_split_phase
    (n := n) (b := b) (c := c) (d := d)
    hn2 hn hb2 hc2 hd2
    (mixedOverlap hn hb2 hc2 hd2 s).1
    (mixedOverlap hn hb2 hc2 hd2 s).2 r

theorem descendedCross_ker_rightRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (s : K4BaseMixedScalarSector n) :
    LinearMap.ker (rightRead hn hb2 hc2 hd2) <=
      LinearMap.ker (descendedCross hn2 hn hb2 hc2 hd2 s) := by
  intro A hA
  apply LinearMap.mem_ker.mpr
  obtain ⟨r, rfl⟩ := k4BaseRightToDiamondReachable_surjective A
  exact descendedCross_zero_on_baseRight_scalarKernel
    hn2 hn hb2 hc2 hd2 s r (LinearMap.mem_ker.mp hA)

theorem scalarPhaseFullSupport
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (s : K4BaseMixedScalarSector n)
    (A : DiamondEvenPReachableA n b c d) :
    descendedCross hn2 hn hb2 hc2 hd2 s A =
      descendedCross hn2 hn hb2 hc2 hd2 s
        (rightSection hn hb2 hc2 hd2
          (rightRead hn hb2 hc2 hd2 A)) := by
  let D : DiamondEvenPReachableA n b c d :=
    A - rightSection hn hb2 hc2 hd2
      (rightRead hn hb2 hc2 hd2 A)
  have hDread : rightRead hn hb2 hc2 hd2 D = 0 := by
    dsimp only [D]
    rw [map_sub, rightRead_rightSection, sub_self]
  have hDcross : descendedCross hn2 hn hb2 hc2 hd2 s D = 0 :=
    LinearMap.mem_ker.mp
      (descendedCross_ker_rightRead hn2 hn hb2 hc2 hd2 s
        (LinearMap.mem_ker.mpr hDread))
  have hsub :
      descendedCross hn2 hn hb2 hc2 hd2 s A -
          descendedCross hn2 hn hb2 hc2 hd2 s
            (rightSection hn hb2 hc2 hd2
              (rightRead hn hb2 hc2 hd2 A)) = 0 := by
    rw [<- map_sub]
    exact hDcross
  exact sub_eq_zero.mp hsub

theorem descendedCross_eq_rightRead_dual_localCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d) :
    descendedCross hn2 hn hb2 hc2 hd2 =
      (rightRead hn hb2 hc2 hd2).dualMap.comp
        (localScalarCross hn2 hn hb2 hc2 hd2) := by
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro A
  exact scalarPhaseFullSupport hn2 hn hb2 hc2 hd2 s A

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
