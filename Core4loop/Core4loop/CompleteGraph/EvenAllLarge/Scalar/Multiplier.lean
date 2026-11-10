import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Phase
import Core4loop.SquareDiagonal.EvenP.EEEE.Projection

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEEPhase
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

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


private noncomputable def kappaCoeff
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun B := fun i j k => B i j k + B (i + 1) j (k - 1)
  map_add' _ _ := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' a B := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

private noncomputable def kappaTransposeCoeff
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun W := fun i j k => W i j k + W (i - 1) j (k + 1)
  map_add' _ _ := by
    funext i j k
    simp only [Pi.add_apply]
    abel
  map_smul' a W := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add]

private theorem kappa_eq_dot_coeff
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W = cubeDot (kappaCoeff B) W := by
  unfold k4CubeKappa cubeDot kappaCoeff
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.refl (I n)) (Equiv.addRight (1 : I n)))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

private theorem kappa_eq_dot_transpose
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W = cubeDot B (kappaTransposeCoeff W) := by
  unfold k4CubeKappa cubeDot kappaTransposeCoeff
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.addRight (1 : I n))
      (Equiv.refl (I n × I n))
  apply Fintype.sum_equiv e
  intro q
  simp [e]

private theorem cubeDot_comm
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

private noncomputable def rOrbit
    {n : Nat} [NeZero n] (K : CyclicCube n) (i s : I n) : Profile n :=
  fun t => K i t (s - t)

private noncomputable def pOrbit
    {n : Nat} [NeZero n] (K : CyclicCube n) (s k : I n) : Profile n :=
  fun t => K (s - t) t k

private noncomputable def rStarPrimitive
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun K := fun i j k => explicitCyclicPrefix (rOrbit K i (j + k)) j
  map_add' K K' := by
    funext i j k
    simp only [rOrbit, Pi.add_apply, explicitCyclicPrefix, finPrefix,
      Finset.sum_add_distrib]
  map_smul' a K := by
    funext i j k
    simp only [rOrbit, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      explicitCyclicPrefix, finPrefix, ← Finset.mul_sum]

private noncomputable def pStarPrimitive
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun K := fun i j k => explicitCyclicPrefix (pOrbit K (i + j) k) j
  map_add' K K' := by
    funext i j k
    simp only [pOrbit, Pi.add_apply, explicitCyclicPrefix, finPrefix,
      Finset.sum_add_distrib]
  map_smul' a K := by
    funext i j k
    simp only [pOrbit, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      explicitCyclicPrefix, finPrefix, ← Finset.mul_sum]

private theorem cubeDiffRStar_rStarPrimitive
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hzero : ∀ i s : I n, ∑ t : I n, rOrbit K i s t = 0) :
    cubeDiffRStar (rStarPrimitive K) = K := by
  funext i j k
  rw [EEOEInternal.cubeDiffRStar_apply]
  change
    explicitCyclicPrefix (rOrbit K i (j + k)) j +
        explicitCyclicPrefix (rOrbit K i (j + 1 + (k - 1))) (j + 1) =
      K i j k
  have hs : j + 1 + (k - 1) = j + k := by abel
  rw [hs]
  let u : ZeroSumProfile n :=
    ⟨rOrbit K i (j + k), LinearMap.mem_ker.mpr (hzero i (j + k))⟩
  have hdiff := congrFun (cycDiff_explicitCyclicPrimitive u) j
  change
    explicitCyclicPrefix (rOrbit K i (j + k)) j +
        explicitCyclicPrefix (rOrbit K i (j + k)) (j + 1) =
      rOrbit K i (j + k) j at hdiff
  rw [hdiff]
  simp only [rOrbit]
  congr 3
  abel

private theorem cubeDiffPStar_pStarPrimitive
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hzero : ∀ s k : I n, ∑ t : I n, pOrbit K s k t = 0) :
    cubeDiffPStar (pStarPrimitive K) = K := by
  funext i j k
  rw [EEOEInternal.cubeDiffPStar_apply]
  change
    explicitCyclicPrefix (pOrbit K (i + j) k) j +
        explicitCyclicPrefix (pOrbit K ((i - 1) + (j + 1)) k) (j + 1) =
      K i j k
  have hs : (i - 1) + (j + 1) = i + j := by abel
  rw [hs]
  let u : ZeroSumProfile n :=
    ⟨pOrbit K (i + j) k, LinearMap.mem_ker.mpr (hzero (i + j) k)⟩
  have hdiff := congrFun (cycDiff_explicitCyclicPrimitive u) j
  change
    explicitCyclicPrefix (pOrbit K (i + j) k) j +
        explicitCyclicPrefix (pOrbit K (i + j) k) (j + 1) =
      pOrbit K (i + j) k j at hdiff
  rw [hdiff]
  simp only [pOrbit]
  congr 3
  abel

private theorem rOrbit_zero_of_mem_range
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hK : K ∈ LinearMap.range (cubeDiffRStar (n := n)))
    (i s : I n) :
    ∑ t : I n, rOrbit K i s t = 0 := by
  rcases hK with ⟨lambda, rfl⟩
  let f : Profile n := fun t => lambda i t (s - t)
  change ∑ t : I n, cubeDiffRStar lambda i t (s - t) = 0
  simp only [EEOEInternal.cubeDiffRStar_apply]
  have hf (t : I n) :
      lambda i (t + 1) (s - t - 1) = f (t + 1) := by
    dsimp only [f]
    apply congrArg (fun x => lambda i (t + 1) x)
    abel
  simp_rw [hf]
  change ∑ t : I n, (f t + f (t + 1)) = 0
  rw [Finset.sum_add_distrib]
  have hshift : (∑ t : I n, f (t + 1)) = ∑ t : I n, f t := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : I n)) f)
  rw [hshift]
  exact F_add_self _

private theorem pOrbit_zero_of_mem_range
    {n : Nat} [NeZero n] (K : CyclicCube n)
    (hK : K ∈ LinearMap.range (cubeDiffPStar (n := n)))
    (s k : I n) :
    ∑ t : I n, pOrbit K s k t = 0 := by
  rcases hK with ⟨lambda, rfl⟩
  let f : Profile n := fun t => lambda (s - t) t k
  change ∑ t : I n, cubeDiffPStar lambda (s - t) t k = 0
  simp only [EEOEInternal.cubeDiffPStar_apply]
  have hf (t : I n) :
      lambda (s - t - 1) (t + 1) k = f (t + 1) := by
    dsimp only [f]
    apply congrArg (fun x => lambda x (t + 1) k)
    abel
  simp_rw [hf]
  change ∑ t : I n, (f t + f (t + 1)) = 0
  rw [Finset.sum_add_distrib]
  have hshift : (∑ t : I n, f (t + 1)) = ∑ t : I n, f t := by
    simpa using (Equiv.sum_comp (Equiv.addRight (1 : I n)) f)
  rw [hshift]
  exact F_add_self _

private theorem kappaCoeff_bFree_mem_range_RStar
    {n : Nat} [NeZero n] (B : K4BFreeHeadRadical n) :
    kappaCoeff B.1 ∈ LinearMap.range (cubeDiffRStar (n := n)) := by
  let phi : Module.Dual F (CyclicCube n) :=
    EEEEInternal.cubeDotDual (kappaCoeff B.1)
  have hvanish : ∀ W : CyclicCube n,
      cubeDiffR W ∈ LinearMap.range (0 : CyclicCube n →ₗ[F] CyclicCube n) →
        phi W = 0 := by
    intro W hW
    have hdiff : cubeDiffR W = 0 := by
      rcases hW with ⟨X, hX⟩
      simpa using hX.symm
    let WK : LinearMap.ker (cubeDiffR (n := n)) :=
      ⟨W, LinearMap.mem_ker.mpr hdiff⟩
    have hcross := LinearMap.congr_fun (LinearMap.mem_ker.mp B.2) WK
    change k4CubeKappa B.1 W = 0 at hcross
    simpa [phi, EEEEInternal.cubeDotDual, kappa_eq_dot_coeff] using hcross
  rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
      cubeDiffR (0 : CyclicCube n →ₗ[F] CyclicCube n) phi hvanish with
    ⟨psi, hfactor, _⟩
  rcases EEEEInternal.dual_exists_cubeDot psi with ⟨lambda, hlambda⟩
  refine ⟨lambda, ?_⟩
  apply EEEEInternal.cubeDot_left_ext
  intro W
  calc
    cubeDot (cubeDiffRStar lambda) W = cubeDot lambda (cubeDiffR W) :=
      cubeDiffR_pairing_adjoint lambda W
    _ = psi (cubeDiffR W) := (hlambda _).symm
    _ = phi W := LinearMap.congr_fun hfactor W |>.symm
    _ = cubeDot (kappaCoeff B.1) W := rfl

private theorem kappaTransposeCoeff_wFree_mem_range_PStar
    {n : Nat} [NeZero n] (W : K4WFreeHeadRadical n) :
    kappaTransposeCoeff W.1 ∈
      LinearMap.range (cubeDiffPStar (n := n)) := by
  let phi : Module.Dual F (CyclicCube n) :=
    EEEEInternal.cubeDotDual (kappaTransposeCoeff W.1)
  have hvanish : ∀ B : CyclicCube n,
      cubeDiffP B ∈ LinearMap.range (0 : CyclicCube n →ₗ[F] CyclicCube n) →
        phi B = 0 := by
    intro B hB
    have hdiff : cubeDiffP B = 0 := by
      rcases hB with ⟨X, hX⟩
      simpa using hX.symm
    let BK : LinearMap.ker (cubeDiffP (n := n)) :=
      ⟨B, LinearMap.mem_ker.mpr hdiff⟩
    have hcross := LinearMap.congr_fun (LinearMap.mem_ker.mp W.2) BK
    change k4CubeKappa B W.1 = 0 at hcross
    rw [kappa_eq_dot_transpose, cubeDot_comm] at hcross
    simpa [phi, EEEEInternal.cubeDotDual] using hcross
  rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
      cubeDiffP (0 : CyclicCube n →ₗ[F] CyclicCube n) phi hvanish with
    ⟨psi, hfactor, _⟩
  rcases EEEEInternal.dual_exists_cubeDot psi with ⟨lambda, hlambda⟩
  refine ⟨lambda, ?_⟩
  apply EEEEInternal.cubeDot_left_ext
  intro B
  calc
    cubeDot (cubeDiffPStar lambda) B = cubeDot lambda (cubeDiffP B) :=
      cubeDiffP_pairing_adjoint lambda B
    _ = psi (cubeDiffP B) := (hlambda _).symm
    _ = phi B := LinearMap.congr_fun hfactor B |>.symm
    _ = cubeDot (kappaTransposeCoeff W.1) B := rfl

private theorem cubeDiffRStar_rStarPrimitive_bFree
    {n : Nat} [NeZero n] (B : K4BFreeHeadRadical n) :
    cubeDiffRStar (rStarPrimitive (kappaCoeff B.1)) = kappaCoeff B.1 := by
  apply cubeDiffRStar_rStarPrimitive
  exact fun i s => rOrbit_zero_of_mem_range _
    (kappaCoeff_bFree_mem_range_RStar B) i s

private theorem cubeDiffPStar_pStarPrimitive_wFree
    {n : Nat} [NeZero n] (W : K4WFreeHeadRadical n) :
    cubeDiffPStar (pStarPrimitive (kappaTransposeCoeff W.1)) =
      kappaTransposeCoeff W.1 := by
  apply cubeDiffPStar_pStarPrimitive
  exact fun s k => pOrbit_zero_of_mem_range _
    (kappaTransposeCoeff_wFree_mem_range_PStar W) s k

private noncomputable def bFreeLambda
    {n : Nat} [NeZero n] :
    K4BFreeHeadRadical n →ₗ[F] CyclicCube n :=
  rStarPrimitive.comp
    (kappaCoeff.comp (K4BFreeHeadRadical n).subtype)

private noncomputable def wFreeLambda
    {n : Nat} [NeZero n] :
    K4WFreeHeadRadical n →ₗ[F] CyclicCube n :=
  pStarPrimitive.comp
    (kappaTransposeCoeff.comp (K4WFreeHeadRadical n).subtype)

private theorem bFree_added_pairing
    {n : Nat} [NeZero n]
    (B : K4BFreeHeadRadical n) (A W : CyclicCube n)
    (hA : cubeDiffJInv A = cubeDiffR W) :
    cubeDot (cubeDiffJStar (bFreeLambda B)) A = k4CubeKappa B.1 W := by
  calc
    cubeDot (cubeDiffJStar (bFreeLambda B)) A =
        cubeDot (bFreeLambda B) (cubeDiffJInv A) :=
      cubeDiffJ_pairing_adjoint _ _
    _ = cubeDot (bFreeLambda B) (cubeDiffR W) := by rw [hA]
    _ = cubeDot (cubeDiffRStar (bFreeLambda B)) W :=
      (cubeDiffR_pairing_adjoint _ _).symm
    _ = cubeDot (kappaCoeff B.1) W := by
      change cubeDot
        (cubeDiffRStar (rStarPrimitive (kappaCoeff B.1))) W = _
      rw [cubeDiffRStar_rStarPrimitive_bFree]
    _ = k4CubeKappa B.1 W := (kappa_eq_dot_coeff _ _).symm

private theorem wFree_added_pairing
    {n : Nat} [NeZero n]
    (W : K4WFreeHeadRadical n) (A B : CyclicCube n)
    (hA : cubeDiffJInv A = cubeDiffP B) :
    cubeDot (cubeDiffJStar (wFreeLambda W)) A = k4CubeKappa B W.1 := by
  calc
    cubeDot (cubeDiffJStar (wFreeLambda W)) A =
        cubeDot (wFreeLambda W) (cubeDiffJInv A) :=
      cubeDiffJ_pairing_adjoint _ _
    _ = cubeDot (wFreeLambda W) (cubeDiffP B) := by rw [hA]
    _ = cubeDot (cubeDiffPStar (wFreeLambda W)) B :=
      (cubeDiffP_pairing_adjoint _ _).symm
    _ = cubeDot (kappaTransposeCoeff W.1) B := by
      change cubeDot
        (cubeDiffPStar (pStarPrimitive (kappaTransposeCoeff W.1))) B = _
      rw [cubeDiffPStar_pStarPrimitive_wFree]
    _ = cubeDot B (kappaTransposeCoeff W.1) := cubeDot_comm _ _
    _ = k4CubeKappa B W.1 := (kappa_eq_dot_transpose _ _).symm

private noncomputable def scalarBFreeRead
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F] K4BFreeHeadRadical n where
  toFun s := s.2.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def scalarWFreeRead
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F] K4WFreeHeadRadical n where
  toFun s := s.2.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def scalarAddedCoeffMap
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F] DiamondEEEERightAmbient n :=
  let bCell := cubeDiffJStar.comp (bFreeLambda.comp scalarBFreeRead)
  let wCell := cubeDiffJStar.comp (wFreeLambda.comp scalarWFreeRead)
  LinearMap.prod
    (LinearMap.prod
      (LinearMap.prod 0 bCell)
      (LinearMap.prod 0 0))
    (LinearMap.prod
      (LinearMap.prod wCell 0)
      (LinearMap.prod 0 0))

noncomputable def scalarCoeffMap
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedScalarSector n →ₗ[F] DiamondEEEERightAmbient n :=
  (diamondEEEECoeffMap.comp
      ((DiamondEEEELeftSource n).subtype.comp
        (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2))) +
    scalarAddedCoeffMap

private theorem polar_build_B_free
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (Scalar.polarSource (c := c) x)
    (k4BAggregateCoordEquiv hn hc2 u.1.1).1.2 = x.1.2.1 := by
  dsimp only
  have h := k4AggregatePolarKernelCoordinateRead_build hn2 hn hc2
    (Scalar.polarSource (c := c) x)
  exact congrArg (fun q => q.1.1.2.1) h

private theorem polar_build_W_free
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (Scalar.polarSource (c := c) x)
    (k4WAggregateCoordEquiv hn hc2 u.1.2).1.1 = x.2.1.1 := by
  dsimp only
  have h := k4AggregatePolarKernelCoordinateRead_build hn2 hn hc2
    (Scalar.polarSource (c := c) x)
  exact congrArg (fun q => q.2.1.1.1) h

private theorem aggregateKappa_left_scalar
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n)
    (WK : PVec n c → CyclicCube n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (Scalar.polarSource (c := c) x)
    k4AggregateKappaScalar u.1.1.1 WK =
      k4CubeKappa x.1.2.1 (∑ zt, WK zt) := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (Scalar.polarSource (c := c) x)
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
  change k4AggregateKappaScalar u.1.1.1 WK = _
  rw [k4AggregateKappaScalar, hpair]
  change
    k4CubeKappa Bc.1.1.1 yw.1.1 +
        k4CubeKappa Bc.1.2 yw.1.2 +
        (∑ t, k4CubeKappa (Bc.2.1 t) (yw.2.1 t)) = _
  have hhead := LinearMap.congr_fun
    (LinearMap.mem_ker.mp hu.1) yw.1.1
  change k4CubeKappa Bc.1.1.1 yw.1.1 = 0 at hhead
  have htail : (∑ t, k4CubeKappa (Bc.2.1 t) (yw.2.1 t)) = 0 := by
    apply Fintype.sum_eq_zero
    intro t
    have ht := LinearMap.congr_fun (hu.2.2.1 t) (yw.2.1 t)
    exact ht
  have hfree := polar_build_B_free hn2 hn hc2 x
  change Bc.1.2 = x.1.2.1 at hfree
  have hsum := TotalEEEERightInternal.axisDualHead_eq_totalSum
    (CyclicCube n) hn hc2 WK
  change yw.1.2 = (∑ zt, WK zt) at hsum
  rw [hhead, zero_add, htail, add_zero, hfree, hsum]

private theorem aggregateKappa_right_scalar
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c)
    (x : K4AggregatePolarScalarCoordinates n)
    (BK : PVec n c → CyclicCube n) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (Scalar.polarSource (c := c) x)
    k4AggregateKappaScalar BK u.1.2.1 =
      k4CubeKappa (∑ zt, BK zt) x.2.1.1 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (Scalar.polarSource (c := c) x)
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
  change k4AggregateKappaScalar BK u.1.2.1 = _
  rw [k4AggregateKappaScalar, hpair]
  change
    k4CubeKappa xb.1.1 Wc.1.1 +
        k4CubeKappa xb.1.2 Wc.1.2.1 +
        (∑ t, k4CubeKappa (xb.2.1 t) (Wc.2.1 t)) = _
  have hhead := LinearMap.congr_fun
    (LinearMap.mem_ker.mp hu.2.2.2.2.1) xb.1.2
  change k4CubeKappa xb.1.2 Wc.1.2.1 = 0 at hhead
  have htail : (∑ t, k4CubeKappa (xb.2.1 t) (Wc.2.1 t)) = 0 := by
    apply Fintype.sum_eq_zero
    intro t
    have ht := LinearMap.congr_fun (hu.2.2.2.2.2 t) (xb.2.1 t)
    change k4CubeKappa (xb.2.1 t) (Wc.2.1 t) = 0 at ht
    exact ht
  have hfree := polar_build_W_free hn2 hn hc2 x
  change Wc.1.1 = x.2.1.1 at hfree
  have hsum := pointedSrcEvenValueEquiv_apply_sigma
    (zeroVec : PVec n c) (even_card_PVec hn hc2) BK
  change xb.1.1 = (∑ zt, BK zt) at hsum
  rw [hhead, add_zero, htail, add_zero, hfree, hsum]

private theorem scalarBaseCoeff
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n)
    (q : DiamondEEEERightSource n)
    (r : K4EvenPBaseRight n b c d)
    (hr : k4BaseRightToDiamondReachable r =
      Scalar.rightSection hn hb2 hc2 hd2 q) :
    let z := Scalar.mixedOverlap hn hb2 hc2 hd2 s
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
    let lift : K4EvenPLeft n b c d :=
      k4AggregateLift (by omega) (by omega) (by omega) u.1
    diamondEvenPCross z.1.1 (k4BaseRightToDiamondReachable r) +
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 =
      diamondEEEECross
        (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s) q := by
  dsimp only
  let z := Scalar.mixedOverlap hn hb2 hc2 hd2 s
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2
  let lift : K4EvenPLeft n b c d :=
    k4AggregateLift (by omega) (by omega) (by omega) u.1
  let A : DiamondEvenPReachableA n b c d :=
    k4BaseRightToDiamondReachable r
  have hrightRead :
      Scalar.rightRead hn hb2 hc2 hd2 A = q := by
    dsimp only [A]
    rw [hr, Scalar.rightRead_rightSection]
  have hright :
      (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A).1 = q := by
    exact (Scalar.rightRead_apply hn hb2 hc2 hd2 A).symm.trans hrightRead
  have hfull :
      diamondEvenPCross
          (Scalar.gPolarSource hn2 hn hb2 hc2 hd2 s).1 A =
        diamondEEEECross
          (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s) q := by
    rw [totalEEEELiteralPhaseCoordinateSplit]
    change
      totalEEEECoordinatePhase
          (Scalar.fullLeftCoordinate hn2 hn hb2 hc2 hd2 s)
          (diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A) =
        diamondEEEECross
          (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s) q
    rw [fullLeftCoordinate_eq_scalar_injection]
    simp only [totalEEEECoordinatePhase]
    rw [hright]
    simp only [
      totalEEEEYWBasePhase, totalEEEEYWZBasePhase,
      Finset.sum_const_zero, add_zero, zero_add]
    simp [totalEEEEYBasePhase, totalEEEEWBasePhase,
      totalEEEEYZBasePhase, totalEEEEWZBasePhase,
      diamondTailAllEvenZCross, diamondEEEECross,
      EEEEInternal.diamondEEEERestrictRightDual,
      EEEEInternal.diamondEEEERightPairing]
  have hval :
      (Scalar.gPolarSource hn2 hn hb2 hc2 hd2 s).1 = z.1.1 + lift := by
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
        coeffApplyA (KBMap lift.1.1 + KWMap lift.1.2) r.1.1 = _
  rw [← hlift, ← LinearMap.add_apply, ← map_add, ← hval]
  exact hfull

private theorem two_aggregate_kappa_eq_added_cells
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n)
    (q : DiamondEEEERightSource n)
    (r : K4EvenPBaseRight n b c d)
    (hr : k4BaseRightToDiamondReachable r =
      Scalar.rightSection hn hb2 hc2 hd2 q) :
    let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (Scalar.polarSource (n := n) (c := c) s.2)
    let BK := k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1
    let WK := k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2
    k4AggregateKappaScalar u.1.1.1 WK +
        k4AggregateKappaScalar BK u.1.2.1 =
      cubeDot (cubeDiffJStar (bFreeLambda s.2.1.2)) q.1.1.1.2 +
        cubeDot (cubeDiffJStar (wFreeLambda s.2.2.1)) q.1.2.1.1 := by
  dsimp only
  let u := k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
    (Scalar.polarSource (n := n) (c := c) s.2)
  let BK := k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1
  let WK := k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2
  have hBreduce := aggregateKappa_left_scalar hn2 hn hc2 s.2 WK
  have hWreduce := aggregateKappa_right_scalar hn2 hn hc2 s.2 BK
  have hWdef := g2_baseRight_WAggregateConstraint_eq_right_A001
    hn hb2 hc2 hd2 r
  rw [k4WAggregateConstraint_apply, hr,
    Scalar.rightRead_rightSection] at hWdef
  have hWA :
      cubeDiffJInv q.1.1.1.2 = cubeDiffR (∑ zt, WK zt) := hWdef.symm
  have hBdef := g2_baseRight_BAggregateConstraint_eq_right_A100
    hn hb2 hc2 hd2 r
  rw [k4BAggregateConstraint_apply, hr,
    Scalar.rightRead_rightSection] at hBdef
  have hBA :
      cubeDiffJInv q.1.2.1.1 = cubeDiffP (∑ zt, BK zt) := hBdef.symm
  have hBpair := bFree_added_pairing s.2.1.2 q.1.1.1.2
    (∑ zt, WK zt) hWA
  have hWpair := wFree_added_pairing s.2.2.1 q.1.2.1.1
    (∑ zt, BK zt) hBA
  rw [hBreduce, hWreduce, ← hBpair, ← hWpair]

private theorem localScalarCross_point_formula
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n)
    (q : DiamondEEEERightSource n) :
    Scalar.localScalarCross hn2 hn hb2 hc2 hd2 s q =
      diamondEEEECross
          (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s) q +
        cubeDot (cubeDiffJStar (bFreeLambda s.2.1.2)) q.1.1.1.2 +
        cubeDot (cubeDiffJStar (wFreeLambda s.2.2.1)) q.1.2.1.1 := by
  obtain ⟨r, hr⟩ := k4BaseRightToDiamondReachable_surjective
    (Scalar.rightSection hn hb2 hc2 hd2 q)
  have hfour := Scalar.localScalarCross_four_terms
    hn2 hn hb2 hc2 hd2 s q r hr
  have hbase := scalarBaseCoeff hn2 hn hb2 hc2 hd2 s q r hr
  have hadd := two_aggregate_kappa_eq_added_cells
    hn2 hn hb2 hc2 hd2 s q r hr
  have hz : (Scalar.mixedOverlap hn hb2 hc2 hd2 s).2 =
      Scalar.polarSource (n := n) (c := c) s.2 := by
    rfl
  dsimp only at hfour hbase hadd
  rw [hfour, hbase]
  rw [hz]
  let D : F := diamondEEEECross
    (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s) q
  let K1 : F := k4AggregateKappaScalar
    (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (Scalar.polarSource (n := n) (c := c) s.2)).1.1.1
    (k4BaseWAggregateRaw (by omega) (by omega) r.1.2.2)
  let K2 : F := k4AggregateKappaScalar
    (k4BaseBAggregateRaw (by omega) (by omega) r.1.2.1
    )
    (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2
      (Scalar.polarSource (n := n) (c := c) s.2)).1.2.1
  let C1 : F := cubeDot
    (cubeDiffJStar (bFreeLambda s.2.1.2)) q.1.1.1.2
  let C2 : F := cubeDot
    (cubeDiffJStar (wFreeLambda s.2.2.1)) q.1.2.1.1
  change (D + K1) + K2 = (D + C1) + C2
  change K1 + K2 = C1 + C2 at hadd
  calc
    (D + K1) + K2 = D + (K1 + K2) := by abel
    _ = D + (C1 + C2) := by rw [hadd]
    _ = (D + C1) + C2 := by abel

private theorem scalarAddedCoeffMap_pairing
    {n : Nat} [NeZero n]
    (s : K4BaseMixedScalarSector n)
    (q : DiamondEEEERightSource n) :
    EEEEInternal.diamondEEEERightPairing
        (scalarAddedCoeffMap s) q.1 =
      cubeDot (cubeDiffJStar (bFreeLambda s.2.1.2)) q.1.1.1.2 +
        cubeDot (cubeDiffJStar (wFreeLambda s.2.2.1)) q.1.2.1.1 := by
  simp only [scalarAddedCoeffMap, LinearMap.prod_apply,
    LinearMap.comp_apply, LinearMap.zero_apply,
    scalarBFreeRead, scalarWFreeRead]
  simp [EEEEInternal.diamondEEEERightPairing, cubeDot]

theorem localScalarCross_eq_restrict_pairing_coeffMap
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Scalar.localScalarCross hn2 hn hb2 hc2 hd2 =
      EEEEInternal.diamondEEEERestrictRightDual.comp
        (EEEEInternal.diamondEEEERightPairing.comp
          (scalarCoeffMap hn2 hn hb2 hc2 hd2)) := by
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro q
  rw [localScalarCross_point_formula hn2 hn hb2 hc2 hd2 s q]
  simp only [LinearMap.comp_apply]
  change
    diamondEEEECross
          (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s) q +
        cubeDot (cubeDiffJStar (bFreeLambda s.2.1.2)) q.1.1.1.2 +
        cubeDot (cubeDiffJStar (wFreeLambda s.2.2.1)) q.1.2.1.1 =
      EEEEInternal.diamondEEEERightPairing
        (((diamondEEEECoeffMap.comp
            ((DiamondEEEELeftSource n).subtype.comp
              (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2))) s) +
          scalarAddedCoeffMap s) q.1
  rw [map_add]
  have hdiamond :
      diamondEEEECross
          (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s) q =
        EEEEInternal.diamondEEEERightPairing
          (diamondEEEECoeffMap
            (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1) q.1 := by
    rfl
  rw [hdiamond]
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [scalarAddedCoeffMap_pairing]
  let D : F := EEEEInternal.diamondEEEERightPairing
    (diamondEEEECoeffMap
      (Scalar.scalarLeftCoordinate hn2 hn hb2 hc2 hd2 s).1) q.1
  let C1 : F := cubeDot
    (cubeDiffJStar (bFreeLambda s.2.1.2)) q.1.1.1.2
  let C2 : F := cubeDot
    (cubeDiffJStar (wFreeLambda s.2.2.1)) q.1.2.1.1
  simpa only [D, C1, C2] using (add_assoc D C1 C2)

noncomputable abbrev K4ScalarMultiplierAmbient
    (n : Nat) [NeZero n] :=
  K4BaseMixedScalarSector n ×
    ((CyclicCube n × CyclicCube n) ×
      (CyclicCube n × CyclicCube n))

private noncomputable def scalarCoefficientConstraintMap
    {n : Nat} [NeZero n] :
    (DiamondEEEERightAmbient n ×
      ((CyclicCube n × CyclicCube n) ×
        (CyclicCube n × CyclicCube n))) →ₗ[F]
      EEEEInternal.ConstraintAmbient n where
  toFun z :=
    let R := z.1
    let lambda00 := z.2.1.1
    let lambda01 := z.2.1.2
    let lambda10 := z.2.2.1
    let lambda11 := z.2.2.2
    fun q =>
      match q with
      | 0 => R.1.2.2
      | 1 => R.2.2.1
      | 2 => R.1.2.1
      | 3 => R.1.1.2 + cubeDiffJStar lambda01
      | 4 => cubeDiffRStar lambda01
      | 5 => R.2.1.1 + cubeDiffJStar lambda10
      | 6 => cubeDiffPStar lambda10
      | 7 => R.1.1.1 + cubeDiffJStar lambda00
      | 8 => cubeDiffJStar lambda11
      | 9 => cubeDiffPStar lambda11
      | 10 => cubeDiffRStar lambda11
  map_add' x y := by
    funext q
    fin_cases q <;> simp [DiamondEEEERightAmbient] <;> abel
  map_smul' r x := by
    funext q
    fin_cases q <;> simp [DiamondEEEERightAmbient]

private noncomputable def scalarMultiplierCoefficientPack
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierAmbient n →ₗ[F]
      (DiamondEEEERightAmbient n ×
        ((CyclicCube n × CyclicCube n) ×
          (CyclicCube n × CyclicCube n))) :=
  LinearMap.prod
    ((scalarCoeffMap hn2 hn hb2 hc2 hd2).comp
      (LinearMap.fst F _ _))
    (LinearMap.snd F _ _)

noncomputable def scalarMultiplierConstraintMap
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierAmbient n →ₗ[F]
      EEEEInternal.ConstraintAmbient n :=
  scalarCoefficientConstraintMap.comp
    (scalarMultiplierCoefficientPack hn2 hn hb2 hc2 hd2)

theorem scalarMultiplierConstraintMap_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierAmbient n) :
    scalarMultiplierConstraintMap hn2 hn hb2 hc2 hd2 z =
      let R := scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1
      let lambda00 := z.2.1.1
      let lambda01 := z.2.1.2
      let lambda10 := z.2.2.1
      let lambda11 := z.2.2.2
      fun q =>
        match q with
        | 0 => R.1.2.2
        | 1 => R.2.2.1
        | 2 => R.1.2.1
        | 3 => R.1.1.2 + cubeDiffJStar lambda01
        | 4 => cubeDiffRStar lambda01
        | 5 => R.2.1.1 + cubeDiffJStar lambda10
        | 6 => cubeDiffPStar lambda10
        | 7 => R.1.1.1 + cubeDiffJStar lambda00
        | 8 => cubeDiffJStar lambda11
        | 9 => cubeDiffPStar lambda11
        | 10 => cubeDiffRStar lambda11 := by
  rfl

noncomputable abbrev K4ScalarMultiplierSolution
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Submodule F (K4ScalarMultiplierAmbient n) :=
  LinearMap.ker
    (scalarMultiplierConstraintMap hn2 hn hb2 hc2 hd2)

theorem k4ScalarMultiplierSolution_mem_iff
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierAmbient n) :
    z ∈ K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 ↔
      scalarMultiplierConstraintMap hn2 hn hb2 hc2 hd2 z = 0 := by
  rfl

noncomputable def scalarMultiplierProjection
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4BaseMixedScalarSector n :=
  (LinearMap.fst F (K4BaseMixedScalarSector n)
    ((CyclicCube n × CyclicCube n) ×
      (CyclicCube n × CyclicCube n))).comp
    (K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2).subtype

theorem scalarMultiplierProjection_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2) :
    scalarMultiplierProjection hn2 hn hb2 hc2 hd2 z = z.1.1 := by
  rfl

noncomputable abbrev K4ScalarLeftKernel
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Submodule F (K4BaseMixedScalarSector n) :=
  LinearMap.ker (Scalar.localScalarCross hn2 hn hb2 hc2 hd2)

noncomputable abbrev K4ScalarMultiplierGauge
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Submodule F (K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2) :=
  LinearMap.ker
    (scalarMultiplierProjection hn2 hn hb2 hc2 hd2)

set_option maxHeartbeats 4000000 in
-- The reverse exactness proof constructs three finite-dual factorizations.
theorem range_scalarMultiplierProjection_eq_leftKernel
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.range
        (scalarMultiplierProjection hn2 hn hb2 hc2 hd2) =
      K4ScalarLeftKernel hn2 hn hb2 hc2 hd2 := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    change (Scalar.localScalarCross hn2 hn hb2 hc2 hd2 z.1.1) A = 0
    let R := scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1.1
    let lambda00 := z.1.2.1.1
    let lambda01 := z.1.2.1.2
    let lambda10 := z.1.2.2.1
    have hcon := LinearMap.mem_ker.mp z.2
    have h0 := congrFun hcon (0 : Fin 11)
    have h1 := congrFun hcon (1 : Fin 11)
    have h2 := congrFun hcon (2 : Fin 11)
    have h3 := congrFun hcon (3 : Fin 11)
    have h4 := congrFun hcon (4 : Fin 11)
    have h5 := congrFun hcon (5 : Fin 11)
    have h6 := congrFun hcon (6 : Fin 11)
    have h7 := congrFun hcon (7 : Fin 11)
    change R.1.2.2 = 0 at h0
    change R.2.2.1 = 0 at h1
    change R.1.2.1 = 0 at h2
    change R.1.1.2 + cubeDiffJStar lambda01 = 0 at h3
    change cubeDiffRStar lambda01 = 0 at h4
    change R.2.1.1 + cubeDiffJStar lambda10 = 0 at h5
    change cubeDiffPStar lambda10 = 0 at h6
    change R.1.1.1 + cubeDiffJStar lambda00 = 0 at h7
    have hR001 : R.1.1.2 = cubeDiffJStar lambda01 :=
      EEEEInternal.cube_eq_of_add_eq_zero h3
    have hR100 : R.2.1.1 = cubeDiffJStar lambda10 :=
      EEEEInternal.cube_eq_of_add_eq_zero h5
    have hR000 : R.1.1.1 = cubeDiffJStar lambda00 :=
      EEEEInternal.cube_eq_of_add_eq_zero h7
    rcases A.2.2.1 with ⟨X01, hX01⟩
    rcases A.2.2.2.1 with ⟨X10, hX10⟩
    have hpair000 :=
      EEEEInternal.pairing_zero_of_j
        R.1.1.1 lambda00 A.1.1.1.1 hR000 A.2.1
    have hpair001 :=
      EEEEInternal.pairing_zero_of_j_range_r
        R.1.1.2 lambda01 A.1.1.1.2 X01 hR001 h4 hX01.symm
    have hpair100 :=
      EEEEInternal.pairing_zero_of_j_range_p
        R.2.1.1 lambda10 A.1.2.1.1 X10 hR100 h6 hX10.symm
    have hpair :
        cubeDot R.1.1.1 A.1.1.1.1 + cubeDot R.1.1.2 A.1.1.1.2 +
          cubeDot R.1.2.1 A.1.1.2.1 + cubeDot R.1.2.2 A.1.1.2.2 +
          cubeDot R.2.1.1 A.1.2.1.1 + cubeDot R.2.1.2 A.1.2.1.2 +
          cubeDot R.2.2.1 A.1.2.2.1 + cubeDot R.2.2.2 A.1.2.2.2 = 0 := by
      rw [hpair000, hpair001, hpair100, h0, h1, h2]
      simp [R, scalarCoeffMap, scalarAddedCoeffMap,
        diamondEEEECoeffMap, cubeDot]
    have hrep :=
      LinearMap.congr_fun
        (LinearMap.congr_fun
          (localScalarCross_eq_restrict_pairing_coeffMap
            hn2 hn hb2 hc2 hd2) z.1.1) A
    rw [hrep]
    simpa [EEEEInternal.diamondEEEERestrictRightDual,
      EEEEInternal.diamondEEEERightPairing, R] using hpair
  · intro l hl
    let R := scalarCoeffMap hn2 hn hb2 hc2 hd2 l
    have hcross (A : DiamondEEEERightSource n) :
        cubeDot R.1.1.1 A.1.1.1.1 + cubeDot R.1.1.2 A.1.1.1.2 +
          cubeDot R.1.2.1 A.1.1.2.1 + cubeDot R.1.2.2 A.1.1.2.2 +
          cubeDot R.2.1.1 A.1.2.1.1 + cubeDot R.2.1.2 A.1.2.1.2 +
          cubeDot R.2.2.1 A.1.2.2.1 + cubeDot R.2.2.2 A.1.2.2.2 = 0 := by
      have hA := LinearMap.congr_fun (LinearMap.mem_ker.mp hl) A
      have hrep :=
        LinearMap.congr_fun
          (LinearMap.congr_fun
            (localScalarCross_eq_restrict_pairing_coeffMap
              hn2 hn hb2 hc2 hd2) l) A
      rw [hrep] at hA
      simpa [EEEEInternal.diamondEEEERestrictRightDual,
        EEEEInternal.diamondEEEERightPairing, R] using hA
    have hR010 : R.1.2.1 = 0 := by
      apply EEEEInternal.cubeDot_left_ext R.1.2.1 0
      intro A010
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (A010, 0)), ((0, 0), (0, 0))), by
          constructor
          · exact map_zero cubeDiffJInv
          constructor
          · exact (LinearMap.range (cubeDiffR (n := n))).zero_mem
          constructor
          · exact (LinearMap.range (cubeDiffP (n := n))).zero_mem
          · exact (LinearMap.range
              (LinearMap.coprod (cubeDiffP (n := n))
                (cubeDiffR (n := n)))).zero_mem⟩
      simpa [A, cubeDot] using hcross A
    have hR011 : R.1.2.2 = 0 := by
      apply EEEEInternal.cubeDot_left_ext R.1.2.2 0
      intro A011
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (0, A011)), ((0, 0), (0, 0))), by
          constructor
          · exact map_zero cubeDiffJInv
          constructor
          · exact (LinearMap.range (cubeDiffR (n := n))).zero_mem
          constructor
          · exact (LinearMap.range (cubeDiffP (n := n))).zero_mem
          · exact (LinearMap.range
              (LinearMap.coprod (cubeDiffP (n := n))
                (cubeDiffR (n := n)))).zero_mem⟩
      simpa [A, cubeDot] using hcross A
    have hR110 : R.2.2.1 = 0 := by
      apply EEEEInternal.cubeDot_left_ext R.2.2.1 0
      intro A110
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (0, 0)), ((0, 0), (A110, 0))), by
          constructor
          · exact map_zero cubeDiffJInv
          constructor
          · exact (LinearMap.range (cubeDiffR (n := n))).zero_mem
          constructor
          · exact (LinearMap.range (cubeDiffP (n := n))).zero_mem
          · exact (LinearMap.range
              (LinearMap.coprod (cubeDiffP (n := n))
                (cubeDiffR (n := n)))).zero_mem⟩
      simpa [A, cubeDot] using hcross A
    have hvanish000 (A000 : CyclicCube n)
        (hA000 : cubeDiffJInv A000 = 0) :
        EEEEInternal.cubeDotDual R.1.1.1 A000 = 0 := by
      let A : DiamondEEEERightSource n :=
        ⟨(((A000, 0), (0, 0)), ((0, 0), (0, 0))), by
          constructor
          · exact hA000
          simp⟩
      simpa [A, hR010, hR011, hR110,
        EEEEInternal.cubeDotDual, cubeDot] using hcross A
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        (U := CyclicCube n) cubeDiffJInv
        (0 : CyclicCube n →ₗ[F] CyclicCube n)
        (EEEEInternal.cubeDotDual R.1.1.1)
        (fun A000 hmem => hvanish000 A000 (by simpa using hmem)) with
      ⟨psi00, hfactor00, _⟩
    rcases EEEEInternal.dual_exists_cubeDot psi00 with
      ⟨lambda00, hpsi00⟩
    have hR000 : R.1.1.1 = cubeDiffJStar lambda00 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A000
      calc
        cubeDot R.1.1.1 A000 = psi00 (cubeDiffJInv A000) :=
          LinearMap.congr_fun hfactor00 A000
        _ = cubeDot lambda00 (cubeDiffJInv A000) := hpsi00 _
        _ = cubeDot (cubeDiffJStar lambda00) A000 :=
          (cubeDiffJ_pairing_adjoint lambda00 A000).symm
    have hvanish001 (A001 : CyclicCube n)
        (hA001 : cubeDiffJInv A001 ∈
          LinearMap.range (cubeDiffR (n := n))) :
        EEEEInternal.cubeDotDual R.1.1.2 A001 = 0 := by
      let A : DiamondEEEERightSource n :=
        ⟨(((0, A001), (0, 0)), ((0, 0), (0, 0))), by
          constructor
          · simp
          constructor
          · exact hA001
          simp⟩
      simpa [A, hR010, hR011, hR110,
        EEEEInternal.cubeDotDual, cubeDot] using hcross A
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv cubeDiffR
        (EEEEInternal.cubeDotDual R.1.1.2) hvanish001 with
      ⟨psi01, hfactor01, hann01⟩
    rcases EEEEInternal.dual_exists_cubeDot psi01 with
      ⟨lambda01, hpsi01⟩
    have hR001 : R.1.1.2 = cubeDiffJStar lambda01 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A001
      calc
        cubeDot R.1.1.2 A001 = psi01 (cubeDiffJInv A001) :=
          LinearMap.congr_fun hfactor01 A001
        _ = cubeDot lambda01 (cubeDiffJInv A001) := hpsi01 _
        _ = cubeDot (cubeDiffJStar lambda01) A001 :=
          (cubeDiffJ_pairing_adjoint lambda01 A001).symm
    have hr01 : cubeDiffRStar lambda01 = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffRStar lambda01) X =
            cubeDot lambda01 (cubeDiffR X) :=
          cubeDiffR_pairing_adjoint lambda01 X
        _ = psi01 (cubeDiffR X) := (hpsi01 _).symm
        _ = 0 := hann01 X
        _ = cubeDot 0 X := by simp [cubeDot]
    have hvanish100 (A100 : CyclicCube n)
        (hA100 : cubeDiffJInv A100 ∈
          LinearMap.range (cubeDiffP (n := n))) :
        EEEEInternal.cubeDotDual R.2.1.1 A100 = 0 := by
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (0, 0)), ((A100, 0), (0, 0))), by
          constructor
          · simp
          constructor
          · simp
          constructor
          · exact hA100
          simp⟩
      simpa [A, hR010, hR011, hR110,
        EEEEInternal.cubeDotDual, cubeDot] using hcross A
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv cubeDiffP
        (EEEEInternal.cubeDotDual R.2.1.1) hvanish100 with
      ⟨psi10, hfactor10, hann10⟩
    rcases EEEEInternal.dual_exists_cubeDot psi10 with
      ⟨lambda10, hpsi10⟩
    have hR100 : R.2.1.1 = cubeDiffJStar lambda10 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A100
      calc
        cubeDot R.2.1.1 A100 = psi10 (cubeDiffJInv A100) :=
          LinearMap.congr_fun hfactor10 A100
        _ = cubeDot lambda10 (cubeDiffJInv A100) := hpsi10 _
        _ = cubeDot (cubeDiffJStar lambda10) A100 :=
          (cubeDiffJ_pairing_adjoint lambda10 A100).symm
    have hp10 : cubeDiffPStar lambda10 = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffPStar lambda10) X =
            cubeDot lambda10 (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda10 X
        _ = psi10 (cubeDiffP X) := (hpsi10 _).symm
        _ = 0 := hann10 X
        _ = cubeDot 0 X := by simp [cubeDot]
    let z0 : K4ScalarMultiplierAmbient n :=
      (l, ((lambda00, lambda01), (lambda10, 0)))
    have hz0 : scalarMultiplierConstraintMap hn2 hn hb2 hc2 hd2 z0 = 0 := by
      funext q
      fin_cases q <;>
        simp [scalarMultiplierConstraintMap,
          scalarMultiplierCoefficientPack,
          scalarCoefficientConstraintMap, z0, R,
          hR011, hR110, hR010, hR001, hr01, hR100, hp10,
          hR000, EEEEInternal.cube_add_self]
    exact ⟨⟨z0, hz0⟩, rfl⟩


theorem ker_scalarMultiplierProjection_eq_gauge
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.ker
        (scalarMultiplierProjection hn2 hn hb2 hc2 hd2) =
      K4ScalarMultiplierGauge hn2 hn hb2 hc2 hd2 := rfl


end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
