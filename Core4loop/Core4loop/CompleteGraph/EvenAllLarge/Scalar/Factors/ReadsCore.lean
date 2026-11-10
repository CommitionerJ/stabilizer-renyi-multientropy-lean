import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.Carriers

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

noncomputable def aggregateCoordinatesRead
    {n : Nat} [NeZero n] :
    K4AggregateEEEEScalarKernel n →ₗ[F]
      K4ScalarAggregateCoordinates n :=
  LinearMap.prod linkedRead (LinearMap.prod b11Read w11Read)

@[simp] theorem aggregateCoordinatesRead_build
    {n : Nat} [NeZero n] (x : K4ScalarAggregateCoordinates n) :
    aggregateCoordinatesRead (aggregateBuild x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · rfl

@[simp] theorem aggregateBuild_read
    {n : Nat} [NeZero n] (q : K4AggregateEEEEScalarKernel n) :
    aggregateBuild (aggregateCoordinatesRead q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · have h := congrArg (fun x => x.1.1)
          (LinearMap.mem_ker.mp q.2)
        have hv := congrArg Subtype.val h
        change q.1.1.1.1.1 = 0 at hv
        exact hv.symm
      · rfl
    · apply Prod.ext
      · have h := congrArg (fun x => x.1.2)
          (LinearMap.mem_ker.mp q.2)
        change q.1.1.1.2.1 = 0 at h
        exact h.symm
      · rfl
  · apply Prod.ext
    · apply Prod.ext
      · have h := congrArg (fun x => x.2.2)
          (LinearMap.mem_ker.mp q.2)
        have hv := congrArg Subtype.val h
        change q.1.1.2.1.1 = 0 at hv
        exact hv.symm
      · have hsum := congrArg (fun x => x.2.1)
          (LinearMap.mem_ker.mp q.2)
        have hzero := congrArg (fun x => x.2.2)
          (LinearMap.mem_ker.mp q.2)
        have hzeroVal := congrArg Subtype.val hzero
        change q.1.1.2.1.1 = 0 at hzeroVal
        change q.1.1.2.1.1 + q.1.1.2.1.2 = 0 at hsum
        rw [hzeroVal, zero_add] at hsum
        exact hsum.symm
    · rfl

noncomputable def aggregateCoordinatesEquiv
    {n : Nat} [NeZero n] :
    K4AggregateEEEEScalarKernel n ≃ₗ[F]
      K4ScalarAggregateCoordinates n where
  toLinearMap := aggregateCoordinatesRead
  invFun := aggregateBuild
  left_inv := aggregateBuild_read
  right_inv := aggregateCoordinatesRead_build


noncomputable def baseBFactorRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 where
  toFun z := ⟨z.1.1.2.1.1, by
    apply LinearMap.mem_ker.mpr
    have h := congrFun (LinearMap.mem_ker.mp z.2) (0 : Fin 11)
    change
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1.1).1.2.2 = 0 at h
    rw [row011_normal_form] at h
    exact h⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def baseWFactorRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2 where
  toFun z := ⟨z.1.1.2.2.2, by
    apply LinearMap.mem_ker.mpr
    have h := congrFun (LinearMap.mem_ker.mp z.2) (1 : Fin 11)
    change
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 z.1.1).2.2.1 = 0 at h
    rw [row110_normal_form] at h
    exact h⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def linkedFactorRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      CubePairPRDISolution n where
  toFun z := by
    let s := z.1.1
    let linked := linkedRead s.1
    have hm := LinearMap.mem_ker.mp z.2
    have h0 := congrFun hm (0 : Fin 11)
    have h1 := congrFun hm (1 : Fin 11)
    have h2 := congrFun hm (2 : Fin 11)
    change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 = 0 at h0
    change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.2.1 = 0 at h1
    change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.1 = 0 at h2
    rw [row011_normal_form] at h0
    rw [row110_normal_form] at h1
    rw [row010_normal_form] at h2
    have hLinkedRow :
        linkedRow hn2 hn hb2 hc2 hd2 linked = 0 := by
      simpa only [h0, h1, zero_add] using h2
    have hLinkedDI :
        cubeDiffI linked.1.1 + cubeDiffK linked.1.2 = 0 := by
      rw [linkedRow_normalized] at hLinkedRow
      exact hLinkedRow
    refine ⟨linked.1, ?_⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · exact LinearMap.mem_ker.mp linked.2
    · exact hLinkedDI
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def transportedRFactorRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2 where
  toFun z := by
    let s := z.1.1
    let lambda01 := z.1.2.1.2
    have hm := LinearMap.mem_ker.mp z.2
    have h0 := congrFun hm (0 : Fin 11)
    have h3 := congrFun hm (3 : Fin 11)
    have h4 := congrFun hm (4 : Fin 11)
    change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 = 0 at h0
    change
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.2 +
        cubeDiffJStar lambda01 = 0 at h3
    change cubeDiffRStar lambda01 = 0 at h4
    rw [row011_normal_form] at h0
    rw [row001_normal_form] at h3
    have hR :
        transportedBRow hn2 hn hb2 hc2 hd2 s.2.1.2 +
          cubeDiffJStar lambda01 = 0 := by
      simpa only [h0, zero_add] using h3
    refine ⟨(s.2.1.2, lambda01), ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [transportedRMap_apply]
    exact Prod.ext hR h4
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def transportedPFactorRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2 where
  toFun z := by
    let s := z.1.1
    let lambda10 := z.1.2.2.1
    have hm := LinearMap.mem_ker.mp z.2
    have h5 := congrFun hm (5 : Fin 11)
    have h6 := congrFun hm (6 : Fin 11)
    change
      (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.1.1 +
        cubeDiffJStar lambda10 = 0 at h5
    change cubeDiffPStar lambda10 = 0 at h6
    rw [row100_normal_form] at h5
    refine ⟨(s.2.2.1, lambda10), ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [transportedPMap_apply]
    exact Prod.ext h5 h6
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
