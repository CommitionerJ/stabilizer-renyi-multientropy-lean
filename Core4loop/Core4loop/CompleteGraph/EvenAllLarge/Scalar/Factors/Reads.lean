import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.ReadsCore

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

noncomputable def scalarSectorSolutionRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4BaseMixedScalarSector n where
  toFun z := z.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def lambda00SolutionRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      CyclicCube n where
  toFun z := z.1.2.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def starCandidateRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      ((CyclicCube n × CyclicCube n) × CyclicCube n) :=
  LinearMap.prod
    (scalarStarRead.comp
      (scalarSectorSolutionRead hn2 hn hb2 hc2 hd2))
    (lambda00SolutionRead hn2 hn hb2 hc2 hd2)

theorem starCandidateRead_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2) :
    starCandidateRead hn2 hn hb2 hc2 hd2 z =
      ((z.1.1.2.1.2.1 + b11Read z.1.1.1,
        z.1.1.2.2.1.1 + w11Read z.1.1.1),
        z.1.2.1.1) := rfl

set_option maxHeartbeats 8000000 in
-- The nested multiplier solution subtype is normalized only in this owner.
noncomputable def starFactorRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      StarFactor n :=
  LinearMap.codRestrict (StarFactor n)
    (starCandidateRead hn2 hn hb2 hc2 hd2)
    (fun z => by
      apply LinearMap.mem_ker.mpr
      rw [starCandidateRead_apply]
      change
        cubeDiffI (z.1.1.2.1.2.1 + b11Read z.1.1.1) +
            cubeDiffK (z.1.1.2.2.1.1 + w11Read z.1.1.1) +
          cubeDiffJStar z.1.2.1.1 = 0
      let s := z.1.1
      let lambda00 := z.1.2.1.1
      have hm := LinearMap.mem_ker.mp z.2
      have h0 := congrFun hm (0 : Fin 11)
      have h1 := congrFun hm (1 : Fin 11)
      have h2 := congrFun hm (2 : Fin 11)
      have h7 := congrFun hm (7 : Fin 11)
      change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 = 0 at h0
      change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.2.1 = 0 at h1
      change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.1 = 0 at h2
      change
        (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.1 +
          cubeDiffJStar lambda00 = 0 at h7
      rw [row011_normal_form] at h0
      rw [row110_normal_form] at h1
      rw [row010_normal_form] at h2
      rw [row000_normal_form] at h7
      simp only [row000CanonicalMap, LinearMap.add_apply,
        LinearMap.comp_apply, scalarPBRead, scalarAggregateRead,
        LinearMap.coe_mk, AddHom.coe_mk] at h7
      let linked := linkedRead s.1
      have hLinkedRow :
          linkedRow hn2 hn hb2 hc2 hd2 linked = 0 := by
        simpa only [h0, h1, zero_add] using h2
      rw [starRow_normalized] at h7
      rw [scalarStarRead_fst_apply, scalarStarRead_snd_apply] at h7
      rw [h0, hLinkedRow, zero_add] at h7
      simpa only [zero_add] using h7)

noncomputable def lambda11FactorRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      Lambda11Factor n where
  toFun z := ⟨z.1.2.2.2, by
    apply LinearMap.mem_ker.mpr
    have hm := LinearMap.mem_ker.mp z.2
    have h8 := congrFun hm (8 : Fin 11)
    have h9 := congrFun hm (9 : Fin 11)
    have h10 := congrFun hm (10 : Fin 11)
    change cubeDiffJStar z.1.2.2.2 = 0 at h8
    change cubeDiffPStar z.1.2.2.2 = 0 at h9
    change cubeDiffRStar z.1.2.2.2 = 0 at h10
    exact Prod.ext (Prod.ext h8 h9) h10⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def multiplierToFaithfulFactors
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4ScalarFaithfulSevenFactors hn2 hn hb2 hc2 hd2 :=
  LinearMap.prod
    (LinearMap.prod
      (LinearMap.prod
        (LinearMap.prod
          (LinearMap.prod
            (LinearMap.prod
              (baseBFactorRead hn2 hn hb2 hc2 hd2)
              (baseWFactorRead hn2 hn hb2 hc2 hd2))
            (linkedFactorRead hn2 hn hb2 hc2 hd2))
          (transportedRFactorRead hn2 hn hb2 hc2 hd2))
        (transportedPFactorRead hn2 hn hb2 hc2 hd2))
      (starFactorRead hn2 hn hb2 hc2 hd2))
    (lambda11FactorRead hn2 hn hb2 hc2 hd2)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
