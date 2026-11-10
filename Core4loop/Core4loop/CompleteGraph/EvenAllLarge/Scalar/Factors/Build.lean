import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.Reads

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

set_option maxHeartbeats 8000000 in
-- The inverse reconstructs the nested scalar source and all eleven rows.
noncomputable def faithfulFactorsToMultiplier
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarFaithfulSevenFactors hn2 hn hb2 hc2 hd2 →ₗ[F]
      K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 where
  toFun q := by
    let baseB := q.1.1.1.1.1.1
    let baseW := q.1.1.1.1.1.2
    let linkedFactor := q.1.1.1.1.2
    let transportedR := q.1.1.1.2
    let transportedP := q.1.1.2
    let star := q.1.2
    let lambdaFactor := q.2
    let PB := baseB.1
    let PW := baseW.1
    let BFree := transportedR.1.1
    let lambda01 := transportedR.1.2
    let WFree := transportedP.1.1
    let lambda10 := transportedP.1.2
    let U := star.1.1.1
    let V := star.1.1.2
    let lambda00 := star.1.2
    let lambda11 := lambdaFactor.1
    let B11 := U + BFree.1
    let W11 := V + WFree.1
    have hLinkedFactor := LinearMap.mem_ker.mp linkedFactor.2
    have hLinkedPR :
        LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n))
            linkedFactor.1 = 0 :=
      congrArg Prod.fst hLinkedFactor
    have hLinkedDI :
        cubeDiffI linkedFactor.1.1 +
          cubeDiffK linkedFactor.1.2 = 0 := by
      exact congrArg Prod.snd hLinkedFactor
    let linkedSource : LinkedSource n :=
      ⟨linkedFactor.1, LinearMap.mem_ker.mpr hLinkedPR⟩
    let coordinates : K4ScalarAggregateCoordinates n :=
      (linkedSource, (B11, W11))
    let aggregate := aggregateBuild coordinates
    let s : K4BaseMixedScalarSector n :=
      (aggregate, ((PB, BFree), (WFree, PW)))
    have hCoordinates := aggregateCoordinatesRead_build coordinates
    have hLinkedRead : linkedRead aggregate = linkedSource :=
      congrArg Prod.fst hCoordinates
    have hB11Read : b11Read aggregate = B11 :=
      congrArg (fun x => x.2.1) hCoordinates
    have hW11Read : w11Read aggregate = W11 :=
      congrArg (fun x => x.2.2) hCoordinates
    have hBaseB := LinearMap.mem_ker.mp baseB.2
    have hBaseW := LinearMap.mem_ker.mp baseW.2
    have hR := LinearMap.mem_ker.mp transportedR.2
    have hP := LinearMap.mem_ker.mp transportedP.2
    have hStar := LinearMap.mem_ker.mp star.2
    have hLambda := LinearMap.mem_ker.mp lambdaFactor.2
    have hR0 :
        transportedBRow hn2 hn hb2 hc2 hd2 BFree +
          cubeDiffJStar lambda01 = 0 := by
      exact congrArg Prod.fst hR
    have hR1 : cubeDiffRStar lambda01 = 0 := by
      exact congrArg Prod.snd hR
    have hP0 :
        transportedWRow hn2 hn hb2 hc2 hd2 WFree +
          cubeDiffJStar lambda10 = 0 := by
      exact congrArg Prod.fst hP
    have hP1 : cubeDiffPStar lambda10 = 0 := by
      exact congrArg Prod.snd hP
    have hStar0 :
        cubeDiffI U + cubeDiffK V +
          cubeDiffJStar lambda00 = 0 := by
      change
        cubeDiffI U + cubeDiffK V +
          cubeDiffJStar lambda00 = 0 at hStar
      exact hStar
    have hLambdaJ : cubeDiffJStar lambda11 = 0 := by
      exact congrArg (fun x => x.1.1) hLambda
    have hLambdaP : cubeDiffPStar lambda11 = 0 := by
      exact congrArg (fun x => x.1.2) hLambda
    have hLambdaR : cubeDiffRStar lambda11 = 0 := by
      exact congrArg Prod.snd hLambda
    have hLinkedRow :
        linkedRow hn2 hn hb2 hc2 hd2 (linkedRead aggregate) = 0 := by
      rw [hLinkedRead, linkedRow_normalized]
      exact hLinkedDI
    have hU : (scalarStarRead s).1 = U := by
      rw [scalarStarRead_fst_apply]
      change BFree.1 + b11Read aggregate = U
      rw [hB11Read]
      dsimp only [B11]
      calc
        BFree.1 + (U + BFree.1) = U + (BFree.1 + BFree.1) := by
          abel
        _ = U + 0 := by rw [module_add_self]
        _ = U := add_zero U
    have hV : (scalarStarRead s).2 = V := by
      rw [scalarStarRead_snd_apply]
      change WFree.1 + w11Read aggregate = V
      rw [hW11Read]
      dsimp only [W11]
      calc
        WFree.1 + (V + WFree.1) = V + (WFree.1 + WFree.1) := by
          abel
        _ = V + 0 := by rw [module_add_self]
        _ = V := add_zero V
    refine ⟨(s, ((lambda00, lambda01), (lambda10, lambda11))), ?_⟩
    apply LinearMap.mem_ker.mpr
    funext idx
    fin_cases idx
    · change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.2 = 0
      rw [row011_normal_form]
      exact hBaseB
    · change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.2.1 = 0
      rw [row110_normal_form]
      exact hBaseW
    · change (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.2.1 = 0
      rw [row010_normal_form]
      rw [hBaseB, hBaseW, zero_add, hLinkedRow]
      rfl
    · change
        (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.2 +
          cubeDiffJStar lambda01 = 0
      rw [row001_normal_form]
      rw [hBaseB, zero_add]
      exact hR0
    · change cubeDiffRStar lambda01 = 0
      exact hR1
    · change
        (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).2.1.1 +
          cubeDiffJStar lambda10 = 0
      rw [row100_normal_form]
      exact hP0
    · change cubeDiffPStar lambda10 = 0
      exact hP1
    · change
        (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.1 +
          cubeDiffJStar lambda00 = 0
      rw [row000_normal_form]
      simp only [row000CanonicalMap, LinearMap.add_apply,
        LinearMap.comp_apply, scalarPBRead, scalarAggregateRead,
        LinearMap.coe_mk, AddHom.coe_mk]
      rw [hBaseB, hLinkedRow, zero_add, starRow_normalized, hU, hV]
      simpa only [zero_add] using hStar0
    · change cubeDiffJStar lambda11 = 0
      exact hLambdaJ
    · change cubeDiffPStar lambda11 = 0
      exact hLambdaP
    · change cubeDiffRStar lambda11 = 0
      exact hLambdaR
  map_add' q r := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        ext <;> simp [aggregateBuild]
        all_goals abel
      · rfl
    · rfl
  map_smul' r q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        apply Subtype.ext
        ext <;> simp [aggregateBuild, smul_add]
      · rfl
    · rfl

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
