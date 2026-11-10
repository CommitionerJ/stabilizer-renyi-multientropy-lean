import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.Build

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

private theorem f2_add_cancel_sandwich
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    (x + y) + x = y := by
  calc
    (x + y) + x = y + (x + x) := by abel
    _ = y + 0 := by rw [module_add_self]
    _ = y := add_zero y

set_option maxHeartbeats 8000000 in
-- The explicit aggregate source wrapper normalizes a nested kernel subtype.
theorem aggregateBuild_sandwich_read
    {n : Nat} [NeZero n] (q : K4AggregateEEEEScalarKernel n)
    (xB xW : CyclicCube n) :
    aggregateBuild
      (linkedRead q,
        (((xB + b11Read q) + xB),
          ((xW + w11Read q) + xW))) = q := by
  rw [f2_add_cancel_sandwich, f2_add_cancel_sandwich]
  exact aggregateBuild_read q

set_option maxHeartbeats 8000000 in
-- Reading and rebuilding restores the aggregate and both polar heads.
theorem faithfulFactorsToMultiplier_left_inv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2) :
    faithfulFactorsToMultiplier hn2 hn hb2 hc2 hd2
        (multiplierToFaithfulFactors hn2 hn hb2 hc2 hd2 z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · change
        aggregateBuild
          (linkedRead z.1.1.1,
            ((z.1.1.2.1.2.1 + b11Read z.1.1.1) +
                z.1.1.2.1.2.1,
              (z.1.1.2.2.1.1 + w11Read z.1.1.1) +
                z.1.1.2.2.1.1)) = z.1.1.1
      exact aggregateBuild_sandwich_read z.1.1.1
        z.1.1.2.1.2.1 z.1.1.2.2.1.1
    · rfl
  · rfl

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

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

private theorem f2_add_cancel_sandwich_right
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    x + (y + x) = y := by
  calc
    x + (y + x) = y + (x + x) := by abel
    _ = y + 0 := by rw [module_add_self]
    _ = y := add_zero y

set_option maxHeartbeats 8000000 in
-- The seven nested factor fields are compared without reopening memberships.
theorem multiplierToFaithfulFactors_right_inv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (q : K4ScalarFaithfulSevenFactors hn2 hn hb2 hc2 hd2) :
    multiplierToFaithfulFactors hn2 hn hb2 hc2 hd2
        (faithfulFactorsToMultiplier hn2 hn hb2 hc2 hd2 q) = q := by
  let baseB := q.1.1.1.1.1.1
  let baseW := q.1.1.1.1.1.2
  let linkedFactor := q.1.1.1.1.2
  let transportedR := q.1.1.1.2
  let transportedP := q.1.1.2
  let star := q.1.2
  let PB := baseB.1
  let PW := baseW.1
  let BFree := transportedR.1.1
  let lambda01 := transportedR.1.2
  let WFree := transportedP.1.1
  let lambda10 := transportedP.1.2
  let U := star.1.1.1
  let V := star.1.1.2
  let B11 := U + BFree.1
  let W11 := V + WFree.1
  have hLinkedFactor := LinearMap.mem_ker.mp linkedFactor.2
  have hLinkedPR :
      LinearMap.coprod (cubeDiffP (n := n)) (cubeDiffR (n := n))
          linkedFactor.1 = 0 :=
    congrArg Prod.fst hLinkedFactor
  let linkedSource : LinkedSource n :=
    ⟨linkedFactor.1, LinearMap.mem_ker.mpr hLinkedPR⟩
  let coordinates : K4ScalarAggregateCoordinates n :=
    (linkedSource, (B11, W11))
  let aggregate := aggregateBuild coordinates
  have hCoordinates := aggregateCoordinatesRead_build coordinates
  have hLinkedRead : linkedRead aggregate = linkedSource :=
    congrArg Prod.fst hCoordinates
  have hB11Read : b11Read aggregate = B11 :=
    congrArg (fun x => x.2.1) hCoordinates
  have hW11Read : w11Read aggregate = W11 :=
    congrArg (fun x => x.2.2) hCoordinates
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Prod.ext
            · apply Subtype.ext
              change PB = baseB.1
              rfl
            · apply Subtype.ext
              change PW = baseW.1
              rfl
          · apply Subtype.ext
            change (linkedRead aggregate).1 = linkedFactor.1
            rw [hLinkedRead]
        · apply Subtype.ext
          change (BFree, lambda01) = transportedR.1
          rfl
      · apply Subtype.ext
        change (WFree, lambda10) = transportedP.1
        rfl
    · apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · change BFree.1 + b11Read aggregate = U
          rw [hB11Read]
          dsimp only [B11]
          exact f2_add_cancel_sandwich_right BFree.1 U
        · change WFree.1 + w11Read aggregate = V
          rw [hW11Read]
          dsimp only [W11]
          exact f2_add_cancel_sandwich_right WFree.1 V
      · rfl
  · apply Subtype.ext
    rfl

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
