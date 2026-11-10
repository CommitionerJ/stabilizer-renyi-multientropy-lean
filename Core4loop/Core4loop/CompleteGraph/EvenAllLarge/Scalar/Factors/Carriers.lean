import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.RowNormalForms
import Core4loop.SquareDiagonal.EvenP.EEEE.Factors

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

noncomputable abbrev K4ScalarBaseBFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :=
  LinearMap.ker (baseBRow hn2 hn hb2 hc2 hd2)

noncomputable abbrev K4ScalarBaseWFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :=
  LinearMap.ker (baseWRow hn2 hn hb2 hc2 hd2)

noncomputable def transportedRMap
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    (K4BFreeHeadRadical n × CyclicCube n) →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  let left := LinearMap.fst F (K4BFreeHeadRadical n) (CyclicCube n)
  let right := LinearMap.snd F (K4BFreeHeadRadical n) (CyclicCube n)
  LinearMap.prod
    ((transportedBRow hn2 hn hb2 hc2 hd2).comp left +
      cubeDiffJStar.comp right)
    (cubeDiffRStar.comp right)

noncomputable def transportedPMap
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    (K4WFreeHeadRadical n × CyclicCube n) →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  let left := LinearMap.fst F (K4WFreeHeadRadical n) (CyclicCube n)
  let right := LinearMap.snd F (K4WFreeHeadRadical n) (CyclicCube n)
  LinearMap.prod
    ((transportedWRow hn2 hn hb2 hc2 hd2).comp left +
      cubeDiffJStar.comp right)
    (cubeDiffPStar.comp right)

theorem transportedRMap_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BFreeHeadRadical n × CyclicCube n) :
    transportedRMap hn2 hn hb2 hc2 hd2 x =
      (transportedBRow hn2 hn hb2 hc2 hd2 x.1 +
          cubeDiffJStar x.2,
        cubeDiffRStar x.2) := rfl

theorem transportedPMap_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4WFreeHeadRadical n × CyclicCube n) :
    transportedPMap hn2 hn hb2 hc2 hd2 x =
      (transportedWRow hn2 hn hb2 hc2 hd2 x.1 +
          cubeDiffJStar x.2,
        cubeDiffPStar x.2) := rfl

noncomputable abbrev K4ScalarTransportedRFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :=
  LinearMap.ker (transportedRMap hn2 hn hb2 hc2 hd2)

noncomputable abbrev K4ScalarTransportedPFactor
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :=
  LinearMap.ker (transportedPMap hn2 hn hb2 hc2 hd2)

noncomputable abbrev K4ScalarFaithfulSevenFactors
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :=
  ((((((K4ScalarBaseBFactor hn2 hn hb2 hc2 hd2 ×
            K4ScalarBaseWFactor hn2 hn hb2 hc2 hd2) ×
          CubePairPRDISolution n) ×
        K4ScalarTransportedRFactor hn2 hn hb2 hc2 hd2) ×
      K4ScalarTransportedPFactor hn2 hn hb2 hc2 hd2) ×
    StarFactor n) × Lambda11Factor n)

noncomputable abbrev K4ScalarAggregateCoordinates
    (n : Nat) [NeZero n] :=
  LinkedSource n × (CyclicCube n × CyclicCube n)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
