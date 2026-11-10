import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.InverseLaws

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

-- The literal eleven-row multiplier solution is exactly the faithful
-- seven-factor carrier; no rank or final evaluator is used here.
noncomputable def k4ScalarMultiplierFaithfulSevenFactorsEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4ScalarMultiplierSolution hn2 hn hb2 hc2 hd2 ≃ₗ[F]
      K4ScalarFaithfulSevenFactors hn2 hn hb2 hc2 hd2 where
  toLinearMap := multiplierToFaithfulFactors hn2 hn hb2 hc2 hd2
  invFun := faithfulFactorsToMultiplier hn2 hn hb2 hc2 hd2
  left_inv := faithfulFactorsToMultiplier_left_inv hn2 hn hb2 hc2 hd2
  right_inv := multiplierToFaithfulFactors_right_inv hn2 hn hb2 hc2 hd2

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
