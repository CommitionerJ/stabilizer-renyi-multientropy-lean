import Core4loop.CompleteGraph.EvenAllLarge.DescSplitPhase

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY

open Core4loop
open Core4loop.SquareDiagonal.EvenP

noncomputable section

theorem diamondCross_eq_of_coordinates
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b c d)
    (A : DiamondEvenPReachableA n b c d)
    (l' : TotalEEEELeftSourceTarget n b c d)
    (q' : TotalEEEERightReachableTarget n b c d)
    (t : F)
    (hl : diamondEvenPLeftEEEEEquiv hn hb2 hc2 hd2 l = l')
    (hA : diamondEvenPReachableAEEEEEquiv hn hb2 hc2 hd2 A = q')
    (ht : TotalEEEEPhase.totalEEEECoordinatePhase l' q' = t) :
    diamondEvenPCross l A = t := by
  have hPhase :=
    @TotalEEEEPhase.totalEEEELiteralPhaseCoordinateSplit
      n b c d _ hn hb2 hc2 hd2 l A
  have hCoordinates := congrArg₂
    (fun l'' q'' => TotalEEEEPhase.totalEEEECoordinatePhase l'' q'')
    hl hA
  exact hPhase.trans (hCoordinates.trans ht)

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.PassiveY
