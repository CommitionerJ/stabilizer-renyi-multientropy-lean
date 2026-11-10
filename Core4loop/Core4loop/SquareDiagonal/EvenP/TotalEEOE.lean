import Core4loop.SquareDiagonal.EvenP.TotalEEOE.Rank

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

set_option synthInstance.maxHeartbeats 12000000 in
-- The nested restricted left source needs the compiled P0 instance budget.
/-- Literal EEOE left-source coordinates in the frozen
`scalar × (Y × (W × mixed))` association. -/
noncomputable def diamondEvenPLeftEEOEEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    DiamondEvenPLeft n b 1 d ≃ₗ[F]
      T37LeftP0.T37LeftSourceTarget n b d :=
  T37LeftP0.t37LeftSourceEquiv
    (n := n) (b := b) (d := d) hn hb2 hd2

set_option synthInstance.maxHeartbeats 12000000 in
-- The nested reachable right source needs the compiled P1 instance budget.
/-- Literal reachable EEOE right-source coordinates.  The first-coordinate
`J`-kernel tails remain distinct from the second-coordinate typed tails. -/
noncomputable def diamondEvenPReachableAEEOEEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n b 1 d ≃ₗ[F]
      T37RightP1.T37RightReachableTarget n b d :=
  T37RightP1.t37RightReachableEquiv
    (n := n) (b := b) (d := d) hn hb2 hd2

set_option maxHeartbeats 12000000 in
-- The frozen four-block map has a deeply nested restricted dual.
set_option synthInstance.maxHeartbeats 12000000 in
/-- The typed EEOE cross, associated addition-first as
`scalar + (Y + (W + mixed))`. -/
noncomputable def diamondEEOETotalBlockCross
    {n b d : Nat} [NeZero n] :
    T37LeftP0.T37LeftSourceTarget n b d →ₗ[F]
      Module.Dual F
        (T37RightP1.T37RightReachableTarget n b d) :=
  T37TypedBlockP2.t37TotalBlockCross
    (n := n) (b := b) (d := d)

set_option maxHeartbeats 12000000 in
-- The pointwise square elaborates both frozen coordinate equivalences.
set_option synthInstance.maxHeartbeats 12000000 in
/-- The literal EEOE phase equals the typed four-block phase pointwise.
No rank identity is used in this theorem. -/
theorem diamondEvenPCross_EEOE_phase
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    diamondEEOETotalBlockCross
        (diamondEvenPLeftEEOEEquiv hn hb2 hd2 l)
        (diamondEvenPReachableAEEOEEquiv hn hb2 hd2 A) =
      diamondEvenPCross l A :=
  T37TypedBlockP2.t37PointwisePhaseSquare
    (n := n) (b := b) (d := d) hn hb2 hd2 l A

set_option maxHeartbeats 12000000 in
-- The range transport uses both nested restricted-source equivalences.
set_option synthInstance.maxHeartbeats 12000000 in
/-- Range transport from the literal EEOE cross to the frozen typed cross,
oriented from the literal range to the typed range. -/
noncomputable def diamondEvenPCross_EEOE_rangeEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := b) (c := 1) (d := d)) ≃ₗ[F]
      LinearMap.range
        (diamondEEOETotalBlockCross
          (n := n) (b := b) (d := d)) :=
  T37RangeRankP3.t37RangeTransport
    (n := n) (b := b) (d := d) hn hb2 hd2

set_option maxHeartbeats 12000000 in
-- The final literal rank is transported through the compiled P3 certificate.
set_option synthInstance.maxHeartbeats 12000000 in
/-- Exact all-`n` rank of the literal EEOE cross for positive
non-singleton B and W blocks. -/
theorem rank_diamondEvenPCross_EEOE
    {n b d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := 1) (d := d))) =
      2 * (n - 1) ^ 2 :=
  T37RangeRankP3.t37LiteralCross_rank
    (n := n) (b := b) (d := d) hn2 hn hb2 hd2

end

end Core4loop.SquareDiagonal.EvenP
