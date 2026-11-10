import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RankMid

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

set_option maxHeartbeats 12000000 in
-- The outer product rank needs more than the project heartbeat default.
set_option synthInstance.maxHeartbeats 1000000 in
-- The outer product rank uses the separately compiled nested-product instances.
theorem rank_totalEOEEBlockCross_addition_first
    {n c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (totalEOEEBlockCross
            (n := n) (c := c) (d := d))) =
      3 * n ^ 2 * (n - 1) +
        (n ^ (d - 1) - 2) * n ^ 2 * (n - 1) +
        (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) +
        (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          n ^ 2 * (n - 1) := by
  letI : FiniteDimensional F (DiamondEOEELeftSource n) :=
    FiniteDimensional.of_injective
      (DiamondEOEELeftSource n).subtype Subtype.val_injective
  letI : FiniteDimensional F
      (DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) ×
        (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
          DiamondMixedTailZero n c d (CyclicCube n))) :=
    totalEOEEWZAndZWLeftFiniteDimensional n c d
  unfold totalEOEEBlockCross
  rw [finrank_range_diamondCrossProd
      (U₁ := DiamondEOEELeftSource n)
      (U₂ :=
        DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) ×
          (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
            DiamondMixedTailZero n c d (CyclicCube n)))
      (V₁ := DiamondEOEERightSource n)
      (V₂ :=
        DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n) ×
          (DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
            DiamondMixedTailZero n c d (CyclicCube n)))
      (diamondEOEECross (n := n))
      (totalEOEEWZAndZWCross (n := n) (c := c) (d := d)),
    rank_diamondEvenP_cross_EOEE_scalar hn2 hn,
    rank_totalEOEEWZAndZWCross hn2 hn hc2 hd2]
  omega

end TotalEOEEInternal

/-- Literal EOEE left-source coordinates in the frozen
`scalar × (W × (Z × ZW))` order. -/
noncomputable def diamondEvenPLeftEOEEEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPLeft n 1 c d ≃ₗ[F]
      TotalEOEEInternal.TotalEOEELeftSourceTarget n c d :=
  TotalEOEEInternal.leftSourceEquiv hn hc2 hd2

/-- Literal reachable EOEE right-source coordinates, including the proved
W-block shear `(A,D) ↦ (D,A+D)`. -/
noncomputable def diamondEvenPReachableAEOEEEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n 1 c d ≃ₗ[F]
      TotalEOEEInternal.RightReachableTarget n c d :=
  TotalEOEEInternal.rightReachableEquiv hn hc2 hd2

set_option maxHeartbeats 4000000 in
-- Elaborating the full four-block linear map needs a larger heartbeat budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The nested restricted dual needs the same budget as its compiled certificate.
/-- The four EOEE blocks, associated as `scalar × (W × (Z × ZW))`.
The mixed block uses Z as the outer tail and W as the inner tail. -/
noncomputable def diamondEOEETotalBlockCross
    {n c d : Nat} [NeZero n] :
    TotalEOEEInternal.TotalEOEELeftSourceTarget n c d →ₗ[F]
      Module.Dual F (TotalEOEEInternal.RightReachableTarget n c d) :=
  TotalEOEEInternal.totalEOEEBlockCross

set_option maxHeartbeats 4000000 in
-- The literal-to-block pointwise rewrite needs a larger heartbeat budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Unfolding both literal coordinate equivalences is elaboration-heavy.
/-- The literal finite-assignment EOEE phase is pointwise equal to the
four-block cross; no rank identity is used in this proof. -/
theorem diamondEvenPCross_EOEE_phase
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    diamondEOEETotalBlockCross
        (diamondEvenPLeftEOEEEquiv hn hc2 hd2 l)
        (diamondEvenPReachableAEOEEEquiv hn hc2 hd2 A) =
      diamondEvenPCross l A := by
  exact
    (TotalEOEEInternal.literal_phase_eq_totalEOEEBlockCross
      hn hc2 hd2 l A).symm

set_option maxHeartbeats 4000000 in
-- Constructing the nested range transport needs a larger heartbeat budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- Both nested restricted source modules are synthesized by this transport.
/-- Range transport from the literal EOEE cross to its four independent
block coordinates. -/
noncomputable def diamondEvenPCross_EOEE_rangeEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := 1) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.range
        (diamondEOEETotalBlockCross (n := n) (c := c) (d := d)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (L := DiamondEvenPLeft n 1 c d)
    (R := DiamondEvenPReachableA n 1 c d)
    (L' := TotalEOEEInternal.TotalEOEELeftSourceTarget n c d)
    (R' := TotalEOEEInternal.RightReachableTarget n c d)
    (diamondEvenPCross
      (n := n) (b := 1) (c := c) (d := d))
    (diamondEOEETotalBlockCross (n := n) (c := c) (d := d))
    (diamondEvenPLeftEOEEEquiv hn hc2 hd2)
    (diamondEvenPReachableAEOEEEquiv hn hc2 hd2)
    (diamondEvenPCross_EOEE_phase hn hc2 hd2)

set_option maxHeartbeats 12000000 in
-- Transporting and elaborating the exact rank equality needs this budget.
set_option synthInstance.maxHeartbeats 1000000 in
-- The proof transports to the separately compiled addition-first rank theorem.
/-- Exact all-`n` rank of the literal EOEE cross for positive non-singleton
Z and W blocks. -/
theorem rank_diamondEvenPCross_EOEE
    {n c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := c) (d := d))) =
      3 * n ^ 2 * (n - 1) +
        (n ^ (d - 1) - 2) * n ^ 2 * (n - 1) +
        (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) +
        (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
          n ^ 2 * (n - 1) := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := c) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (diamondEOEETotalBlockCross
              (n := n) (c := c) (d := d))) :=
      LinearEquiv.finrank_eq
        (diamondEvenPCross_EOEE_rangeEquiv hn hc2 hd2)
    _ =
        3 * n ^ 2 * (n - 1) +
          (n ^ (d - 1) - 2) * n ^ 2 * (n - 1) +
          (n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) +
          (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
            n ^ 2 * (n - 1) := by
      exact
        TotalEOEEInternal.rank_totalEOEEBlockCross_addition_first
          hn2 hn hc2 hd2

end

end Core4loop.SquareDiagonal.EvenP
