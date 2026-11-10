import Core4loop.SquareDiagonal.EvenP.CrossProjection
import Core4loop.SquareDiagonal.DirectWitt.BilinearSignSum

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

noncomputable section

section InternalFintypes

private local instance
    {n a b c d : Nat} [NeZero n] :
    Fintype (DiamondPreCSource n a b c d) :=
  Fintype.ofInjective
    (fun x : DiamondPreCSource n a b c d => x.1)
    Subtype.val_injective

private local instance
    {n b c d : Nat} [NeZero n] :
    Fintype (DiamondEvenPLeft n b c d) :=
  Fintype.ofInjective
    (fun x : DiamondEvenPLeft n b c d => x.1)
    Subtype.val_injective

private local instance
    {n b c d : Nat} [NeZero n] :
    Fintype (DiamondEvenPReachableA n b c d) :=
  Fintype.ofInjective
    (fun x : DiamondEvenPReachableA n b c d => x.1)
    Subtype.val_injective

noncomputable def diamondEvenPResidualExponent
    (n a b c d : Nat) [NeZero n] : Nat :=
  (n ^ (a - 1) - 1) *
      Module.finrank F (DiamondEvenPLeft n b c d) +
    Module.finrank F
      (LinearMap.ker
        (diamondEvenPCross
          (n := n) (b := b) (c := c) (d := d))) +
    Module.finrank F (DiamondEvenPReachableA n b c d)

private theorem diamondEvenP_sum_eq_pow_residual_internal
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    (∑ x : DiamondPreCSource n a b c d,
        bitSign (diamondPreCQ x)) =
      (2 : Int) ^ diamondEvenPResidualExponent n a b c d := by
  rw [diamondEvenP_sum_eq_phaseFree_mul_crossSum hn ha2]
  rw [show
    (∑ z :
        DiamondEvenPLeft n b c d ×
          DiamondEvenPReachableA n b c d,
        bitSign (diamondEvenPCrossQ z)) =
      (2 : Int) ^
        (Module.finrank F
            (LinearMap.ker
              (diamondEvenPCross
                (n := n) (b := b) (c := c) (d := d))) +
          Module.finrank F (DiamondEvenPReachableA n b c d)) by
    simpa only [diamondEvenPCrossQ] using
      (DirectWitt.sum_bitSign_bilinear_eq_pow
        (diamondEvenPCross (n := n) (b := b) (c := c) (d := d)))]
  rw [← pow_add]
  simp only [diamondEvenPResidualExponent, add_assoc]

end InternalFintypes

attribute [local instance] Fintype.ofFinite

theorem diamondEvenP_sum_eq_pow_residual
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    (∑ x : DiamondPreCSource n a b c d,
        bitSign (diamondPreCQ x)) =
      (2 : Int) ^ diamondEvenPResidualExponent n a b c d := by
  have h :=
    diamondEvenP_sum_eq_pow_residual_internal
      (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  convert h using 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 500000 in
theorem diamondEvenP_residual_add_crossRank_eq_source
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    diamondEvenPResidualExponent n a b c d +
      Module.finrank F
        (LinearMap.range
          (diamondEvenPCross (n := n) (b := b) (c := c) (d := d))) =
      Module.finrank F (DiamondPreCSource n a b c d) := by
  let P :=
    diamondEvenPCrossProjection
      (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  let L :=
    diamondEvenPCross (n := n) (b := b) (c := c) (d := d)
  have hP :=
    LinearMap.finrank_range_add_finrank_ker P
  have hPrange : LinearMap.range P = ⊤ :=
    LinearMap.range_eq_top.mpr
      (diamondEvenPCrossProjection_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2)
  have hL :=
    LinearMap.finrank_range_add_finrank_ker L
  have hPker :=
    finrank_ker_diamondEvenPCrossProjection
      (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  rw [hPrange, finrank_top, Module.finrank_prod] at hP
  change
    Module.finrank F (LinearMap.range L) +
        Module.finrank F (LinearMap.ker L) =
      Module.finrank F (DiamondEvenPLeft n b c d) at hL
  change
    ((n ^ (a - 1) - 1) *
          Module.finrank F (DiamondEvenPLeft n b c d) +
        Module.finrank F (LinearMap.ker L) +
        Module.finrank F (DiamondEvenPReachableA n b c d)) +
      Module.finrank F (LinearMap.range L) =
      Module.finrank F (DiamondPreCSource n a b c d)
  change
    Module.finrank F (LinearMap.ker P) =
      (n ^ (a - 1) - 1) *
        Module.finrank F (DiamondEvenPLeft n b c d) at hPker
  omega

end

end Core4loop.SquareDiagonal.EvenP
