import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RankLower

set_option autoImplicit false
set_option warningAsError true
-- Nested restricted-product instances require one shared completion-first budget.
set_option linter.style.setOption false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 1000000

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

local instance t35PBlockLeftFiniteDimensional
    (n : Nat) [NeZero n] :
    FiniteDimensional F (EEOEInternal.PBlockLeft n) :=
  FiniteDimensional.of_injective
    (EEOEInternal.PBlockLeft n).subtype Subtype.val_injective

local instance t35EOEEWLeftTailFiniteDimensional
    (n d : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n)) :=
  FiniteDimensional.of_injective
    (DiamondEvenAxisValueTailZero n d
      (DiamondEOEEWLeftSource n)).subtype Subtype.val_injective

local instance t35EOOELeftTailFiniteDimensional
    (n c : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n)) :=
  FiniteDimensional.of_injective
    (DiamondEvenAxisValueTailZero n c
      (DiamondEOOELeftAmbient n)).subtype Subtype.val_injective

local instance t35CubeTailFiniteDimensional
    (n d : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondEvenAxisValueTailZero n d (CyclicCube n)) :=
  FiniteDimensional.of_injective
    (DiamondEvenAxisValueTailZero n d
      (CyclicCube n)).subtype Subtype.val_injective

local instance t35MixedTailFiniteDimensional
    (n c d : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondMixedTailZero n c d (CyclicCube n)) :=
  FiniteDimensional.of_injective
    (DiamondMixedTailZero n c d
      (CyclicCube n)).subtype Subtype.val_injective

local instance t35ZAndZWFiniteDimensional
    (n c d : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n)) :=
  inferInstance

theorem totalEOEEWZAndZWLeftFiniteDimensional
    (n c d : Nat) [NeZero n] :
    FiniteDimensional F
      (DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) ×
        (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
          DiamondMixedTailZero n c d (CyclicCube n))) :=
  inferInstance

theorem rank_totalEOEEWZAndZWCross
    {n c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (totalEOEEWZAndZWCross
            (n := n) (c := c) (d := d))) =
      (n ^ (d - 1) - 2) * n ^ 2 * (n - 1) +
        ((n ^ (c - 1) - 2) * n * (n - 1) * (2 * n + 1) +
          (n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
            n ^ 2 * (n - 1)) := by
  unfold totalEOEEWZAndZWCross
  rw [finrank_range_diamondCrossProd
      (U₁ :=
        DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n))
      (U₂ :=
        DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
          DiamondMixedTailZero n c d (CyclicCube n))
      (V₁ :=
        DiamondEvenAxisValueTailZero n d (DiamondEOEEWRightSource n))
      (V₂ :=
        DiamondEvenAxisValueTailZero n c (DiamondEOOERightAmbient n) ×
          DiamondMixedTailZero n c d (CyclicCube n))
      (totalEOEEWAmplifiedCross (n := n) (d := d))
      (totalEOEEZAndZWCross (n := n) (c := c) (d := d)),
    rank_totalEOEEWAmplifiedCross hn2 hn hd2,
    rank_totalEOEEZAndZWCross hn2 hn hc2 hd2]


end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP
