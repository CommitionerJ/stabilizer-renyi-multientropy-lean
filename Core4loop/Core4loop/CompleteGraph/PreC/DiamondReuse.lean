import Core4loop.CompleteGraph.PreC.Reduction
import Core4loop.SquareDiagonal.PreC.Reduction
import Core4loop.SquareDiagonal.DirectWitt.SourceRank

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop

attribute [local instance] Fintype.ofFinite

theorem k4CPhaseCoeffClean_eq_diamondCPhaseCoeffClean
    {n a b c d : Nat} [NeZero n] :
    k4CPhaseCoeffClean (n := n) (a := a) (b := b) (c := c) (d := d) =
      diamondCPhaseCoeffClean (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rfl

theorem k4PreCMap_eq_diamondPreCMap
    {n a b c d : Nat} [NeZero n] :
    k4PreCMap (n := n) (a := a) (b := b) (c := c) (d := d) =
      diamondPreCMap (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rfl

noncomputable def k4PreCSourceEquivDiamond
    {n a b c d : Nat} [NeZero n] :
    K4PreCSource n a b c d ≃ₗ[F] DiamondPreCSource n a b c d :=
  LinearEquiv.refl F _

@[simp] theorem k4PreCSourceEquivDiamond_apply_A
    {n a b c d : Nat} [NeZero n]
    (x : K4PreCSource n a b c d) :
    (k4PreCSourceEquivDiamond x).1.1 = x.1.1 := by
  rfl

@[simp] theorem k4PreCSourceEquivDiamond_apply_B
    {n a b c d : Nat} [NeZero n]
    (x : K4PreCSource n a b c d) :
    (k4PreCSourceEquivDiamond x).1.2.1 = x.1.2.1 := by
  rfl

@[simp] theorem k4PreCSourceEquivDiamond_apply_W
    {n a b c d : Nat} [NeZero n]
    (x : K4PreCSource n a b c d) :
    (k4PreCSourceEquivDiamond x).1.2.2 = x.1.2.2 := by
  rfl

theorem k4PreCQ_transport
    {n a b c d : Nat} [NeZero n]
    (x : K4PreCSource n a b c d) :
    k4PreCQ x =
      diamondPreCQ (k4PreCSourceEquivDiamond x) +
        k4BWPhaseClean x.1.2.1 x.1.2.2 := by
  rfl

theorem sum_k4PreCQ_eq_sum_diamondPreCQ_add_BW
    {n a b c d : Nat} [NeZero n] :
    (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
      ∑ x : DiamondPreCSource n a b c d,
        bitSign
          (diamondPreCQ x +
            k4BWPhaseClean x.1.2.1 x.1.2.2) := by
  rfl

theorem DeltaNF_complete_eq_shared_preC_source_sum
    {n a b c d : Nat} [NeZero n] :
    DeltaNF .complete a b c d n =
      (Fintype.card (CFun4 n a b d) : Int) *
        ∑ x : DiamondPreCSource n a b c d,
          bitSign
            (diamondPreCQ x +
              k4BWPhaseClean x.1.2.1 x.1.2.2) := by
  exact DeltaNF_complete_eq_preC_kernel_sum

theorem finrank_K4PreCSource_add_range
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) :
    Module.finrank F (K4PreCSource n a b c d) +
        Module.finrank F
          (LinearMap.range
            (k4PreCMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) =
      n ^ (b + c + d) + n ^ (a + c + d) + n ^ (a + b + c) := by
  exact
    SquareDiagonal.DirectWitt.finrank_diamondPreCSource_add_range
      (n := n) (a := a) (b := b) (c := c) (d := d) ha

theorem finrank_range_k4PreCMap_add_vertex_terms
    {n a b c d : Nat} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (k4PreCMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
        (n - 1) ^ 2 * (n ^ a + n ^ b + n ^ d) =
      (n - 1) *
          (n ^ (a + b) + n ^ (a + d) + n ^ (b + d)) +
        (n - 1) ^ 3 := by
  exact
    SquareDiagonal.DirectWitt.finrank_range_diamondPreCMap_add_vertex_terms
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd

end Core4loop
