import TreeGraph.Examples
import Core2
import Core3tree

namespace TreeGraph

theorem DeltaTreeModel_edge_matches_core2_formula
    (n a b : Nat) :
    DeltaTreeModel n (edgeTree a b)
      = (2 : ℤ) ^ Int.toNat ((n : ℤ)^a + (n : ℤ)^b - ((n : ℤ)-1)) := by
  rw [DeltaTreeModel_closed_Xpoly, Xpoly_edgeTree]

theorem edgeTree_regression_to_Core2_closed_form
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    FormalMathLab.CombinatorialAssignments.deltaCore (n := n) (a - 1) (b - 1) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) :=
  FormalMathLab.CombinatorialAssignments.signed_imbalance_user
    (a := a) (b := b) (n := n) ha hb

theorem core3Star_exponent_matches_Core3tree_formula
    (n a b c : Nat) :
    Xpoly n (core3Star a b c) =
      (n : ℤ)^(a+b) + (n : ℤ)^(a+c) + (n : ℤ)^(b+c)
        - (n : ℤ)^(b+1) - (n : ℤ)^(c+1)
        + (n : ℤ)^b + (n : ℤ)^c + ((n : ℤ)-1)^2 := by
  rw [Xpoly_core3Star]
  simp [pow_add]
  ring_nf

theorem core3Star_delta_matches_core3tree_formula
    (n a b c : Nat) :
    DeltaTreeModel n (core3Star a b c)
      = (2 : ℤ) ^ Int.toNat
        ((n : ℤ)^(a+b) + (n : ℤ)^(a+c) + (n : ℤ)^(b+c)
          - (n : ℤ)^(b+1) - (n : ℤ)^(c+1)
          + (n : ℤ)^b + (n : ℤ)^c + ((n : ℤ)-1)^2) := by
  rw [DeltaTreeModel_closed_Xpoly, core3Star_exponent_matches_Core3tree_formula]

theorem core3Star_regression_to_Core3tree_final_closed_form
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    No13Migration.deltaABCraw_final a b c n =
      (2 : ℤ) ^
        (n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
          - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2) :=
  No13Migration.signed_imbalance_abc_final_closed
    (a := a) (b := b) (c := c) (n := n) ha hb hc

end TreeGraph
