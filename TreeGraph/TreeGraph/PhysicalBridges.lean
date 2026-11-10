import TreeGraph.VerifiedShapes
import Core2
import Core3tree

namespace TreeGraph

namespace RawPrimitive

theorem signedSum_edge_eq_core2_deltaCore
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    RawNormal.signedSum n (RTree.node a [RTree.node b []]) =
      FormalMathLab.CombinatorialAssignments.deltaCore (n := n) (a - 1) (b - 1) := by
  rw [signedSum_edge_closed ha hb,
    FormalMathLab.CombinatorialAssignments.signed_imbalance_user
      (a := a) (b := b) (n := n) ha hb]

theorem rawBitStringSignedSum_edge_eq_core2_deltaCore
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    rawBitStringSignedSum n (RTree.node a [RTree.node b []]) =
      FormalMathLab.CombinatorialAssignments.deltaCore (n := n) (a - 1) (b - 1) := by
  rw [rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := RTree.node a [RTree.node b []])
    (hT := by simp [RTree.PositiveWeights, ha, hb])]
  exact signedSum_edge_eq_core2_deltaCore ha hb

theorem rawBitStringSignedSum_edge_closed_via_core2
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    rawBitStringSignedSum n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  rw [rawBitStringSignedSum_edge_eq_core2_deltaCore ha hb]
  exact FormalMathLab.CombinatorialAssignments.signed_imbalance_user
    (a := a) (b := b) (n := n) ha hb

theorem signedSum_star_eq_core3_deltaABCraw_final
    {a b c n : Nat} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    RawNormal.signedSum n (StarTree a b c) =
      No13Migration.deltaABCraw_final a b c n := by
  rw [signedSum_star_eq_deltaABCraw_real n a b c]
  simpa [No13Migration.deltaABCraw_final] using
    (No13Migration.deltaABCraw_primitive_honest_eq_real
      (a := a) (b := b) (c := c) (n := n) hb hc).symm

theorem rawBitStringSignedSum_star_eq_core3_deltaABCraw_final
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    rawBitStringSignedSum n (StarTree a b c) =
      No13Migration.deltaABCraw_final a b c n := by
  rw [rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := StarTree a b c)
    (hT := by simp [StarTree, RTree.PositiveWeights, ha, hb, hc])]
  exact signedSum_star_eq_core3_deltaABCraw_final hb hc

theorem rawBitStringSignedSum_star_closed_via_core3_final
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    rawBitStringSignedSum n (StarTree a b c) =
      (2 : ℤ) ^
        (n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
          - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2) := by
  rw [rawBitStringSignedSum_star_eq_core3_deltaABCraw_final ha hb hc]
  exact No13Migration.signed_imbalance_abc_final_closed
    (a := a) (b := b) (c := c) (n := n) ha hb hc

end RawPrimitive

end TreeGraph
