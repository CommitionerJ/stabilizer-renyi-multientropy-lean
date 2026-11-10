import TreeGraph.StarABCBridge

namespace TreeGraph

namespace RawPrimitive

inductive VerifiedShape : RTree → Prop where
  | leaf (a : Nat) (ha : 0 < a) :
      VerifiedShape (RTree.node a [])
  | edge (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
      VerifiedShape (RTree.node a [RTree.node b []])
  | star (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      VerifiedShape (StarTree a b c)

theorem verifiedShape_positiveWeights {T : RTree} (hT : VerifiedShape T) :
    RTree.PositiveWeights T := by
  cases hT with
  | leaf a ha =>
      simpa [RTree.PositiveWeights] using ha
  | edge a b ha hb =>
      simp [RTree.PositiveWeights, ha, hb]
  | star a b c ha hb hc =>
      simp [StarTree, RTree.PositiveWeights, ha, hb, hc]

theorem verifiedShape_signedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n] {T : RTree} (hT : VerifiedShape T) :
    RawNormal.signedSum n T = DeltaTreeModel n T := by
  cases hT with
  | leaf a ha =>
      exact RawNormal.signedSum_leaf_eq_DeltaTreeModel n a
  | edge a b ha hb =>
      exact signedSum_edge_eq_DeltaTreeModel ha hb
  | star a b c ha hb hc =>
      exact signedSum_star_eq_DeltaTreeModel ha hb hc

theorem verifiedShape_normalFormSignedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n] {T : RTree} (hT : VerifiedShape T) :
    normalFormSignedSum n T = DeltaTreeModel n T := by
  exact normalFormSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := T)
    (verifiedShape_positiveWeights hT)
    (verifiedShape_signedSum_eq_DeltaTreeModel n hT)

theorem verifiedShape_normalFormSignedSum_closed_Xpoly
    (n : Nat) [NeZero n] {T : RTree} (hT : VerifiedShape T) :
    normalFormSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  exact normalFormSignedSum_closed_Xpoly_of_signedSum_eq
    (n := n) (T := T)
    (verifiedShape_positiveWeights hT)
    (verifiedShape_signedSum_eq_DeltaTreeModel n hT)

theorem verifiedShape_normalFormSignedSum_closed_connected_terms
    (n : Nat) [NeZero n] {T : RTree} (hT : VerifiedShape T) :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  exact normalFormSignedSum_closed_connected_terms_of_signedSum_eq
    (n := n) (T := T)
    (verifiedShape_positiveWeights hT)
    (verifiedShape_signedSum_eq_DeltaTreeModel n hT)

theorem verifiedShape_rawBitStringSignedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n] {T : RTree} (hT : VerifiedShape T) :
    rawBitStringSignedSum n T = DeltaTreeModel n T := by
  exact rawBitStringSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := T)
    (verifiedShape_positiveWeights hT)
    (verifiedShape_signedSum_eq_DeltaTreeModel n hT)

theorem verifiedShape_rawBitStringSignedSum_closed_Xpoly
    (n : Nat) [NeZero n] {T : RTree} (hT : VerifiedShape T) :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  exact rawBitStringSignedSum_closed_Xpoly_of_signedSum_eq
    (n := n) (T := T)
    (verifiedShape_positiveWeights hT)
    (verifiedShape_signedSum_eq_DeltaTreeModel n hT)

theorem verifiedShape_rawBitStringSignedSum_closed_connected_terms
    (n : Nat) [NeZero n] {T : RTree} (hT : VerifiedShape T) :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  exact rawBitStringSignedSum_closed_connected_terms_of_signedSum_eq
    (n := n) (T := T)
    (verifiedShape_positiveWeights hT)
    (verifiedShape_signedSum_eq_DeltaTreeModel n hT)

end RawPrimitive

end TreeGraph
