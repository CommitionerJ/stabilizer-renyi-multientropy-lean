import TreeGraph.PhysicalBridges

namespace TreeGraph

namespace RawPrimitive

structure ModelCertificate (T : RTree) : Prop where
  positiveWeights : RTree.PositiveWeights T
  signedSum_eq_DeltaTreeModel :
    ∀ (n : Nat) [NeZero n], RawNormal.signedSum n T = DeltaTreeModel n T

namespace ModelCertificate

theorem normalFormSignedSum_eq_DeltaTreeModel
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    normalFormSignedSum n T = DeltaTreeModel n T :=
  normalFormSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := T) hT.positiveWeights
    (hT.signedSum_eq_DeltaTreeModel n)

theorem normalFormSignedSum_closed_Xpoly
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    normalFormSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  normalFormSignedSum_closed_Xpoly_of_signedSum_eq
    (n := n) (T := T) hT.positiveWeights
    (hT.signedSum_eq_DeltaTreeModel n)

theorem normalFormSignedSum_closed_connected_terms
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  normalFormSignedSum_closed_connected_terms_of_signedSum_eq
    (n := n) (T := T) hT.positiveWeights
    (hT.signedSum_eq_DeltaTreeModel n)

theorem rawBitStringSignedSum_eq_DeltaTreeModel
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = DeltaTreeModel n T :=
  rawBitStringSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := T) hT.positiveWeights
    (hT.signedSum_eq_DeltaTreeModel n)

theorem rawBitStringSignedSum_closed_Xpoly
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  rawBitStringSignedSum_closed_Xpoly_of_signedSum_eq
    (n := n) (T := T) hT.positiveWeights
    (hT.signedSum_eq_DeltaTreeModel n)

theorem rawBitStringSignedSum_closed_connected_terms
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  rawBitStringSignedSum_closed_connected_terms_of_signedSum_eq
    (n := n) (T := T) hT.positiveWeights
    (hT.signedSum_eq_DeltaTreeModel n)

end ModelCertificate

theorem modelCertificate_of_verifiedShape {T : RTree}
    (hT : VerifiedShape T) : ModelCertificate T where
  positiveWeights := verifiedShape_positiveWeights hT
  signedSum_eq_DeltaTreeModel := by
    intro n _
    exact verifiedShape_signedSum_eq_DeltaTreeModel n hT

theorem modelCertificate_leaf (a : Nat) (ha : 0 < a) :
    ModelCertificate (RTree.node a []) :=
  modelCertificate_of_verifiedShape (VerifiedShape.leaf a ha)

theorem modelCertificate_edge (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    ModelCertificate (RTree.node a [RTree.node b []]) :=
  modelCertificate_of_verifiedShape (VerifiedShape.edge a b ha hb)

theorem modelCertificate_star
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ModelCertificate (StarTree a b c) :=
  modelCertificate_of_verifiedShape (VerifiedShape.star a b c ha hb hc)

theorem certified_rawBitStringSignedSum_closed_connected_terms
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  ModelCertificate.rawBitStringSignedSum_closed_connected_terms hT n

theorem certified_rawBitStringSignedSum_closed_Xpoly
    {T : RTree} (hT : ModelCertificate T) (n : Nat) [NeZero n] :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  ModelCertificate.rawBitStringSignedSum_closed_Xpoly hT n

end RawPrimitive

end TreeGraph
