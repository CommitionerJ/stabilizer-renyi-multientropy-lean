import TreeGraph.MessageRecursion

namespace TreeGraph

noncomputable def DeltaTreeModel (n : Nat) (T : RTree) : ℤ :=
  (2 : ℤ) ^ Int.toNat (Xassign n T)

theorem DeltaTreeModel_closed_Xpoly (n : Nat) (T : RTree) :
    DeltaTreeModel n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rfl

theorem DeltaTreeModel_closed (n : Nat) (T : RTree) :
    DeltaTreeModel n T = (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [DeltaTreeModel, Xassign_eq_connected_terms]

theorem tree_imbalance_Xpoly (n : Nat) (T : RTree) :
    DeltaTreeModel n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  DeltaTreeModel_closed_Xpoly n T

theorem tree_imbalance_connected_terms (n : Nat) (T : RTree) :
    DeltaTreeModel n T = (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  DeltaTreeModel_closed n T

end TreeGraph
