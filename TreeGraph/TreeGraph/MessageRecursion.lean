import TreeGraph.ConnectedTerms
import TreeGraph.AlgebraLemmas

namespace TreeGraph

noncomputable def Yassign (n : Nat) (T : RTree) : ℤ := Ypoly n T
noncomputable def Xassign (n : Nat) (T : RTree) : ℤ := Xpoly n T

theorem Yassign_node (n a : Nat) (cs : List RTree) :
    Yassign n (RTree.node a cs) =
      (cs.map (fun C => (nZ n) ^ RTree.totalWeight C - (tZ n) * Yassign n C)).prod := by
  simp [Yassign, Ypoly]

theorem Xassign_node (n a : Nat) (cs : List RTree) :
    Xassign n (RTree.node a cs) =
      Yassign n (RTree.node a cs) + childContribSum n a cs 0 := by
  simp [Xassign, Yassign, Xpoly]

theorem Xassign_eq_connected_terms (n : Nat) (T : RTree) :
    Xassign n T = termSum n (allTerms T) := by
  simpa [Xassign] using Xpoly_eq_allTerms n T

end TreeGraph
