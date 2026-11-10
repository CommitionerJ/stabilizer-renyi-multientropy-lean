import TreeGraph.Imbalance.RecursiveMessageSpace
import TreeGraph.ConnectedTerms

namespace TreeGraph
namespace Imbalance

theorem Ydim_cast_eq_rootedTerms (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Ydim n T hT : Nat) : ℤ) = termSum n (rootedTerms T) := by
  rw [Ydim_cast_eq_Ypoly n T hT]
  exact Ypoly_eq_rootedTerms n T

theorem Xdim_cast_eq_allTerms (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Xdim n T : Nat) : ℤ) = termSum n (allTerms T) := by
  rw [Xdim_cast_eq_Xpoly n T hT]
  exact Xpoly_eq_allTerms n T

theorem Ypoly_nonneg_of_positiveWeights (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    0 ≤ Ypoly n T := by
  rw [← Ydim_cast_eq_Ypoly n T hT]
  exact Int.natCast_nonneg _

theorem Xpoly_nonneg_of_positiveWeights (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    0 ≤ Xpoly n T := by
  rw [← Xdim_cast_eq_Xpoly n T hT]
  exact Int.natCast_nonneg _

theorem termSum_allTerms_nonneg_of_positiveWeights
    (n : Nat) [NeZero n] (T : RTree)
    (hT : RTree.PositiveWeights T) :
    0 ≤ termSum n (allTerms T) := by
  rw [← Xdim_cast_eq_allTerms n T hT]
  exact Int.natCast_nonneg _

end Imbalance
end TreeGraph
