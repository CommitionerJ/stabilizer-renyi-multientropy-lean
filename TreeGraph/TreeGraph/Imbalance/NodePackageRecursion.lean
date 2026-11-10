import TreeGraph.Imbalance.NodePackageStepCertificate
import TreeGraph.Imbalance.AssignmentRecursion

namespace TreeGraph
namespace Imbalance

noncomputable def packageNodeAllowedSum
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) : ℤ :=
  allowedSignedSum
    (independentAllowed
      (packageChildSliceFactors n cs
        (child_positive_of_node hT) I.childPackage))
    0

theorem packageNodeAllowedSum_eq_two_pow_Ydim
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    packageNodeAllowedSum n a cs hT I =
      (2 : ℤ) ^ Ydim n (RTree.node a cs) hT := by
  unfold packageNodeAllowedSum
  rw [allowedSignedSum_zero]
  rw [finrank_independentAllowed]
  rw [factorDimProduct_packageChildSliceFactors_node_Ydim]

noncomputable def packageNodeNormalSum
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) : ℤ :=
  packageNodeAllowedSum n a cs hT I *
    childBranchScalarProduct n a cs 0

theorem packageNodeNormalSum_eq_two_pow_Xdim
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    packageNodeNormalSum n a cs hT I =
      (2 : ℤ) ^ Xdim n (RTree.node a cs) := by
  unfold packageNodeNormalSum
  rw [packageNodeAllowedSum_eq_two_pow_Ydim]
  rw [childBranchScalarProduct_eq_two_pow_contrib]
  rw [← pow_add]
  rw [← Xdim_node_eq_Ydim_add_childContrib n a cs hT]

end Imbalance
end TreeGraph
