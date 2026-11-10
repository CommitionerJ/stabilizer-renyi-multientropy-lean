import TreeGraph.Imbalance.NodeHeadPhysicalReduction
import TreeGraph.Imbalance.NodeHeadBoundaryTransport
import TreeGraph.Imbalance.NodeOpenAssignmentSplit

namespace TreeGraph
namespace Imbalance

structure HeadChildPhysicalPackageReduction
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT) where
  head_reduction_eq :
    ∀ root : RootFieldAssignmentClean n (RTree.node a (C :: rest)),
      headChildPhysicalSignedSum n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) root =
        (2 : ℤ) ^
            branchDescendantScalarExponent n a 0 C rest
              (child_positive_of_node hT C (by simp)) *
          headBranchMessageSignedSum n a C rest
            (child_positive_of_node hT C (by simp))
            (I.childPackage C (by simp)) root

structure ConsOpenPhysicalReductionCertificate
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT) where
  headChildReduction :
    HeadChildPhysicalPackageReduction n a C rest hT I
  open_sum_cons_eq : Prop

end Imbalance
end TreeGraph
