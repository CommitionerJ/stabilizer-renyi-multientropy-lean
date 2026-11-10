import TreeGraph.Imbalance.NodeOpenPackageInputsCanonical

namespace TreeGraph
namespace Imbalance

namespace NodeOpenPackageStepInputs

noncomputable def canonicalNodeInputsOfPackages
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C
          (child_positive_of_node hT C hCmem)) :
    NodeOpenPackageStepInputs n a cs hT :=
  ofChildPackagesCanonical n a cs hT childPackage

@[simp] theorem canonicalNodeInputsOfPackages_childPackage
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C
          (child_positive_of_node hT C hCmem))
    (C : RTree) (hCmem : C ∈ cs) :
    (canonicalNodeInputsOfPackages n a cs hT childPackage).childPackage
        C hCmem =
      childPackage C hCmem :=
  rfl

@[simp] theorem canonicalNodeInputsOfPackages_parentRootCopenBridge
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C
          (child_positive_of_node hT C hCmem)) :
    (canonicalNodeInputsOfPackages n a cs hT childPackage).parentRootCopenBridge =
      RootFieldCleanCopenBridge.node n a cs :=
  rfl

end NodeOpenPackageStepInputs

end Imbalance
end TreeGraph
