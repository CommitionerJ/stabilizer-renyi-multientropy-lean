import TreeGraph.Imbalance.NodePackageBoundary

namespace TreeGraph
namespace Imbalance

@[simp] theorem mem_independentAllowed_nil
    (h : factorProduct ([] : List SliceFactor) → F2) :
    h ∈ independentAllowed [] := by
  simp [independentAllowed]

theorem mem_independentAllowed_cons_iff
    (F : SliceFactor) (Fs : List SliceFactor)
    (h : factorProduct (F :: Fs) → F2) :
    h ∈ independentAllowed (F :: Fs) ↔
      (∀ c : F.C,
        (fun rest : factorProduct Fs => h (c, rest)) ∈
          independentAllowed Fs) ∧
      (∀ rest : factorProduct Fs,
        (fun c : F.C => h (c, rest)) ∈ F.K) := by
  change
    h ∈ sliceIntersection F.C (factorProduct Fs) F.K
      (independentAllowed Fs) ↔
      (∀ c : F.C,
        (fun rest : factorProduct Fs => h (c, rest)) ∈
          independentAllowed Fs) ∧
      (∀ rest : factorProduct Fs,
        (fun c : F.C => h (c, rest)) ∈ F.K)
  exact mem_sliceIntersection_iff F.K (independentAllowed Fs) h

theorem mem_packageAllowedBoundarySpace_iff_exists_factor
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT)
    (h : BoundaryField n (RTree.node a cs)) :
    h ∈ packageAllowedBoundarySpace n a cs hT I ↔
      ∃ g :
          factorProduct
            (packageChildSliceFactors n cs
              (child_positive_of_node hT) I.childPackage) → F2,
        g ∈ independentAllowed
          (packageChildSliceFactors n cs
            (child_positive_of_node hT) I.childPackage) ∧
        (fun x : CoordsList n cs =>
          g ((packageFactorProductEquivCoordsList n cs
              (child_positive_of_node hT) I.childPackage).symm x)) = h := by
  exact
    mem_transportedSubmodule_iff
      (CoordsList n cs)
      (factorProduct
        (packageChildSliceFactors n cs
          (child_positive_of_node hT) I.childPackage))
      F2
      (packageFactorProductEquivCoordsList n cs
        (child_positive_of_node hT) I.childPackage).symm
      (independentAllowed
        (packageChildSliceFactors n cs
          (child_positive_of_node hT) I.childPackage))
      h

theorem mem_packageAllowedRootFieldSpace_iff_boundary
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT)
    (root : RootFieldAssignmentClean n (RTree.node a cs)) :
    root ∈ packageAllowedRootFieldSpace n a cs hT I ↔
      I.parentRootCopenBridge.linearEquiv root ∈
        packageAllowedBoundarySpace n a cs hT I := by
  rfl

end Imbalance
end TreeGraph
