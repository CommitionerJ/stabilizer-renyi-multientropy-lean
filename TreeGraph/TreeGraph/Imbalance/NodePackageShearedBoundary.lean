import TreeGraph.Imbalance.NodeHeadShearedAllowed
import TreeGraph.Imbalance.NodeHeadProjectionBridge

namespace TreeGraph
namespace Imbalance

noncomputable def packageShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n] :
    (cs : List RTree) →
      (hT : RTree.PositiveWeights (RTree.node a cs)) →
      NodeOpenPackageStepInputs n a cs hT →
      Submodule F2 (BoundaryField n (RTree.node a cs))
  | [], _hT, _I => ⊤
  | C :: rest, hT, I =>
      headShearedAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ⊓
        rowsIn (Cplus n C) (CoordsList n rest)
          (packageShearedAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I))

theorem packageShearedAllowedBoundarySpace_nil_eq_top
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : NodeOpenPackageStepInputs n a [] hT) :
    packageShearedAllowedBoundarySpace n a [] hT I = ⊤ := by
  rfl

theorem mem_packageShearedAllowedBoundarySpace_nil
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : NodeOpenPackageStepInputs n a [] hT)
    (h : BoundaryField n (RTree.node a [])) :
    h ∈ packageShearedAllowedBoundarySpace n a [] hT I := by
  rw [packageShearedAllowedBoundarySpace_nil_eq_top n a hT I]
  exact Submodule.mem_top

theorem mem_packageShearedAllowedBoundarySpace_cons_iff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (h : BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ packageShearedAllowedBoundarySpace n a (C :: rest) hT I ↔
      h ∈ headShearedAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∧
        ∀ p : Cplus n C,
          (fun tail : CoordsList n rest => h (p, tail)) ∈
            packageShearedAllowedBoundarySpace n a rest
              (positiveWeights_node_tail_of_cons hT)
              (nodeTailInputsOfCons n a C rest hT I) := by
  change
    h ∈
        headShearedAllowedBoundarySpace n a C rest
            (child_positive_of_node hT C (by simp))
            (I.childPackage C (by simp)) ⊓
          rowsIn (Cplus n C) (CoordsList n rest)
            (packageShearedAllowedBoundarySpace n a rest
              (positiveWeights_node_tail_of_cons hT)
              (nodeTailInputsOfCons n a C rest hT I)) ↔
      _
  rw [Submodule.mem_inf]
  rfl

noncomputable def packageShearedAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Submodule F2
      (RootFieldAssignmentClean n (RTree.node a cs)) :=
  (packageShearedAllowedBoundarySpace n a cs hT I).comap
    I.parentRootCopenBridge.linearEquiv.toLinearMap

theorem mem_packageShearedAllowedRootFieldSpace_iff_boundary
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT)
    (root : RootFieldAssignmentClean n (RTree.node a cs)) :
    root ∈ packageShearedAllowedRootFieldSpace n a cs hT I ↔
      I.parentRootCopenBridge.linearEquiv root ∈
        packageShearedAllowedBoundarySpace n a cs hT I := by
  rfl

theorem packageShearedAllowedRootFieldSpace_nil_eq_top
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : NodeOpenPackageStepInputs n a [] hT) :
    packageShearedAllowedRootFieldSpace n a [] hT I = ⊤ := by
  unfold packageShearedAllowedRootFieldSpace
  rw [packageShearedAllowedBoundarySpace_nil_eq_top n a hT I]
  ext root
  simp

theorem mem_packageShearedAllowedRootFieldSpace_nil
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : NodeOpenPackageStepInputs n a [] hT)
    (root : RootFieldAssignmentClean n (RTree.node a [])) :
    root ∈ packageShearedAllowedRootFieldSpace n a [] hT I := by
  rw [packageShearedAllowedRootFieldSpace_nil_eq_top n a hT I]
  exact Submodule.mem_top

theorem tailRootFieldFromHeadCplus_mem_packageShearedAllowedRootFieldSpace_iff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C) :
    tailRootFieldFromHeadCplus n a C rest root p ∈
        packageShearedAllowedRootFieldSpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons n a C rest hT I) ↔
      (fun tail : CoordsList n rest =>
        headParentRootBoundaryFieldFromRoot n a C rest root (p, tail)) ∈
        packageShearedAllowedBoundarySpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons n a C rest hT I) := by
  rw [mem_packageShearedAllowedRootFieldSpace_iff_boundary]
  change
    (RootFieldCleanCopenBridge.node n a rest).linearEquiv
          (tailRootFieldFromHeadCplus n a C rest root p) ∈
        packageShearedAllowedBoundarySpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons n a C rest hT I) ↔
      (fun tail : CoordsList n rest =>
        headParentRootBoundaryFieldFromRoot n a C rest root (p, tail)) ∈
        packageShearedAllowedBoundarySpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons n a C rest hT I)
  rw [tailRootFieldFromHeadCplus_boundary]
  rfl

theorem root_mem_packageShearedAllowedRootFieldSpace_iff_head_tailRootRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageShearedAllowedRootFieldSpace n a (C :: rest) hT I ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headShearedAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∧
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageShearedAllowedRootFieldSpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I) := by
  rw [mem_packageShearedAllowedRootFieldSpace_iff_boundary]
  have hboundary :
      I.parentRootCopenBridge.linearEquiv root =
        headParentRootBoundaryFieldFromRoot n a C rest root := by
    simp [headParentRootBoundaryFieldFromRoot, hbridge]
  rw [hboundary]
  rw [mem_packageShearedAllowedBoundarySpace_cons_iff]
  constructor
  · intro hh
    exact ⟨hh.1, fun p =>
      (tailRootFieldFromHeadCplus_mem_packageShearedAllowedRootFieldSpace_iff
        n a C rest hT I root p).2 (hh.2 p)⟩
  · intro hh
    exact ⟨hh.1, fun p =>
      (tailRootFieldFromHeadCplus_mem_packageShearedAllowedRootFieldSpace_iff
        n a C rest hT I root p).1 (hh.2 p)⟩

end Imbalance
end TreeGraph
