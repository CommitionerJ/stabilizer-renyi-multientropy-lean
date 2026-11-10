import TreeGraph.Imbalance.NodePackageFactors

namespace TreeGraph
namespace Imbalance

noncomputable def packageFactorProductEquivCoordsList (n : Nat) [NeZero n] :
    ∀ (cs : List RTree)
      (hcs : ∀ C ∈ cs, RTree.PositiveWeights C)
      (childPackage :
        ∀ C, (hCmem : C ∈ cs) →
          OpenNormalCleanPackage n C (hcs C hCmem)),
      factorProduct
        (packageChildSliceFactors n cs hcs childPackage) ≃
        CoordsList n cs
  | [], _, _ => Equiv.refl _
  | C :: rest, hcs, childPackage =>
      let hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hcs D (by simp [hD])
      let Prest :
          ∀ D, (hDmem : D ∈ rest) →
            OpenNormalCleanPackage n D (hrest D hDmem) := by
        intro D hDmem
        exact childPackage D (by simp [hDmem])
      let erest :=
        packageFactorProductEquivCoordsList n rest hrest Prest
      { toFun := fun x => (x.1, erest x.2)
        invFun := fun x => (x.1, erest.symm x.2)
        left_inv := by
          intro x
          rcases x with ⟨p, e⟩
          simp [erest]
        right_inv := by
          intro x
          rcases x with ⟨p, e⟩
          simp [erest] }

noncomputable def packageAllowedBoundarySpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Submodule F2 (BoundaryField n (RTree.node a cs)) :=
  transportedSubmodule
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

theorem finrank_packageAllowedBoundarySpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Module.finrank F2
      (packageAllowedBoundarySpace n a cs hT I) =
      Ydim n (RTree.node a cs) hT := by
  let Fs :=
    packageChildSliceFactors n cs
      (child_positive_of_node hT) I.childPackage
  let e :=
    (packageFactorProductEquivCoordsList n cs
      (child_positive_of_node hT) I.childPackage).symm
  calc
    Module.finrank F2
        (packageAllowedBoundarySpace n a cs hT I) =
        Module.finrank F2
          (transportedSubmodule
            (CoordsList n cs) (factorProduct Fs) F2 e
            (independentAllowed Fs)) := by
      rfl
    _ = Module.finrank F2 (independentAllowed Fs) := by
      exact finrank_transportedSubmodule
        (CoordsList n cs) (factorProduct Fs) F2 e
        (independentAllowed Fs)
    _ = factorDimProduct Fs := by
      exact finrank_independentAllowed Fs
    _ = Ydim n (RTree.node a cs) hT := by
      exact factorDimProduct_packageChildSliceFactors_node_Ydim
        n a cs hT I.childPackage

noncomputable instance packageAllowedBoundarySpaceFintype
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype (packageAllowedBoundarySpace n a cs hT I) := by
  classical
  exact Fintype.ofFinite (packageAllowedBoundarySpace n a cs hT I)

theorem card_packageAllowedBoundarySpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype.card
      (packageAllowedBoundarySpace n a cs hT I) =
      2 ^ Ydim n (RTree.node a cs) hT := by
  rw [submodule_card_eq_pow_finrank]
  rw [finrank_packageAllowedBoundarySpace]

theorem packageAllowedBoundarySpace_nil_eq_top
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : NodeOpenPackageStepInputs n a [] hT) :
    packageAllowedBoundarySpace n a [] hT I = ⊤ := by
  simp [packageAllowedBoundarySpace, packageChildSliceFactors,
    packageFactorProductEquivCoordsList, independentAllowed,
    transportedSubmodule_top]
  rfl

noncomputable def packageAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Submodule F2
      (RootFieldAssignmentClean n (RTree.node a cs)) :=
  (packageAllowedBoundarySpace n a cs hT I).comap
    I.parentRootCopenBridge.linearEquiv.toLinearMap

theorem finrank_packageAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Module.finrank F2
      (packageAllowedRootFieldSpace n a cs hT I) =
      Ydim n (RTree.node a cs) hT := by
  rw [packageAllowedRootFieldSpace]
  rw [finrank_submodule_comap_linearEquiv]
  exact finrank_packageAllowedBoundarySpace n a cs hT I

noncomputable instance packageAllowedRootFieldSpaceFintype
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype (packageAllowedRootFieldSpace n a cs hT I) := by
  classical
  exact Fintype.ofFinite (packageAllowedRootFieldSpace n a cs hT I)

theorem card_packageAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype.card
      (packageAllowedRootFieldSpace n a cs hT I) =
      2 ^ Ydim n (RTree.node a cs) hT := by
  rw [submodule_card_eq_pow_finrank]
  rw [finrank_packageAllowedRootFieldSpace]

theorem packageAllowedRootFieldSpace_nil_eq_top
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : NodeOpenPackageStepInputs n a [] hT) :
    packageAllowedRootFieldSpace n a [] hT I = ⊤ := by
  unfold packageAllowedRootFieldSpace
  rw [packageAllowedBoundarySpace_nil_eq_top n a hT I]
  ext root
  simp

theorem mem_packageAllowedRootFieldSpace_nil
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : NodeOpenPackageStepInputs n a [] hT)
    (root : RootFieldAssignmentClean n (RTree.node a [])) :
    root ∈ packageAllowedRootFieldSpace n a [] hT I := by
  rw [packageAllowedRootFieldSpace_nil_eq_top n a hT I]
  exact Submodule.mem_top

end Imbalance
end TreeGraph
