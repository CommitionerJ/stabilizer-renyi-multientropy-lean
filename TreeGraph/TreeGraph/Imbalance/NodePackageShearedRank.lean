import TreeGraph.Imbalance.NodePackageShearedBoundary
import TreeGraph.Imbalance.NodeHeadShearedRank

namespace TreeGraph
namespace Imbalance

theorem packageShearedAllowedBoundarySpace_cons_eq_sliceIntersection
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT) :
    packageShearedAllowedBoundarySpace n a (C :: rest) hT I =
      sliceIntersection (Cplus n C) (CoordsList n rest)
        (headShearedOneSliceKernel n C
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)))
        (packageShearedAllowedBoundarySpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons n a C rest hT I)) := by
  change
    headShearedAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ⊓
        rowsIn (Cplus n C) (CoordsList n rest)
          (packageShearedAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I)) =
      sliceIntersection (Cplus n C) (CoordsList n rest)
        (headShearedOneSliceKernel n C
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)))
        (packageShearedAllowedBoundarySpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons n a C rest hT I))
  rw [headShearedAllowedBoundarySpace_eq_colsIn]
  change
    colsIn (Cplus n C) (CoordsList n rest)
          (headShearedOneSliceKernel n C
            (child_positive_of_node hT C (by simp))
            (I.childPackage C (by simp))) ⊓
        rowsIn (Cplus n C) (CoordsList n rest)
          (packageShearedAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I)) =
      rowsIn (Cplus n C) (CoordsList n rest)
          (packageShearedAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I)) ⊓
        colsIn (Cplus n C) (CoordsList n rest)
          (headShearedOneSliceKernel n C
            (child_positive_of_node hT C (by simp))
            (I.childPackage C (by simp)))
  rw [inf_comm]

theorem finrank_packageShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n] :
    (cs : List RTree) →
      (hT : RTree.PositiveWeights (RTree.node a cs)) →
      (I : NodeOpenPackageStepInputs n a cs hT) →
      Module.finrank F2
        (packageShearedAllowedBoundarySpace n a cs hT I) =
        Ydim n (RTree.node a cs) hT
  | [], hT, I => by
      rw [packageShearedAllowedBoundarySpace_nil_eq_top]
      rw [finrank_top]
      rw [finrank_boundaryField_leaf]
      rw [Ydim_eq_YdimCandidate, YdimCandidate_leaf]
  | C :: rest, hT, I => by
      let hC : RTree.PositiveWeights C :=
        child_positive_of_node hT C (by simp)
      let hTail : RTree.PositiveWeights (RTree.node a rest) :=
        positiveWeights_node_tail_of_cons hT
      let Itail : NodeOpenPackageStepInputs n a rest hTail :=
        nodeTailInputsOfCons n a C rest hT I
      calc
        Module.finrank F2
            (packageShearedAllowedBoundarySpace n a (C :: rest) hT I) =
            Module.finrank F2
              (sliceIntersection (Cplus n C) (CoordsList n rest)
                (headShearedOneSliceKernel n C hC
                  (I.childPackage C (by simp)))
                (packageShearedAllowedBoundarySpace n a rest hTail Itail)) := by
              rw [packageShearedAllowedBoundarySpace_cons_eq_sliceIntersection]
              rfl
        _ =
            Module.finrank F2
                (headShearedOneSliceKernel n C hC
                  (I.childPackage C (by simp))) *
              Module.finrank F2
                (packageShearedAllowedBoundarySpace n a rest hTail Itail) := by
              exact finrank_sliceIntersection
                (Cplus n C) (CoordsList n rest)
                (headShearedOneSliceKernel n C hC
                  (I.childPackage C (by simp)))
                (packageShearedAllowedBoundarySpace n a rest hTail Itail)
        _ =
            branchAllowedDim n (RTree.totalWeight C) (Ydim n C hC) *
              Ydim n (RTree.node a rest) hTail := by
              rw [finrank_headShearedOneSliceKernel]
              rw [finrank_packageShearedAllowedBoundarySpace n a rest hTail Itail]
        _ = Ydim n (RTree.node a (C :: rest)) hT := by
              rw [Ydim_eq_YdimCandidate n C hC]
              rw [Ydim_eq_YdimCandidate n (RTree.node a rest) hTail]
              rw [Ydim_eq_YdimCandidate n (RTree.node a (C :: rest)) hT]
              simp [YdimCandidate]

theorem finrank_packageShearedAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Module.finrank F2
      (packageShearedAllowedRootFieldSpace n a cs hT I) =
      Ydim n (RTree.node a cs) hT := by
  rw [packageShearedAllowedRootFieldSpace]
  rw [finrank_submodule_comap_linearEquiv]
  exact finrank_packageShearedAllowedBoundarySpace n a cs hT I

noncomputable instance packageShearedAllowedBoundarySpaceFintype
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype (packageShearedAllowedBoundarySpace n a cs hT I) := by
  classical
  exact Fintype.ofFinite (packageShearedAllowedBoundarySpace n a cs hT I)

noncomputable instance packageShearedAllowedRootFieldSpaceFintype
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype (packageShearedAllowedRootFieldSpace n a cs hT I) := by
  classical
  exact Fintype.ofFinite (packageShearedAllowedRootFieldSpace n a cs hT I)

theorem card_packageShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype.card
      (packageShearedAllowedBoundarySpace n a cs hT I) =
      2 ^ Ydim n (RTree.node a cs) hT := by
  rw [submodule_card_eq_pow_finrank]
  rw [finrank_packageShearedAllowedBoundarySpace]

theorem card_packageShearedAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) :
    Fintype.card
      (packageShearedAllowedRootFieldSpace n a cs hT I) =
      2 ^ Ydim n (RTree.node a cs) hT := by
  rw [submodule_card_eq_pow_finrank]
  rw [finrank_packageShearedAllowedRootFieldSpace]

end Imbalance
end TreeGraph
