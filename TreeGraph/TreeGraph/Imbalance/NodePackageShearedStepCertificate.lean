import TreeGraph.Imbalance.NodePackageShearedBoundary
import TreeGraph.Imbalance.NodeConsOpenSumReduction
import TreeGraph.Imbalance.NodeHeadActualShearedPhysicalReduction

namespace TreeGraph
namespace Imbalance

open Classical in
structure NodeShearedOpenPackageStepCertificate
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : NodeOpenPackageStepInputs n a cs hT) where
  open_signed_sum_eq :
    ∀ root : RootFieldAssignmentClean n (RTree.node a cs),
      openNormalSignedSumClean n (RTree.node a cs) root =
        if root ∈ packageShearedAllowedRootFieldSpace n a cs hT I then
          (2 : ℤ) ^ (Xdim n (RTree.node a cs) -
            Ydim n (RTree.node a cs) hT)
        else 0

theorem prod_tailOpenAtCplus_eq_if_forall_tailShearedAllowed_card
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeShearedOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if ∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageShearedAllowedRootFieldSpace n a rest hTail Itail then
            ((2 : ℤ) ^ (Xdim n (RTree.node a rest) -
              Ydim n (RTree.node a rest) hTail)) ^
                Fintype.card (Cplus n C)
          else
            0) := by
  classical
  by_cases hall :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageShearedAllowedRootFieldSpace n a rest hTail Itail
  · rw [if_pos hall]
    calc
      (∏ p : Cplus n C,
          openNormalSignedSumClean n (RTree.node a rest)
            (tailRootFieldFromHeadCplus n a C rest root p)) =
          ∏ _p : Cplus n C,
            (2 : ℤ) ^ (Xdim n (RTree.node a rest) -
              Ydim n (RTree.node a rest) hTail) := by
        apply Finset.prod_congr rfl
        intro p _hp
        rw [Wtail.open_signed_sum_eq]
        rw [if_pos (hall p)]
      _ =
          ((2 : ℤ) ^ (Xdim n (RTree.node a rest) -
            Ydim n (RTree.node a rest) hTail)) ^
              Fintype.card (Cplus n C) := by
        simp
  · rw [if_neg hall]
    rcases not_forall.mp hall with ⟨p, hp⟩
    exact
      Finset.prod_eq_zero
        (s := (Finset.univ : Finset (Cplus n C)))
        (f := fun p : Cplus n C =>
          openNormalSignedSumClean n (RTree.node a rest)
            (tailRootFieldFromHeadCplus n a C rest root p))
        (i := p) (by simp)
        (by
          change
            openNormalSignedSumClean n (RTree.node a rest)
              (tailRootFieldFromHeadCplus n a C rest root p) = 0
          rw [Wtail.open_signed_sum_eq]
          rw [if_neg hp])

theorem prod_tailOpenAtCplus_eq_if_forall_tailShearedAllowed_unshifted
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeShearedOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if ∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageShearedAllowedRootFieldSpace n a rest hTail Itail then
            (childBranchScalarProduct n a rest 0) ^
                Fintype.card (Cplus n C)
          else
            0) := by
  classical
  rw [prod_tailOpenAtCplus_eq_if_forall_tailShearedAllowed_card
    n a C rest hTail Itail Wtail root]
  by_cases hall :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageShearedAllowedRootFieldSpace n a rest hTail Itail
  · rw [if_pos hall, if_pos hall]
    rw [two_pow_Xdim_sub_Ydim_node_eq_childBranchScalarProduct]
  · rw [if_neg hall, if_neg hall]

theorem prod_tailOpenAtCplus_eq_if_forall_tailShearedAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeShearedOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if ∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageShearedAllowedRootFieldSpace n a rest hTail Itail then
            childBranchScalarProduct n a rest (RTree.totalWeight C)
          else
            0) := by
  classical
  rw [prod_tailOpenAtCplus_eq_if_forall_tailShearedAllowed_unshifted
    n a C rest hTail Itail Wtail root]
  by_cases hall :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageShearedAllowedRootFieldSpace n a rest hTail Itail
  · rw [if_pos hall, if_pos hall]
    rw [childBranchScalarProduct_pow_card_Cplus_eq_shifted]
  · rw [if_neg hall, if_neg hall]

theorem canonical_openNormalSignedSumClean_node_cons_eq_if_packageShearedAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeShearedOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a (RTree.node b ds) rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (RTree.node b ds :: rest) hT childPackage)))
    (hPhead :
      (childPackage (RTree.node b ds) (by simp)).IsCanonical)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) :
    openNormalSignedSumClean
        n (RTree.node a (RTree.node b ds :: rest)) root =
      (by
        classical
        exact
          if root ∈
              packageShearedAllowedRootFieldSpace
                n a (RTree.node b ds :: rest) hT
                (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                  n a (RTree.node b ds :: rest) hT childPackage) then
            (2 : ℤ) ^
              (Xdim n (RTree.node a (RTree.node b ds :: rest)) -
                Ydim n (RTree.node a (RTree.node b ds :: rest)) hT)
          else
            0) := by
  classical
  let hC : RTree.PositiveWeights (RTree.node b ds) :=
    child_positive_of_node hT (RTree.node b ds) (by simp)
  let P : OpenNormalCleanPackage n (RTree.node b ds) hC :=
    childPackage (RTree.node b ds) (by simp)
  let I :
      NodeOpenPackageStepInputs n a (RTree.node b ds :: rest) hT :=
    NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
      n a (RTree.node b ds :: rest) hT childPackage
  let Itail :
      NodeOpenPackageStepInputs n a rest
        (positiveWeights_node_tail_of_cons hT) :=
    nodeTailInputsOfCons n a (RTree.node b ds) rest hT I
  let headSum : ℤ :=
    if headParentRootBoundaryFieldFromRoot
        n a (RTree.node b ds) rest root ∈
        headShearedAllowedBoundarySpace
          n a (RTree.node b ds) rest hC P then
      (2 : ℤ) ^
        branchScalarExponent n a 0 (RTree.node b ds) rest
    else
      0
  have hheadSum :
      ∀ tail : ParentOpenTailFields n a (RTree.node b ds) rest,
        parentActualHeadPhaseSignedSumAtTail
            n a (RTree.node b ds) rest root tail =
          headSum := by
    intro tail
    exact
      parentActualHeadPhaseSignedSumAtTail_eq_if_headShearedAllowed_branchScalar_of_canonical
        n a b ds rest (rootWeight_pos_of_positiveWeights hT)
        hC P hPhead root tail
  have hrootIff :
      root ∈ packageShearedAllowedRootFieldSpace
          n a (RTree.node b ds :: rest) hT I ↔
        headParentRootBoundaryFieldFromRoot
            n a (RTree.node b ds) rest root ∈
            headShearedAllowedBoundarySpace
              n a (RTree.node b ds) rest hC P ∧
          ∀ p : Cplus n (RTree.node b ds),
            tailRootFieldFromHeadCplus
              n a (RTree.node b ds) rest root p ∈
              packageShearedAllowedRootFieldSpace
                n a rest (positiveWeights_node_tail_of_cons hT) Itail := by
    simpa [I, Itail, hC, P] using
      (root_mem_packageShearedAllowedRootFieldSpace_iff_head_tailRootRows
        n a (RTree.node b ds) rest hT I
        (by
          simp [I])
        root)
  rw [
    openNormalSignedSumClean_node_cons_eq_headSum_mul_tailSum_of_bridges
      n a (RTree.node b ds) rest root headSum
      (tailOpenProductAtCplus n a (RTree.node b ds) rest root)
      hheadSum
      (by
        intro head tail
        exact parentTailPhaseSiteProductAtHeadTail_eq_tailOpenProductAtCplus
          n a (RTree.node b ds) rest root head tail)]
  rw [sum_tailOpenProductAtCplus_eq_prod_tailOpenAtCplus]
  rw [
    prod_tailOpenAtCplus_eq_if_forall_tailShearedAllowed
      n a (RTree.node b ds) rest
      (positiveWeights_node_tail_of_cons hT) Itail Wtail root]
  dsimp [headSum]
  by_cases hhead :
      headParentRootBoundaryFieldFromRoot
          n a (RTree.node b ds) rest root ∈
          headShearedAllowedBoundarySpace
            n a (RTree.node b ds) rest hC P
  · by_cases htails :
      ∀ p : Cplus n (RTree.node b ds),
        tailRootFieldFromHeadCplus
          n a (RTree.node b ds) rest root p ∈
          packageShearedAllowedRootFieldSpace
            n a rest (positiveWeights_node_tail_of_cons hT) Itail
    · rw [if_pos hhead]
      have htails' :
          ∀ p : Block n b × CoordsList n ds,
            tailRootFieldFromHeadCplus
              n a (RTree.node b ds) rest root p ∈
              packageShearedAllowedRootFieldSpace
                n a rest (positiveWeights_node_tail_of_cons hT) Itail := by
        simpa [Cplus_node] using htails
      rw [if_pos htails']
      have hrootAllowed :
          root ∈
            packageShearedAllowedRootFieldSpace
              n a (RTree.node b ds :: rest) hT
              (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                n a (RTree.node b ds :: rest) hT childPackage) := by
        simpa [I] using (hrootIff).2 ⟨hhead, htails⟩
      rw [if_pos hrootAllowed]
      rw [← two_pow_Xdim_sub_Ydim_node_cons_eq_childBranchScalarProduct
        n a (RTree.node b ds) rest hT]
    · rw [if_pos hhead]
      have htails' :
          ¬ ∀ p : Block n b × CoordsList n ds,
            tailRootFieldFromHeadCplus
              n a (RTree.node b ds) rest root p ∈
              packageShearedAllowedRootFieldSpace
                n a rest (positiveWeights_node_tail_of_cons hT) Itail := by
        intro hall
        exact htails (by simpa [Cplus_node] using hall)
      rw [if_neg htails']
      have hrootNotAllowed :
          root ∉
            packageShearedAllowedRootFieldSpace
              n a (RTree.node b ds :: rest) hT
              (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                n a (RTree.node b ds :: rest) hT childPackage) := by
        intro hroot
        exact htails ((hrootIff).1 (by simpa [I] using hroot)).2
      rw [if_neg (by
        intro hroot
        exact hrootNotAllowed hroot)]
      rw [mul_zero]
  · rw [if_neg hhead]
    rw [zero_mul]
    have hrootNotAllowed :
        root ∉
          packageShearedAllowedRootFieldSpace
            n a (RTree.node b ds :: rest) hT
            (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
              n a (RTree.node b ds :: rest) hT childPackage) := by
      intro hroot
      exact hhead ((hrootIff).1 (by simpa [I] using hroot)).1
    rw [if_neg (by
      intro hroot
      exact hrootNotAllowed hroot)]

end Imbalance
end TreeGraph
