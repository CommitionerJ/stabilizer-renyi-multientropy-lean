import TreeGraph.Imbalance.NodeTailOpenReduction
import TreeGraph.Imbalance.NodeOpenExponent

namespace TreeGraph
namespace Imbalance

theorem XdimChildContrib_shift_left
    (n a : Nat) :
    ∀ (rest : List RTree) (left shift : Nat),
      XdimChildContrib n a rest (left + shift) =
        n ^ shift * XdimChildContrib n a rest left
  | [], _left, _shift => by
      simp
  | D :: ds, left, shift => by
      rw [XdimChildContrib_cons, XdimChildContrib_cons]
      have hpow :
          n ^ (a + (left + shift) + (ds.map RTree.totalWeight).sum) =
            n ^ shift *
              n ^ (a + left + (ds.map RTree.totalWeight).sum) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hrec :
          XdimChildContrib n a ds ((left + shift) + RTree.totalWeight D) =
            n ^ shift *
              XdimChildContrib n a ds (left + RTree.totalWeight D) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          XdimChildContrib_shift_left n a ds
            (left + RTree.totalWeight D) shift
      rw [hpow, hrec]
      ring

theorem card_Cplus_mul_XdimChildContrib_zero_eq_shifted
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    Fintype.card (Cplus n C) * XdimChildContrib n a rest 0 =
      XdimChildContrib n a rest (RTree.totalWeight C) := by
  rw [card_Cplus]
  simpa using
    (XdimChildContrib_shift_left n a rest 0 (RTree.totalWeight C)).symm

theorem childBranchScalarProduct_pow_card_Cplus_eq_shifted
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    (childBranchScalarProduct n a rest 0) ^ Fintype.card (Cplus n C) =
      childBranchScalarProduct n a rest (RTree.totalWeight C) := by
  rw [childBranchScalarProduct_eq_two_pow_contrib]
  rw [childBranchScalarProduct_eq_two_pow_contrib]
  rw [← pow_mul]
  have hExp :
      XdimChildContrib n a rest 0 * Fintype.card (Cplus n C) =
        XdimChildContrib n a rest (RTree.totalWeight C) := by
    rw [Nat.mul_comm]
    exact card_Cplus_mul_XdimChildContrib_zero_eq_shifted n a C rest
  rw [hExp]

theorem prod_tailOpenAtCplus_eq_if_forall_tailAllowed_card
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if ∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageAllowedRootFieldSpace n a rest hTail Itail then
            ((2 : ℤ) ^ (Xdim n (RTree.node a rest) -
              Ydim n (RTree.node a rest) hTail)) ^
                Fintype.card (Cplus n C)
          else
            0) := by
  classical
  by_cases hall :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageAllowedRootFieldSpace n a rest hTail Itail
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
        exact
          tailOpenSignedSumAtHeadCplus_of_tail_allowed
            n a C rest hTail Itail Wtail root p (hall p)
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
        (tailOpenSignedSumAtHeadCplus_of_tail_notAllowed
          n a C rest hTail Itail Wtail root p hp)

theorem prod_tailOpenAtCplus_eq_if_forall_tailAllowed_unshifted
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if ∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageAllowedRootFieldSpace n a rest hTail Itail then
            (childBranchScalarProduct n a rest 0) ^
                Fintype.card (Cplus n C)
          else
            0) := by
  classical
  rw [prod_tailOpenAtCplus_eq_if_forall_tailAllowed_card
    n a C rest hTail Itail Wtail root]
  by_cases hall :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageAllowedRootFieldSpace n a rest hTail Itail
  · rw [if_pos hall, if_pos hall]
    rw [two_pow_Xdim_sub_Ydim_node_eq_childBranchScalarProduct]
  · rw [if_neg hall, if_neg hall]

theorem prod_tailOpenAtCplus_eq_if_forall_tailAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if ∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageAllowedRootFieldSpace n a rest hTail Itail then
            childBranchScalarProduct n a rest (RTree.totalWeight C)
          else
            0) := by
  classical
  rw [prod_tailOpenAtCplus_eq_if_forall_tailAllowed_unshifted
    n a C rest hTail Itail Wtail root]
  by_cases hall :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageAllowedRootFieldSpace n a rest hTail Itail
  · rw [if_pos hall, if_pos hall]
    rw [childBranchScalarProduct_pow_card_Cplus_eq_shifted]
  · rw [if_neg hall, if_neg hall]

theorem canonical_prod_tailOpenAtCplus_of_parent_root_mem
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage)))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈
        packageAllowedRootFieldSpace n a (C :: rest) hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage) →
      (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
        childBranchScalarProduct n a rest (RTree.totalWeight C) := by
  intro hroot
  have hall :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageAllowedRootFieldSpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT
              (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                n a (C :: rest) hT childPackage)) :=
    ((canonical_root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
      n a C rest hT childPackage root).1 hroot).2
  rw [prod_tailOpenAtCplus_eq_if_forall_tailAllowed
    n a C rest (positiveWeights_node_tail_of_cons hT)
    (nodeTailInputsOfCons n a C rest hT
      (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
        n a (C :: rest) hT childPackage))
    Wtail root]
  rw [if_pos hall]

theorem canonical_parentHeadDataSignedSum_mul_prod_tailOpenAtCplus_eq_if_head_tailAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage)))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentHeadFieldsDataSignedSum n a C rest
        (child_positive_of_node hT C (by simp))
        (childPackage C (by simp)) root *
      (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headAllowedBoundarySpace n a C rest
                (child_positive_of_node hT C (by simp))
                (childPackage C (by simp)) ∧
            (∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageAllowedRootFieldSpace n a rest
                  (positiveWeights_node_tail_of_cons hT)
                  (nodeTailInputsOfCons n a C rest hT
                    (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                      n a (C :: rest) hT childPackage))) then
            (2 : ℤ) ^ branchScalarExponent n a 0 C rest *
              childBranchScalarProduct n a rest (RTree.totalWeight C)
          else
            0) := by
  classical
  have ha : 0 < a := by
    exact rootWeight_pos_of_positiveWeights hT
  by_cases hhead :
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (childPackage C (by simp))
  · by_cases htails :
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageAllowedRootFieldSpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT
              (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                n a (C :: rest) hT childPackage))
    · rw [if_pos ⟨hhead, htails⟩]
      rw [parentHeadFieldsDataSignedSum_of_head_allowed
        n a C rest ha
        (child_positive_of_node hT C (by simp))
        (childPackage C (by simp)) root hhead]
      rw [prod_tailOpenAtCplus_eq_if_forall_tailAllowed
        n a C rest (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage))
        Wtail root]
      rw [if_pos htails]
    · rw [if_neg (by
        intro h
        exact htails h.2)]
      rw [prod_tailOpenAtCplus_eq_if_forall_tailAllowed
        n a C rest (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage))
        Wtail root]
      rw [if_neg htails]
      rw [mul_zero]
  · rw [if_neg (by
      intro h
      exact hhead h.1)]
    rw [parentHeadFieldsDataSignedSum_of_head_notAllowed
      n a C rest
      (child_positive_of_node hT C (by simp))
      (childPackage C (by simp)) root hhead]
    rw [zero_mul]

theorem canonical_parentHeadDataSignedSum_mul_prod_tailOpenAtCplus_eq_if_packageAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D
          (child_positive_of_node hT D hDmem))
    (Wtail :
      NodeOpenPackageStepCertificate n a rest
        (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage)))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    parentHeadFieldsDataSignedSum n a C rest
        (child_positive_of_node hT C (by simp))
        (childPackage C (by simp)) root *
      (∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p)) =
      (by
        classical
        exact
          if root ∈
              packageAllowedRootFieldSpace n a (C :: rest) hT
                (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                  n a (C :: rest) hT childPackage) then
            (2 : ℤ) ^ (Xdim n (RTree.node a (C :: rest)) -
              Ydim n (RTree.node a (C :: rest)) hT)
          else
            0) := by
  classical
  rw [canonical_parentHeadDataSignedSum_mul_prod_tailOpenAtCplus_eq_if_head_tailAllowed
    n a C rest hT childPackage Wtail root]
  by_cases hroot :
      root ∈
        packageAllowedRootFieldSpace n a (C :: rest) hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage)
  · rw [if_pos hroot]
    have hcond :=
      (canonical_root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
        n a C rest hT childPackage root).1 hroot
    rw [if_pos hcond]
    rw [← two_pow_Xdim_sub_Ydim_node_cons_eq_childBranchScalarProduct
      n a C rest hT]
  · rw [if_neg hroot]
    have hnot :
        ¬ (headParentRootBoundaryFieldFromRoot n a C rest root ∈
              headAllowedBoundarySpace n a C rest
                (child_positive_of_node hT C (by simp))
                (childPackage C (by simp)) ∧
            (∀ p : Cplus n C,
              tailRootFieldFromHeadCplus n a C rest root p ∈
                packageAllowedRootFieldSpace n a rest
                  (positiveWeights_node_tail_of_cons hT)
                  (nodeTailInputsOfCons n a C rest hT
                    (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                      n a (C :: rest) hT childPackage)))) := by
      intro hcond
      exact hroot
        ((canonical_root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
          n a C rest hT childPackage root).2 hcond)
    rw [if_neg hnot]

end Imbalance
end TreeGraph
