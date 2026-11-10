import TreeGraph.Imbalance.NodeCanonicalProjection

namespace TreeGraph
namespace Imbalance

theorem tailRootFieldFromHeadCplus_nil_mem_packageAllowed
    (n a : Nat) [NeZero n]
    (C : RTree)
    (hTail : RTree.PositiveWeights (RTree.node a []))
    (Itail : NodeOpenPackageStepInputs n a [] hTail)
    (root : RootFieldAssignmentClean n (RTree.node a [C]))
    (p : Cplus n C) :
    tailRootFieldFromHeadCplus n a C [] root p ∈
        packageAllowedRootFieldSpace n a [] hTail Itail := by
  exact
    mem_packageAllowedRootFieldSpace_nil n a hTail Itail
      (tailRootFieldFromHeadCplus n a C [] root p)

theorem tailOpenSignedSumAtHeadCplus_nil
    (n a : Nat) [NeZero n]
    (C : RTree)
    (root : RootFieldAssignmentClean n (RTree.node a [C]))
    (p : Cplus n C) :
    openNormalSignedSumClean n (RTree.node a [])
        (tailRootFieldFromHeadCplus n a C [] root p) = 1 := by
  rw [openNormalSignedSumClean_leaf]

theorem tailOpenSignedSumAtHeadCplus_nil_eq_openScalar
    (n a : Nat) [NeZero n]
    (C : RTree)
    (hTail : RTree.PositiveWeights (RTree.node a []))
    (root : RootFieldAssignmentClean n (RTree.node a [C]))
    (p : Cplus n C) :
    openNormalSignedSumClean n (RTree.node a [])
        (tailRootFieldFromHeadCplus n a C [] root p) =
      (2 : ℤ) ^ (Xdim n (RTree.node a []) -
        Ydim n (RTree.node a []) hTail) := by
  rw [tailOpenSignedSumAtHeadCplus_nil]
  have hX : Xdim n (RTree.node a []) = 1 := Xdim_leaf n a
  have hY : Ydim n (RTree.node a []) hTail = 1 := by
    rw [Ydim_eq_YdimCandidate, YdimCandidate_leaf]
  rw [hX, hY]
  norm_num

theorem tailOpenSignedSumAtHeadCplus_eq_if
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C) :
    openNormalSignedSumClean n (RTree.node a rest)
        (tailRootFieldFromHeadCplus n a C rest root p) =
      (by
        classical
        exact
          if tailRootFieldFromHeadCplus n a C rest root p ∈
              packageAllowedRootFieldSpace n a rest hTail Itail then
            (2 : ℤ) ^ (Xdim n (RTree.node a rest) -
              Ydim n (RTree.node a rest) hTail)
          else 0) := by
  classical
  exact Wtail.open_signed_sum_eq
    (tailRootFieldFromHeadCplus n a C rest root p)

theorem tailOpenSignedSumAtHeadCplus_of_tail_allowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C) :
    tailRootFieldFromHeadCplus n a C rest root p ∈
        packageAllowedRootFieldSpace n a rest hTail Itail →
      openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p) =
        (2 : ℤ) ^ (Xdim n (RTree.node a rest) -
          Ydim n (RTree.node a rest) hTail) := by
  classical
  intro hmem
  rw [tailOpenSignedSumAtHeadCplus_eq_if n a C rest hTail Itail Wtail]
  rw [if_pos hmem]

theorem tailOpenSignedSumAtHeadCplus_of_tail_notAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hTail : RTree.PositiveWeights (RTree.node a rest))
    (Itail : NodeOpenPackageStepInputs n a rest hTail)
    (Wtail : NodeOpenPackageStepCertificate n a rest hTail Itail)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C) :
    tailRootFieldFromHeadCplus n a C rest root p ∉
        packageAllowedRootFieldSpace n a rest hTail Itail →
      openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p) = 0 := by
  classical
  intro hmem
  rw [tailOpenSignedSumAtHeadCplus_eq_if n a C rest hTail Itail Wtail]
  rw [if_neg hmem]

theorem canonical_tailOpenSignedSumAtHeadCplus_of_parent_root_mem
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
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C) :
    root ∈
        packageAllowedRootFieldSpace n a (C :: rest) hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (C :: rest) hT childPackage) →
      openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p) =
        (2 : ℤ) ^ (Xdim n (RTree.node a rest) -
          Ydim n (RTree.node a rest)
            (positiveWeights_node_tail_of_cons hT)) := by
  intro hroot
  have htailAllowed :
      tailRootFieldFromHeadCplus n a C rest root p ∈
        packageAllowedRootFieldSpace n a rest
          (positiveWeights_node_tail_of_cons hT)
          (nodeTailInputsOfCons n a C rest hT
            (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
              n a (C :: rest) hT childPackage)) :=
    ((canonical_root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
      n a C rest hT childPackage root).1 hroot).2 p
  exact
    tailOpenSignedSumAtHeadCplus_of_tail_allowed
      n a C rest (positiveWeights_node_tail_of_cons hT)
      (nodeTailInputsOfCons n a C rest hT
        (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
          n a (C :: rest) hT childPackage))
      Wtail root p htailAllowed

end Imbalance
end TreeGraph
