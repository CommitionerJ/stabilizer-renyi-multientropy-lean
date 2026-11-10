import TreeGraph.Imbalance.NodeHeadOpenData
import TreeGraph.Imbalance.NodeHeadBranchCharacterSum

namespace TreeGraph
namespace Imbalance

noncomputable def headChildOpenDataRootMessage
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (_root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (r : RootFieldAssignmentClean n C) :
    P.boundaryMessageSpace :=
  by
    classical
    exact
      if hmem : r ∈ P.openBridge.rootMessageSpace then
        ⟨P.rootCopenBridge.linearEquiv r, by
          have hmap :
              P.rootCopenBridge.linearEquiv r ∈
                P.openBridge.rootMessageSpace.map
                  (P.rootCopenBridge.linearEquiv).toLinearMap := by
            change
              (P.rootCopenBridge.linearEquiv).toLinearMap r ∈
                P.openBridge.rootMessageSpace.map
                  (P.rootCopenBridge.linearEquiv).toLinearMap
            exact Submodule.mem_map_of_mem hmem
          simpa [OpenNormalCleanPackage.boundaryMessageSpace] using hmap⟩
      else
        0

noncomputable def headChildOpenDataBoundaryExponent
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest) : F2 :=
  multiplicityExponent n
    (Q := Block n (a - 1))
    (E := CoordsList n rest)
    (M := P.boundaryMessageSpace)
    (branchMessageCoeff n
      (CoordsList n rest)
      (BranchField n C)
      P.boundaryMessageSpace
      (headChildR n C hC P)
      (headParentRootBranchFieldFromRoot n a C rest root))
    (fun idx =>
      headChildOpenDataRootMessage
        n a C rest hC P root (data idx).1)

noncomputable def headChildOpenDataInternalWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) : ℤ :=
  ∏ idx : HeadChildIndex n a rest,
    weightClean C
      (closeOpenNormalAssignmentClean
        (data idx).1 (data idx).2)

noncomputable def headChildOpenDataSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  by
    classical
    letI : Fintype (HeadChildOpenData n a C rest) := Pi.instFintype
    exact
      ∑ data : HeadChildOpenData n a C rest,
        headChildOpenDataInternalWeight n a C rest data *
          chi (headChildOpenDataBoundaryExponent
            n a C rest hC P root data)

noncomputable def headChildPhysicalSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) : ℤ :=
  headChildOpenDataSignedSum n a C rest hC P root

theorem headChildOpenData_descendant_exponent_eq
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C) :
    Fintype.card (HeadChildIndex n a rest) *
        (Xdim n C - Ydim n C hC) =
      branchDescendantScalarExponent n a 0 C rest hC := by
  rw [card_HeadChildIndex]
  unfold branchDescendantScalarExponent branchMessageFamilyCardFactor
    rootMultiplicityCard visibleExternalCard
  rw [card_Block, card_CoordsList]
  simp [Nat.mul_assoc, Nat.mul_comm]

end Imbalance
end TreeGraph
