import TreeGraph.Imbalance.NodeHeadBoundaryTransport
import TreeGraph.Imbalance.NodeHeadLocalAssignment
import TreeGraph.Imbalance.NodeHeadProjectionBridge
import TreeGraph.Imbalance.OpenNormalPackage

namespace TreeGraph
namespace Imbalance

abbrev HeadChildIndex
    (n a : Nat) [NeZero n] (rest : List RTree) : Type :=
  Block n (a - 1) × CoordsList n rest × Rep n

abbrev HeadChildOpenData
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) : Type :=
  HeadChildIndex n a rest →
    RootFieldAssignmentClean n C × OpenNormalAssignmentClean n C

noncomputable def headChildIndexParentRoot
    {n a : Nat} [NeZero n] {rest : List RTree}
    (idx : HeadChildIndex n a rest) :
    Block n (a - 1) :=
  idx.1

noncomputable def headChildIndexTail
    {n a : Nat} [NeZero n] {rest : List RTree}
    (idx : HeadChildIndex n a rest) :
    CoordsList n rest :=
  idx.2.1

noncomputable def headChildIndexRootDiag
    {n a : Nat} [NeZero n] {rest : List RTree}
    (idx : HeadChildIndex n a rest) :
    Rep n :=
  idx.2.2

noncomputable def headChildRootDomainFromHeadIndexCopen
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest)
    (y : Copen n C) :
    NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm
          (Sum.inl (Vertex.root C)))) :=
  let childCoords := vertexCoordDomainFromBoundaryOpen n C y
  let parentCoords :=
    (parentNonRootCoordsHeadTailEquiv n a C rest).symm
      (childCoords, headChildIndexTail idx)
  { rootCoord := headChildIndexParentRoot idx
    diagonal := headChildIndexRootDiag idx
    otherCoord := fun u => parentCoords u.1 }

noncomputable def headChildRootBoundaryFromParentOpenHead
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (head : ParentOpenHeadFields n a C rest)
    (idx : HeadChildIndex n a rest) :
    BoundaryField n C :=
  fun y =>
    head (Vertex.root C)
      (headChildRootDomainFromHeadIndexCopen n a C rest idx y)

noncomputable def childVertexCoordFromHeadIndexChildDomain
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    VertexCoordDomainClean n C :=
  fun w j => by
    by_cases hroot : w.1 = []
    · have hw : w = Vertex.root C := by
        apply Subtype.ext
        exact hroot
      subst w
      exact
        ((blockSplitLastEquiv n C.rootWeight
            (rootWeight_pos_of_positiveWeights hC)).symm
          (dom.rootCoord, headChildIndexRootDiag idx)) j
    · let wnr : NonRootVertex C := ⟨w, hroot⟩
      by_cases hsame : w.1 = v.1.1
      · exact 0
      · exact dom.otherCoord ⟨wnr, hsame⟩ j

noncomputable def parentHeadNonRootDomainFromChildDomain
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm
          (Sum.inl v.1))) :=
  let childCoords :=
    childVertexCoordFromHeadIndexChildDomain
      n a C rest hC idx v dom
  let parentCoords :=
    (parentNonRootCoordsHeadTailEquiv n a C rest).symm
      (childCoords, headChildIndexTail idx)
  { rootCoord := headChildIndexParentRoot idx
    diagonal := dom.diagonal
    otherCoord := fun u => parentCoords u.1 }

noncomputable def parentOpenHeadFieldsToHeadChildOpenData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (head : ParentOpenHeadFields n a C rest) :
    HeadChildOpenData n a C rest :=
  fun idx =>
    ((P.rootCopenBridge.linearEquiv).symm
      (headChildRootBoundaryFromParentOpenHead n a C rest head idx),
      { nodeField := fun v dom =>
          head v.1
            (parentHeadNonRootDomainFromChildDomain
              n a C rest hC idx v dom) })

theorem parentOpenHeadFieldsToHeadChildOpenData_root_boundary
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (head : ParentOpenHeadFields n a C rest)
    (idx : HeadChildIndex n a rest) :
    P.rootCopenBridge.linearEquiv
        ((parentOpenHeadFieldsToHeadChildOpenData
          n a C rest hC P head idx).1) =
      headChildRootBoundaryFromParentOpenHead
        n a C rest head idx := by
  simp [parentOpenHeadFieldsToHeadChildOpenData]

theorem parentOpenHeadFieldsToHeadChildOpenData_open_projection
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (head : ParentOpenHeadFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    ((parentOpenHeadFieldsToHeadChildOpenData
        n a C rest hC P head idx).2).nodeField v dom =
      head v.1
        (parentHeadNonRootDomainFromChildDomain
          n a C rest hC idx v dom) := by
  rfl

theorem card_HeadChildIndex
    (n a : Nat) [NeZero n] (rest : List RTree) :
    Fintype.card (HeadChildIndex n a rest) =
      Fintype.card (Block n (a - 1)) *
        Fintype.card (CoordsList n rest) * n := by
  unfold HeadChildIndex
  rw [Fintype.card_prod, Fintype.card_prod]
  simp [Rep, ZMod.card, Nat.mul_assoc]

end Imbalance
end TreeGraph
