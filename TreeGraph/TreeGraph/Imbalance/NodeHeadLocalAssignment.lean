import TreeGraph.Imbalance.NodeHeadInternalPhaseReindex
import TreeGraph.Imbalance.NodeChildPhaseDecomposition

namespace TreeGraph
namespace Imbalance

def headChildRootInParent
    {a : Nat} {C : RTree} {rest : List RTree} :
    Vertex (RTree.node a (C :: rest)) :=
  headChildVertexInParent (a := a) (C := C) (rest := rest)
    (Vertex.root C)

@[simp] theorem headChildRootInParent_addr
    {a : Nat} {C : RTree} {rest : List RTree} :
    (headChildRootInParent (a := a) (C := C) (rest := rest)).1 =
      [0] := by
  simp [headChildRootInParent, Vertex.root]

def headChildRootNonRootInParent
    {a : Nat} {C : RTree} {rest : List RTree} :
    NonRootVertex (RTree.node a (C :: rest)) :=
  ⟨headChildRootInParent (a := a) (C := C) (rest := rest), by
    simp⟩

@[simp] theorem headChildRootNonRootInParent_addr
    {a : Nat} {C : RTree} {rest : List RTree} :
    (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)).1.1 =
      [0] := by
  simp [headChildRootNonRootInParent]

noncomputable def headChildLocalRootFieldFromParent
    {n a : Nat} [NeZero n]
    {C : RTree} {rest : List RTree}
    (_hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    RootFieldAssignmentClean n C :=
  fun _ =>
    A.nodeField (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
      (nonRootDomainOfSiteClean site
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) 0)

noncomputable def headChildLocalNodeFieldFromParent
    {n a : Nat} [NeZero n]
    {C : RTree} {rest : List RTree}
    (_hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    NodeFieldAssignmentClean n C :=
  fun v _ =>
    A.nodeField (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
      (nonRootDomainOfSiteClean site
        (headChildNonRootInParent (a := a) (C := C) (rest := rest) v) 0)

noncomputable def headChildLocalNormalAssignmentFromParent
    {n a : Nat} [NeZero n]
    {C : RTree} {rest : List RTree}
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    NormalAssignmentClean n C where
  rootField := headChildLocalRootFieldFromParent hC A site
  nodeField := headChildLocalNodeFieldFromParent hC A site

@[simp] theorem headChildLocalNormalAssignmentFromParent_rootField
    {n a : Nat} [NeZero n]
    {C : RTree} {rest : List RTree}
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (rd : RootFieldDomainClean n C) :
    (headChildLocalNormalAssignmentFromParent hC A site).rootField rd =
      A.nodeField
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
        (nonRootDomainOfSiteClean site
          (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
          0) := by
  rfl

@[simp] theorem headChildLocalNormalAssignmentFromParent_nodeField
    {n a : Nat} [NeZero n]
    {C : RTree} {rest : List RTree}
    (hC : RTree.PositiveWeights C)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) :
    (headChildLocalNormalAssignmentFromParent hC A site).nodeField v dom =
      A.nodeField
        (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
        (nonRootDomainOfSiteClean site
          (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
          0) := by
  rfl

end Imbalance
end TreeGraph
