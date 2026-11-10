import TreeGraph.Imbalance.NodeHeadLocalSite

namespace TreeGraph
namespace Imbalance

def headChildVertexInParent
    {a : Nat} {C : RTree} {rest : List RTree}
    (v : Vertex C) : Vertex (RTree.node a (C :: rest)) :=
  childVertexAtInNode (a := a) (cs := C :: rest) ⟨0, by simp⟩
    ((castVertexOfEq (childAt_cons_zero C rest).symm) v)

@[simp] theorem headChildVertexInParent_addr
    {a : Nat} {C : RTree} {rest : List RTree}
    (v : Vertex C) :
    (headChildVertexInParent (a := a) (C := C) (rest := rest) v).1 =
      0 :: v.1 := by
  simp [headChildVertexInParent, castVertexOfEq]
  rfl

@[simp] theorem headChildVertexInParent_weight
    {a : Nat} {C : RTree} {rest : List RTree}
    (v : Vertex C) :
    Vertex.weight
      (headChildVertexInParent (a := a) (C := C) (rest := rest) v) =
      Vertex.weight v := by
  have hparent :=
    childVertexAtInNode_weight
      (a := a) (cs := C :: rest) ⟨0, by simp⟩
      ((castVertexOfEq (childAt_cons_zero C rest).symm) v)
  have hcast :=
    castVertexOfEq_weight (childAt_cons_zero C rest).symm v
  exact hparent.trans hcast

def headChildNonRootInParent
    {a : Nat} {C : RTree} {rest : List RTree}
    (v : NonRootVertex C) : NonRootVertex (RTree.node a (C :: rest)) :=
  ⟨headChildVertexInParent (a := a) (C := C) (rest := rest) v.1, by
    simp⟩

@[simp] theorem headChildNonRootInParent_addr
    {a : Nat} {C : RTree} {rest : List RTree}
    (v : NonRootVertex C) :
    (headChildNonRootInParent (a := a) (C := C) (rest := rest) v).1.1 =
      0 :: v.1.1 := by
  simp [headChildNonRootInParent]

@[simp] theorem headChildNonRootInParent_weight
    {a : Nat} {C : RTree} {rest : List RTree}
    (v : NonRootVertex C) :
    NonRootVertex.weight
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v) =
      NonRootVertex.weight v := by
  change Vertex.weight
      (headChildVertexInParent (a := a) (C := C) (rest := rest) v.1) =
    Vertex.weight v.1
  exact headChildVertexInParent_weight
    (a := a) (C := C) (rest := rest) v.1

end Imbalance
end TreeGraph
