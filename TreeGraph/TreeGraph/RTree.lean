import TreeGraph.Basic

namespace TreeGraph

inductive RTree where
  | node : Nat → List RTree → RTree
  deriving Repr

namespace RTree

protected def rootWeight : RTree → Nat
  | node a _ => a

protected def children : RTree → List RTree
  | node _ cs => cs

protected def totalWeight : RTree → Nat
  | node a cs => a + (cs.map RTree.totalWeight).sum

protected def numVertices : RTree → Nat
  | node _ cs => 1 + (cs.map RTree.numVertices).sum

protected def PositiveWeights : RTree → Prop
  | node a cs => 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C

end RTree

end TreeGraph
