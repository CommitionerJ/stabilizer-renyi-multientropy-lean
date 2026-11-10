import TreeGraph.Imbalance.VertexCplusEquiv

namespace TreeGraph
namespace Imbalance

noncomputable def rootFieldDomainCleanEquivCopen_node
    (n a : Nat) [NeZero n] (cs : List RTree) :
    RootFieldDomainClean n (RTree.node a cs) ≃ CoordsList n cs :=
  (rootFieldDomainCleanEquivNodeChildVertex n a cs).trans
    (nodeChildVertexCoordsEquivCoordsList n cs)

noncomputable def rootFieldDomainCleanEquivCopen
    (n : Nat) [NeZero n] :
    (T : RTree) → RootFieldDomainClean n T ≃ Copen n T
  | RTree.node a cs => rootFieldDomainCleanEquivCopen_node n a cs

namespace RootFieldCleanCopenBridge

noncomputable def ofTree
    (n : Nat) [NeZero n] (T : RTree) :
    RootFieldCleanCopenBridge n T where
  domEquiv := rootFieldDomainCleanEquivCopen n T

noncomputable def node
    (n a : Nat) [NeZero n] (cs : List RTree) :
    RootFieldCleanCopenBridge n (RTree.node a cs) :=
  ofTree n (RTree.node a cs)

end RootFieldCleanCopenBridge

end Imbalance
end TreeGraph
