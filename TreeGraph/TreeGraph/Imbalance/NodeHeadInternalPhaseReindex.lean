import TreeGraph.Imbalance.NodeHeadPathReindex

namespace TreeGraph
namespace Imbalance

noncomputable def headChildSiteContextOfParent
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    HeadChildSiteContext n a C rest :=
  ((normalSiteClean_node_headEquiv n a C rest hC) site).1

noncomputable def headChildLocalSiteOfParent
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    NormalSiteClean n C :=
  ((normalSiteClean_node_headEquiv n a C rest hC) site).2

theorem normalSiteClean_node_headEquiv_context_local
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    ((normalSiteClean_node_headEquiv n a C rest hC) site) =
      (headChildSiteContextOfParent n a C rest hC site,
        headChildLocalSiteOfParent n a C rest hC site) := by
  rfl

end Imbalance
end TreeGraph
