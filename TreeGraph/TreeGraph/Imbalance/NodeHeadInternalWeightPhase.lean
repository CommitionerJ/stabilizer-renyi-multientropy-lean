import TreeGraph.Imbalance.NodeHeadTotalSiteShear
import TreeGraph.Imbalance.NodeHeadPhysicalReduction

namespace TreeGraph
namespace Imbalance

theorem headChildOpenDataInternalWeight_eq_prod_phase
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataInternalWeight n a C rest data =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          chi (phaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              (data idx).1 (data idx).2) site) := by
  classical
  unfold headChildOpenDataInternalWeight weightClean totalPhaseClean
  refine Finset.prod_congr rfl ?_
  intro idx _
  exact chi_sum_univ_apply
    (fun site : NormalSiteClean n C =>
      phaseAtSiteClean C
        (closeOpenNormalAssignmentClean (data idx).1 (data idx).2) site)

theorem headChildOpenDataInternalWeight_totalShearWithBridge_eq_prod_phase
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataInternalWeight n a C rest
        (headTotalShearDataWithBridge n a C rest B data) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          chi (phaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge
                n a C rest B data idx).1)
              ((headTotalShearDataWithBridge
                n a C rest B data idx).2)) site) := by
  rw [headChildOpenDataInternalWeight_eq_prod_phase]

theorem headChildOpenDataInternalWeight_totalShearWithBridge_eq_prod_phase_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataInternalWeight n a C rest
        (headTotalShearDataWithBridge n a C rest B data) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          chi (phaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge n a C rest B data) idx).1
              ((headTotalShearDataWithBridge n a C rest B data) idx).2)
            site) := by
  rw [headChildOpenDataInternalWeight_eq_prod_phase]

end Imbalance
end TreeGraph
