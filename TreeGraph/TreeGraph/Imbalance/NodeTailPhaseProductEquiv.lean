import TreeGraph.Imbalance.NodeTailOpenDataEquiv
import TreeGraph.Imbalance.NodeHeadPhaseProduct

namespace TreeGraph
namespace Imbalance

noncomputable def tailOpenProductAtCplus
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest) : ℤ :=
  ∏ p : Cplus n C,
    weightClean (RTree.node a rest)
      (closeOpenNormalAssignmentClean
        (tailRootFieldFromHeadCplus n a C rest root p)
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest tail) p))

private theorem sum_pi_prod_factorized
    {ι α : Type} [DecidableEq ι] [Fintype ι] [Fintype α]
    (w : ι → α → ℤ) :
    (∑ f : ι → α, ∏ i : ι, w i (f i)) =
      ∏ i : ι, ∑ x : α, w i x := by
  classical
  have h :=
    Finset.prod_univ_sum
      (fun _ : ι => (Finset.univ : Finset α))
      (fun i x => w i x)
  simpa [Finset.univ_pi_univ] using h.symm

theorem tailOpenProductAtCplus_equiv_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : TailOpenByCplus n a C rest) :
    tailOpenProductAtCplus n a C rest root
        ((parentOpenTailFieldsEquivTailOpenByCplus n a C rest).symm data) =
      ∏ p : Cplus n C,
        weightClean (RTree.node a rest)
          (closeOpenNormalAssignmentClean
            (tailRootFieldFromHeadCplus n a C rest root p)
            (data p)) := by
  classical
  unfold tailOpenProductAtCplus
  let e := parentOpenTailFieldsEquivTailOpenByCplus n a C rest
  refine Finset.prod_congr rfl ?_
  intro p _
  have hp := congrFun (e.right_inv data) p
  change
    weightClean (RTree.node a rest)
        (closeOpenNormalAssignmentClean
          (tailRootFieldFromHeadCplus n a C rest root p)
          (e (e.symm data) p)) =
      weightClean (RTree.node a rest)
        (closeOpenNormalAssignmentClean
          (tailRootFieldFromHeadCplus n a C rest root p)
          (data p))
  exact congrArg
    (fun A : OpenNormalAssignmentClean n (RTree.node a rest) =>
      weightClean (RTree.node a rest)
        (closeOpenNormalAssignmentClean
          (tailRootFieldFromHeadCplus n a C rest root p) A)) hp

theorem sum_tailOpenProductAtCplus_eq_prod_tailOpenAtCplus
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    (∑ tail : ParentOpenTailFields n a C rest,
        tailOpenProductAtCplus n a C rest root tail) =
      ∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p) := by
  classical
  let e := parentOpenTailFieldsEquivTailOpenByCplus n a C rest
  let w :
      Cplus n C → OpenNormalAssignmentClean n (RTree.node a rest) → ℤ :=
    fun p A =>
      weightClean (RTree.node a rest)
        (closeOpenNormalAssignmentClean
          (tailRootFieldFromHeadCplus n a C rest root p) A)
  calc
    (∑ tail : ParentOpenTailFields n a C rest,
        tailOpenProductAtCplus n a C rest root tail) =
        ∑ data : TailOpenByCplus n a C rest,
          tailOpenProductAtCplus n a C rest root (e.symm data) := by
          exact (Equiv.sum_comp e.symm
            (fun tail : ParentOpenTailFields n a C rest =>
              tailOpenProductAtCplus n a C rest root tail)).symm
    _ =
        ∑ data : TailOpenByCplus n a C rest,
          ∏ p : Cplus n C, w p (data p) := by
          refine Finset.sum_congr rfl ?_
          intro data _
          rw [tailOpenProductAtCplus_equiv_symm]
    _ =
        ∏ p : Cplus n C,
          ∑ A : OpenNormalAssignmentClean n (RTree.node a rest), w p A := by
          exact sum_pi_prod_factorized w
    _ =
        ∏ p : Cplus n C,
          openNormalSignedSumClean n (RTree.node a rest)
            (tailRootFieldFromHeadCplus n a C rest root p) := by
          rfl

theorem parentOpenTailPhaseSignedSumAtHead_eq_prod_tailOpenAtCplus_of_phaseProduct
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (head : ParentOpenHeadFields n a C rest)
    (hphase :
      ∀ tail : ParentOpenTailFields n a C rest,
        parentTailPhaseSiteProductAtHeadTail n a C rest root head tail =
          tailOpenProductAtCplus n a C rest root tail) :
    parentOpenTailPhaseSignedSumAtHead n a C rest root head =
      ∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p) := by
  classical
  rw [parentOpenTailPhaseSignedSumAtHead_eq_sum_tailSiteProduct]
  calc
    (∑ tail : ParentOpenTailFields n a C rest,
        parentTailPhaseSiteProductAtHeadTail n a C rest root head tail) =
        ∑ tail : ParentOpenTailFields n a C rest,
          tailOpenProductAtCplus n a C rest root tail := by
          refine Finset.sum_congr rfl ?_
          intro tail _
          exact hphase tail
    _ =
      ∏ p : Cplus n C,
        openNormalSignedSumClean n (RTree.node a rest)
          (tailRootFieldFromHeadCplus n a C rest root p) := by
        exact sum_tailOpenProductAtCplus_eq_prod_tailOpenAtCplus
          n a C rest root

end Imbalance
end TreeGraph
