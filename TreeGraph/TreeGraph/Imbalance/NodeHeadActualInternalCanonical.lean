import TreeGraph.Imbalance.CanonicalPackage
import TreeGraph.Imbalance.NodeHeadActualInternalSelectors
import TreeGraph.Imbalance.NodeHeadInternalWeightPhase

namespace TreeGraph
namespace Imbalance

noncomputable def edgeKetPhaseAtSiteClean
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (e : List Nat × List Nat) : F2 :=
  ketAtPathClean A site e.1 * ketAtPathClean A site e.2

noncomputable def edgeBraPhaseAtSiteClean
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (e : List Nat × List Nat) : F2 :=
  braAtPathClean A site e.1 * braAtPathClean A site e.2

noncomputable def ketPhaseAtSiteClean
    {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T) : F2 :=
  (RTree.edgeList T).map (edgeKetPhaseAtSiteClean A site) |>.sum

noncomputable def braPhaseAtSiteClean
    {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T) : F2 :=
  (RTree.edgeList T).map (edgeBraPhaseAtSiteClean A site) |>.sum

noncomputable def headChildPulledEdgeKetPhaseFromParent
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (e : List Nat × List Nat) : F2 :=
  headChildPulledKetAtPathFromParent A site e.1 *
    headChildPulledKetAtPathFromParent A site e.2

noncomputable def headChildPulledEdgeBraPhaseFromParent
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (e : List Nat × List Nat) : F2 :=
  headChildPulledBraAtPathFromParent A site e.1 *
    headChildPulledBraAtPathFromParent A site e.2

noncomputable def headChildPulledKetPhaseFromParent
    {n a : Nat} [NeZero n] (C : RTree) {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  ((RTree.edgeList C).map
    (headChildPulledEdgeKetPhaseFromParent A site)).sum

noncomputable def headChildPulledBraPhaseFromParent
    {n a : Nat} [NeZero n] (C : RTree) {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  ((RTree.edgeList C).map
    (headChildPulledEdgeBraPhaseFromParent A site)).sum

theorem edgePhaseAtSiteClean_eq_ket_add_bra
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (e : List Nat × List Nat) :
    edgePhaseAtSiteClean A site e =
      edgeKetPhaseAtSiteClean A site e +
        edgeBraPhaseAtSiteClean A site e := by
  rfl

theorem phaseAtSiteClean_eq_ket_add_bra
    {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T) :
    phaseAtSiteClean T A site =
      ketPhaseAtSiteClean T A site + braPhaseAtSiteClean T A site := by
  unfold phaseAtSiteClean ketPhaseAtSiteClean braPhaseAtSiteClean
  rw [← List.sum_map_add]
  rfl

theorem headChildPulledEdgePhaseFromParent_eq_ket_add_bra
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (e : List Nat × List Nat) :
    headChildPulledEdgePhaseFromParent A site e =
      headChildPulledEdgeKetPhaseFromParent A site e +
        headChildPulledEdgeBraPhaseFromParent A site e := by
  rfl

theorem headChildPulledPhaseFromParent_eq_ket_add_bra
    {n a : Nat} [NeZero n] (C : RTree) {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headChildPulledPhaseFromParent C A site =
      headChildPulledKetPhaseFromParent C A site +
        headChildPulledBraPhaseFromParent C A site := by
  unfold headChildPulledPhaseFromParent headChildPulledKetPhaseFromParent
    headChildPulledBraPhaseFromParent
  rw [← List.sum_map_add]
  rfl

theorem ketAtPathClean_root
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T) :
    ketAtPathClean A site [] = A.rootField site.nonRootCoord := by
  unfold ketAtPathClean ketAtVertexClean
  simp

theorem braAtPathClean_root
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T) :
    braAtPathClean A site [] = A.rootField site.nonRootCoord := by
  unfold braAtPathClean braAtVertexClean
  simp

theorem ketAtPathClean_nonRoot
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (v : NonRootVertex T) :
    ketAtPathClean A site v.1.1 =
      A.nodeField v (nonRootDomainOfSiteClean site v 0) := by
  unfold ketAtPathClean ketAtVertexClean
  rw [dif_pos v.1.2]
  rw [dif_neg v.2]

theorem braAtPathClean_nonRoot
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (v : NonRootVertex T) :
    braAtPathClean A site v.1.1 =
      A.nodeField v (nonRootDomainOfSiteClean site v 1) := by
  unfold braAtPathClean braAtVertexClean
  rw [dif_pos v.1.2]
  rw [dif_neg v.2]

theorem parentHeadDiagData_childRootPulledKet_eq_shearedRaw_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    headChildPulledKetAtPathFromParent A site [] =
      ((headTotalShearDataWithBridge n a C rest
        P.rootCopenBridge data)
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx +
            normalSiteCleanCopenTotalDiag n C childSite)).1
        childSite.nonRootCoord := by
  intro head Aopen A site
  rw [parentHeadDiagData_childRootPulledKet_eq_shearedData]
  rw [rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical]
  exact hP

theorem parentHeadDiagData_childRootPulledBra_eq_shearedRaw_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    headChildPulledBraAtPathFromParent A site [] =
      ((headTotalShearDataWithBridge n a C rest
        P.rootCopenBridge data)
        (headChildIndexParentRoot idx,
          headChildIndexTail idx,
          headChildIndexRootDiag idx +
            normalSiteCleanCopenTotalDiag n C childSite + 1)).1
        childSite.nonRootCoord := by
  intro head Aopen A site
  rw [parentHeadDiagData_childRootPulledBra_eq_shearedData]
  rw [rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical]
  exact hP

theorem parentHeadDiagData_childPulledKetAtVertex_eq_shearedLocal_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (p : Vertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let localA :=
      closeOpenNormalAssignmentClean
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite)).1
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite)).2
    headChildPulledKetAtPathFromParent A site p.1 =
      ketAtPathClean localA childSite p.1 := by
  intro head Aopen A site localA
  rcases p with ⟨path, hpath⟩
  by_cases hroot : path = []
  · subst path
    rw [parentHeadDiagData_childRootPulledKet_eq_shearedRaw_of_canonical
      (hP := hP)]
    rw [ketAtPathClean_root]
    rfl
  · let v : NonRootVertex C := ⟨⟨path, hpath⟩, hroot⟩
    change
      headChildPulledKetAtPathFromParent A site v.1.1 =
        ketAtPathClean localA childSite v.1.1
    rw [parentHeadDiagData_childNonRootPulledKet_eq_shearedData]
    rw [ketAtPathClean_nonRoot]
    rfl

theorem parentHeadDiagData_childPulledBraAtVertex_eq_shearedLocal_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (p : Vertex C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let localA :=
      closeOpenNormalAssignmentClean
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite + 1)).1
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite + 1)).2
    headChildPulledBraAtPathFromParent A site p.1 =
      braAtPathClean localA childSite p.1 := by
  intro head Aopen A site localA
  rcases p with ⟨path, hpath⟩
  by_cases hroot : path = []
  · subst path
    rw [parentHeadDiagData_childRootPulledBra_eq_shearedRaw_of_canonical
      (hP := hP)]
    rw [braAtPathClean_root]
    rfl
  · let v : NonRootVertex C := ⟨⟨path, hpath⟩, hroot⟩
    change
      headChildPulledBraAtPathFromParent A site v.1.1 =
        braAtPathClean localA childSite v.1.1
    rw [parentHeadDiagData_childNonRootPulledBra_eq_shearedData]
    rw [braAtPathClean_nonRoot]
    rfl

theorem parentHeadDiagData_childPulledEdgeKet_eq_shearedLocal_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (e : List Nat × List Nat)
    (he : e ∈ RTree.edgeList C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let localA :=
      closeOpenNormalAssignmentClean
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite)).1
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite)).2
    headChildPulledEdgeKetPhaseFromParent A site e =
      edgeKetPhaseAtSiteClean localA childSite e := by
  intro head Aopen A site localA
  rcases e with ⟨u, v⟩
  have hu : u ∈ RTree.addresses C :=
    RTree.edgeList_edge_left_mem_addresses C he
  have hv : v ∈ RTree.addresses C :=
    RTree.edgeList_edge_right_mem_addresses C he
  change
    headChildPulledKetAtPathFromParent A site u *
        headChildPulledKetAtPathFromParent A site v =
      ketAtPathClean localA childSite u *
        ketAtPathClean localA childSite v
  rw [parentHeadDiagData_childPulledKetAtVertex_eq_shearedLocal_of_canonical
    n a C rest hC P hP root data tail idx childSite ⟨u, hu⟩]
  rw [parentHeadDiagData_childPulledKetAtVertex_eq_shearedLocal_of_canonical
    n a C rest hC P hP root data tail idx childSite ⟨v, hv⟩]

theorem parentHeadDiagData_childPulledEdgeBra_eq_shearedLocal_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C)
    (e : List Nat × List Nat)
    (he : e ∈ RTree.edgeList C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let localA :=
      closeOpenNormalAssignmentClean
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite + 1)).1
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite + 1)).2
    headChildPulledEdgeBraPhaseFromParent A site e =
      edgeBraPhaseAtSiteClean localA childSite e := by
  intro head Aopen A site localA
  rcases e with ⟨u, v⟩
  have hu : u ∈ RTree.addresses C :=
    RTree.edgeList_edge_left_mem_addresses C he
  have hv : v ∈ RTree.addresses C :=
    RTree.edgeList_edge_right_mem_addresses C he
  change
    headChildPulledBraAtPathFromParent A site u *
        headChildPulledBraAtPathFromParent A site v =
      braAtPathClean localA childSite u *
        braAtPathClean localA childSite v
  rw [parentHeadDiagData_childPulledBraAtVertex_eq_shearedLocal_of_canonical
    n a C rest hC P hP root data tail idx childSite ⟨u, hu⟩]
  rw [parentHeadDiagData_childPulledBraAtVertex_eq_shearedLocal_of_canonical
    n a C rest hC P hP root data tail idx childSite ⟨v, hv⟩]

theorem parentHeadDiagData_childPulledKetPhase_eq_shearedLocal_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let localA :=
      closeOpenNormalAssignmentClean
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite)).1
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite)).2
    headChildPulledKetPhaseFromParent C A site =
      ketPhaseAtSiteClean C localA childSite := by
  intro head Aopen A site localA
  unfold headChildPulledKetPhaseFromParent ketPhaseAtSiteClean
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact parentHeadDiagData_childPulledEdgeKet_eq_shearedLocal_of_canonical
    n a C rest hC P hP root data tail idx childSite e he

theorem parentHeadDiagData_childPulledBraPhase_eq_shearedLocal_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : HeadChildOpenData n a C rest)
    (tail : ParentOpenTailFields n a C rest)
    (idx : HeadChildIndex n a rest)
    (childSite : NormalSiteClean n C) :
    let head :=
      (parentOpenHeadFieldsEquivHeadChildOpenData
        n a C rest hC P).symm data
    let Aopen :=
      (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
        (head, tail)
    let A := closeOpenNormalAssignmentClean root Aopen
    let site :=
      (normalSiteClean_node_headDiagIndexEquiv
        n a C rest hC).symm (idx, childSite)
    let localA :=
      closeOpenNormalAssignmentClean
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite + 1)).1
        ((headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data)
          (headChildIndexParentRoot idx,
            headChildIndexTail idx,
            headChildIndexRootDiag idx +
              normalSiteCleanCopenTotalDiag n C childSite + 1)).2
    headChildPulledBraPhaseFromParent C A site =
      braPhaseAtSiteClean C localA childSite := by
  intro head Aopen A site localA
  unfold headChildPulledBraPhaseFromParent braPhaseAtSiteClean
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  exact parentHeadDiagData_childPulledEdgeBra_eq_shearedLocal_of_canonical
    n a C rest hC P hP root data tail idx childSite e he

noncomputable def headIndexChildSiteDiagToCopenTotalSuccEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    HeadChildIndex n a rest × NormalSiteClean n C ≃
      HeadChildIndex n a rest × NormalSiteClean n C :=
  (headIndexChildSiteDiagToCopenTotalEquiv n a C rest).trans
    (Equiv.prodCongr
      (headChildIndexRootSuccEquiv n a rest)
      (Equiv.refl (NormalSiteClean n C)))

theorem parentActualHeadDiagInternalKetProduct_eq_shearedKetProduct_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        let head :=
          (parentOpenHeadFieldsEquivHeadChildOpenData
            n a C rest hC P).symm data
        let Aopen :=
          (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail)
        let A := closeOpenNormalAssignmentClean root Aopen
        let site :=
          (normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)
        chi (headChildPulledKetPhaseFromParent C A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (ketPhaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).1
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).2)
            childSite) := by
  classical
  let S := headTotalShearDataWithBridge n a C rest P.rootCopenBridge data
  let e := headIndexChildSiteDiagToCopenTotalEquiv n a C rest
  let w : HeadChildIndex n a rest × NormalSiteClean n C → ℤ :=
    fun P' =>
      chi (ketPhaseAtSiteClean C
        (closeOpenNormalAssignmentClean (S P'.1).1 (S P'.1).2)
        P'.2)
  calc
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        let head :=
          (parentOpenHeadFieldsEquivHeadChildOpenData
            n a C rest hC P).symm data
        let Aopen :=
          (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail)
        let A := closeOpenNormalAssignmentClean root Aopen
        let site :=
          (normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)
        chi (headChildPulledKetPhaseFromParent C A site)) =
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C, w (e (idx, childSite)) := by
          refine Finset.prod_congr rfl ?_
          intro idx _
          refine Finset.prod_congr rfl ?_
          intro childSite _
          dsimp [w, e, S]
          rw [parentHeadDiagData_childPulledKetPhase_eq_shearedLocal_of_canonical
            (hP := hP)]
          rfl
    _ =
        ∏ P' : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e P') := by
          exact
            (Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun childSite : NormalSiteClean n C =>
                  w (e (idx, childSite)))).symm
    _ =
        ∏ P' : HeadChildIndex n a rest × NormalSiteClean n C, w P' := by
          exact Equiv.prod_comp e w
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (ketPhaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).1
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).2)
            childSite) := by
          exact
            Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun childSite : NormalSiteClean n C => w (idx, childSite))

theorem parentActualHeadDiagInternalBraProduct_eq_shearedBraProduct_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        let head :=
          (parentOpenHeadFieldsEquivHeadChildOpenData
            n a C rest hC P).symm data
        let Aopen :=
          (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail)
        let A := closeOpenNormalAssignmentClean root Aopen
        let site :=
          (normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)
        chi (headChildPulledBraPhaseFromParent C A site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (braPhaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).1
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).2)
            childSite) := by
  classical
  let S := headTotalShearDataWithBridge n a C rest P.rootCopenBridge data
  let e := headIndexChildSiteDiagToCopenTotalSuccEquiv n a C rest
  let w : HeadChildIndex n a rest × NormalSiteClean n C → ℤ :=
    fun P' =>
      chi (braPhaseAtSiteClean C
        (closeOpenNormalAssignmentClean (S P'.1).1 (S P'.1).2)
        P'.2)
  calc
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        let head :=
          (parentOpenHeadFieldsEquivHeadChildOpenData
            n a C rest hC P).symm data
        let Aopen :=
          (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
            (head, tail)
        let A := closeOpenNormalAssignmentClean root Aopen
        let site :=
          (normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)
        chi (headChildPulledBraPhaseFromParent C A site)) =
        ∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C, w (e (idx, childSite)) := by
          refine Finset.prod_congr rfl ?_
          intro idx _
          refine Finset.prod_congr rfl ?_
          intro childSite _
          dsimp [w, e, headIndexChildSiteDiagToCopenTotalSuccEquiv, S]
          rw [parentHeadDiagData_childPulledBraPhase_eq_shearedLocal_of_canonical
            (hP := hP)]
          rfl
    _ =
        ∏ P' : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e P') := by
          exact
            (Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun childSite : NormalSiteClean n C =>
                  w (e (idx, childSite)))).symm
    _ =
        ∏ P' : HeadChildIndex n a rest × NormalSiteClean n C, w P' := by
          exact Equiv.prod_comp e w
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (braPhaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).1
              ((headTotalShearDataWithBridge n a C rest
                P.rootCopenBridge data) idx).2)
            childSite) := by
          exact
            Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun childSite : NormalSiteClean n C => w (idx, childSite))

theorem headChildOpenDataInternalWeight_totalShearWithBridge_eq_ket_mul_bra
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest) :
    headChildOpenDataInternalWeight n a C rest
        (headTotalShearDataWithBridge n a C rest B data) =
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (ketPhaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge n a C rest B data) idx).1
              ((headTotalShearDataWithBridge n a C rest B data) idx).2)
            childSite)) *
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (braPhaseAtSiteClean C
            (closeOpenNormalAssignmentClean
              ((headTotalShearDataWithBridge n a C rest B data) idx).1
              ((headTotalShearDataWithBridge n a C rest B data) idx).2)
            childSite)) := by
  classical
  rw [headChildOpenDataInternalWeight_totalShearWithBridge_eq_prod_phase_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro idx _
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro childSite _
  rw [phaseAtSiteClean_eq_ket_add_bra]
  rw [chi_add]

theorem parentActualHeadDiagInternalProductAtTail_eq_shearedInternalWeight_of_canonical
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (hP : P.IsCanonical)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : ParentOpenTailFields n a C rest)
    (data : HeadChildOpenData n a C rest) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headInternalPhaseAtSiteClean_node C rest
          (closeOpenNormalAssignmentClean root
            ((openNormalAssignmentCleanEquivHeadTail
              n a C rest).symm
              ((parentOpenHeadFieldsEquivHeadChildOpenData
                n a C rest hC P).symm data, tail)))
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)))) =
      headChildOpenDataInternalWeight
        n a C rest
        (headTotalShearDataWithBridge n a C rest
          P.rootCopenBridge data) := by
  classical
  let head :=
    (parentOpenHeadFieldsEquivHeadChildOpenData
      n a C rest hC P).symm data
  let Aopen :=
    (openNormalAssignmentCleanEquivHeadTail n a C rest).symm
      (head, tail)
  let A := closeOpenNormalAssignmentClean root Aopen
  let S := headTotalShearDataWithBridge n a C rest P.rootCopenBridge data
  have hsplit :
      (∏ idx : HeadChildIndex n a rest,
        ∏ childSite : NormalSiteClean n C,
          chi (headInternalPhaseAtSiteClean_node C rest A
            ((normalSiteClean_node_headDiagIndexEquiv
              n a C rest hC).symm (idx, childSite)))) =
        (∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (headChildPulledKetPhaseFromParent C A
              ((normalSiteClean_node_headDiagIndexEquiv
                n a C rest hC).symm (idx, childSite)))) *
        (∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (headChildPulledBraPhaseFromParent C A
              ((normalSiteClean_node_headDiagIndexEquiv
                n a C rest hC).symm (idx, childSite)))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro idx _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro childSite _
    rw [headInternalPhaseAtSiteClean_node_eq_child_local n a C rest hC]
    rw [headChildPulledPhaseFromParent_eq_ket_add_bra]
    rw [chi_add]
  calc
    (∏ idx : HeadChildIndex n a rest,
      ∏ childSite : NormalSiteClean n C,
        chi (headInternalPhaseAtSiteClean_node C rest
          (closeOpenNormalAssignmentClean root
            ((openNormalAssignmentCleanEquivHeadTail
              n a C rest).symm
              ((parentOpenHeadFieldsEquivHeadChildOpenData
                n a C rest hC P).symm data, tail)))
          ((normalSiteClean_node_headDiagIndexEquiv
            n a C rest hC).symm (idx, childSite)))) =
        (∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (ketPhaseAtSiteClean C
              (closeOpenNormalAssignmentClean (S idx).1 (S idx).2)
              childSite)) *
        (∏ idx : HeadChildIndex n a rest,
          ∏ childSite : NormalSiteClean n C,
            chi (braPhaseAtSiteClean C
              (closeOpenNormalAssignmentClean (S idx).1 (S idx).2)
              childSite)) := by
          change
            (∏ idx : HeadChildIndex n a rest,
              ∏ childSite : NormalSiteClean n C,
                chi (headInternalPhaseAtSiteClean_node C rest A
                  ((normalSiteClean_node_headDiagIndexEquiv
                    n a C rest hC).symm (idx, childSite)))) =
              _
          rw [hsplit]
          rw [parentActualHeadDiagInternalKetProduct_eq_shearedKetProduct_of_canonical
            n a C rest hC P hP root tail data]
          rw [parentActualHeadDiagInternalBraProduct_eq_shearedBraProduct_of_canonical
            n a C rest hC P hP root tail data]
    _ =
        headChildOpenDataInternalWeight n a C rest S := by
          rw [headChildOpenDataInternalWeight_totalShearWithBridge_eq_ket_mul_bra]

end Imbalance
end TreeGraph
