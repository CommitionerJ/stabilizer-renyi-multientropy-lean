import TreeGraph.Imbalance.NodeHeadBoundaryPairing

namespace TreeGraph
namespace Imbalance

@[simp] theorem nonRootVertexNodeEquivChildVertex_childVertexAtAsNonRootInNode
    {a : Nat} {cs : List RTree} (p : NodeChildVertex cs) :
    (nonRootVertexNodeEquivChildVertex a cs)
      (childVertexAtAsNonRootInNode (a := a) p) = p := by
  exact (nonRootVertexNodeEquivChildVertex a cs).right_inv p

theorem rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child
    (n a : Nat) [NeZero n]
    (cs : List RTree)
    (F : (p : NodeChildVertex cs) → Fin (Vertex.weight p.2) → Rep n)
    (p : NodeChildVertex cs)
    (j : Fin (Vertex.weight p.2)) :
    ((rootFieldDomainCleanEquivNodeChildVertex n a cs).symm F)
      (childVertexAtAsNonRootInNode (a := a) p)
      (Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p).symm j) =
    F p j := by
  let rd := (rootFieldDomainCleanEquivNodeChildVertex n a cs).symm F
  have h :=
    Equiv.apply_symm_apply
      (rootFieldDomainCleanEquivNodeChildVertex n a cs) F
  change (rootFieldDomainCleanEquivNodeChildVertex n a cs) rd = F at h
  have hpj := congrFun (congrFun h p) j
  have hleft :
      rd (childVertexAtAsNonRootInNode (a := a) p)
        (Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p).symm j) =
      (rootFieldDomainCleanEquivNodeChildVertex n a cs) rd p j := by
    simp [rd, rootFieldDomainCleanEquivNodeChildVertex, finCastEquivOfEqClean]
    let q := (nonRootVertexNodeEquivChildVertex a cs)
      (childVertexAtAsNonRootInNode (a := a) p)
    let k : Fin (Vertex.weight q.2) :=
      Fin.cast (by
        dsimp [q]
        exact (Eq.trans (childVertexAtAsNonRootInNode_weight (a := a) p).symm
          (nonRootVertexNodeEquivChildVertex_weight
            (a := a) (cs := cs)
            (childVertexAtAsNonRootInNode (a := a) p)))) j
    change (fun x : Sigma fun q : NodeChildVertex cs =>
        Fin (Vertex.weight q.2) => F x.1 x.2) ⟨q, k⟩ =
      (fun x : Sigma fun q : NodeChildVertex cs =>
        Fin (Vertex.weight q.2) => F x.1 x.2) ⟨p, j⟩
    have hp : q = p := by
      dsimp [q]
      exact (nonRootVertexNodeEquivChildVertex a cs).right_inv p
    have hpair :
        (⟨q, k⟩ : Sigma fun q : NodeChildVertex cs =>
          Fin (Vertex.weight q.2)) = ⟨p, j⟩ := by
      apply Sigma.ext hp
      subst q
      dsimp [k]
      convert heq_of_eq (Fin.cast_eq_self j)
    rw [hpair]
  exact hleft.trans hpj

theorem rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child_of_eq
    (n a : Nat) [NeZero n]
    (cs : List RTree)
    (F : (p : NodeChildVertex cs) → Fin (Vertex.weight p.2) → Rep n)
    (p : NodeChildVertex cs)
    (u : NonRootVertex (RTree.node a cs))
    (hu : childVertexAtAsNonRootInNode (a := a) p = u)
    (j : Fin (NonRootVertex.weight u)) :
    ((rootFieldDomainCleanEquivNodeChildVertex n a cs).symm F) u j =
    F p (Fin.cast (by
      rw [← hu]
      exact childVertexAtAsNonRootInNode_weight (a := a) p) j) := by
  subst u
  let jp : Fin (Vertex.weight p.2) :=
    Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p) j
  have hidx :
      Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p).symm jp = j := by
    dsimp [jp]
  calc
    ((rootFieldDomainCleanEquivNodeChildVertex n a cs).symm F)
        (childVertexAtAsNonRootInNode (a := a) p) j =
      ((rootFieldDomainCleanEquivNodeChildVertex n a cs).symm F)
        (childVertexAtAsNonRootInNode (a := a) p)
        (Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p).symm jp) := by
          rw [hidx]
    _ = F p jp :=
      rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child n a cs F p jp
    _ = F p (Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p) j) := rfl

theorem nodeChildVertexCoordsEquivSum_symm_inl
    (n : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (F : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n)
    (v : Vertex C) (j : Fin (Vertex.weight v)) :
    ((nodeChildVertexCoordsEquivSum n C rest).symm F)
      ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))
      (Fin.cast
        (nodeChildVertexConsEquiv_weight
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))).symm j) =
    F (Sum.inl v) j := by
  let G := (nodeChildVertexCoordsEquivSum n C rest).symm F
  have h :=
    Equiv.apply_symm_apply (nodeChildVertexCoordsEquivSum n C rest) F
  change (nodeChildVertexCoordsEquivSum n C rest) G = F at h
  have hvj := congrFun (congrFun h (Sum.inl v)) j
  have hleft :
      G ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))
        (Fin.cast
          (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))).symm j) =
      (nodeChildVertexCoordsEquivSum n C rest) G (Sum.inl v) j := by
    simp [G, nodeChildVertexCoordsEquivSum, finCastEquivOfEqClean]
    let q := (nodeChildVertexConsEquiv C rest)
      ((nodeChildVertexConsEquiv C rest).symm (Sum.inl v))
    let k : Fin (nodeChildVertexSumWeight q) := by
      dsimp [q, nodeChildVertexConsEquiv]
      exact j
    change (fun x : Sigma fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) => F x.1 x.2) ⟨q, k⟩ =
      (fun x : Sigma fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) => F x.1 x.2) ⟨Sum.inl v, j⟩
    have hq : q = Sum.inl v := by
      dsimp [q]
      exact Equiv.apply_symm_apply
        (nodeChildVertexConsEquiv C rest) (Sum.inl v)
    have hpair :
        (⟨q, k⟩ : Sigma fun s : Vertex C ⊕ NodeChildVertex rest =>
          Fin (nodeChildVertexSumWeight s)) = ⟨Sum.inl v, j⟩ := by
      apply Sigma.ext hq
      subst q
      dsimp [k]
      exact heq_of_eq (Fin.cast_eq_self j)
    rw [hpair]
  exact hleft.trans hvj

theorem nodeChildVertexCoordsEquivSum_symm_inr
    (n : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (F : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n)
    (p : NodeChildVertex rest) (j : Fin (Vertex.weight p.2)) :
    ((nodeChildVertexCoordsEquivSum n C rest).symm F)
      ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))
      (Fin.cast
        (nodeChildVertexConsEquiv_weight
          ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm j) =
    F (Sum.inr p) j := by
  let G := (nodeChildVertexCoordsEquivSum n C rest).symm F
  have h :=
    Equiv.apply_symm_apply (nodeChildVertexCoordsEquivSum n C rest) F
  change (nodeChildVertexCoordsEquivSum n C rest) G = F at h
  have hpj := congrFun (congrFun h (Sum.inr p)) j
  have hleft :
      G ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))
        (Fin.cast
          (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm j) =
      (nodeChildVertexCoordsEquivSum n C rest) G (Sum.inr p) j := by
    simp [G, nodeChildVertexCoordsEquivSum, finCastEquivOfEqClean]
    let q := (nodeChildVertexConsEquiv C rest)
      ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))
    let k : Fin (nodeChildVertexSumWeight q) := by
      dsimp [q, nodeChildVertexConsEquiv]
      exact j
    change (fun x : Sigma fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) => F x.1 x.2) ⟨q, k⟩ =
      (fun x : Sigma fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) => F x.1 x.2) ⟨Sum.inr p, j⟩
    have hq : q = Sum.inr p := by
      dsimp [q]
      exact Equiv.apply_symm_apply
        (nodeChildVertexConsEquiv C rest) (Sum.inr p)
    have hpair :
        (⟨q, k⟩ : Sigma fun s : Vertex C ⊕ NodeChildVertex rest =>
          Fin (nodeChildVertexSumWeight s)) = ⟨Sum.inr p, j⟩ := by
      apply Sigma.ext hq
      subst q
      dsimp [k]
      exact heq_of_eq (Fin.cast_eq_self j)
    rw [hpair]
  exact hleft.trans hpj

theorem nodeChildVertexCoordsEquivSum_symm_apply_of_eq
    (n : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (F : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n)
    (p : NodeChildVertex (C :: rest))
    (s : Vertex C ⊕ NodeChildVertex rest)
    (hs : (nodeChildVertexConsEquiv C rest) p = s)
    (j : Fin (Vertex.weight p.2)) :
    ((nodeChildVertexCoordsEquivSum n C rest).symm F) p j =
    F s (Fin.cast (by
      rw [← hs]
      exact nodeChildVertexConsEquiv_weight (C := C) (rest := rest) p) j) := by
  subst s
  let js : Fin (nodeChildVertexSumWeight ((nodeChildVertexConsEquiv C rest) p)) :=
    Fin.cast (nodeChildVertexConsEquiv_weight (C := C) (rest := rest) p) j
  have hidx :
      Fin.cast (nodeChildVertexConsEquiv_weight (C := C) (rest := rest) p).symm js = j := by
    dsimp [js]
  calc
    ((nodeChildVertexCoordsEquivSum n C rest).symm F) p j =
      ((nodeChildVertexCoordsEquivSum n C rest).symm F) p
        (Fin.cast
          (nodeChildVertexConsEquiv_weight (C := C) (rest := rest) p).symm js) := by
          rw [hidx]
    _ = F ((nodeChildVertexConsEquiv C rest) p) js := by
      let G := (nodeChildVertexCoordsEquivSum n C rest).symm F
      have h :=
        Equiv.apply_symm_apply (nodeChildVertexCoordsEquivSum n C rest) F
      change (nodeChildVertexCoordsEquivSum n C rest) G = F at h
      have hjs := congrFun (congrFun h ((nodeChildVertexConsEquiv C rest) p)) js
      have hleft :
          G p (Fin.cast
              (nodeChildVertexConsEquiv_weight (C := C) (rest := rest) p).symm js) =
          (nodeChildVertexCoordsEquivSum n C rest) G
            ((nodeChildVertexConsEquiv C rest) p) js := by
        simp [G, nodeChildVertexCoordsEquivSum, finCastEquivOfEqClean]
      exact hleft.trans hjs
    _ = F ((nodeChildVertexConsEquiv C rest) p)
        (Fin.cast (nodeChildVertexConsEquiv_weight (C := C) (rest := rest) p) j) := rfl

theorem vertexCoordDomainFromBoundaryOpen_apply_nonroot
    (n : Nat) [NeZero n]
    (T : RTree) (y : Copen n T)
    (v : NonRootVertex T)
    (j : Fin (NonRootVertex.weight v)) :
    vertexCoordDomainFromBoundaryOpen n T y v.1 j =
      ((rootFieldDomainCleanEquivCopen n T).symm y) v j := by
  cases T with
  | node b cs =>
      let f := vertexCoordDomainFromBoundaryOpen n (RTree.node b cs) y
      let rd := (rootFieldDomainCleanEquivCopen n (RTree.node b cs)).symm y
      have h :=
        Equiv.apply_symm_apply
          (vertexCoordDomainEquivCplus n (RTree.node b cs))
          ((fun _ => 0), y)
      change (vertexCoordDomainEquivCplus n (RTree.node b cs)) f =
          ((fun _ => 0), y) at h
      have h2 := congrArg Prod.snd h
      change ((rootFieldDomainCleanEquivNodeChildVertex n b cs).trans
          (nodeChildVertexCoordsEquivCoordsList n cs))
            ((vertexCoordDomainNodeEquivBlockNonRoot n b cs f).2) = y at h2
      have hrd :
          ((rootFieldDomainCleanEquivNodeChildVertex n b cs).trans
            (nodeChildVertexCoordsEquivCoordsList n cs)) rd = y := by
        dsimp [rd, rootFieldDomainCleanEquivCopen,
          rootFieldDomainCleanEquivCopen_node]
        exact Equiv.apply_symm_apply
          ((rootFieldDomainCleanEquivNodeChildVertex n b cs).trans
            (nodeChildVertexCoordsEquivCoordsList n cs)) y
      have h2' :
          ((rootFieldDomainCleanEquivNodeChildVertex n b cs).trans
              (nodeChildVertexCoordsEquivCoordsList n cs))
                ((vertexCoordDomainNodeEquivBlockNonRoot n b cs f).2) =
            ((rootFieldDomainCleanEquivNodeChildVertex n b cs).trans
              (nodeChildVertexCoordsEquivCoordsList n cs)) rd :=
        h2.trans hrd.symm
      have h3 := congrArg
        (fun z => ((rootFieldDomainCleanEquivNodeChildVertex n b cs).trans
          (nodeChildVertexCoordsEquivCoordsList n cs)).symm z) h2'
      simp [rd] at h3
      calc
        f v.1 j = ((vertexCoordDomainNodeEquivBlockNonRoot n b cs) f).2 v j := by
          simp [vertexCoordDomainNodeEquivBlockNonRoot]
        _ = rd v j := by
          exact congrFun (congrFun h3 v) j

theorem vertexCoordDomainEquivExtraSite_apply_nonroot
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (x : VertexCoordDomainClean n C)
    (v : NonRootVertex C)
    (j : Fin (NonRootVertex.weight v)) :
    x v.1 j = ((vertexCoordDomainEquivExtraSite n C hC x).2).nonRootCoord v j := by
  cases C with
  | node b cs =>
      dsimp [vertexCoordDomainEquivExtraSite, splitFullRootOpenEquivExtraSite,
        vertexCoordDomainEquivCplus]
      let rd := (vertexCoordDomainNodeEquivBlockNonRoot n b cs x).2
      have hx : x v.1 j = rd v j := by
        simp [rd, vertexCoordDomainNodeEquivBlockNonRoot]
      rw [hx]
      have hrd := (rootFieldDomainCleanEquivCopen_node n b cs).left_inv rd
      exact (congrFun (congrFun hrd v) j).symm

theorem headBoundaryParentRootContext_eq_site_rootCoord
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryParentRootContext n a C rest hC site = site.rootCoord := by
  unfold headBoundaryParentRootContext headChildSiteContextOfParent
    normalSiteClean_node_headEquiv
  change (((parentSiteHeadChildComponentsEquiv n a C rest hC)
    (((Equiv.refl (Block n (a - 1))).prodCongr
      (parentNonRootCoordsHeadTailEquiv n a C rest))
        ((normalSiteCleanEquivRootNonRoot n (RTree.node a (C :: rest))) site))).1).1 =
      site.rootCoord
  simp [normalSiteCleanEquivRootNonRoot, parentSiteHeadChildComponentsEquiv]

theorem headBoundaryTailCoords_eq_parentNonRootCoordsHeadTailEquiv_snd
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryTailCoords n a C rest hC site =
      ((parentNonRootCoordsHeadTailEquiv n a C rest) site.nonRootCoord).2 := by
  unfold headBoundaryTailCoords headChildSiteContextOfParent
    normalSiteClean_node_headEquiv
  change ((((parentSiteHeadChildComponentsEquiv n a C rest hC)
    (((Equiv.refl (Block n (a - 1))).prodCongr
      (parentNonRootCoordsHeadTailEquiv n a C rest))
        ((normalSiteCleanEquivRootNonRoot n (RTree.node a (C :: rest))) site))).1).2).2 =
      ((parentNonRootCoordsHeadTailEquiv n a C rest) site.nonRootCoord).2
  simp [normalSiteCleanEquivRootNonRoot, parentSiteHeadChildComponentsEquiv]

theorem headChildLocalSiteOfParent_eq_childFull_snd
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headChildLocalSiteOfParent n a C rest hC site =
      (vertexCoordDomainEquivExtraSite n C hC
        ((parentNonRootCoordsHeadTailEquiv n a C rest)
          site.nonRootCoord).1).2 := by
  unfold headChildLocalSiteOfParent normalSiteClean_node_headEquiv
  change ((parentSiteHeadChildComponentsEquiv n a C rest hC)
    (((Equiv.refl (Block n (a - 1))).prodCongr
      (parentNonRootCoordsHeadTailEquiv n a C rest))
        ((normalSiteCleanEquivRootNonRoot n (RTree.node a (C :: rest))) site))).2 =
      (vertexCoordDomainEquivExtraSite n C hC
        ((parentNonRootCoordsHeadTailEquiv n a C rest) site.nonRootCoord).1).2
  simp [normalSiteCleanEquivRootNonRoot, parentSiteHeadChildComponentsEquiv]

theorem headChildBoundaryVertexCoord_eq_parentHeadCoord_nonroot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (v : NonRootVertex C)
    (j : Fin (NonRootVertex.weight v)) :
    vertexCoordDomainFromBoundaryOpen n C
      (headChildLocalOpenCoordOfParentSite n a C rest hC site) v.1 j =
    ((parentNonRootCoordsHeadTailEquiv n a C rest) site.nonRootCoord).1
      v.1 j := by
  rw [vertexCoordDomainFromBoundaryOpen_apply_nonroot]
  unfold headChildLocalOpenCoordOfParentSite
  simp
  rw [headChildLocalSiteOfParent_eq_childFull_snd n a C rest hC site]
  exact (vertexCoordDomainEquivExtraSite_apply_nonroot n C hC
    ((parentNonRootCoordsHeadTailEquiv n a C rest) site.nonRootCoord).1
    v j).symm

theorem parentNonRootCoordsHeadTailEquiv_symm_head
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tail : CoordsList n rest)
    (v : NonRootVertex C)
    (j : Fin (NonRootVertex.weight v)) :
    ((parentNonRootCoordsHeadTailEquiv n a C rest).symm (child, tail))
      (headChildNonRootInParent (a := a) (C := C) (rest := rest) v)
      (Fin.cast
        (headChildNonRootInParent_weight
          (a := a) (C := C) (rest := rest) v).symm j) =
    child v.1 j := by
  let p : NodeChildVertex (C :: rest) :=
    (nodeChildVertexConsEquiv C rest).symm (Sum.inl v.1)
  let F : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n :=
    (dependentSumPiEquivProd
      (fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) → Rep n)).symm
      (child, (nodeChildVertexCoordsEquivCoordsList n rest).symm tail)
  change ((rootFieldDomainCleanEquivNodeChildVertex n a (C :: rest)).symm
      ((nodeChildVertexCoordsEquivSum n C rest).symm F))
      (childVertexAtAsNonRootInNode (a := a) p)
      (Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) p).symm
        (Fin.cast (nodeChildVertexConsEquiv_weight p).symm j)) =
    child v.1 j
  rw [rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child]
  rw [nodeChildVertexCoordsEquivSum_symm_inl]
  rfl

theorem parentNonRootCoordsHeadTailEquiv_symm_tail
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (child : VertexCoordDomainClean n C)
    (tail : CoordsList n rest)
    (p : NodeChildVertex rest)
    (j : Fin (Vertex.weight p.2)) :
    ((parentNonRootCoordsHeadTailEquiv n a C rest).symm (child, tail))
      (childVertexAtAsNonRootInNode (a := a)
        ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p)))
      (Fin.cast
        (childVertexAtAsNonRootInNode_weight
          (a := a) ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm
        (Fin.cast
          (nodeChildVertexConsEquiv_weight
            ((nodeChildVertexConsEquiv C rest).symm (Sum.inr p))).symm j)) =
    ((nodeChildVertexCoordsEquivCoordsList n rest).symm tail) p j := by
  let parentChild : NodeChildVertex (C :: rest) :=
    (nodeChildVertexConsEquiv C rest).symm (Sum.inr p)
  let F : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n :=
    (dependentSumPiEquivProd
      (fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) → Rep n)).symm
      (child, (nodeChildVertexCoordsEquivCoordsList n rest).symm tail)
  change ((rootFieldDomainCleanEquivNodeChildVertex n a (C :: rest)).symm
      ((nodeChildVertexCoordsEquivSum n C rest).symm F))
      (childVertexAtAsNonRootInNode (a := a) parentChild)
      (Fin.cast (childVertexAtAsNonRootInNode_weight (a := a) parentChild).symm
        (Fin.cast (nodeChildVertexConsEquiv_weight parentChild).symm j)) =
    ((nodeChildVertexCoordsEquivCoordsList n rest).symm tail) p j
  rw [rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child]
  rw [nodeChildVertexCoordsEquivSum_symm_inr]
  rfl

theorem headChildRootBoundaryData_otherCoord_eq_parentSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (u : OtherNonRootVertexClean (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)))
    (j : Fin (NonRootVertex.weight u.1)) :
    (parentNonRootCoordsHeadTailEquiv n a C rest).symm
      (vertexCoordDomainFromBoundaryOpen n C
          (headChildLocalOpenCoordOfParentSite n a C rest hC site),
        headBoundaryTailCoords n a C rest hC site)
      u.1 j = site.nonRootCoord u.1 j := by
  let E := parentNonRootCoordsHeadTailEquiv n a C rest
  have hsite := E.left_inv site.nonRootCoord
  rw [← hsite]
  let childData := vertexCoordDomainFromBoundaryOpen n C
    (headChildLocalOpenCoordOfParentSite n a C rest hC site)
  let tailData := headBoundaryTailCoords n a C rest hC site
  let P := E site.nonRootCoord
  let Fdata : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n :=
    (dependentSumPiEquivProd
      (fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) → Rep n)).symm
      (childData, (nodeChildVertexCoordsEquivCoordsList n rest).symm tailData)
  let Fsite : (s : Vertex C ⊕ NodeChildVertex rest) →
      Fin (nodeChildVertexSumWeight s) → Rep n :=
    (dependentSumPiEquivProd
      (fun s : Vertex C ⊕ NodeChildVertex rest =>
        Fin (nodeChildVertexSumWeight s) → Rep n)).symm
      (P.1, (nodeChildVertexCoordsEquivCoordsList n rest).symm P.2)
  change ((rootFieldDomainCleanEquivNodeChildVertex n a (C :: rest)).symm
      ((nodeChildVertexCoordsEquivSum n C rest).symm Fdata)) u.1 j =
    ((rootFieldDomainCleanEquivNodeChildVertex n a (C :: rest)).symm
      ((nodeChildVertexCoordsEquivSum n C rest).symm Fsite)) u.1 j
  cases u with
  | mk u hu =>
      let p := (nonRootVertexNodeEquivChildVertex a (C :: rest)) u
      have hu_from_p : childVertexAtAsNonRootInNode (a := a) p = u := by
        dsimp [p]
        exact (nonRootVertexNodeEquivChildVertex a (C :: rest)).left_inv u
      rw [rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child_of_eq
        n a (C :: rest) ((nodeChildVertexCoordsEquivSum n C rest).symm Fdata)
        p u hu_from_p j]
      rw [rootFieldDomainCleanEquivNodeChildVertex_symm_apply_child_of_eq
        n a (C :: rest) ((nodeChildVertexCoordsEquivSum n C rest).symm Fsite)
        p u hu_from_p j]
      cases hsum : (nodeChildVertexConsEquiv C rest) p with
      | inl v =>
          rw [nodeChildVertexCoordsEquivSum_symm_apply_of_eq
            n C rest Fdata p (Sum.inl v) hsum]
          rw [nodeChildVertexCoordsEquivSum_symm_apply_of_eq
            n C rest Fsite p (Sum.inl v) hsum]
          by_cases hvroot : v.1 = []
          · have hp : p = (nodeChildVertexConsEquiv C rest).symm (Sum.inl v) := by
              exact (Equiv.apply_eq_iff_eq_symm_apply
                (nodeChildVertexConsEquiv C rest)).mp hsum
            have hu_addr : u.1.1 = [0] := by
              rw [← hu_from_p, hp]
              dsimp [nodeChildVertexConsEquiv]
              simp
              exact hvroot
            exact False.elim (hu (by simpa using hu_addr))
          · let vnr : NonRootVertex C := ⟨v, hvroot⟩
            exact headChildBoundaryVertexCoord_eq_parentHeadCoord_nonroot
              n a C rest hC site vnr _
      | inr pTail =>
          rw [nodeChildVertexCoordsEquivSum_symm_apply_of_eq
            n C rest Fdata p (Sum.inr pTail) hsum]
          rw [nodeChildVertexCoordsEquivSum_symm_apply_of_eq
            n C rest Fsite p (Sum.inr pTail) hsum]
          have htail : tailData = P.2 := by
            dsimp [tailData, P, E]
            exact headBoundaryTailCoords_eq_parentNonRootCoordsHeadTailEquiv_snd
              n a C rest hC site
          subst tailData
          rfl

theorem headChildRootDomainFromBoundaryData_eq_parentSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (s : Rep n) :
    headChildRootDomainFromBoundaryData n a C rest hC
      (headBoundaryParentRootContext n a C rest hC site)
      (headBoundaryTailCoords n a C rest hC site)
      s
      (headChildLocalOpenCoordOfParentSite n a C rest hC site) =
    headChildRootDomainFromParentSite site s := by
  unfold headChildRootDomainFromBoundaryData headChildRootDomainFromParentSite
  rw [NonRootFieldDomainClean.mk.injEq]
  constructor
  · exact headBoundaryParentRootContext_eq_site_rootCoord
      n a C rest hC site
  constructor
  · rfl
  · funext u j
    exact headChildRootBoundaryData_otherCoord_eq_parentSite
      n a C rest hC site u j

theorem headChildRootBoundaryFieldFromParent_eq_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (s : Rep n) :
    headChildRootBoundaryFieldFromParent n a C rest hC Aopen
      (headBoundaryParentRootContext n a C rest hC site)
      (headBoundaryTailCoords n a C rest hC site)
      s
      (headChildLocalOpenCoordOfParentSite n a C rest hC site) =
    headChildRootBoundaryFieldFromParentSite Aopen site s := by
  unfold headChildRootBoundaryFieldFromParent
    headChildRootBoundaryFieldFromParentSite
  rw [headChildRootDomainFromBoundaryData_eq_parentSite n a C rest hC site s]

theorem headChildRootBoundaryFieldFromParent_diag_eq_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headChildRootBoundaryFieldFromParent n a C rest hC Aopen
      (headBoundaryParentRootContext n a C rest hC site)
      (headBoundaryTailCoords n a C rest hC site)
      (diagonalClean site
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)))
      (headChildLocalOpenCoordOfParentSite n a C rest hC site) =
    headChildRootBoundaryFieldFromParentSite Aopen site
      (diagonalClean site
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) := by
  exact headChildRootBoundaryFieldFromParent_eq_site
    n a C rest hC Aopen site
    (diagonalClean site
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)))

theorem headChildRootBoundaryFieldFromParent_succ_eq_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headChildRootBoundaryFieldFromParent n a C rest hC Aopen
      (headBoundaryParentRootContext n a C rest hC site)
      (headBoundaryTailCoords n a C rest hC site)
      (diagonalClean site
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) + 1)
      (headChildLocalOpenCoordOfParentSite n a C rest hC site) =
    headChildRootBoundaryFieldFromParentSite Aopen site
      (diagonalClean site
        (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) + 1) := by
  exact headChildRootBoundaryFieldFromParent_eq_site
    n a C rest hC Aopen site
    (diagonalClean site
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) + 1)

noncomputable def headBoundaryOpenPairingDataExpressionAtSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) : F2 :=
  let s :=
    diagonalClean site
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
  let q := headBoundaryParentRootContext n a C rest hC site
  let tail := headBoundaryTailCoords n a C rest hC site
  let y := headChildLocalOpenCoordOfParentSite n a C rest hC site
  headBoundaryParentRootKet (closeOpenNormalAssignmentClean root Aopen) site *
      headChildRootBoundaryFieldFromParent n a C rest hC Aopen q tail s y +
    headBoundaryParentRootBra (closeOpenNormalAssignmentClean root Aopen) site *
      headChildRootBoundaryFieldFromParent n a C rest hC Aopen q tail (s + 1) y

theorem headBoundaryOpenPairingExpressionAtSite_eq_dataExpression
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryOpenPairingExpressionAtSite n a C rest root Aopen site =
      headBoundaryOpenPairingDataExpressionAtSite
        n a C rest hC root Aopen site := by
  unfold headBoundaryOpenPairingExpressionAtSite
    headBoundaryOpenPairingDataExpressionAtSite
  let s :=
    diagonalClean site
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
  change
    headBoundaryParentRootKet (closeOpenNormalAssignmentClean root Aopen) site *
        headChildRootBoundaryFieldFromParentSite Aopen site s +
      headBoundaryParentRootBra (closeOpenNormalAssignmentClean root Aopen) site *
        headChildRootBoundaryFieldFromParentSite Aopen site (s + 1) =
    headBoundaryParentRootKet (closeOpenNormalAssignmentClean root Aopen) site *
        headChildRootBoundaryFieldFromParent n a C rest hC Aopen
          (headBoundaryParentRootContext n a C rest hC site)
          (headBoundaryTailCoords n a C rest hC site) s
          (headChildLocalOpenCoordOfParentSite n a C rest hC site) +
      headBoundaryParentRootBra (closeOpenNormalAssignmentClean root Aopen) site *
        headChildRootBoundaryFieldFromParent n a C rest hC Aopen
          (headBoundaryParentRootContext n a C rest hC site)
          (headBoundaryTailCoords n a C rest hC site) (s + 1)
          (headChildLocalOpenCoordOfParentSite n a C rest hC site)
  rw [← headChildRootBoundaryFieldFromParent_eq_site
    n a C rest hC Aopen site s]
  rw [← headChildRootBoundaryFieldFromParent_eq_site
    n a C rest hC Aopen site (s + 1)]

theorem headBoundaryPhaseAtSiteClean_node_eq_dataOpenPairingAtSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryPhaseAtSiteClean_node C rest
        (closeOpenNormalAssignmentClean root Aopen) site =
      headBoundaryOpenPairingDataExpressionAtSite
        n a C rest hC root Aopen site := by
  rw [headBoundaryPhaseAtSiteClean_node_eq_openPairingAtSite
    n a C rest hC root Aopen site]
  exact headBoundaryOpenPairingExpressionAtSite_eq_dataExpression
    n a C rest hC root Aopen site

end Imbalance
end TreeGraph
