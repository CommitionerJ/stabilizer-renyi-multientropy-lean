import TreeGraph.Imbalance.NodeRootCopenBridgeCanonical

namespace TreeGraph
namespace Imbalance

private def finInitOfPred {b : Nat} (_hb : 0 < b) (i : Fin (b - 1)) :
    Fin b :=
  ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le b 1)⟩

private def finLastOfPos {b : Nat} (hb : 0 < b) : Fin b :=
  ⟨b - 1, by omega⟩

noncomputable def blockSplitLastEquiv
    (n b : Nat) [NeZero n] (hb : 0 < b) :
    Block n b ≃ (Block n (b - 1) × Rep n) where
  toFun f := (fun i => f (finInitOfPred hb i), f (finLastOfPos hb))
  invFun P := fun j =>
    if hlast : j.1 = b - 1 then
      P.2
    else
      P.1 ⟨j.1, by
        have hle : j.1 ≤ b - 1 := Nat.le_pred_of_lt j.2
        exact Nat.lt_of_le_of_ne hle hlast⟩
  left_inv f := by
    funext j
    by_cases hlast : j.1 = b - 1
    · have hj : j = finLastOfPos hb := Fin.ext hlast
      simp [hj, finLastOfPos]
    · have hj :
          finInitOfPred hb
              (⟨j.1, by
                have hle : j.1 ≤ b - 1 := Nat.le_pred_of_lt j.2
                exact Nat.lt_of_le_of_ne hle hlast⟩ : Fin (b - 1)) = j := by
        exact Fin.ext rfl
      simp [hlast, hj]
  right_inv P := by
    cases P with
    | mk init last =>
        apply Prod.ext
        · funext i
          have hne : ¬ (i.1 = b - 1) :=
            Nat.ne_of_lt i.2
          simp [hne, finInitOfPred]
        · simp [finLastOfPos]

noncomputable def normalSiteCleanEquivRootNonRoot
    (n : Nat) [NeZero n] (T : RTree) :
    NormalSiteClean n T ≃
      Block n (T.rootWeight - 1) × RootFieldDomainClean n T where
  toFun site := (site.rootCoord, site.nonRootCoord)
  invFun P := { rootCoord := P.1, nonRootCoord := P.2 }
  left_inv site := by
    cases site
    rfl
  right_inv P := by
    cases P
    rfl

noncomputable def normalSiteCleanEquivRootCopen
    (n : Nat) [NeZero n] (T : RTree) :
    NormalSiteClean n T ≃ Block n (T.rootWeight - 1) × Copen n T where
  toFun site :=
    (site.rootCoord, (rootFieldDomainCleanEquivCopen n T) site.nonRootCoord)
  invFun P :=
    { rootCoord := P.1
      nonRootCoord := (rootFieldDomainCleanEquivCopen n T).symm P.2 }
  left_inv site := by
    cases site
    simp
  right_inv P := by
    cases P
    simp

noncomputable def splitFullRootOpenEquivExtraSite
    (n b : Nat) [NeZero n] (cs : List RTree) (hb : 0 < b) :
    Block n b × CoordsList n cs ≃
      Rep n × NormalSiteClean n (RTree.node b cs) where
  toFun P :=
    let split := (blockSplitLastEquiv n b hb) P.1
    (split.2,
      { rootCoord := split.1
        nonRootCoord :=
          (rootFieldDomainCleanEquivCopen n (RTree.node b cs)).symm P.2 })
  invFun Q :=
    ((blockSplitLastEquiv n b hb).symm (Q.2.rootCoord, Q.1),
      (rootFieldDomainCleanEquivCopen n (RTree.node b cs)) Q.2.nonRootCoord)
  left_inv P := by
    cases P with
    | mk root openCoords =>
        dsimp
        have hroot := (blockSplitLastEquiv n b hb).left_inv root
        have hopen :=
          (rootFieldDomainCleanEquivCopen n (RTree.node b cs)).right_inv
            openCoords
        apply Prod.ext
        · exact hroot
        · exact hopen
  right_inv Q := by
    cases Q with
    | mk extra site =>
        cases site with
        | mk rootCoord nonRootCoord =>
        dsimp
        have hblock :=
          (blockSplitLastEquiv n b hb).right_inv
            (rootCoord, extra)
        have hnonRoot :=
          (rootFieldDomainCleanEquivCopen n (RTree.node b cs)).left_inv
            nonRootCoord
        apply Prod.ext
        · exact congrArg Prod.snd hblock
        · exact congrArg₂
            (fun root nonRoot =>
              ({ rootCoord := root, nonRootCoord := nonRoot } :
                NormalSiteClean n (RTree.node b cs)))
            (congrArg Prod.fst hblock) hnonRoot

noncomputable def vertexCoordDomainEquivExtraSite
    (n : Nat) [NeZero n] (C : RTree) (hC : RTree.PositiveWeights C) :
    VertexCoordDomainClean n C ≃ Rep n × NormalSiteClean n C := by
  cases C with
  | node b cs =>
      have hb : 0 < b := by
        have hparts : 0 < b ∧
            ∀ D ∈ cs, RTree.PositiveWeights D := by
          simpa [RTree.PositiveWeights] using hC
        exact hparts.1
      exact (vertexCoordDomainEquivCplus n (RTree.node b cs)).trans
        (splitFullRootOpenEquivExtraSite n b cs hb)

abbrev HeadChildSiteContext
    (n a : Nat) [NeZero n] (_C : RTree) (rest : List RTree) : Type :=
  Block n (a - 1) × Rep n × CoordsList n rest

noncomputable def parentNonRootCoordsHeadTailEquiv
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    RootFieldDomainClean n (RTree.node a (C :: rest)) ≃
      VertexCoordDomainClean n C × CoordsList n rest :=
  (rootFieldDomainCleanEquivNodeChildVertex n a (C :: rest)).trans
    ((nodeChildVertexCoordsEquivSum n C rest).trans
      ((dependentSumPiEquivProd
        (fun s : Vertex C ⊕ NodeChildVertex rest =>
          Fin (nodeChildVertexSumWeight s) → Rep n)).trans
        (Equiv.prodCongr
          (Equiv.refl (VertexCoordDomainClean n C))
          (nodeChildVertexCoordsEquivCoordsList n rest))))

noncomputable def parentSiteHeadChildComponentsEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C) :
    Block n (a - 1) × (VertexCoordDomainClean n C × CoordsList n rest) ≃
      HeadChildSiteContext n a C rest × NormalSiteClean n C where
  toFun P :=
    let child := (vertexCoordDomainEquivExtraSite n C hC) P.2.1
    ((P.1, child.1, P.2.2), child.2)
  invFun Q :=
    let child :=
      (vertexCoordDomainEquivExtraSite n C hC).symm (Q.1.2.1, Q.2)
    (Q.1.1, (child, Q.1.2.2))
  left_inv P := by
    cases P with
    | mk parentRoot childTail =>
        cases childTail with
        | mk childFull tail =>
            dsimp
            exact congrArg (fun childFull' => (parentRoot, childFull', tail))
              ((vertexCoordDomainEquivExtraSite n C hC).left_inv childFull)
  right_inv Q := by
    cases Q with
    | mk context childSite =>
        cases context with
        | mk parentRoot extraTail =>
            cases extraTail with
            | mk extra tail =>
                dsimp
                exact congrArg
                  (fun child' : Rep n × NormalSiteClean n C =>
                    ((parentRoot, child'.1, tail), child'.2))
                  ((vertexCoordDomainEquivExtraSite n C hC).right_inv
                    (extra, childSite))

noncomputable def normalSiteClean_node_headEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C) :
    NormalSiteClean n (RTree.node a (C :: rest)) ≃
      HeadChildSiteContext n a C rest × NormalSiteClean n C :=
  (normalSiteCleanEquivRootNonRoot n (RTree.node a (C :: rest))).trans
    ((Equiv.prodCongr (Equiv.refl (Block n (a - 1)))
      (parentNonRootCoordsHeadTailEquiv n a C rest)).trans
      (parentSiteHeadChildComponentsEquiv n a C rest hC))

end Imbalance
end TreeGraph
