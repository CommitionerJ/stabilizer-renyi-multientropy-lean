import TreeGraph.Imbalance.NodeHeadTotalShearData

namespace TreeGraph
namespace Imbalance

noncomputable def normalSiteCleanCopenTotalDiag
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C) : Rep n :=
  copenTotalDiag n C
    ((rootFieldDomainCleanEquivCopen n C) site.nonRootCoord)

noncomputable def normalSiteCleanCopenTotalDiagWithBridge
    (n : Nat) [NeZero n] (C : RTree)
    (B : RootFieldCleanCopenBridge n C)
    (site : NormalSiteClean n C) : Rep n :=
  rootDomainTotalDiagWithBridge n C B site.nonRootCoord

noncomputable def normalSiteCleanRootTotalDiag
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C) : Rep n :=
  ∑ i : Fin (C.rootWeight - 1), site.rootCoord i

noncomputable def normalSiteCleanTotalDiag
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C) : Rep n :=
  normalSiteCleanRootTotalDiag n C site +
    normalSiteCleanCopenTotalDiag n C site

noncomputable def normalSiteCleanTotalDiagWithBridge
    (n : Nat) [NeZero n] (C : RTree)
    (B : RootFieldCleanCopenBridge n C)
    (site : NormalSiteClean n C) : Rep n :=
  normalSiteCleanRootTotalDiag n C site +
    normalSiteCleanCopenTotalDiagWithBridge n C B site

theorem normalSiteCleanTotalDiag_eq_nonRootDomainTotalDiag_zero
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C)
    (v : NonRootVertex C) :
    normalSiteCleanTotalDiag n C site =
      nonRootDomainTotalDiag n C v
        (nonRootDomainOfSiteClean site v 0) := by
  rw [nonRootDomainTotalDiag_nonRootDomainOfSiteClean_zero]
  rfl

theorem nonRootDomainTotalDiag_site_zero_eq_normalSiteCleanTotalDiag
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C)
    (v : NonRootVertex C) :
    nonRootDomainTotalDiag n C v
        (nonRootDomainOfSiteClean site v 0) =
      normalSiteCleanTotalDiag n C site := by
  exact (normalSiteCleanTotalDiag_eq_nonRootDomainTotalDiag_zero
    n C site v).symm

theorem nonRootDomainTotalDiag_site_one_eq_normalSiteCleanTotalDiag_add_one
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C)
    (v : NonRootVertex C) :
    nonRootDomainTotalDiag n C v
        (nonRootDomainOfSiteClean site v 1) =
      normalSiteCleanTotalDiag n C site + 1 := by
  rw [nonRootDomainTotalDiag_nonRootDomainOfSiteClean_one]
  rfl

noncomputable def headIndexChildSiteDiagToCopenTotalEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    HeadChildIndex n a rest × NormalSiteClean n C ≃
      HeadChildIndex n a rest × NormalSiteClean n C where
  toFun P :=
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1,
        headChildIndexRootDiag P.1 +
          normalSiteCleanCopenTotalDiag n C P.2), P.2)
  invFun P :=
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1,
        headChildIndexRootDiag P.1 -
          normalSiteCleanCopenTotalDiag n C P.2), P.2)
  left_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨q, tail, s⟩
    simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag]
  right_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨q, tail, s⟩
    simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag]

noncomputable def headIndexChildSiteDiagToBridgeCopenTotalEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C) :
    HeadChildIndex n a rest × NormalSiteClean n C ≃
      HeadChildIndex n a rest × NormalSiteClean n C where
  toFun P :=
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1,
        headChildIndexRootDiag P.1 +
          normalSiteCleanCopenTotalDiagWithBridge n C B P.2), P.2)
  invFun P :=
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1,
        headChildIndexRootDiag P.1 -
          normalSiteCleanCopenTotalDiagWithBridge n C B P.2), P.2)
  left_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨q, tail, s⟩
    simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag]
  right_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨q, tail, s⟩
    simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag]

noncomputable def headIndexChildSiteDiagToTotalEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) :
    HeadChildIndex n a rest × NormalSiteClean n C ≃
      HeadChildIndex n a rest × NormalSiteClean n C where
  toFun P :=
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1,
        headChildIndexRootDiag P.1 +
          normalSiteCleanTotalDiag n C P.2), P.2)
  invFun P :=
    ((headChildIndexParentRoot P.1, headChildIndexTail P.1,
        headChildIndexRootDiag P.1 -
          normalSiteCleanTotalDiag n C P.2), P.2)
  left_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨q, tail, s⟩
    simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag]
  right_inv P := by
    rcases P with ⟨idx, site⟩
    rcases idx with ⟨q, tail, s⟩
    simp [headChildIndexParentRoot, headChildIndexTail,
      headChildIndexRootDiag]

theorem headIndexChildSiteDiagToCopenTotalEquiv_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        ((headIndexChildSiteDiagToCopenTotalEquiv
          n a C rest (idx, site)).1) =
      headChildIndexRootDiag idx +
        normalSiteCleanCopenTotalDiag n C site := by
  rfl

theorem headIndexChildSiteDiagToCopenTotalEquiv_symm_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        (((headIndexChildSiteDiagToCopenTotalEquiv
          n a C rest).symm (idx, site)).1) =
      headChildIndexRootDiag idx -
        normalSiteCleanCopenTotalDiag n C site := by
  rfl

theorem headIndexChildSiteDiagToBridgeCopenTotalEquiv_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        ((headIndexChildSiteDiagToBridgeCopenTotalEquiv
          n a C rest B (idx, site)).1) =
      headChildIndexRootDiag idx +
        normalSiteCleanCopenTotalDiagWithBridge n C B site := by
  rfl

theorem headIndexChildSiteDiagToBridgeCopenTotalEquiv_symm_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        (((headIndexChildSiteDiagToBridgeCopenTotalEquiv
          n a C rest B).symm (idx, site)).1) =
      headChildIndexRootDiag idx -
        normalSiteCleanCopenTotalDiagWithBridge n C B site := by
  rfl

theorem headIndexChildSiteDiagToTotalEquiv_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        ((headIndexChildSiteDiagToTotalEquiv n a C rest (idx, site)).1) =
      headChildIndexRootDiag idx + normalSiteCleanTotalDiag n C site := by
  rfl

theorem headIndexChildSiteDiagToTotalEquiv_symm_rootDiag
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    headChildIndexRootDiag
        (((headIndexChildSiteDiagToTotalEquiv n a C rest).symm
          (idx, site)).1) =
      headChildIndexRootDiag idx - normalSiteCleanTotalDiag n C site := by
  rfl

theorem headIndexChildSiteDiagToCopenTotalEquiv_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    (headIndexChildSiteDiagToCopenTotalEquiv
      n a C rest (idx, site)).2 = site := by
  rfl

theorem headIndexChildSiteDiagToBridgeCopenTotalEquiv_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    (headIndexChildSiteDiagToBridgeCopenTotalEquiv
      n a C rest B (idx, site)).2 = site := by
  rfl

theorem headIndexChildSiteDiagToTotalEquiv_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (idx : HeadChildIndex n a rest) (site : NormalSiteClean n C) :
    (headIndexChildSiteDiagToTotalEquiv n a C rest (idx, site)).2 =
      site := by
  rfl

theorem prod_headIndex_childSite_eq_prod_copenTotal_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (w : HeadChildIndex n a rest × NormalSiteClean n C → ℤ) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteDiagToCopenTotalEquiv
            n a C rest).symm (idx, site)) := by
  classical
  let e := headIndexChildSiteDiagToCopenTotalEquiv n a C rest
  calc
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C, w P := by
          exact
            (Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C => w (idx, site))).symm
    _ =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e.symm P) := by
          exact (Equiv.prod_comp e.symm w).symm
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteDiagToCopenTotalEquiv
            n a C rest).symm (idx, site)) := by
          exact
            Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C =>
                  w ((headIndexChildSiteDiagToCopenTotalEquiv
                    n a C rest).symm (idx, site)))

theorem prod_headIndex_childSite_eq_prod_bridgeCopenTotal_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (w : HeadChildIndex n a rest × NormalSiteClean n C → ℤ) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteDiagToBridgeCopenTotalEquiv
            n a C rest B).symm (idx, site)) := by
  classical
  let e := headIndexChildSiteDiagToBridgeCopenTotalEquiv n a C rest B
  calc
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C, w P := by
          exact
            (Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C => w (idx, site))).symm
    _ =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e.symm P) := by
          exact (Equiv.prod_comp e.symm w).symm
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteDiagToBridgeCopenTotalEquiv
            n a C rest B).symm (idx, site)) := by
          exact
            Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C =>
                  w ((headIndexChildSiteDiagToBridgeCopenTotalEquiv
                    n a C rest B).symm (idx, site)))

theorem prod_headIndex_childSite_eq_prod_total_symm
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (w : HeadChildIndex n a rest × NormalSiteClean n C → ℤ) :
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteDiagToTotalEquiv
            n a C rest).symm (idx, site)) := by
  classical
  let e := headIndexChildSiteDiagToTotalEquiv n a C rest
  calc
    (∏ idx : HeadChildIndex n a rest,
      ∏ site : NormalSiteClean n C, w (idx, site)) =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C, w P := by
          exact
            (Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C => w (idx, site))).symm
    _ =
        ∏ P : HeadChildIndex n a rest × NormalSiteClean n C,
          w (e.symm P) := by
          exact (Equiv.prod_comp e.symm w).symm
    _ =
      ∏ idx : HeadChildIndex n a rest,
        ∏ site : NormalSiteClean n C,
          w ((headIndexChildSiteDiagToTotalEquiv
            n a C rest).symm (idx, site)) := by
          exact
            Fintype.prod_prod_type'
              (fun idx : HeadChildIndex n a rest =>
                fun site : NormalSiteClean n C =>
                  w ((headIndexChildSiteDiagToTotalEquiv
                    n a C rest).symm (idx, site)))

theorem headTotalShearDataWithBridge_root_site_total
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (q : Block n (a - 1)) (tail : CoordsList n rest)
    (s : Rep n) (site : NormalSiteClean n C) :
    B.linearEquiv
        ((headTotalShearDataWithBridge n a C rest B data)
          (q, tail, s + normalSiteCleanCopenTotalDiag n C site)).1
        ((rootFieldDomainCleanEquivCopen n C) site.nonRootCoord) =
      B.linearEquiv (data (q, tail, s)).1
        ((rootFieldDomainCleanEquivCopen n C) site.nonRootCoord) := by
  exact headTotalShearDataWithBridge_boundary_apply_total n a C rest B data
    q tail s ((rootFieldDomainCleanEquivCopen n C) site.nonRootCoord)

theorem headTotalShearDataWithBridge_root_site_bridgeTotal
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (q : Block n (a - 1)) (tail : CoordsList n rest)
    (s : Rep n) (site : NormalSiteClean n C) :
    ((headTotalShearDataWithBridge n a C rest B data)
        (q, tail,
          s + normalSiteCleanCopenTotalDiagWithBridge n C B site)).1
        site.nonRootCoord =
      (data (q, tail, s)).1 site.nonRootCoord := by
  rw [headTotalShearDataWithBridge_root_apply]
  have hidx :
      ((q, tail,
          s + normalSiteCleanCopenTotalDiagWithBridge n C B site -
            normalSiteCleanCopenTotalDiagWithBridge n C B site) :
          HeadChildIndex n a rest) =
        (q, tail, s) := by
    simp
  change
    (data
        (((q, tail,
          s + normalSiteCleanCopenTotalDiagWithBridge n C B site -
            normalSiteCleanCopenTotalDiagWithBridge n C B site) :
          HeadChildIndex n a rest))).1 site.nonRootCoord =
      (data (q, tail, s)).1 site.nonRootCoord
  rw [hidx]

theorem headTotalShearDataWithBridge_node_site_zero_total
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (q : Block n (a - 1)) (tail : CoordsList n rest)
    (s : Rep n) (site : NormalSiteClean n C)
    (v : NonRootVertex C) :
    ((headTotalShearDataWithBridge n a C rest B data)
        (q, tail, s + normalSiteCleanTotalDiag n C site)).2.nodeField
        v (nonRootDomainOfSiteClean site v 0) =
      (data (q, tail, s)).2.nodeField v
        (nonRootDomainOfSiteClean site v 0) := by
  rw [normalSiteCleanTotalDiag_eq_nonRootDomainTotalDiag_zero n C site v]
  exact headTotalShearDataWithBridge_node_apply_total n a C rest B data
    q tail s v (nonRootDomainOfSiteClean site v 0)

theorem headTotalShearDataWithBridge_node_site_one_total
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : RootFieldCleanCopenBridge n C)
    (data : HeadChildOpenData n a C rest)
    (q : Block n (a - 1)) (tail : CoordsList n rest)
    (s : Rep n) (site : NormalSiteClean n C)
    (v : NonRootVertex C) :
    ((headTotalShearDataWithBridge n a C rest B data)
        (q, tail,
          s + normalSiteCleanTotalDiag n C site + 1)).2.nodeField
        v (nonRootDomainOfSiteClean site v 1) =
      (data (q, tail, s)).2.nodeField v
        (nonRootDomainOfSiteClean site v 1) := by
  rw [add_assoc]
  rw [← nonRootDomainTotalDiag_site_one_eq_normalSiteCleanTotalDiag_add_one]
  exact headTotalShearDataWithBridge_node_apply_total n a C rest B data
    q tail s v (nonRootDomainOfSiteClean site v 1)

end Imbalance
end TreeGraph
