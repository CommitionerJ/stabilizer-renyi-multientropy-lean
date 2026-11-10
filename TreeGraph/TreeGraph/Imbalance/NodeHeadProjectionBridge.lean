import TreeGraph.Imbalance.NodePackageMembership
import TreeGraph.Imbalance.NodeHeadBoundaryPairing

namespace TreeGraph
namespace Imbalance

theorem mem_rtildeVisibleKernel_iff_forall_oneSliceCyclicKernel
    (n : Nat) [NeZero n]
    (E P M : Type)
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (h : E → P) :
    h ∈ rtildeVisibleKernel n E P M R ↔
      ∀ e : E, h e ∈ oneSliceCyclicKernel n P M R := by
  constructor
  · intro hh e
    rw [oneSliceCyclicKernel]
    apply LinearMap.mem_ker.mpr
    ext t x
    have hzero :
        ((familyCycDiff n E (Module.Dual F2 M)).comp
            (RtildeAbstract n E P M R)) h = 0 :=
      LinearMap.mem_ker.mp hh
    simpa [RtildeAbstract, familyCycDiff, cycDiff] using
      congrArg (fun ell : Module.Dual F2 M => ell x)
        (congrFun hzero (e, t))
  · intro hh
    rw [rtildeVisibleKernel]
    apply LinearMap.mem_ker.mpr
    ext et x
    have hker :
        h et.1 ∈
          LinearMap.ker
            ((cycDiff n (Module.Dual F2 M)).comp R) := by
      simpa [oneSliceCyclicKernel] using hh et.1
    have hzero :
        ((cycDiff n (Module.Dual F2 M)).comp R) (h et.1) = 0 :=
      LinearMap.mem_ker.mp hker
    simpa [RtildeAbstract, familyCycDiff, cycDiff] using
      congrArg (fun ell : Module.Dual F2 M => ell x)
        (congrFun hzero et.2)

theorem mem_headAllowedBoundarySpace_iff_forall_headBranch_mem_Kchild
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (h : BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ headAllowedBoundarySpace n a C rest hC P ↔
      ∀ tail : CoordsList n rest,
        (boundaryHeadSliceLinearEquiv n a C rest h tail) ∈
          Kchild n C (rootWeight_pos_of_positiveWeights hC)
            P.boundaryMessageSpace := by
  change
    boundaryHeadSliceLinearEquiv n a C rest h ∈
        rtildeVisibleKernel n (CoordsList n rest)
          (BranchField n C) P.boundaryMessageSpace
          (headChildR n C hC P) ↔
      ∀ tail : CoordsList n rest,
        (boundaryHeadSliceLinearEquiv n a C rest h tail) ∈
          Kchild n C (rootWeight_pos_of_positiveWeights hC)
            P.boundaryMessageSpace
  rw [mem_rtildeVisibleKernel_iff_forall_oneSliceCyclicKernel]
  simp [oneSliceCyclicKernel, Kchild, headChildR]

theorem mem_headAllowedBoundarySpace_iff_forall_headChildR_cycDiff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (h : BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ headAllowedBoundarySpace n a C rest hC P ↔
      ∀ tail : CoordsList n rest,
        cycDiff n (Module.Dual F2 P.boundaryMessageSpace)
          (headChildR n C hC P
            (boundaryHeadSliceLinearEquiv n a C rest h tail)) = 0 := by
  rw [mem_headAllowedBoundarySpace_iff_forall_headBranch_mem_Kchild]
  constructor
  · intro hh tail
    exact
      (mem_Kchild_iff n C (rootWeight_pos_of_positiveWeights hC)
        P.boundaryMessageSpace
        (boundaryHeadSliceLinearEquiv n a C rest h tail)).1 (hh tail)
  · intro hh tail
    exact
      (mem_Kchild_iff n C (rootWeight_pos_of_positiveWeights hC)
        P.boundaryMessageSpace
        (boundaryHeadSliceLinearEquiv n a C rest h tail)).2 (hh tail)

theorem headChildR_node_apply
    (n : Nat) [NeZero n]
    (b : Nat) (ds : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (branch : BranchField n (RTree.node b ds))
    (s : Rep n) (m : P.boundaryMessageSpace) :
    headChildR n (RTree.node b ds) hC P branch s m =
      ∑ y : Copen n (RTree.node b ds),
        m.1 y *
          (∑ x : Block n b,
            if diag n b x = s then branch (x, y) else 0) := by
  simp only [headChildR, branchProjection]
  change
    (restrictDual P.boundaryMessageSpace
      (PiFull n (rootWeight_pos_of_positiveWeights hC)
        (Copen n (RTree.node b ds)) branch s)) m =
      ∑ y : Copen n (RTree.node b ds),
        m.1 y *
          (∑ x : Block n b,
            if diag n b x = s then branch (x, y) else 0)
  rw [PiFull_apply]
  change
    (∑ y : Copen n (RTree.node b ds),
      m.1 y *
        PiCoeff n (rootWeight_pos_of_positiveWeights hC)
          (Copen n (RTree.node b ds)) branch (s, y)) =
      ∑ y : Copen n (RTree.node b ds),
        m.1 y *
          (∑ x : Block n b,
            if diag n b x = s then branch (x, y) else 0)
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [PiCoeff_apply]
  change
    m.1 y *
        (∑ x : Block n b,
          if diag n b x = s then branch (x, y) else 0) =
      m.1 y *
        (∑ x : Block n b,
          if diag n b x = s then branch (x, y) else 0)
  rfl

theorem headChildR_headParentRootBranch_node_apply
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : OpenNormalCleanPackage n (RTree.node b ds) hC)
    (root :
      RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : CoordsList n rest)
    (s : Rep n) (m : P.boundaryMessageSpace) :
    headChildR n (RTree.node b ds) hC P
        (headParentRootBranchFieldFromRoot n a
          (RTree.node b ds) rest root tail) s m =
      ∑ y : Copen n (RTree.node b ds),
        m.1 y *
          (∑ x : Block n b,
            if diag n b x = s then
              headParentRootBoundaryFieldFromRoot n a
                (RTree.node b ds) rest root ((x, y), tail)
            else 0) := by
  rw [headChildR_node_apply]
  rfl

theorem headBoundaryParentRootKet_eq_parentRootBra
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryParentRootKet A site =
      headBoundaryParentRootBra A site := by
  unfold headBoundaryParentRootKet headBoundaryParentRootBra
    ketAtPathClean braAtPathClean ketAtVertexClean braAtVertexClean
  simp

theorem headBoundaryParentRootKet_eq_boundaryField_at_site
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryParentRootKet
        (closeOpenNormalAssignmentClean root Aopen) site =
      headParentRootBoundaryFieldFromRoot n a C rest root
        ((rootFieldDomainCleanEquivCopen_node n a (C :: rest))
          site.nonRootCoord) := by
  unfold headBoundaryParentRootKet headParentRootBoundaryFieldFromRoot
    ketAtPathClean ketAtVertexClean
  simp only [RTree.addresses_node, List.mem_cons, true_or, ↓reduceDIte,
    CoordsList_cons]
  change root site.nonRootCoord =
    root
      ((rootFieldDomainCleanEquivCopen_node n a (C :: rest)).symm
        ((rootFieldDomainCleanEquivCopen_node n a (C :: rest))
          site.nonRootCoord))
  exact
    (congrArg root
      ((rootFieldDomainCleanEquivCopen_node n a (C :: rest)).left_inv
        site.nonRootCoord)).symm

theorem headBoundaryOpenPairingExpressionAtSite_eq_parentRoot_mul
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryOpenPairingExpressionAtSite n a C rest root Aopen site =
      let s :=
        diagonalClean site
          (headChildRootNonRootInParent
            (a := a) (C := C) (rest := rest))
      headBoundaryParentRootKet
          (closeOpenNormalAssignmentClean root Aopen) site *
        (headChildRootBoundaryFieldFromParentSite Aopen site s +
          headChildRootBoundaryFieldFromParentSite Aopen site (s + 1)) := by
  unfold headBoundaryOpenPairingExpressionAtSite
  rw [headBoundaryParentRootKet_eq_parentRootBra n a C rest]
  rw [mul_add]

theorem headParentRootBoundaryFieldFromRoot_mem_headAllowedBoundarySpace_iff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest hC P ↔
      ∀ tail : CoordsList n rest,
        headParentRootBranchFieldFromRoot n a C rest root tail ∈
          Kchild n C (rootWeight_pos_of_positiveWeights hC)
            P.boundaryMessageSpace := by
  rw [mem_headAllowedBoundarySpace_iff_forall_headBranch_mem_Kchild]
  rfl

theorem headParentRootBoundaryFieldFromRoot_mem_headAllowedBoundarySpace_iff_cycDiff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest hC P ↔
      ∀ tail : CoordsList n rest,
        cycDiff n (Module.Dual F2 P.boundaryMessageSpace)
          (headChildR n C hC P
            (headParentRootBranchFieldFromRoot n a C rest root tail)) = 0 := by
  rw [mem_headAllowedBoundarySpace_iff_forall_headChildR_cycDiff]
  rfl

theorem packageFactorProductEquivCoordsList_cons_symm
    (n : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hcs : ∀ D ∈ C :: rest, RTree.PositiveWeights D)
    (childPackage :
      ∀ D, (hDmem : D ∈ C :: rest) →
        OpenNormalCleanPackage n D (hcs D hDmem))
    (x : CoordsList n (C :: rest)) :
    (packageFactorProductEquivCoordsList n (C :: rest) hcs childPackage).symm x =
      (x.1,
        (packageFactorProductEquivCoordsList n rest
          (fun D hDmem => hcs D (by simp [hDmem]))
          (fun D hDmem => childPackage D (by simp [hDmem]))).symm x.2) := by
  rfl

theorem positiveWeights_node_tail_of_cons
    {a : Nat} {C : RTree} {rest : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest))) :
    RTree.PositiveWeights (RTree.node a rest) := by
  have hnode : 0 < a ∧ ∀ D ∈ C :: rest, RTree.PositiveWeights D := by
    simpa [RTree.PositiveWeights] using hT
  have hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
    intro D hDmem
    exact hnode.2 D (by simp [hDmem])
  simpa [RTree.PositiveWeights] using And.intro hnode.1 hrest

noncomputable def nodeTailInputsOfCons
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT) :
    NodeOpenPackageStepInputs n a rest
      (positiveWeights_node_tail_of_cons hT) where
  childPackage := fun D hDmem => I.childPackage D (by simp [hDmem])
  parentRootCopenBridge := RootFieldCleanCopenBridge.node n a rest

theorem mem_packageAllowedBoundarySpace_cons_imp_headAllowedBoundarySpace
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (h : BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ packageAllowedBoundarySpace n a (C :: rest) hT I →
      h ∈ headAllowedBoundarySpace n a C rest
        (child_positive_of_node hT C (by simp))
        (I.childPackage C (by simp)) := by
  intro hh
  rw [mem_headAllowedBoundarySpace_iff_forall_headBranch_mem_Kchild]
  let hcs : ∀ D ∈ C :: rest, RTree.PositiveWeights D :=
    child_positive_of_node hT
  let hrest : ∀ D ∈ rest, RTree.PositiveWeights D :=
    fun D hDmem => hcs D (by simp [hDmem])
  let Prest :
      ∀ D, (hDmem : D ∈ rest) →
        OpenNormalCleanPackage n D (hrest D hDmem) :=
    fun D hDmem => I.childPackage D (by simp [hDmem])
  let Phead : OpenNormalCleanPackage n C (hcs C (by simp)) :=
    I.childPackage C (by simp)
  let Fhead : SliceFactor :=
    { C := Cplus n C
      finite_C := inferInstance
      K := Kchild n C (rootWeight_pos_of_positiveWeights (hcs C (by simp)))
        Phead.boundaryMessageSpace
      finiteDim_K := inferInstance }
  rcases
      (mem_packageAllowedBoundarySpace_iff_exists_factor
        n a (C :: rest) hT I h).1 hh with
    ⟨g, hgind, hgtransport⟩
  have hgind_head :
      g ∈ independentAllowed
        (Fhead :: packageChildSliceFactors n rest hrest Prest) := by
    simpa [packageChildSliceFactors, hcs, hrest, Prest, Phead, Fhead]
      using hgind
  have hcols :
      ∀ tailProd : factorProduct
          (packageChildSliceFactors n rest hrest Prest),
        (fun p : Cplus n C => g (p, tailProd)) ∈
          Kchild n C (rootWeight_pos_of_positiveWeights (hcs C (by simp)))
            Phead.boundaryMessageSpace :=
    ((mem_independentAllowed_cons_iff Fhead
      (packageChildSliceFactors n rest hrest Prest) g).1
        hgind_head).2
  intro tail
  let tailProd :=
    (packageFactorProductEquivCoordsList n rest hrest Prest).symm tail
  have hslice :
      boundaryHeadSliceLinearEquiv n a C rest h tail =
        fun p : Cplus n C => g (p, tailProd) := by
    funext p
    have hrel := congrFun hgtransport (p, tail)
    simpa [tailProd, packageFactorProductEquivCoordsList_cons_symm,
      hcs, hrest, Prest] using hrel.symm
  simpa [hcs, Phead, hslice] using hcols tailProd

theorem mem_packageAllowedBoundarySpace_cons_imp_tailRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (h : BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ packageAllowedBoundarySpace n a (C :: rest) hT I →
      ∀ p : Cplus n C,
        (fun tail : CoordsList n rest => h (p, tail)) ∈
          packageAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I) := by
  intro hh
  let hcs : ∀ D ∈ C :: rest, RTree.PositiveWeights D :=
    child_positive_of_node hT
  let hrest : ∀ D ∈ rest, RTree.PositiveWeights D :=
    fun D hDmem => hcs D (by simp [hDmem])
  let Prest :
      ∀ D, (hDmem : D ∈ rest) →
        OpenNormalCleanPackage n D (hrest D hDmem) :=
    fun D hDmem => I.childPackage D (by simp [hDmem])
  let Phead : OpenNormalCleanPackage n C (hcs C (by simp)) :=
    I.childPackage C (by simp)
  let Fhead : SliceFactor :=
    { C := Cplus n C
      finite_C := inferInstance
      K := Kchild n C (rootWeight_pos_of_positiveWeights (hcs C (by simp)))
        Phead.boundaryMessageSpace
      finiteDim_K := inferInstance }
  rcases
      (mem_packageAllowedBoundarySpace_iff_exists_factor
        n a (C :: rest) hT I h).1 hh with
    ⟨g, hgind, hgtransport⟩
  have hgind_head :
      g ∈ independentAllowed
        (Fhead :: packageChildSliceFactors n rest hrest Prest) := by
    simpa [packageChildSliceFactors, hcs, hrest, Prest, Phead, Fhead]
      using hgind
  have hrows :
      ∀ p : Cplus n C,
        (fun tailProd : factorProduct
            (packageChildSliceFactors n rest hrest Prest) =>
          g (p, tailProd)) ∈
          independentAllowed
            (packageChildSliceFactors n rest hrest Prest) :=
    ((mem_independentAllowed_cons_iff Fhead
      (packageChildSliceFactors n rest hrest Prest) g).1
        hgind_head).1
  intro p
  apply
    (mem_packageAllowedBoundarySpace_iff_exists_factor
      n a rest (positiveWeights_node_tail_of_cons hT)
      (nodeTailInputsOfCons n a C rest hT I)
      (fun tail : CoordsList n rest => h (p, tail))).2
  refine ⟨fun tailProd => g (p, tailProd), ?_, ?_⟩
  · simpa [nodeTailInputsOfCons, hcs, hrest, Prest] using hrows p
  · funext tail
    have hrel := congrFun hgtransport (p, tail)
    simpa [packageFactorProductEquivCoordsList_cons_symm,
      nodeTailInputsOfCons, hcs, hrest, Prest] using hrel

theorem mem_packageAllowedBoundarySpace_cons_iff_headAllowed_tailRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (h : BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ packageAllowedBoundarySpace n a (C :: rest) hT I ↔
      h ∈ headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∧
        ∀ p : Cplus n C,
          (fun tail : CoordsList n rest => h (p, tail)) ∈
            packageAllowedBoundarySpace n a rest
              (positiveWeights_node_tail_of_cons hT)
              (nodeTailInputsOfCons n a C rest hT I) := by
  constructor
  · intro hh
    exact ⟨
      mem_packageAllowedBoundarySpace_cons_imp_headAllowedBoundarySpace
        n a C rest hT I h hh,
      mem_packageAllowedBoundarySpace_cons_imp_tailRows
        n a C rest hT I h hh⟩
  · intro hh
    rcases hh with ⟨hhead, hrows⟩
    let hcs : ∀ D ∈ C :: rest, RTree.PositiveWeights D :=
      child_positive_of_node hT
    let Phead : OpenNormalCleanPackage n C (hcs C (by simp)) :=
      I.childPackage C (by simp)
    let Fhead : SliceFactor :=
      { C := Cplus n C
        finite_C := inferInstance
        K := Kchild n C (rootWeight_pos_of_positiveWeights (hcs C (by simp)))
          Phead.boundaryMessageSpace
        finiteDim_K := inferInstance }
    let hTail := positiveWeights_node_tail_of_cons hT
    let Itail := nodeTailInputsOfCons n a C rest hT I
    let Fs := packageChildSliceFactors n rest (child_positive_of_node hTail)
      Itail.childPackage
    let erest := packageFactorProductEquivCoordsList n rest
      (child_positive_of_node hTail) Itail.childPackage
    let g : factorProduct (Fhead :: Fs) → F2 := fun x => h (x.1, erest x.2)
    apply
      (mem_packageAllowedBoundarySpace_iff_exists_factor
        n a (C :: rest) hT I h).2
    refine ⟨g, ?_, ?_⟩
    · have hcols :
          ∀ tailProd : factorProduct Fs,
            (fun p : Cplus n C => g (p, tailProd)) ∈ Fhead.K := by
        intro tailProd
        have htail :=
          (mem_headAllowedBoundarySpace_iff_forall_headBranch_mem_Kchild
            n a C rest (hcs C (by simp)) Phead h).1 hhead (erest tailProd)
        simpa [g, Fhead, Phead, erest] using htail
      have hrowInd :
          ∀ p : Cplus n C,
            (fun tailProd : factorProduct Fs => g (p, tailProd)) ∈
              independentAllowed Fs := by
        intro p
        rcases
            (mem_packageAllowedBoundarySpace_iff_exists_factor
              n a rest hTail Itail
              (fun tail : CoordsList n rest => h (p, tail))).1 (hrows p) with
          ⟨row, hrow, htransport⟩
        have heq :
            (fun tailProd : factorProduct Fs => g (p, tailProd)) = row := by
          funext tailProd
          have hrel := congrFun htransport (erest tailProd)
          change row (erest.symm (erest tailProd)) =
            h (p, erest tailProd) at hrel
          have hs : erest.symm (erest tailProd) = tailProd :=
            erest.left_inv tailProd
          rw [hs] at hrel
          simpa [g, erest] using hrel.symm
        rw [heq]
        simpa [Fs] using hrow
      have hg : g ∈ independentAllowed (Fhead :: Fs) :=
        (mem_independentAllowed_cons_iff Fhead Fs g).2 ⟨hrowInd, hcols⟩
      simpa [packageChildSliceFactors, hcs, Phead, Fhead, Fs, hTail, Itail,
        nodeTailInputsOfCons] using hg
    · funext x
      rcases x with ⟨p, tail⟩
      change
        g ((packageFactorProductEquivCoordsList n (C :: rest) hcs
            I.childPackage).symm (p, tail)) = h (p, tail)
      rw [packageFactorProductEquivCoordsList_cons_symm n C rest hcs I.childPackage]
      have hEqv :
          packageFactorProductEquivCoordsList n rest
            (fun D hDmem => hcs D (by simp [hDmem]))
            (fun D hDmem => I.childPackage D (by simp [hDmem])) =
            erest := by
        rfl
      rw [hEqv]
      change h (p, erest (erest.symm tail)) = h (p, tail)
      have hs : erest (erest.symm tail) = tail := erest.right_inv tail
      simp [hs]

theorem root_mem_packageAllowedRootFieldSpace_imp_headParentRootBoundary_mem_headAllowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) := by
  intro hroot
  have hboundary :
      I.parentRootCopenBridge.linearEquiv root ∈
        packageAllowedBoundarySpace n a (C :: rest) hT I :=
    (mem_packageAllowedRootFieldSpace_iff_boundary
      n a (C :: rest) hT I root).1 hroot
  have hcanonical :
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        packageAllowedBoundarySpace n a (C :: rest) hT I := by
    simpa [headParentRootBoundaryFieldFromRoot, hbridge] using hboundary
  exact
    mem_packageAllowedBoundarySpace_cons_imp_headAllowedBoundarySpace
      n a C rest hT I
      (headParentRootBoundaryFieldFromRoot n a C rest root)
      hcanonical

theorem root_mem_packageAllowedRootFieldSpace_imp_forall_headBranch_mem_Kchild
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      ∀ tail : CoordsList n rest,
        headParentRootBranchFieldFromRoot n a C rest root tail ∈
          Kchild n C
            (rootWeight_pos_of_positiveWeights
              (child_positive_of_node hT C (by simp)))
            (I.childPackage C (by simp)).boundaryMessageSpace := by
  intro hroot
  have hhead :=
    root_mem_packageAllowedRootFieldSpace_imp_headParentRootBoundary_mem_headAllowed
      n a C rest hT I hbridge root hroot
  exact
    (headParentRootBoundaryFieldFromRoot_mem_headAllowedBoundarySpace_iff
      n a C rest
      (child_positive_of_node hT C (by simp))
      (I.childPackage C (by simp)) root).1 hhead

theorem root_mem_packageAllowedRootFieldSpace_imp_forall_headBranch_cycDiff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      ∀ tail : CoordsList n rest,
        cycDiff n
          (Module.Dual F2
            (I.childPackage C (by simp)).boundaryMessageSpace)
          (headChildR n C (child_positive_of_node hT C (by simp))
            (I.childPackage C (by simp))
            (headParentRootBranchFieldFromRoot n a C rest root tail)) = 0 := by
  intro hroot tail
  exact
    (mem_Kchild_iff n C
      (rootWeight_pos_of_positiveWeights
        (child_positive_of_node hT C (by simp)))
      (I.childPackage C (by simp)).boundaryMessageSpace
      (headParentRootBranchFieldFromRoot n a C rest root tail)).1
      (root_mem_packageAllowedRootFieldSpace_imp_forall_headBranch_mem_Kchild
        n a C rest hT I hbridge root hroot tail)

theorem root_mem_packageAllowedRootFieldSpace_imp_tailRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I →
      ∀ p : Cplus n C,
        (fun tail : CoordsList n rest =>
          headParentRootBoundaryFieldFromRoot n a C rest root (p, tail)) ∈
          packageAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I) := by
  intro hroot
  have hboundary :
      I.parentRootCopenBridge.linearEquiv root ∈
        packageAllowedBoundarySpace n a (C :: rest) hT I :=
    (mem_packageAllowedRootFieldSpace_iff_boundary
      n a (C :: rest) hT I root).1 hroot
  have hcanonical :
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        packageAllowedBoundarySpace n a (C :: rest) hT I := by
    simpa [headParentRootBoundaryFieldFromRoot, hbridge] using hboundary
  exact
    mem_packageAllowedBoundarySpace_cons_imp_tailRows
      n a C rest hT I
      (headParentRootBoundaryFieldFromRoot n a C rest root)
      hcanonical

theorem root_mem_packageAllowedRootFieldSpace_iff_head_tailRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∧
      ∀ p : Cplus n C,
        (fun tail : CoordsList n rest =>
          headParentRootBoundaryFieldFromRoot n a C rest root (p, tail)) ∈
          packageAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I) := by
  constructor
  · intro hroot
    exact ⟨
      root_mem_packageAllowedRootFieldSpace_imp_headParentRootBoundary_mem_headAllowed
        n a C rest hT I hbridge root hroot,
      root_mem_packageAllowedRootFieldSpace_imp_tailRows
        n a C rest hT I hbridge root hroot⟩
  · intro hh
    have hboundary :
        headParentRootBoundaryFieldFromRoot n a C rest root ∈
          packageAllowedBoundarySpace n a (C :: rest) hT I :=
      (mem_packageAllowedBoundarySpace_cons_iff_headAllowed_tailRows
        n a C rest hT I
        (headParentRootBoundaryFieldFromRoot n a C rest root)).2 hh
    have hIboundary :
        I.parentRootCopenBridge.linearEquiv root ∈
          packageAllowedBoundarySpace n a (C :: rest) hT I := by
      simpa [headParentRootBoundaryFieldFromRoot, hbridge] using hboundary
    exact
      (mem_packageAllowedRootFieldSpace_iff_boundary
        n a (C :: rest) hT I root).2 hIboundary

theorem root_not_mem_packageAllowedRootFieldSpace_iff_head_notAllowed_or_exists_tailRow
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∉ packageAllowedRootFieldSpace n a (C :: rest) hT I ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∨
      ∃ p : Cplus n C,
        (fun tail : CoordsList n rest =>
          headParentRootBoundaryFieldFromRoot n a C rest root (p, tail)) ∉
          packageAllowedBoundarySpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I) := by
  classical
  rw [root_mem_packageAllowedRootFieldSpace_iff_head_tailRows
    n a C rest hT I hbridge root]
  constructor
  · intro hnot
    by_cases hhead : headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp))
    · right
      have hnotRows :
          ¬ ∀ p : Cplus n C,
            (fun tail : CoordsList n rest =>
              headParentRootBoundaryFieldFromRoot n a C rest root (p, tail)) ∈
              packageAllowedBoundarySpace n a rest
                (positiveWeights_node_tail_of_cons hT)
                (nodeTailInputsOfCons n a C rest hT I) := by
        intro hrows
        exact hnot ⟨hhead, hrows⟩
      exact not_forall.mp hnotRows
    · exact Or.inl hhead
  · intro hcase hall
    rcases hall with ⟨hhead, hrows⟩
    rcases hcase with hheadNot | htail
    · exact hheadNot hhead
    · rcases htail with ⟨p, hp⟩
      exact hp (hrows p)

noncomputable def tailRootFieldFromHeadCplus
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C) :
    RootFieldAssignmentClean n (RTree.node a rest) :=
  (RootFieldCleanCopenBridge.node n a rest).linearEquiv.symm
    (fun tail : CoordsList n rest =>
      headParentRootBoundaryFieldFromRoot n a C rest root (p, tail))

theorem tailRootFieldFromHeadCplus_boundary
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Cplus n C) :
    (RootFieldCleanCopenBridge.node n a rest).linearEquiv
        (tailRootFieldFromHeadCplus n a C rest root p) =
      (fun tail : CoordsList n rest =>
        headParentRootBoundaryFieldFromRoot n a C rest root (p, tail)) := by
  simp [tailRootFieldFromHeadCplus]

theorem root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageAllowedRootFieldSpace n a (C :: rest) hT I ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∧
      ∀ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∈
          packageAllowedRootFieldSpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I) := by
  rw [root_mem_packageAllowedRootFieldSpace_iff_head_tailRows
    n a C rest hT I hbridge root]
  constructor
  · intro hh
    rcases hh with ⟨hhead, hrows⟩
    refine ⟨hhead, ?_⟩
    intro p
    exact
      (mem_packageAllowedRootFieldSpace_iff_boundary
        n a rest (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT I)
        (tailRootFieldFromHeadCplus n a C rest root p)).2 (by
          simpa [tailRootFieldFromHeadCplus, nodeTailInputsOfCons]
            using hrows p)
  · intro hh
    rcases hh with ⟨hhead, htails⟩
    refine ⟨hhead, ?_⟩
    intro p
    have hboundary :=
      (mem_packageAllowedRootFieldSpace_iff_boundary
        n a rest (positiveWeights_node_tail_of_cons hT)
        (nodeTailInputsOfCons n a C rest hT I)
        (tailRootFieldFromHeadCplus n a C rest root p)).1 (htails p)
    simpa [tailRootFieldFromHeadCplus, nodeTailInputsOfCons]
      using hboundary

theorem root_not_mem_packageAllowedRootFieldSpace_iff_head_notAllowed_or_exists_tailRoot
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∉ packageAllowedRootFieldSpace n a (C :: rest) hT I ↔
      headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∨
      ∃ p : Cplus n C,
        tailRootFieldFromHeadCplus n a C rest root p ∉
          packageAllowedRootFieldSpace n a rest
            (positiveWeights_node_tail_of_cons hT)
            (nodeTailInputsOfCons n a C rest hT I) := by
  classical
  rw [root_mem_packageAllowedRootFieldSpace_iff_head_tailRootRows
    n a C rest hT I hbridge root]
  constructor
  · intro hnot
    by_cases hhead : headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headAllowedBoundarySpace n a C rest
          (child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp))
    · right
      have hnotRows :
          ¬ ∀ p : Cplus n C,
            tailRootFieldFromHeadCplus n a C rest root p ∈
              packageAllowedRootFieldSpace n a rest
                (positiveWeights_node_tail_of_cons hT)
                (nodeTailInputsOfCons n a C rest hT I) := by
        intro hrows
        exact hnot ⟨hhead, hrows⟩
      exact not_forall.mp hnotRows
    · exact Or.inl hhead
  · intro hcase hall
    rcases hall with ⟨hhead, hrows⟩
    rcases hcase with hheadNot | htail
    · exact hheadNot hhead
    · rcases htail with ⟨p, hp⟩
      exact hp (hrows p)

end Imbalance
end TreeGraph
