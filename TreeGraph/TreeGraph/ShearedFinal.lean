import TreeGraph.Imbalance.ShearedFinal
import TreeGraph.Imbalance.NodePackageShearedPredicate
import TreeGraph.FinalTheorem

namespace TreeGraph
namespace ShearedFinal

noncomputable def openPackage
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.OpenNormalCleanPackage n T hT :=
  Imbalance.CanonicalSheared.openPackage n T hT

@[simp] theorem openPackage_isCanonical
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (openPackage n T hT).IsCanonical :=
  Imbalance.CanonicalSheared.openPackage_isCanonical n T hT

open Classical in
theorem openSignedSumClean_eq
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T)
    (root : Imbalance.RootFieldAssignmentClean n T) :
    Imbalance.openNormalSignedSumClean n T root =
      if root ∈ (openPackage n T hT).openBridge.rootMessageSpace then
        (2 : ℤ) ^ (Imbalance.Xdim n T - Imbalance.Ydim n T hT)
      else 0 :=
  Imbalance.CanonicalSheared.open_signed_sum_eq n T hT root

noncomputable def openBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.OpenNormalCleanReductionBridge n T hT :=
  Imbalance.CanonicalSheared.openBridge n T hT

noncomputable def closedBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.NormalCleanReductionBridge n T hT :=
  Imbalance.CanonicalSheared.closedBridge n T hT

theorem rootFieldCleanCopenBridge_ofTree_isCanonical
    (n : Nat) [NeZero n] (T : RTree) :
    (Imbalance.RootFieldCleanCopenBridge.ofTree n T).IsCanonical :=
  Imbalance.RootFieldCleanCopenBridge.ofTree_isCanonical n T

theorem rootFieldCleanCopenBridge_node_isCanonical
    (n a : Nat) [NeZero n] (cs : List RTree) :
    (Imbalance.RootFieldCleanCopenBridge.node n a cs).IsCanonical :=
  Imbalance.RootFieldCleanCopenBridge.node_isCanonical n a cs

theorem rootBridge_linearEquiv_apply_of_isCanonical_copen
    (n : Nat) [NeZero n] (T : RTree)
    (B : Imbalance.RootFieldCleanCopenBridge n T)
    (hB : B.IsCanonical)
    (r : Imbalance.RootFieldAssignmentClean n T)
    (y : Imbalance.Copen n T) :
    B.linearEquiv r y =
      r ((Imbalance.rootFieldDomainCleanEquivCopen n T).symm y) :=
  Imbalance.rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical_copen
    n T B hB r y

theorem rootBridge_linearEquiv_apply_of_isCanonical
    (n : Nat) [NeZero n] (T : RTree)
    (B : Imbalance.RootFieldCleanCopenBridge n T)
    (hB : B.IsCanonical)
    (r : Imbalance.RootFieldAssignmentClean n T)
    (rd : Imbalance.RootFieldDomainClean n T) :
    B.linearEquiv r (Imbalance.rootFieldDomainCleanEquivCopen n T rd) =
      r rd :=
  Imbalance.rootFieldCleanCopenBridge_linearEquiv_apply_of_isCanonical
    n T B hB r rd

theorem rootBridge_symm_apply_of_isCanonical
    (n : Nat) [NeZero n] (T : RTree)
    (B : Imbalance.RootFieldCleanCopenBridge n T)
    (hB : B.IsCanonical)
    (mu : Imbalance.BoundaryField n T)
    (rd : Imbalance.RootFieldDomainClean n T) :
    ((B.linearEquiv).symm mu) rd =
      mu (Imbalance.rootFieldDomainCleanEquivCopen n T rd) :=
  Imbalance.rootFieldCleanCopenBridge_symm_apply_of_isCanonical
    n T B hB mu rd

noncomputable def leafCanonicalOpenPackage
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    Imbalance.OpenNormalCleanPackage n (RTree.node a []) hT :=
  Imbalance.OpenNormalCleanPackage.leafCanonical n a hT

@[simp] theorem leafCanonicalOpenPackage_isCanonical
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    (leafCanonicalOpenPackage n a hT).IsCanonical :=
  Imbalance.OpenNormalCleanPackage.leafCanonical_isCanonical n a hT

noncomputable def singleEdgeCanonicalOpenPackage
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    Imbalance.OpenNormalCleanPackage
      n (RTree.node a [RTree.node b []]) hT :=
  Imbalance.OpenNormalCleanPackage.singleEdgeCanonical n a b hT

@[simp] theorem singleEdgeCanonicalOpenPackage_isCanonical
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    (singleEdgeCanonicalOpenPackage n a b hT).IsCanonical :=
  Imbalance.OpenNormalCleanPackage.singleEdgeCanonical_isCanonical n a b hT

noncomputable def headChildRSheared
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC) :
    Imbalance.BranchField n C →ₗ[F2]
      (Imbalance.Rep n → Module.Dual F2 P.boundaryMessageSpace) :=
  Imbalance.headChildRSheared n C hC P

theorem headChildRSheared_surjective
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC) :
    Function.Surjective (headChildRSheared n C hC P) :=
  Imbalance.headChildRSheared_surjective n C hC P

noncomputable def headChildRShearedFull
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C) :
    Imbalance.BranchField n C →ₗ[F2]
      (Imbalance.Rep n → Module.Dual F2 (Imbalance.BoundaryField n C)) :=
  Imbalance.headChildRShearedFull n C hC

@[simp] theorem headChildRShearedFull_node_apply
    (n b : Nat) [NeZero n]
    (ds : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (h : Imbalance.BranchField n (RTree.node b ds))
    (α : Imbalance.Rep n)
    (μ : Imbalance.BoundaryField n (RTree.node b ds)) :
    headChildRShearedFull n (RTree.node b ds) hC h α μ =
      ∑ y : Imbalance.Copen n (RTree.node b ds),
        μ y *
          (∑ x : Imbalance.Block n b,
            if Imbalance.diag n b x +
                Imbalance.copenTotalDiag n (RTree.node b ds) y = α then
              h (x, y)
            else
              0) := by
  exact Imbalance.headChildRShearedFull_node_apply n b ds hC h α μ

noncomputable def headChildIndexShearedFullBoundaryCoeff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : Imbalance.HeadChildIndex n a rest) :
    Module.Dual F2 (Imbalance.BoundaryField n C) :=
  Imbalance.headChildIndexShearedFullBoundaryCoeff
    n a C rest hC P root idx

theorem headChildIndexShearedFullBoundaryCoeff_apply
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : Imbalance.HeadChildIndex n a rest)
    (μ : Imbalance.BoundaryField n C) :
    headChildIndexShearedFullBoundaryCoeff
        n a C rest hC P root idx μ =
      (headChildRShearedFull n C hC
          (Imbalance.headParentRootBranchFieldFromRoot
            n a C rest root (Imbalance.headChildIndexTail idx))
          (Imbalance.headChildIndexRootDiag idx) +
        headChildRShearedFull n C hC
          (Imbalance.headParentRootBranchFieldFromRoot
            n a C rest root (Imbalance.headChildIndexTail idx))
          (Imbalance.headChildIndexRootDiag idx + 1)) μ := by
  simpa [
    headChildRShearedFull,
    headChildIndexShearedFullBoundaryCoeff
  ] using
    Imbalance.headChildIndexShearedFullBoundaryCoeff_apply
      n a C rest hC P root idx μ

noncomputable def headIndexShearedPhysicalPairWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : Imbalance.HeadChildIndex n a rest)
    (pair :
      Imbalance.RootFieldAssignmentClean n C ×
        Imbalance.OpenNormalAssignmentClean n C) : ℤ :=
  Imbalance.headIndexShearedPhysicalPairWeight
    n a C rest hC P root idx pair

theorem openPackage_pairSum_eq_messageSum_for_dual
    (n : Nat) [NeZero n]
    (C : RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (L : Module.Dual F2 (Imbalance.BoundaryField n C)) :
    (∑ pair :
      Imbalance.RootFieldAssignmentClean n C ×
        Imbalance.OpenNormalAssignmentClean n C,
      Imbalance.weightClean C
          (Imbalance.closeOpenNormalAssignmentClean pair.1 pair.2) *
        Imbalance.chi (L (P.rootCopenBridge.linearEquiv pair.1))) =
      (2 : ℤ) ^ (Imbalance.Xdim n C - Imbalance.Ydim n C hC) *
        (∑ μ : P.boundaryMessageSpace, Imbalance.chi (L μ.1)) :=
  Imbalance.openPackage_pairSum_eq_messageSum_for_dual n C hC P L

theorem headIndexShearedPhysicalPairSum_eq_messageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (idx : Imbalance.HeadChildIndex n a rest) :
    (∑ pair :
      Imbalance.RootFieldAssignmentClean n C ×
        Imbalance.OpenNormalAssignmentClean n C,
      headIndexShearedPhysicalPairWeight
        n a C rest hC P root idx pair) =
        (2 : ℤ) ^ (Imbalance.Xdim n C - Imbalance.Ydim n C hC) *
          (∑ μ : P.boundaryMessageSpace,
            Imbalance.chi
              (headChildIndexShearedFullBoundaryCoeff
                n a C rest hC P root idx μ.1)) := by
  simpa [
    headIndexShearedPhysicalPairWeight,
    headChildIndexShearedFullBoundaryCoeff
  ] using
    Imbalance.headIndexShearedPhysicalPairSum_eq_messageSum
      n a C rest hC P root idx

noncomputable def headChildOpenDataShearedFullProductWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (data : Imbalance.HeadChildOpenData n a C rest) : ℤ :=
  Imbalance.headChildOpenDataShearedFullProductWeight
    n a C rest hC P root data

noncomputable def headChildOpenDataShearedFullSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    ℤ :=
  Imbalance.headChildOpenDataShearedFullSignedSum n a C rest hC P root

noncomputable def headShearedBranchMessageSignedSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    ℤ :=
  Imbalance.headShearedBranchMessageSignedSum n a C rest hC P root

theorem headChildOpenDataShearedFullSignedSum_eq_sum_productWeight
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataShearedFullSignedSum n a C rest hC P root =
      ∑ data : Imbalance.HeadChildOpenData n a C rest,
        headChildOpenDataShearedFullProductWeight
          n a C rest hC P root data := by
  classical
  letI : Fintype (Imbalance.HeadChildOpenData n a C rest) := Pi.instFintype
  change
    Imbalance.headChildOpenDataShearedFullSignedSum n a C rest hC P root =
      ∑ data : Imbalance.HeadChildOpenData n a C rest,
        Imbalance.headChildOpenDataShearedFullProductWeight
          n a C rest hC P root data
  exact
    Imbalance.headChildOpenDataShearedFullSignedSum_eq_sum_productWeight
      n a C rest hC P root

theorem headChildOpenDataShearedFullSignedSum_factorized
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataShearedFullSignedSum n a C rest hC P root =
      ∏ idx : Imbalance.HeadChildIndex n a rest,
        ∑ pair :
          Imbalance.RootFieldAssignmentClean n C ×
            Imbalance.OpenNormalAssignmentClean n C,
          headIndexShearedPhysicalPairWeight
            n a C rest hC P root idx pair := by
  simpa [
    headChildOpenDataShearedFullSignedSum,
    headIndexShearedPhysicalPairWeight
  ] using
    Imbalance.headChildOpenDataShearedFullSignedSum_factorized
      n a C rest hC P root

theorem headChildOpenDataShearedFullSignedSum_eq_descScalar_mul_messageSum
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headChildOpenDataShearedFullSignedSum n a C rest hC P root =
      (2 : ℤ) ^
          Imbalance.branchDescendantScalarExponent n a 0 C rest hC *
        headShearedBranchMessageSignedSum n a C rest hC P root := by
  simpa [
    headChildOpenDataShearedFullSignedSum,
    headShearedBranchMessageSignedSum
  ] using
    Imbalance.headChildOpenDataShearedFullSignedSum_eq_descScalar_mul_shearedMessageSum
      n a C rest hC P root

noncomputable def headShearedOneSliceKernel
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC) :
    Submodule F2 (Imbalance.BranchField n C) :=
  Imbalance.headShearedOneSliceKernel n C hC P

theorem finrank_headShearedOneSliceKernel
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC) :
    Module.finrank F2 (headShearedOneSliceKernel n C hC P) =
      Imbalance.branchAllowedDim
        n (RTree.totalWeight C) (Imbalance.Ydim n C hC) :=
  Imbalance.finrank_headShearedOneSliceKernel n C hC P

noncomputable def headShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC) :
    Submodule F2 (Imbalance.BoundaryField n (RTree.node a (C :: rest))) :=
  Imbalance.headShearedAllowedBoundarySpace n a C rest hC P

theorem mem_headShearedAllowedBoundarySpace_iff_forall_headBranch_mem_kernel
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (h : Imbalance.BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ headShearedAllowedBoundarySpace n a C rest hC P ↔
      ∀ tail : Imbalance.CoordsList n rest,
        (Imbalance.boundaryHeadSliceLinearEquiv n a C rest h tail) ∈
          headShearedOneSliceKernel n C hC P :=
  Imbalance.mem_headShearedAllowedBoundarySpace_iff_forall_headBranch_mem_shearedKernel
    n a C rest hC P h

theorem finrank_headShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC) :
    Module.finrank F2
      (headShearedAllowedBoundarySpace n a C rest hC P) =
      Fintype.card (Imbalance.CoordsList n rest) *
        Module.finrank F2 (Imbalance.BranchField n C) -
      Fintype.card (Imbalance.CoordsList n rest) * (n - 1) *
        Module.finrank F2 P.boundaryMessageSpace :=
  Imbalance.finrank_headShearedAllowedBoundarySpace n a C rest hC P

theorem finrank_headShearedAllowedBoundarySpace_Ydim_shape
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC) :
    Module.finrank F2
      (headShearedAllowedBoundarySpace n a C rest hC P) =
      Fintype.card (Imbalance.CoordsList n rest) *
        (n ^ RTree.totalWeight C - (n - 1) * Imbalance.Ydim n C hC) :=
  Imbalance.finrank_headShearedAllowedBoundarySpace_Ydim_shape
    n a C rest hC P

theorem headShearedBranchMessageSignedSum_eq_if_allowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    headShearedBranchMessageSignedSum n a C rest hC P root =
      (by
        classical
        exact
          if Imbalance.headParentRootBoundaryFieldFromRoot
              n a C rest root ∈
              headShearedAllowedBoundarySpace n a C rest hC P then
            (2 : ℤ) ^
              Imbalance.branchMessageScalarExponent n a 0 C rest hC
          else
            0) :=
  by
    simpa [headShearedBranchMessageSignedSum] using
      Imbalance.headShearedBranchMessageSignedSum_eq_if_headShearedAllowed_branchScalar
        n a C rest hC P root

theorem headShearedBranchMessageSignedSum_of_allowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    Imbalance.headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headShearedAllowedBoundarySpace n a C rest hC P →
      headShearedBranchMessageSignedSum n a C rest hC P root =
        (2 : ℤ) ^
          Imbalance.branchMessageScalarExponent n a 0 C rest hC := by
  intro hhead
  simpa [hhead] using
    headShearedBranchMessageSignedSum_eq_if_allowed
      n a C rest hC P root

theorem headShearedBranchMessageSignedSum_of_not_allowed
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    Imbalance.headParentRootBoundaryFieldFromRoot n a C rest root ∉
        headShearedAllowedBoundarySpace n a C rest hC P →
      headShearedBranchMessageSignedSum n a C rest hC P root = 0 := by
  intro hhead
  simpa [headShearedBranchMessageSignedSum] using
    Imbalance.headShearedBranchMessageSignedSum_of_head_notShearedAllowed
      n a C rest hC P root hhead

noncomputable def packageShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Submodule F2 (Imbalance.BoundaryField n (RTree.node a cs)) :=
  Imbalance.packageShearedAllowedBoundarySpace n a cs hT I

noncomputable def packageShearedAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Submodule F2
      (Imbalance.RootFieldAssignmentClean n (RTree.node a cs)) :=
  Imbalance.packageShearedAllowedRootFieldSpace n a cs hT I

theorem packageShearedAllowedBoundarySpace_nil_eq_top
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : Imbalance.NodeOpenPackageStepInputs n a [] hT) :
    packageShearedAllowedBoundarySpace n a [] hT I = ⊤ :=
  Imbalance.packageShearedAllowedBoundarySpace_nil_eq_top n a hT I

theorem mem_packageShearedAllowedBoundarySpace_nil
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : Imbalance.NodeOpenPackageStepInputs n a [] hT)
    (h : Imbalance.BoundaryField n (RTree.node a [])) :
    h ∈ packageShearedAllowedBoundarySpace n a [] hT I :=
  Imbalance.mem_packageShearedAllowedBoundarySpace_nil n a hT I h

theorem mem_packageShearedAllowedBoundarySpace_cons_iff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : Imbalance.NodeOpenPackageStepInputs n a (C :: rest) hT)
    (h : Imbalance.BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ packageShearedAllowedBoundarySpace n a (C :: rest) hT I ↔
      h ∈ headShearedAllowedBoundarySpace n a C rest
          (Imbalance.child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∧
        ∀ p : Imbalance.Cplus n C,
          (fun tail : Imbalance.CoordsList n rest => h (p, tail)) ∈
            packageShearedAllowedBoundarySpace n a rest
              (Imbalance.positiveWeights_node_tail_of_cons hT)
              (Imbalance.nodeTailInputsOfCons n a C rest hT I) :=
  Imbalance.mem_packageShearedAllowedBoundarySpace_cons_iff
    n a C rest hT I h

theorem packageShearedAllowedBoundarySpace_cons_eq_sliceIntersection
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : Imbalance.NodeOpenPackageStepInputs n a (C :: rest) hT) :
    packageShearedAllowedBoundarySpace n a (C :: rest) hT I =
      Imbalance.sliceIntersection
        (Imbalance.Cplus n C) (Imbalance.CoordsList n rest)
        (headShearedOneSliceKernel n C
          (Imbalance.child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)))
        (packageShearedAllowedBoundarySpace n a rest
          (Imbalance.positiveWeights_node_tail_of_cons hT)
          (Imbalance.nodeTailInputsOfCons n a C rest hT I)) :=
  Imbalance.packageShearedAllowedBoundarySpace_cons_eq_sliceIntersection
    n a C rest hT I

theorem mem_packageShearedAllowedRootFieldSpace_iff_boundary
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a cs)) :
    root ∈ packageShearedAllowedRootFieldSpace n a cs hT I ↔
      I.parentRootCopenBridge.linearEquiv root ∈
        packageShearedAllowedBoundarySpace n a cs hT I :=
  Imbalance.mem_packageShearedAllowedRootFieldSpace_iff_boundary
    n a cs hT I root

theorem packageShearedAllowedRootFieldSpace_nil_eq_top
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : Imbalance.NodeOpenPackageStepInputs n a [] hT) :
    packageShearedAllowedRootFieldSpace n a [] hT I = ⊤ :=
  Imbalance.packageShearedAllowedRootFieldSpace_nil_eq_top n a hT I

theorem mem_packageShearedAllowedRootFieldSpace_nil
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a []))
    (I : Imbalance.NodeOpenPackageStepInputs n a [] hT)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a [])) :
    root ∈ packageShearedAllowedRootFieldSpace n a [] hT I :=
  Imbalance.mem_packageShearedAllowedRootFieldSpace_nil n a hT I root

theorem tailRootFieldFromHeadCplus_mem_packageShearedAllowedRootFieldSpace_iff
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : Imbalance.NodeOpenPackageStepInputs n a (C :: rest) hT)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (p : Imbalance.Cplus n C) :
    Imbalance.tailRootFieldFromHeadCplus n a C rest root p ∈
        packageShearedAllowedRootFieldSpace n a rest
          (Imbalance.positiveWeights_node_tail_of_cons hT)
          (Imbalance.nodeTailInputsOfCons n a C rest hT I) ↔
      (fun tail : Imbalance.CoordsList n rest =>
        Imbalance.headParentRootBoundaryFieldFromRoot
          n a C rest root (p, tail)) ∈
        packageShearedAllowedBoundarySpace n a rest
          (Imbalance.positiveWeights_node_tail_of_cons hT)
          (Imbalance.nodeTailInputsOfCons n a C rest hT I) :=
  Imbalance.tailRootFieldFromHeadCplus_mem_packageShearedAllowedRootFieldSpace_iff
    n a C rest hT I root p

theorem root_mem_packageShearedAllowedRootFieldSpace_iff_head_tailRootRows
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a (C :: rest)))
    (I : Imbalance.NodeOpenPackageStepInputs n a (C :: rest) hT)
    (hbridge :
      I.parentRootCopenBridge =
        Imbalance.RootFieldCleanCopenBridge.node n a (C :: rest))
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest))) :
    root ∈ packageShearedAllowedRootFieldSpace n a (C :: rest) hT I ↔
      Imbalance.headParentRootBoundaryFieldFromRoot n a C rest root ∈
        headShearedAllowedBoundarySpace n a C rest
          (Imbalance.child_positive_of_node hT C (by simp))
          (I.childPackage C (by simp)) ∧
      ∀ p : Imbalance.Cplus n C,
        Imbalance.tailRootFieldFromHeadCplus n a C rest root p ∈
          packageShearedAllowedRootFieldSpace n a rest
            (Imbalance.positiveWeights_node_tail_of_cons hT)
            (Imbalance.nodeTailInputsOfCons n a C rest hT I) :=
  Imbalance.root_mem_packageShearedAllowedRootFieldSpace_iff_head_tailRootRows
    n a C rest hT I hbridge root

theorem finrank_packageShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Module.finrank F2
      (packageShearedAllowedBoundarySpace n a cs hT I) =
      Imbalance.Ydim n (RTree.node a cs) hT :=
  Imbalance.finrank_packageShearedAllowedBoundarySpace n a cs hT I

theorem finrank_packageShearedAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Module.finrank F2
      (packageShearedAllowedRootFieldSpace n a cs hT I) =
      Imbalance.Ydim n (RTree.node a cs) hT :=
  Imbalance.finrank_packageShearedAllowedRootFieldSpace n a cs hT I

noncomputable instance packageShearedAllowedBoundarySpaceFintype
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Fintype (packageShearedAllowedBoundarySpace n a cs hT I) := by
  exact Imbalance.packageShearedAllowedBoundarySpaceFintype n a cs hT I

noncomputable instance packageShearedAllowedRootFieldSpaceFintype
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Fintype (packageShearedAllowedRootFieldSpace n a cs hT I) := by
  exact Imbalance.packageShearedAllowedRootFieldSpaceFintype n a cs hT I

theorem card_packageShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Fintype.card (packageShearedAllowedBoundarySpace n a cs hT I) =
      2 ^ Imbalance.Ydim n (RTree.node a cs) hT :=
  Imbalance.card_packageShearedAllowedBoundarySpace n a cs hT I

theorem card_packageShearedAllowedRootFieldSpace
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) :
    Fintype.card (packageShearedAllowedRootFieldSpace n a cs hT I) =
      2 ^ Imbalance.Ydim n (RTree.node a cs) hT :=
  Imbalance.card_packageShearedAllowedRootFieldSpace n a cs hT I

abbrev NodeShearedOpenPackageStepCertificate
    (n a : Nat) [NeZero n] (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (I : Imbalance.NodeOpenPackageStepInputs n a cs hT) : Prop :=
  Imbalance.NodeShearedOpenPackageStepCertificate n a cs hT I

theorem canonicalStepCertificateOfCanonicalChildren
    (n a : Nat) [NeZero n]
    (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        Imbalance.OpenNormalCleanPackage n C
          (Imbalance.child_positive_of_node hT C hCmem))
    (hcanon :
      ∀ C (hCmem : C ∈ cs), (childPackage C hCmem).IsCanonical) :
    NodeShearedOpenPackageStepCertificate n a cs hT
      (Imbalance.NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
        n a cs hT childPackage) :=
  Imbalance.canonicalShearedStepCertificateOfCanonicalChildren
    n a cs hT childPackage hcanon

noncomputable def openPackageStepTheoremOfStepCertificate
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : Imbalance.NodeOpenPackageStepInputs n a cs hT}
    (W : NodeShearedOpenPackageStepCertificate n a cs hT I) :
    Imbalance.NodeOpenPackageStepTheorem n a cs hT I :=
  Imbalance.NodeShearedOpenPackageStepCertificate.toOpenPackageStepTheorem W

noncomputable def openBridgeOfStepCertificate
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : Imbalance.NodeOpenPackageStepInputs n a cs hT}
    (W : NodeShearedOpenPackageStepCertificate n a cs hT I) :
    Imbalance.OpenNormalCleanReductionBridge n (RTree.node a cs) hT :=
  Imbalance.NodeShearedOpenPackageStepCertificate.toOpenBridge W

noncomputable def closedBridgeOfStepCertificate
    {n a : Nat} [NeZero n] {cs : List RTree}
    {hT : RTree.PositiveWeights (RTree.node a cs)}
    {I : Imbalance.NodeOpenPackageStepInputs n a cs hT}
    (W : NodeShearedOpenPackageStepCertificate n a cs hT I) :
    Imbalance.NormalCleanReductionBridge n (RTree.node a cs) hT :=
  Imbalance.NodeShearedOpenPackageStepCertificate.toClosedBridge W

def rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        Imbalance.OpenNormalCleanPackage n D
          (Imbalance.child_positive_of_node hT D hDmem))
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) : Prop :=
  Imbalance.rootShearedHeadTailAllowed n a b ds rest hT childPackage root

open Classical in
theorem openSignedSumClean_node_cons_eq_if_rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        Imbalance.OpenNormalCleanPackage n D
          (Imbalance.child_positive_of_node hT D hDmem))
    (Wtail :
      NodeShearedOpenPackageStepCertificate n a rest
        (Imbalance.positiveWeights_node_tail_of_cons hT)
        (Imbalance.nodeTailInputsOfCons n a (RTree.node b ds) rest hT
          (Imbalance.NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (RTree.node b ds :: rest) hT childPackage)))
    (hPhead :
      (childPackage (RTree.node b ds) (by simp)).IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) :
    Imbalance.openNormalSignedSumClean
        n (RTree.node a (RTree.node b ds :: rest)) root =
      if rootShearedHeadTailAllowed n a b ds rest hT childPackage root then
        (2 : ℤ) ^
          (Imbalance.Xdim n (RTree.node a (RTree.node b ds :: rest)) -
            Imbalance.Ydim n (RTree.node a (RTree.node b ds :: rest)) hT)
      else
        0 := by
  simpa [rootShearedHeadTailAllowed] using
    Imbalance.canonical_openNormalSignedSumClean_node_cons_eq_if_rootShearedHeadTailAllowed
      n a b ds rest hT childPackage Wtail hPhead root

theorem openSignedSumClean_node_cons_of_rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        Imbalance.OpenNormalCleanPackage n D
          (Imbalance.child_positive_of_node hT D hDmem))
    (Wtail :
      NodeShearedOpenPackageStepCertificate n a rest
        (Imbalance.positiveWeights_node_tail_of_cons hT)
        (Imbalance.nodeTailInputsOfCons n a (RTree.node b ds) rest hT
          (Imbalance.NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (RTree.node b ds :: rest) hT childPackage)))
    (hPhead :
      (childPackage (RTree.node b ds) (by simp)).IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) :
    rootShearedHeadTailAllowed n a b ds rest hT childPackage root →
      Imbalance.openNormalSignedSumClean
          n (RTree.node a (RTree.node b ds :: rest)) root =
        (2 : ℤ) ^
          (Imbalance.Xdim n (RTree.node a (RTree.node b ds :: rest)) -
            Imbalance.Ydim n (RTree.node a (RTree.node b ds :: rest)) hT) := by
  intro hroot
  exact
    Imbalance.canonical_openNormalSignedSumClean_node_cons_of_rootShearedHeadTailAllowed
      n a b ds rest hT childPackage Wtail hPhead root hroot

theorem openSignedSumClean_node_cons_of_not_rootShearedHeadTailAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hT : RTree.PositiveWeights
      (RTree.node a (RTree.node b ds :: rest)))
    (childPackage :
      ∀ D, (hDmem : D ∈ RTree.node b ds :: rest) →
        Imbalance.OpenNormalCleanPackage n D
          (Imbalance.child_positive_of_node hT D hDmem))
    (Wtail :
      NodeShearedOpenPackageStepCertificate n a rest
        (Imbalance.positiveWeights_node_tail_of_cons hT)
        (Imbalance.nodeTailInputsOfCons n a (RTree.node b ds) rest hT
          (Imbalance.NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a (RTree.node b ds :: rest) hT childPackage)))
    (hPhead :
      (childPackage (RTree.node b ds) (by simp)).IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest))) :
    ¬ rootShearedHeadTailAllowed n a b ds rest hT childPackage root →
      Imbalance.openNormalSignedSumClean
          n (RTree.node a (RTree.node b ds :: rest)) root = 0 := by
  intro hroot
  exact
    Imbalance.canonical_openNormalSignedSumClean_node_cons_of_not_rootShearedHeadTailAllowed
      n a b ds rest hT childPackage Wtail hPhead root hroot

noncomputable def headRootSuccTotalShearDataWithBridgeEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (B : Imbalance.RootFieldCleanCopenBridge n C) :
    Imbalance.HeadChildOpenData n a C rest ≃
      Imbalance.HeadChildOpenData n a C rest :=
  Imbalance.headRootSuccTotalShearDataWithBridgeEquiv n a C rest B

theorem actualHeadDiagDataWeight_eq_shearedFullProductWeight_of_canonical
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : Imbalance.OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail :
      Imbalance.ParentOpenTailFields n a (RTree.node b ds) rest)
    (data :
      Imbalance.HeadChildOpenData n a (RTree.node b ds) rest) :
    Imbalance.parentActualHeadDiagDataWeightAtTail
        n a (RTree.node b ds) rest hC P root tail data =
      headChildOpenDataShearedFullProductWeight
        n a (RTree.node b ds) rest hC P root
        (headRootSuccTotalShearDataWithBridgeEquiv
          n a (RTree.node b ds) rest P.rootCopenBridge data) := by
  simpa [
    headChildOpenDataShearedFullProductWeight,
    headRootSuccTotalShearDataWithBridgeEquiv
  ] using
    Imbalance.actualHeadDiagDataWeight_eq_shearedFullProductWeight_of_canonical
      n a b ds rest hC P hP root tail data

theorem actualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : Imbalance.ParentOpenTailFields n a C rest)
    (e :
      Imbalance.HeadChildOpenData n a C rest ≃
        Imbalance.HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : Imbalance.HeadChildOpenData n a C rest,
        Imbalance.parentActualHeadDataWeightAtTail
            n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    Imbalance.parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      headChildOpenDataShearedFullSignedSum n a C rest hC P root := by
  simpa [
    headChildOpenDataShearedFullProductWeight,
    headChildOpenDataShearedFullSignedSum
  ] using
    Imbalance.parentActualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_equiv
      n a C rest hC P root tail e hweight

theorem actualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_diagEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : Imbalance.ParentOpenTailFields n a C rest)
    (e :
      Imbalance.HeadChildOpenData n a C rest ≃
        Imbalance.HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : Imbalance.HeadChildOpenData n a C rest,
        Imbalance.parentActualHeadDiagDataWeightAtTail
            n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    Imbalance.parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      headChildOpenDataShearedFullSignedSum n a C rest hC P root := by
  simpa [
    headChildOpenDataShearedFullProductWeight,
    headChildOpenDataShearedFullSignedSum
  ] using
    Imbalance.parentActualHeadPhaseSignedSumAtTail_eq_shearedFullSignedSum_of_diagEquiv
      n a C rest hC P root tail e hweight

theorem actualHeadPhaseSignedSumAtTail_eq_descScalar_mul_messageSum_of_equiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : Imbalance.ParentOpenTailFields n a C rest)
    (e :
      Imbalance.HeadChildOpenData n a C rest ≃
        Imbalance.HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : Imbalance.HeadChildOpenData n a C rest,
        Imbalance.parentActualHeadDataWeightAtTail
            n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    Imbalance.parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      (2 : ℤ) ^
          Imbalance.branchDescendantScalarExponent n a 0 C rest hC *
        headShearedBranchMessageSignedSum n a C rest hC P root := by
  simpa [
    headChildOpenDataShearedFullProductWeight,
    headShearedBranchMessageSignedSum
  ] using
    Imbalance.parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_shearedMessageSum_of_equiv
      n a C rest hC P root tail e hweight

theorem actualHeadPhaseSignedSumAtTail_eq_descScalar_mul_messageSum_of_diagEquiv
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : Imbalance.OpenNormalCleanPackage n C hC)
    (root : Imbalance.RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (tail : Imbalance.ParentOpenTailFields n a C rest)
    (e :
      Imbalance.HeadChildOpenData n a C rest ≃
        Imbalance.HeadChildOpenData n a C rest)
    (hweight :
      ∀ data : Imbalance.HeadChildOpenData n a C rest,
        Imbalance.parentActualHeadDiagDataWeightAtTail
            n a C rest hC P root tail data =
          headChildOpenDataShearedFullProductWeight
            n a C rest hC P root (e data)) :
    Imbalance.parentActualHeadPhaseSignedSumAtTail n a C rest root tail =
      (2 : ℤ) ^
          Imbalance.branchDescendantScalarExponent n a 0 C rest hC *
        headShearedBranchMessageSignedSum n a C rest hC P root := by
  simpa [
    headChildOpenDataShearedFullProductWeight,
    headShearedBranchMessageSignedSum
  ] using
    Imbalance.parentActualHeadPhaseSignedSumAtTail_eq_descScalar_mul_shearedMessageSum_of_diagEquiv
      n a C rest hC P root tail e hweight

theorem actualHeadPhaseSum_eq_descScalar_mul_messageSum_of_canonical
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : Imbalance.OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail :
      Imbalance.ParentOpenTailFields n a (RTree.node b ds) rest) :
    Imbalance.parentActualHeadPhaseSignedSumAtTail
        n a (RTree.node b ds) rest root tail =
      (2 : ℤ) ^
          Imbalance.branchDescendantScalarExponent
            n a 0 (RTree.node b ds) rest hC *
        headShearedBranchMessageSignedSum
          n a (RTree.node b ds) rest hC P root := by
  simpa [headShearedBranchMessageSignedSum] using
    Imbalance.actualHeadPhaseSum_eq_descScalar_mul_shearedMessageSum_of_canonical
      n a b ds rest hC P hP root tail

theorem actualHeadPhaseSignedSumAtTail_eq_if_headShearedAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : Imbalance.OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : Imbalance.ParentOpenTailFields n a (RTree.node b ds) rest) :
    Imbalance.parentActualHeadPhaseSignedSumAtTail
        n a (RTree.node b ds) rest root tail =
      (by
        classical
        exact
          if Imbalance.headParentRootBoundaryFieldFromRoot
              n a (RTree.node b ds) rest root ∈
              headShearedAllowedBoundarySpace
                n a (RTree.node b ds) rest hC P then
            (2 : ℤ) ^
              Imbalance.branchScalarExponent
                n a 0 (RTree.node b ds) rest
          else
            0) :=
  Imbalance.parentActualHeadPhaseSignedSumAtTail_eq_if_headShearedAllowed_branchScalar_of_canonical
    n a b ds rest ha hC P hP root tail

theorem actualHeadPhaseSignedSumAtTail_of_headShearedAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : Imbalance.OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : Imbalance.ParentOpenTailFields n a (RTree.node b ds) rest) :
    Imbalance.headParentRootBoundaryFieldFromRoot
        n a (RTree.node b ds) rest root ∈
        headShearedAllowedBoundarySpace
          n a (RTree.node b ds) rest hC P →
      Imbalance.parentActualHeadPhaseSignedSumAtTail
          n a (RTree.node b ds) rest root tail =
        (2 : ℤ) ^
          Imbalance.branchScalarExponent
            n a 0 (RTree.node b ds) rest :=
  Imbalance.parentActualHeadPhaseSignedSumAtTail_of_head_shearedAllowed
    n a b ds rest ha hC P hP root tail

theorem actualHeadPhaseSignedSumAtTail_of_headNotShearedAllowed
    (n a b : Nat) [NeZero n]
    (ds rest : List RTree)
    (ha : 0 < a)
    (hC : RTree.PositiveWeights (RTree.node b ds))
    (P : Imbalance.OpenNormalCleanPackage n (RTree.node b ds) hC)
    (hP : P.IsCanonical)
    (root :
      Imbalance.RootFieldAssignmentClean n
        (RTree.node a (RTree.node b ds :: rest)))
    (tail : Imbalance.ParentOpenTailFields n a (RTree.node b ds) rest) :
    Imbalance.headParentRootBoundaryFieldFromRoot
        n a (RTree.node b ds) rest root ∉
        headShearedAllowedBoundarySpace
          n a (RTree.node b ds) rest hC P →
      Imbalance.parentActualHeadPhaseSignedSumAtTail
          n a (RTree.node b ds) rest root tail = 0 :=
  Imbalance.parentActualHeadPhaseSignedSumAtTail_of_head_notShearedAllowed
    n a b ds rest ha hC P hP root tail

theorem normalSignedSumClean_eq_abstract
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalSignedSumClean n T =
      Imbalance.abstractTreeSignedSum n T hT :=
  Imbalance.CanonicalSheared.normal_signed_sum_eq_abstract n T hT

theorem normalSignedSumClean_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalSignedSumClean n T = DeltaTreeModel n T :=
  Imbalance.CanonicalSheared.normal_signed_sum_eq_DeltaTreeModel n T hT

theorem normalFormRawSignedSumClean_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalFormRawSignedSumClean n T = DeltaTreeModel n T :=
  Imbalance.CanonicalSheared.normalFormRaw_signed_sum_eq_DeltaTreeModel
    n T hT

theorem rawNormalSignedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T = DeltaTreeModel n T :=
  Imbalance.CanonicalSheared.legacy_signed_sum_eq_DeltaTreeModel n T hT

theorem normalFormSignedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T = DeltaTreeModel n T :=
  Imbalance.CanonicalSheared.normalFormSignedSum_eq_DeltaTreeModel n T hT

theorem rawBitStringSignedSum_eq_DeltaTreeModel
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T = DeltaTreeModel n T :=
  Imbalance.CanonicalSheared.rawBitStringSignedSum_eq_DeltaTreeModel
    n T hT

theorem normalSignedSumClean_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalSignedSumClean n T = (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.normal_signed_sum_eq_two_pow_Xdim n T hT

theorem Xpoly_toNat_eq_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Int.toNat (Xpoly n T) = Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.Xpoly_toNat_eq_Xdim n T hT

theorem allTerms_toNat_eq_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Int.toNat (termSum n (allTerms T)) = Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.allTerms_toNat_eq_Xdim n T hT

theorem normalSignedSumClean_eq_two_pow_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      Imbalance.normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  Imbalance.CanonicalSheared.normal_signed_sum_eq_two_pow_Xpoly n T hT

theorem normalSignedSumClean_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalSignedSumClean n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.normal_signed_sum_eq_two_pow_Xpoly_toNat
    n T hT

theorem normalSignedSumClean_eq_two_pow_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      Imbalance.normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  Imbalance.CanonicalSheared.normal_signed_sum_eq_two_pow_allTerms n T hT

theorem normalSignedSumClean_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalSignedSumClean n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.normal_signed_sum_eq_two_pow_allTerms_toNat
    n T hT

theorem normalFormRawSignedSumClean_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalFormRawSignedSumClean n T =
      (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.normalFormRaw_signed_sum_eq_two_pow_Xdim
    n T hT

theorem normalFormRawSignedSumClean_eq_two_pow_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      Imbalance.normalFormRawSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  Imbalance.CanonicalSheared.normalFormRaw_signed_sum_eq_two_pow_Xpoly
    n T hT

theorem normalFormRawSignedSumClean_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalFormRawSignedSumClean n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.normalFormRaw_signed_sum_eq_two_pow_Xpoly_toNat
    n T hT

theorem normalFormRawSignedSumClean_eq_two_pow_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      Imbalance.normalFormRawSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  Imbalance.CanonicalSheared.normalFormRaw_signed_sum_eq_two_pow_allTerms
    n T hT

theorem normalFormRawSignedSumClean_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.normalFormRawSignedSumClean n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.normalFormRaw_signed_sum_eq_two_pow_allTerms_toNat
    n T hT

theorem rawNormalSignedSum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T = (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.legacy_signed_sum_eq_two_pow_Xdim n T hT

theorem rawNormalSignedSum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.legacy_signed_sum_eq_two_pow_Xpoly_toNat
    n T hT

theorem rawNormalSignedSum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawNormal.signedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.legacy_signed_sum_eq_two_pow_allTerms_toNat
    n T hT

theorem normalFormSignedSum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T =
      (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.normalFormSignedSum_eq_two_pow_Xdim n T hT

theorem normalFormSignedSum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.normalFormSignedSum_eq_two_pow_Xpoly_toNat
    n T hT

theorem normalFormSignedSum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.normalFormSignedSum_eq_two_pow_allTerms_toNat
    n T hT

theorem rawBitStringSignedSum_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T =
      (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.rawBitStringSignedSum_eq_two_pow_Xdim n T hT

theorem rawBitStringSignedSum_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.rawBitStringSignedSum_eq_two_pow_Xpoly_toNat
    n T hT

theorem rawBitStringSignedSum_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.rawBitStringSignedSum_eq_two_pow_allTerms_toNat
    n T hT

def NormalCleanClosedFormulaForAllPositive : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      Imbalance.normalSignedSumClean n T =
        (2 : ℤ) ^ Imbalance.Xdim n T

theorem normalCleanClosedFormulaForAllPositive :
    NormalCleanClosedFormulaForAllPositive := by
  intro T hT n _
  exact normalSignedSumClean_eq_two_pow_Xdim n T hT

def NormalFormRawCleanClosedFormulaForAllPositive : Prop :=
  ∀ {T : RTree}, RTree.PositiveWeights T →
    ∀ (n : Nat) [NeZero n],
      Imbalance.normalFormRawSignedSumClean n T =
        (2 : ℤ) ^ Imbalance.Xdim n T

theorem normalFormRawCleanClosedFormulaForAllPositive :
    NormalFormRawCleanClosedFormulaForAllPositive := by
  intro T hT n _
  exact normalFormRawSignedSumClean_eq_two_pow_Xdim n T hT

theorem modelCertificate_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.ModelCertificate T :=
  Imbalance.CanonicalSheared.modelCertificate_of_positiveWeights hT

theorem nodeStepRule : RawPrimitive.NodeStepRule :=
  Imbalance.CanonicalSheared.nodeStepRule

theorem nodeStepCertificate_of_positiveWeights
    {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    RawPrimitive.NodeStepCertificate a cs :=
  Imbalance.CanonicalSheared.nodeStepCertificate_of_positiveWeights hT

theorem subtreeModelCertificate_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.SubtreeModelCertificate T :=
  Imbalance.CanonicalSheared.subtreeModelCertificate_of_positiveWeights hT

theorem globalRawBitStringClosedXpoly :
    RawPrimitive.GlobalRawBitStringClosedXpoly :=
  Imbalance.CanonicalSheared.globalRawBitStringClosedXpoly

theorem globalRawBitStringClosedConnectedTerms :
    RawPrimitive.GlobalRawBitStringClosedConnectedTerms :=
  Imbalance.CanonicalSheared.globalRawBitStringClosedConnectedTerms

theorem completeFormalization : RawPrimitive.CompleteFormalization :=
  RawPrimitive.completeFormalization_of_globalRawBitStringClosedXpoly
    globalRawBitStringClosedXpoly

theorem finalClosedFormulaFor_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.FinalClosedFormulaFor T :=
  RawPrimitive.ModelCertificate.finalClosedFormulaFor
    (modelCertificate_of_positiveWeights hT)

theorem finalClosedFormulaForAllPositive :
    RawPrimitive.FinalClosedFormulaForAllPositive := by
  intro T hT
  exact finalClosedFormulaFor_of_positiveWeights hT

theorem finalClosedFormula : RawPrimitive.FinalClosedFormula :=
  RawPrimitive.finalClosedFormula_of_finalClosedFormulaForAllPositive
    finalClosedFormulaForAllPositive

theorem primitiveRawBitStringClosedFormula :
    RawPrimitive.PrimitiveRawBitStringClosedFormula :=
  RawPrimitive.completeFormalization_iff_primitiveRawBitStringClosedFormula.1
    completeFormalization

theorem rawAssignmentBitSignClosedFormula :
    RawPrimitive.RawAssignmentBitSignClosedFormula :=
  RawPrimitive.completeFormalization_iff_rawAssignmentBitSignClosedFormula.1
    completeFormalization

theorem rawAssignmentEdgePhaseClosedFormula :
    RawPrimitive.RawAssignmentEdgePhaseClosedFormula :=
  RawPrimitive.completeFormalization_iff_rawAssignmentEdgePhaseClosedFormula.1
    completeFormalization

theorem rawAssignmentExpandedEdgeClosedFormula :
    RawPrimitive.RawAssignmentExpandedEdgeClosedFormula :=
  RawPrimitive.completeFormalization_iff_rawAssignmentExpandedEdgeClosedFormula.1
    completeFormalization

theorem rawAssignmentExpandedEdgeClosedFormulaFor_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.RawAssignmentExpandedEdgeClosedFormulaFor T where
  positiveWeights := hT
  rawAssignmentExpandedEdgeSum := by
    intro n _
    exact rawAssignmentExpandedEdgeClosedFormula hT n

theorem rawExpandedEdgeDeltaFormula :
    RawPrimitive.RawExpandedEdgeDeltaFormula :=
  RawPrimitive.completeFormalization_iff_rawExpandedEdgeDeltaFormula.1
    completeFormalization

theorem rawExpandedEdgeDeltaFormulaFor_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.RawExpandedEdgeDeltaFormulaFor T where
  positiveWeights := hT
  rawExpandedEdgeDelta := by
    intro n _
    exact rawExpandedEdgeDeltaFormula hT n

theorem globalRawExpandedEdgeSignedSumClosed :
    RawPrimitive.GlobalRawExpandedEdgeSignedSumClosed :=
  RawPrimitive.completeFormalization_iff_globalRawExpandedEdgeSignedSumClosed.1
    completeFormalization

noncomputable def signedReductionBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.SignedReductionBridge n T hT
      (Imbalance.NormalAssignmentClean n T) :=
  Imbalance.CanonicalSheared.signedReductionBridge n T hT

theorem signedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (signedReductionBridge n T hT).DeltaRaw = (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.signedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    n T hT

theorem signedReductionBridge_DeltaRaw_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (signedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.signedReductionBridge_DeltaRaw_eq_two_pow_Xpoly_toNat
    n T hT

theorem signedReductionBridge_DeltaRaw_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (signedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.signedReductionBridge_DeltaRaw_eq_two_pow_allTerms_toNat
    n T hT

noncomputable def realizedRawSignedReductionBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.SignedReductionBridge n T hT
      (Imbalance.NormalFormRawAssignmentsClean n T) :=
  Imbalance.CanonicalSheared.realizedRawSignedReductionBridge n T hT

theorem realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawSignedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xdim
    n T hT

theorem realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawSignedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_Xpoly_toNat
    n T hT

theorem realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawSignedReductionBridge n T hT).DeltaRaw =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.realizedRawSignedReductionBridge_DeltaRaw_eq_two_pow_allTerms_toNat
    n T hT

noncomputable def realizedRawGraphBridge
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.GraphPhysicalRealizedRawBridge n Graph :=
  Imbalance.CanonicalSheared.realizedRawGraphBridge n graph T hT

noncomputable def realizedRawRootedBridge
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Imbalance.GraphPhysicalRealizedRawBridge n PUnit :=
  Imbalance.CanonicalSheared.realizedRawRootedBridge n T hT

theorem realizedRaw_graph_eq_two_pow_Xdim
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawGraphBridge n graph T hT).DeltaGraph =
      (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.realizedRaw_graph_eq_two_pow_Xdim n graph T hT

theorem realizedRaw_graph_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawGraphBridge n graph T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.realizedRaw_graph_eq_two_pow_Xpoly_toNat
    n graph T hT

theorem realizedRaw_graph_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawGraphBridge n graph T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.realizedRaw_graph_eq_two_pow_allTerms_toNat
    n graph T hT

theorem realizedRaw_graph_eq_two_pow_allTerms
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawGraphBridge n graph T hT).DeltaGraph =
        (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  Imbalance.CanonicalSheared.realizedRaw_graph_eq_two_pow_allTerms
    n graph T hT

theorem realizedRaw_graph_eq_two_pow_Xpoly
    (n : Nat) [NeZero n] {Graph : Type}
    (graph : Graph) (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawGraphBridge n graph T hT).DeltaGraph =
        (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  Imbalance.CanonicalSheared.realizedRaw_graph_eq_two_pow_Xpoly
    n graph T hT

theorem realizedRaw_rooted_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawRootedBridge n T hT).DeltaGraph =
      (2 : ℤ) ^ Imbalance.Xdim n T :=
  Imbalance.CanonicalSheared.realizedRaw_rooted_eq_two_pow_Xdim n T hT

theorem realizedRaw_rooted_eq_two_pow_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawRootedBridge n T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) :=
  Imbalance.CanonicalSheared.realizedRaw_rooted_eq_two_pow_Xpoly_toNat n T hT

theorem realizedRaw_rooted_eq_two_pow_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (realizedRawRootedBridge n T hT).DeltaGraph =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) :=
  Imbalance.CanonicalSheared.realizedRaw_rooted_eq_two_pow_allTerms_toNat n T hT

theorem realizedRaw_rooted_eq_two_pow_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawRootedBridge n T hT).DeltaGraph =
        (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  Imbalance.CanonicalSheared.realizedRaw_rooted_eq_two_pow_allTerms n T hT

theorem realizedRaw_rooted_eq_two_pow_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      (realizedRawRootedBridge n T hT).DeltaGraph =
        (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  Imbalance.CanonicalSheared.realizedRaw_rooted_eq_two_pow_Xpoly n T hT

theorem rawExpandedEdgeCompleteFormalization :
    RawPrimitive.RawExpandedEdgeCompleteFormalization :=
  RawPrimitive.rawExpandedEdgeCompleteFormalization_of_completeFormalization
    completeFormalization

theorem tree_imbalance_delta_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    DeltaTreeModel n T =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_delta_final_closed hT n

theorem tree_imbalance_signed_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawNormal.signedSum n T =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_signed_final_closed
    completeFormalization hT n

theorem tree_imbalance_raw_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawPrimitive.rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_raw_final_closed
    completeFormalization hT n

theorem tree_imbalance_normal_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawPrimitive.normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_normal_final_closed
    completeFormalization hT n

theorem tree_imbalance_primitive_raw_sum_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    (∑ Araw : RawPrimitive.NormalFormRawAssignments n T,
      RawPrimitive.weight T Araw.1) =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_primitive_raw_sum_final_closed
    completeFormalization hT n

theorem tree_imbalance_raw_assignment_bitSign_sum_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    (∑ Araw :
      { Araw : RawPrimitive.RawAssignment n T //
        RawPrimitive.RealizedByNormal T Araw },
      bitSign (RawPrimitive.totalPhase T Araw.1)) =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_raw_assignment_bitSign_sum_final_closed
    completeFormalization hT n

theorem tree_imbalance_raw_assignment_edge_phase_sum_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    (∑ Araw :
      { Araw : RawPrimitive.RawAssignment n T //
        RawPrimitive.RealizedByNormal T Araw },
      bitSign
        (∑ site : RawNormal.NormalSite n T,
          ((RTree.edgeList T).map
            (RawPrimitive.localEdgePhase Araw.1 site)).sum)) =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_raw_assignment_edge_phase_sum_final_closed
    completeFormalization hT n

theorem tree_imbalance_raw_expanded_edge_sum_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    (∑ Araw :
      { Araw : RawPrimitive.RawAssignment n T //
        RawPrimitive.RealizedByNormal T Araw },
      bitSign
        (∑ site : RawNormal.NormalSite n T,
          ((RTree.edgeList T).map
            (fun e =>
              let ketAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.ket ⟨p, hp⟩ site
                else
                  0
              let braAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.bra ⟨p, hp⟩ site
                else
                  0
              ketAt e.1 * ketAt e.2 + braAt e.1 * braAt e.2)).sum)) =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_raw_expanded_edge_sum_final_closed
    completeFormalization hT n

theorem tree_imbalance_rawExpandedEdgeSignedSum_delta
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawPrimitive.rawExpandedEdgeSignedSum n T = DeltaTreeModel n T :=
  RawPrimitive.tree_imbalance_rawExpandedEdgeSignedSum_delta
    completeFormalization hT n

theorem tree_imbalance_rawExpandedEdgeSignedSum_final_closed
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawPrimitive.rawExpandedEdgeSignedSum n T =
      (2 : ℤ) ^ Int.toNat
        (RawPrimitive.assignmentFactorProductExponent n T) :=
  RawPrimitive.tree_imbalance_rawExpandedEdgeSignedSum_final_closed_of_rawExpandedEdgeComplete
    rawExpandedEdgeCompleteFormalization hT n

theorem assignmentFactorProductExponent_toNat_eq_Xpoly_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Int.toNat (RawPrimitive.assignmentFactorProductExponent n T) =
      Int.toNat (Xpoly n T) := by
  rw [RawPrimitive.assignmentFactorProductExponent_eq_Xassign_of_positiveWeights
    (n := n) hT]
  rfl

theorem assignmentFactorProductExponent_toNat_eq_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Int.toNat (RawPrimitive.assignmentFactorProductExponent n T) =
      Imbalance.Xdim n T := by
  rw [assignmentFactorProductExponent_toNat_eq_Xpoly_toNat n T hT]
  exact Xpoly_toNat_eq_Xdim n T hT

theorem assignmentFactorProductExponent_toNat_eq_allTerms_toNat
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Int.toNat (RawPrimitive.assignmentFactorProductExponent n T) =
      Int.toNat (termSum n (allTerms T)) := by
  rw [assignmentFactorProductExponent_toNat_eq_Xdim n T hT,
    allTerms_toNat_eq_Xdim n T hT]

theorem tree_imbalance_rawExpandedEdgeSignedSum_eq_two_pow_Xdim
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawPrimitive.rawExpandedEdgeSignedSum n T =
      (2 : ℤ) ^ Imbalance.Xdim n T := by
  rw [tree_imbalance_rawExpandedEdgeSignedSum_final_closed hT n,
    assignmentFactorProductExponent_toNat_eq_Xdim n T hT]

theorem tree_imbalance_rawExpandedEdgeSignedSum_eq_two_pow_Xpoly_toNat
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawPrimitive.rawExpandedEdgeSignedSum n T =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [tree_imbalance_rawExpandedEdgeSignedSum_final_closed hT n,
    assignmentFactorProductExponent_toNat_eq_Xpoly_toNat n T hT]

theorem tree_imbalance_rawExpandedEdgeSignedSum_eq_two_pow_allTerms_toNat
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    RawPrimitive.rawExpandedEdgeSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [tree_imbalance_rawExpandedEdgeSignedSum_final_closed hT n,
    assignmentFactorProductExponent_toNat_eq_allTerms_toNat n T hT]

theorem tree_imbalance_raw_expanded_edge_sum_eq_two_pow_Xdim
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    (∑ Araw :
      { Araw : RawPrimitive.RawAssignment n T //
        RawPrimitive.RealizedByNormal T Araw },
      bitSign
        (∑ site : RawNormal.NormalSite n T,
          ((RTree.edgeList T).map
            (fun e =>
              let ketAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.ket ⟨p, hp⟩ site
                else
                  0
              let braAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.bra ⟨p, hp⟩ site
                else
                  0
              ketAt e.1 * ketAt e.2 + braAt e.1 * braAt e.2)).sum)) =
      (2 : ℤ) ^ Imbalance.Xdim n T := by
  rw [tree_imbalance_raw_expanded_edge_sum_final_closed hT n,
    assignmentFactorProductExponent_toNat_eq_Xdim n T hT]

theorem tree_imbalance_raw_expanded_edge_sum_eq_two_pow_Xpoly_toNat
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    (∑ Araw :
      { Araw : RawPrimitive.RawAssignment n T //
        RawPrimitive.RealizedByNormal T Araw },
      bitSign
        (∑ site : RawNormal.NormalSite n T,
          ((RTree.edgeList T).map
            (fun e =>
              let ketAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.ket ⟨p, hp⟩ site
                else
                  0
              let braAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.bra ⟨p, hp⟩ site
                else
                  0
              ketAt e.1 * ketAt e.2 + braAt e.1 * braAt e.2)).sum)) =
      (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [tree_imbalance_raw_expanded_edge_sum_final_closed hT n,
    assignmentFactorProductExponent_toNat_eq_Xpoly_toNat n T hT]

theorem tree_imbalance_raw_expanded_edge_sum_eq_two_pow_allTerms_toNat
    {T : RTree} (hT : RTree.PositiveWeights T)
    (n : Nat) [NeZero n] :
    (∑ Araw :
      { Araw : RawPrimitive.RawAssignment n T //
        RawPrimitive.RealizedByNormal T Araw },
      bitSign
        (∑ site : RawNormal.NormalSite n T,
          ((RTree.edgeList T).map
            (fun e =>
              let ketAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.ket ⟨p, hp⟩ site
                else
                  0
              let braAt (p : List Nat) : F2 :=
                if hp : p ∈ RTree.addresses T then
                  Araw.1.bra ⟨p, hp⟩ site
                else
                  0
              ketAt e.1 * ketAt e.2 + braAt e.1 * braAt e.2)).sum)) =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [tree_imbalance_raw_expanded_edge_sum_final_closed hT n,
    assignmentFactorProductExponent_toNat_eq_allTerms_toNat n T hT]

end ShearedFinal
end TreeGraph
