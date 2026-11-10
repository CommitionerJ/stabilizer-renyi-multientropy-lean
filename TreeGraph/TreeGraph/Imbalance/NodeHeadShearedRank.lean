import TreeGraph.Imbalance.NodeHeadShearedAllowed

namespace TreeGraph
namespace Imbalance

theorem headChildRSheared_surjective
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Function.Surjective (headChildRSheared n C hC P) := by
  classical
  cases C with
  | node b ds =>
      intro g
      have hroot : 0 < b :=
        rootWeight_pos_of_positiveWeights hC
      have hdual :
          ∀ α : Rep n,
            ∃ ell : Module.Dual F2
                (BoundaryField n (RTree.node b ds)),
              restrictDual P.boundaryMessageSpace ell = g α := by
        intro α
        exact dual_restrict_surjective P.boundaryMessageSpace (g α)
      choose ell hell using hdual
      let coeff : Rep n × Copen n (RTree.node b ds) → F2 :=
        fun p =>
          TreeGraph.linearFunctionalCoeff
            (Copen n (RTree.node b ds))
            (ell (p.1 + copenTotalDiag n (RTree.node b ds) p.2)) p.2
      rcases PiCoeff_surjective n hroot
          (Copen n (RTree.node b ds)) coeff with
        ⟨h, hh⟩
      refine ⟨h, ?_⟩
      funext α
      apply LinearMap.ext
      intro μ
      rw [headChildRSheared_apply]
      rw [headChildRShearedFull_node_apply]
      change
        (∑ y : Copen n (RTree.node b ds), μ.1 y *
          (∑ x : Block n b,
            if diag n b x + copenTotalDiag n (RTree.node b ds) y = α then
              h (x, y)
            else
              0)) = g α μ
      have hinner :
          ∀ y : Copen n (RTree.node b ds),
            (∑ x : Block n b,
              if diag n b x + copenTotalDiag n (RTree.node b ds) y = α then
                h (x, y)
              else
                0) =
              coeff (α - copenTotalDiag n (RTree.node b ds) y, y) := by
        intro y
        have hy :=
          congrArg
            (fun f : Rep n × Copen n (RTree.node b ds) → F2 =>
              f (α - copenTotalDiag n (RTree.node b ds) y, y)) hh
        have hy' :
            (∑ x : Block n b,
              if diag n b x =
                  α - copenTotalDiag n (RTree.node b ds) y then
                h (x, y)
              else
                0) =
              coeff (α - copenTotalDiag n (RTree.node b ds) y, y) := by
          simpa [PiCoeff_apply] using hy
        rw [← hy']
        refine Finset.sum_congr rfl ?_
        intro x _
        by_cases hx :
            diag n b x + copenTotalDiag n (RTree.node b ds) y = α
        · have hx' :
              diag n b x = α - copenTotalDiag n (RTree.node b ds) y := by
            calc
              diag n b x =
                  diag n b x + copenTotalDiag n (RTree.node b ds) y -
                    copenTotalDiag n (RTree.node b ds) y := by simp
              _ = α - copenTotalDiag n (RTree.node b ds) y := by rw [hx]
          simp [hx']
        · have hx' :
              diag n b x ≠ α - copenTotalDiag n (RTree.node b ds) y := by
            intro hdiag
            apply hx
            calc
              diag n b x + copenTotalDiag n (RTree.node b ds) y =
                  (α - copenTotalDiag n (RTree.node b ds) y) +
                    copenTotalDiag n (RTree.node b ds) y := by rw [hdiag]
              _ = α := by simp
          simp [hx, hx']
      calc
        (∑ y : Copen n (RTree.node b ds), μ.1 y *
          (∑ x : Block n b,
            if diag n b x + copenTotalDiag n (RTree.node b ds) y = α then
              h (x, y)
            else
              0)) =
            ∑ y : Copen n (RTree.node b ds), μ.1 y *
              coeff (α - copenTotalDiag n (RTree.node b ds) y, y) := by
              refine Finset.sum_congr rfl ?_
              intro y _
              rw [hinner y]
        _ =
            ∑ y : Copen n (RTree.node b ds), μ.1 y *
              TreeGraph.linearFunctionalCoeff
                (Copen n (RTree.node b ds)) (ell α) y := by
              refine Finset.sum_congr rfl ?_
              intro y _
              congr 1
              unfold coeff
              have hshift :
                  (α - copenTotalDiag n (RTree.node b ds) y) +
                      copenTotalDiag n (RTree.node b ds) y = α := by
                simp
              rw [hshift]
        _ = (TreeGraph.dotLinear (Copen n (RTree.node b ds))
            (TreeGraph.linearFunctionalCoeff
              (Copen n (RTree.node b ds)) (ell α)) μ.1) := by
              rfl
        _ = ell α μ.1 := by
              have hdot :=
                congrArg
                  (fun φ : Module.Dual F2
                      (BoundaryField n (RTree.node b ds)) =>
                    φ μ.1)
                  (TreeGraph.linearFunctional_eq_dotLinear_coeff
                    (Copen n (RTree.node b ds)) (ell α))
              simpa [BoundaryField] using hdot.symm
        _ = g α μ := by
              have hrestr :=
                congrArg
                  (fun φ : Module.Dual F2 P.boundaryMessageSpace =>
                    φ μ) (hell α)
              simpa [restrictDual_apply] using hrestr

noncomputable def headShearedOneSliceKernel
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Submodule F2 (BranchField n C) :=
  oneSliceCyclicKernel n (BranchField n C) P.boundaryMessageSpace
    (headChildRSheared n C hC P)

theorem finrank_headShearedOneSliceKernel
    (n : Nat) [NeZero n]
    (C : RTree) (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Module.finrank F2 (headShearedOneSliceKernel n C hC P) =
      branchAllowedDim n (RTree.totalWeight C) (Ydim n C hC) := by
  rw [headShearedOneSliceKernel]
  rw [finrank_oneSliceCyclicKernel n
    (BranchField n C) P.boundaryMessageSpace
    (headChildRSheared n C hC P)
    (headChildRSheared_surjective n C hC P)]
  rw [finrank_branchField, OpenNormalCleanPackage.boundaryMessageSpace_finrank]
  rfl

theorem mem_headShearedAllowedBoundarySpace_iff_forall_headBranch_mem_shearedKernel
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC)
    (h : BoundaryField n (RTree.node a (C :: rest))) :
    h ∈ headShearedAllowedBoundarySpace n a C rest hC P ↔
      ∀ tail : CoordsList n rest,
        (boundaryHeadSliceLinearEquiv n a C rest h tail) ∈
          headShearedOneSliceKernel n C hC P := by
  change
    boundaryHeadSliceLinearEquiv n a C rest h ∈
        rtildeVisibleKernel n (CoordsList n rest)
          (BranchField n C) P.boundaryMessageSpace
          (headChildRSheared n C hC P) ↔
      ∀ tail : CoordsList n rest,
        (boundaryHeadSliceLinearEquiv n a C rest h tail) ∈
          headShearedOneSliceKernel n C hC P
  rw [mem_rtildeVisibleKernel_iff_forall_oneSliceCyclicKernel]
  rfl

theorem headShearedAllowedBoundarySpace_eq_colsIn
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    headShearedAllowedBoundarySpace n a C rest hC P =
      colsIn (Cplus n C) (CoordsList n rest)
        (headShearedOneSliceKernel n C hC P) := by
  ext h
  rw [mem_headShearedAllowedBoundarySpace_iff_forall_headBranch_mem_shearedKernel]
  rfl

theorem finrank_headShearedAllowedBoundarySpace
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Module.finrank F2
      (headShearedAllowedBoundarySpace n a C rest hC P) =
      Fintype.card (CoordsList n rest) *
        Module.finrank F2 (BranchField n C) -
      Fintype.card (CoordsList n rest) * (n - 1) *
        Module.finrank F2 P.boundaryMessageSpace := by
  rw [headShearedAllowedBoundarySpace, finrank_submodule_comap_linearEquiv]
  exact finrank_rtildeVisibleKernel n
    (CoordsList n rest)
    (BranchField n C)
    P.boundaryMessageSpace
    (headChildRSheared n C hC P)
    (headChildRSheared_surjective n C hC P)

theorem finrank_headShearedAllowedBoundarySpace_Ydim_shape
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (P : OpenNormalCleanPackage n C hC) :
    Module.finrank F2
      (headShearedAllowedBoundarySpace n a C rest hC P) =
      Fintype.card (CoordsList n rest) *
        (n ^ RTree.totalWeight C - (n - 1) * Ydim n C hC) := by
  rw [finrank_headShearedAllowedBoundarySpace]
  rw [finrank_branchField, OpenNormalCleanPackage.boundaryMessageSpace_finrank]
  rw [Nat.mul_assoc, ← Nat.mul_sub_left_distrib]

end Imbalance
end TreeGraph
