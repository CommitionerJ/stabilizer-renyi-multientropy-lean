import TreeGraph.Imbalance.NodeHeadAllowed

namespace TreeGraph
namespace Imbalance

noncomputable def childYdimFactorProduct (n : Nat) [NeZero n] :
    (cs : List RTree) →
      (∀ C ∈ cs, RTree.PositiveWeights C) → Nat
  | [], _ => 1
  | C :: rest, hcs =>
      let hC : RTree.PositiveWeights C := hcs C (by simp)
      let hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hcs D (by simp [hD])
      branchAllowedDim n (RTree.totalWeight C) (Ydim n C hC) *
        childYdimFactorProduct n rest hrest

noncomputable def packageChildSliceFactors (n : Nat) [NeZero n] :
    (cs : List RTree) →
      (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) →
      (∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C (hcs C hCmem)) →
      List SliceFactor
  | [], _, _ => []
  | C :: rest, hcs, childPackage =>
      let hC : RTree.PositiveWeights C := hcs C (by simp)
      let hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hcs D (by simp [hD])
      let Prest :
          ∀ D, (hDmem : D ∈ rest) →
            OpenNormalCleanPackage n D (hrest D hDmem) := by
        intro D hDmem
        exact childPackage D (by simp [hDmem])
      { C := Cplus n C
        finite_C := inferInstance
        K := Kchild n C (rootWeight_pos_of_positiveWeights hC)
          (childPackage C (by simp)).boundaryMessageSpace
        finiteDim_K := inferInstance } ::
        packageChildSliceFactors n rest hrest Prest

theorem factorDimProduct_packageChildSliceFactors (n : Nat) [NeZero n] :
    ∀ (cs : List RTree)
      (hcs : ∀ C ∈ cs, RTree.PositiveWeights C)
      (childPackage :
        ∀ C, (hCmem : C ∈ cs) →
          OpenNormalCleanPackage n C (hcs C hCmem)),
      factorDimProduct
        (packageChildSliceFactors n cs hcs childPackage) =
        childYdimFactorProduct n cs hcs
  | [], hcs, childPackage => by
      simp [packageChildSliceFactors, factorDimProduct, childYdimFactorProduct]
  | C :: rest, hcs, childPackage => by
      let hC : RTree.PositiveWeights C := hcs C (by simp)
      let hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hcs D (by simp [hD])
      let Prest :
          ∀ D, (hDmem : D ∈ rest) →
            OpenNormalCleanPackage n D (hrest D hDmem) := by
        intro D hDmem
        exact childPackage D (by simp [hDmem])
      simp [packageChildSliceFactors, factorDimProduct, childYdimFactorProduct,
        Prest,
        factorDimProduct_packageChildSliceFactors n rest hrest Prest,
        finrank_Kchild,
        OpenNormalCleanPackage.boundaryMessageSpace_finrank]

theorem childYdimFactorProduct_eq_YdimCandidate (n : Nat) [NeZero n] :
    ∀ (cs : List RTree)
      (hcs : ∀ C ∈ cs, RTree.PositiveWeights C),
      childYdimFactorProduct n cs hcs =
        (cs.map (fun C =>
          branchAllowedDim n (RTree.totalWeight C)
            (YdimCandidate n C))).prod
  | [], hcs => by
      simp [childYdimFactorProduct]
  | C :: rest, hcs => by
      let hC : RTree.PositiveWeights C := hcs C (by simp)
      let hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hcs D (by simp [hD])
      simp [childYdimFactorProduct,
        childYdimFactorProduct_eq_YdimCandidate n rest hrest,
        Ydim_eq_YdimCandidate]

theorem childYdimFactorProduct_node_Ydim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    childYdimFactorProduct n cs hcs =
      Ydim n (RTree.node a cs) hT := by
  rw [childYdimFactorProduct_eq_YdimCandidate]
  rw [Ydim_eq_YdimCandidate]
  simp [YdimCandidate]

theorem factorDimProduct_packageChildSliceFactors_node_Ydim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C
          (child_positive_of_node hT C hCmem)) :
    factorDimProduct
      (packageChildSliceFactors n cs
        (child_positive_of_node hT) childPackage) =
      Ydim n (RTree.node a cs) hT := by
  rw [factorDimProduct_packageChildSliceFactors]
  exact childYdimFactorProduct_node_Ydim n a cs hT
    (child_positive_of_node hT)

theorem card_packageChildIndependentAllowed_node_Ydim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (childPackage :
      ∀ C, (hCmem : C ∈ cs) →
        OpenNormalCleanPackage n C
          (child_positive_of_node hT C hCmem)) :
    Fintype.card
      (independentAllowed
        (packageChildSliceFactors n cs
          (child_positive_of_node hT) childPackage)) =
      2 ^ Ydim n (RTree.node a cs) hT := by
  rw [card_independentAllowed]
  rw [factorDimProduct_packageChildSliceFactors_node_Ydim]

end Imbalance
end TreeGraph
