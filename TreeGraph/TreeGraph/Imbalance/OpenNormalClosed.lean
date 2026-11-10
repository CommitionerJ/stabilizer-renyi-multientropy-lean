import TreeGraph.Imbalance.OpenNormalBridge
import TreeGraph.Imbalance.BranchTransfer

namespace TreeGraph
namespace Imbalance

open Classical in
theorem sum_if_mem_submodule_const
    {V : Type} [AddCommGroup V] [Module F2 V] [Fintype V]
    (K : Submodule F2 V) [Fintype K] (c : ℤ) :
    (∑ v : V, if v ∈ K then c else 0) =
      (Fintype.card K : ℤ) * c := by
  classical
  calc
    (∑ v : V, if v ∈ K then c else 0) =
        (Finset.univ.filter (fun v : V => v ∈ K)).sum (fun _ => c) := by
      rw [Finset.sum_filter]
    _ = ((Finset.univ.filter (fun v : V => v ∈ K)).card : ℤ) * c := by
      simp
    _ = (Fintype.card K : ℤ) * c := by
      rw [Fintype.card_subtype]

namespace OpenNormalCleanReductionBridge

noncomputable def toNormalCleanReductionBridge
    {n : Nat} [NeZero n] {T : RTree}
    {hT : RTree.PositiveWeights T}
    (B : OpenNormalCleanReductionBridge n T hT) :
    NormalCleanReductionBridge n T hT where
  normal_signed_sum_eq_abstract := by
    classical
    haveI : Fintype B.rootMessageSpace := inferInstance
    haveI : FiniteDimensional F2 B.rootMessageSpace := inferInstance
    have hcard_nat : Fintype.card B.rootMessageSpace =
        2 ^ Ydim n T hT := by
      rw [submodule_card_eq_pow_finrank]
      rw [B.rootMessageSpace_finrank]
    have hcard_int : (Fintype.card B.rootMessageSpace : ℤ) =
        (2 : ℤ) ^ Ydim n T hT := by
      exact_mod_cast hcard_nat
    have hsum_exp :
        Ydim n T hT + (Xdim n T - Ydim n T hT) = Xdim n T := by
      have hle := Ydim_le_Xdim n T hT
      omega
    calc
      normalSignedSumClean n T =
          ∑ root : RootFieldAssignmentClean n T,
            openNormalSignedSumClean n T root := by
        exact normalSignedSumClean_eq_sum_openNormalSignedSumClean n T
      _ = ∑ root : RootFieldAssignmentClean n T,
            if root ∈ B.rootMessageSpace then
              (2 : ℤ) ^ (Xdim n T - Ydim n T hT)
            else 0 := by
        refine Finset.sum_congr rfl ?_
        intro root _
        exact B.open_signed_sum_eq root
      _ = (Fintype.card B.rootMessageSpace : ℤ) *
            (2 : ℤ) ^ (Xdim n T - Ydim n T hT) := by
        exact sum_if_mem_submodule_const B.rootMessageSpace
          ((2 : ℤ) ^ (Xdim n T - Ydim n T hT))
      _ = (2 : ℤ) ^ Ydim n T hT *
            (2 : ℤ) ^ (Xdim n T - Ydim n T hT) := by
        rw [hcard_int]
      _ = (2 : ℤ) ^ Xdim n T := by
        rw [← pow_add]
        rw [hsum_exp]
      _ = abstractTreeSignedSum n T hT := by
        exact (rooted_tree_signed_sum_imbalance_formula n T hT).symm

end OpenNormalCleanReductionBridge

end Imbalance
end TreeGraph
