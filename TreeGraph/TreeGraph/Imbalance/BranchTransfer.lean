import TreeGraph.Imbalance.ConnectedExponent
import TreeGraph.Imbalance.MultiplicityRank

namespace TreeGraph
namespace Imbalance

noncomputable def rootMultiplicityCard (n a : Nat) : Nat :=
  n ^ (a - 1)

noncomputable def visibleExternalCard (n left right : Nat) : Nat :=
  n ^ (left + right)

noncomputable def branchMessageFamilyCardFactor
    (n a left right : Nat) : Nat :=
  rootMultiplicityCard n a * visibleExternalCard n left right * n

noncomputable def branchScalarExponent
    (n a left : Nat) (C : RTree) (rest : List RTree) : Nat :=
  n ^ (a + left + (rest.map RTree.totalWeight).sum) * Xdim n C

theorem rootMultiplicityCard_pos (n a : Nat) [NeZero n] :
    0 < rootMultiplicityCard n a := by
  unfold rootMultiplicityCard
  exact Nat.pow_pos (NeZero.pos n)

theorem visibleExternalCard_pos (n left right : Nat) [NeZero n] :
    0 < visibleExternalCard n left right := by
  unfold visibleExternalCard
  exact Nat.pow_pos (NeZero.pos n)

theorem branchMessageFamilyCardFactor_pos
    (n a left right : Nat) [NeZero n] :
    0 < branchMessageFamilyCardFactor n a left right := by
  unfold branchMessageFamilyCardFactor
  exact Nat.mul_pos
    (Nat.mul_pos (rootMultiplicityCard_pos n a)
      (visibleExternalCard_pos n left right))
    (NeZero.pos n)

theorem branchMessageFamilyCardFactor_eq_pow
    (n a left right : Nat) (ha : 0 < a) :
    branchMessageFamilyCardFactor n a left right =
      n ^ (a + left + right) := by
  unfold branchMessageFamilyCardFactor rootMultiplicityCard
    visibleExternalCard
  rw [← Nat.pow_add]
  rw [← Nat.pow_succ]
  congr 1
  omega

theorem Ydim_le_Xdim (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Ydim n T hT ≤ Xdim n T := by
  cases T with
  | node a cs =>
      rw [Xdim_node_eq_Ydim_add_childContrib n a cs hT]
      exact Nat.le_add_right _ _

noncomputable def branchDescendantScalarExponent
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C) : Nat :=
  branchMessageFamilyCardFactor n a left
      (rest.map RTree.totalWeight).sum *
    (Xdim n C - Ydim n C hC)

noncomputable def branchMessageScalarExponent
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C) : Nat :=
  branchMessageFamilyCardFactor n a left
      (rest.map RTree.totalWeight).sum *
    Ydim n C hC

theorem branchScalarExponent_eq_familyFactor_mul_Xdim
    (n a left : Nat) (C : RTree) (rest : List RTree) (ha : 0 < a) :
    branchScalarExponent n a left C rest =
      branchMessageFamilyCardFactor n a left
        (rest.map RTree.totalWeight).sum * Xdim n C := by
  rw [branchMessageFamilyCardFactor_eq_pow n a left
    (rest.map RTree.totalWeight).sum ha]
  rfl

theorem branchScalarExponent_split
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a) (hC : RTree.PositiveWeights C) :
    branchDescendantScalarExponent n a left C rest hC +
      branchMessageScalarExponent n a left C rest hC =
        branchScalarExponent n a left C rest := by
  unfold branchDescendantScalarExponent branchMessageScalarExponent
  rw [branchScalarExponent_eq_familyFactor_mul_Xdim n a left C rest ha]
  rw [← Nat.mul_add]
  rw [Nat.sub_add_cancel (Ydim_le_Xdim n C hC)]

theorem two_pow_branchScalarExponent_split
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a) (hC : RTree.PositiveWeights C) :
    (2 : ℤ) ^ branchScalarExponent n a left C rest =
      (2 : ℤ) ^ branchDescendantScalarExponent n a left C rest hC *
        (2 : ℤ) ^ branchMessageScalarExponent n a left C rest hC := by
  rw [← branchScalarExponent_split n a left C rest ha hC]
  rw [pow_add]

theorem XdimChildContrib_cons_branchScalar
    (n a left : Nat) (C : RTree) (rest : List RTree) :
    XdimChildContrib n a (C :: rest) left =
      branchScalarExponent n a left C rest +
        XdimChildContrib n a rest (left + RTree.totalWeight C) := by
  simp [branchScalarExponent, Xdim, XdimChildContrib_cons]

theorem branchScalarExponent_cast_eq_XrecInt
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) (hC : RTree.PositiveWeights C) :
    ((branchScalarExponent n a left C rest : Nat) : ℤ) =
      (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) *
        XrecInt n C := by
  unfold branchScalarExponent
  rw [Nat.cast_mul, Nat.cast_pow]
  rw [Xdim_cast_eq_XrecInt n C hC]

theorem branchScalarExponent_cast_eq_Xpoly
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) (hC : RTree.PositiveWeights C) :
    ((branchScalarExponent n a left C rest : Nat) : ℤ) =
      (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) *
        Xpoly n C := by
  simpa [XrecInt] using
    branchScalarExponent_cast_eq_XrecInt n a left C rest hC

theorem branchScalarExponent_cast_eq_allTerms
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree) (hC : RTree.PositiveWeights C) :
    ((branchScalarExponent n a left C rest : Nat) : ℤ) =
      (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) *
        termSum n (allTerms C) := by
  rw [branchScalarExponent_cast_eq_Xpoly n a left C rest hC]
  rw [Xpoly_eq_allTerms]

theorem branchMessageScalarExponent_cast_eq_YrecInt
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a) (hC : RTree.PositiveWeights C) :
    ((branchMessageScalarExponent n a left C rest hC : Nat) : ℤ) =
      (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) *
        YrecInt n C := by
  unfold branchMessageScalarExponent
  rw [branchMessageFamilyCardFactor_eq_pow n a left
    (rest.map RTree.totalWeight).sum ha]
  rw [Nat.cast_mul, Nat.cast_pow]
  rw [Ydim_cast_eq_YrecInt n C hC]

theorem branchMessageScalarExponent_cast_eq_Ypoly
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a) (hC : RTree.PositiveWeights C) :
    ((branchMessageScalarExponent n a left C rest hC : Nat) : ℤ) =
      (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) *
        Ypoly n C := by
  simpa [YrecInt] using
    branchMessageScalarExponent_cast_eq_YrecInt n a left C rest ha hC

theorem branchDescendantScalarExponent_cast_eq_recInt
    (n a left : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (ha : 0 < a) (hC : RTree.PositiveWeights C) :
    ((branchDescendantScalarExponent n a left C rest hC : Nat) : ℤ) =
      (nZ n) ^ (a + left + (rest.map RTree.totalWeight).sum) *
        (XrecInt n C - YrecInt n C) := by
  unfold branchDescendantScalarExponent
  rw [branchMessageFamilyCardFactor_eq_pow n a left
    (rest.map RTree.totalWeight).sum ha]
  rw [Nat.cast_mul, Nat.cast_pow]
  rw [Nat.cast_sub (Ydim_le_Xdim n C hC)]
  rw [Xdim_cast_eq_XrecInt n C hC]
  rw [Ydim_cast_eq_YrecInt n C hC]

noncomputable def branchMessageCoeff (n : Nat) [NeZero n]
    (E P M : Type) [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (h : E → P) : E × Rep n → Module.Dual F2 M :=
  familyCycDiff n E (Module.Dual F2 M)
    (RtildeAbstract n E P M R h)

theorem branchMessageCoeff_eq_zero_iff_mem
    (n : Nat) [NeZero n]
    (E P M : Type) [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (h : E → P) :
    branchMessageCoeff n E P M R h = 0 ↔
      h ∈ rtildeVisibleKernel n E P M R := by
  rfl

noncomputable def branchMessageSignedSum (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E] [Fintype M]
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (h : E → P) : ℤ :=
  ∑ μ : Q × E × Rep n → M,
    chi (multiplicityExponent n (Q := Q)
      (branchMessageCoeff n E P M R h) μ)

theorem branchMessageSignedSum_of_mem
    (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (h : E → P) (hh : h ∈ rtildeVisibleKernel n E P M R) :
    branchMessageSignedSum n Q E P M R h =
      (2 : ℤ) ^ (Fintype.card Q * Fintype.card E * n *
        Module.finrank F2 M) := by
  unfold branchMessageSignedSum
  rw [multiplicity_char_sum]
  have hcoeff : branchMessageCoeff n E P M R h = 0 :=
    (branchMessageCoeff_eq_zero_iff_mem n E P M R h).2 hh
  simp [hcoeff]

theorem branchMessageSignedSum_of_not_mem
    (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (h : E → P) (hh : h ∉ rtildeVisibleKernel n E P M R) :
    branchMessageSignedSum n Q E P M R h = 0 := by
  unfold branchMessageSignedSum
  rw [multiplicity_char_sum]
  have hcoeff : branchMessageCoeff n E P M R h ≠ 0 := by
    intro hz
    exact hh ((branchMessageCoeff_eq_zero_iff_mem n E P M R h).1 hz)
  simp [hcoeff]

noncomputable def branchTransferTotalSum (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E] [Fintype P] [Fintype M]
    [AddCommGroup P] [Module F2 P]
    [AddCommGroup M] [Module F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M)) : ℤ :=
  ∑ h : E → P, branchMessageSignedSum n Q E P M R h

theorem branchTransferTotalSum_eq_kernel_card_mul
    (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P] [Fintype P]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M)) :
    branchTransferTotalSum n Q E P M R =
      (Fintype.card (rtildeVisibleKernel n E P M R) : ℤ) *
        (2 : ℤ) ^ (Fintype.card Q * Fintype.card E * n *
          Module.finrank F2 M) := by
  classical
  let K := rtildeVisibleKernel n E P M R
  let scalar : ℤ :=
    (2 : ℤ) ^ (Fintype.card Q * Fintype.card E * n *
      Module.finrank F2 M)
  have hpoint : ∀ h : E → P,
      branchMessageSignedSum n Q E P M R h =
        if h ∈ K then scalar else 0 := by
    intro h
    by_cases hh : h ∈ K
    · have hm := branchMessageSignedSum_of_mem n Q E P M R h hh
      simp [K, scalar, hh, hm]
    · have hn := branchMessageSignedSum_of_not_mem n Q E P M R h hh
      simp [K, scalar, hh, hn]
  have hcard :
      Fintype.card K =
        (Finset.univ.filter (fun h : E → P => h ∈ K)).card := by
    simpa [K] using Fintype.card_subtype (fun h : E → P => h ∈ K)
  unfold branchTransferTotalSum
  calc
    (∑ h : E → P, branchMessageSignedSum n Q E P M R h) =
        ∑ h : E → P, if h ∈ K then scalar else 0 := by
      apply Finset.sum_congr rfl
      intro h _
      exact hpoint h
    _ = ∑ h ∈ (Finset.univ.filter (fun h : E → P => h ∈ K)),
          scalar := by
      rw [Finset.sum_filter]
    _ = ((Finset.univ.filter
          (fun h : E → P => h ∈ K)).card : ℤ) * scalar := by
      rw [Finset.sum_const]
      simp
    _ = (Fintype.card K : ℤ) * scalar := by
      rw [hcard]
    _ = (Fintype.card (rtildeVisibleKernel n E P M R) : ℤ) *
        (2 : ℤ) ^ (Fintype.card Q * Fintype.card E * n *
          Module.finrank F2 M) := by
      rfl

theorem branchTransferTotalSum_eq_two_pow_kernel_dim_mul
    (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P] [Fintype P]
    [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    branchTransferTotalSum n Q E P M R =
      (2 : ℤ) ^ (Fintype.card E * Module.finrank F2 P -
        Fintype.card E * (n - 1) * Module.finrank F2 M) *
        (2 : ℤ) ^ (Fintype.card Q * Fintype.card E * n *
          Module.finrank F2 M) := by
  rw [branchTransferTotalSum_eq_kernel_card_mul]
  rw [card_rtildeVisibleKernel n E P M R hR]
  norm_num

theorem branchTransferTotalSum_eq_two_pow_total_dim
    (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P] [Fintype P]
    [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    branchTransferTotalSum n Q E P M R =
      (2 : ℤ) ^
        ((Fintype.card E * Module.finrank F2 P -
            Fintype.card E * (n - 1) * Module.finrank F2 M) +
          Fintype.card Q * Fintype.card E * n *
            Module.finrank F2 M) := by
  rw [branchTransferTotalSum_eq_two_pow_kernel_dim_mul n Q E P M R hR]
  rw [← pow_add]

theorem whole_branch_transfer
    (n : Nat) [NeZero n]
    (Q E P M : Type) [Fintype Q] [Nonempty Q] [DecidableEq Q]
    [Fintype E] [DecidableEq E]
    [AddCommGroup P] [Module F2 P] [Fintype P]
    [FiniteDimensional F2 P]
    [AddCommGroup M] [Module F2 M] [Fintype M]
    [FiniteDimensional F2 M]
    (R : P →ₗ[F2] (Rep n → Module.Dual F2 M))
    (hR : Function.Surjective R) :
    branchTransferTotalSum n Q E P M R =
      (2 : ℤ) ^
        ((Fintype.card E * Module.finrank F2 P -
            Fintype.card E * (n - 1) * Module.finrank F2 M) +
          Fintype.card Q * Fintype.card E * n *
            Module.finrank F2 M) := by
  exact branchTransferTotalSum_eq_two_pow_total_dim n Q E P M R hR

private lemma rootWeight_pos_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    0 < T.rootWeight := by
  cases T with
  | node a cs =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      simpa [RTree.rootWeight] using hnode.1

theorem child_positive_of_node {a : Nat} {cs : List RTree}
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    ∀ C ∈ cs, RTree.PositiveWeights C := by
  have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
    simpa [RTree.PositiveWeights] using hT
  exact hnode.2

noncomputable def childSliceFactors (n : Nat) [NeZero n] :
    (cs : List RTree) → (∀ C ∈ cs, RTree.PositiveWeights C) →
      List SliceFactor
  | [], _ => []
  | C :: rest, hcs =>
      let hC : RTree.PositiveWeights C := hcs C (by simp)
      let hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hcs D (by simp [hD])
      { C := Cplus n C
        finite_C := inferInstance
        K := Kchild n C (rootWeight_pos_of_positiveWeights hC)
          (recursiveMessageSpace n C hC)
        finiteDim_K := inferInstance } ::
        childSliceFactors n rest hrest

theorem factorDimProduct_childSliceFactors (n : Nat) [NeZero n] :
    ∀ (cs : List RTree) (hcs : ∀ C ∈ cs, RTree.PositiveWeights C),
      factorDimProduct (childSliceFactors n cs hcs) =
        (cs.map (fun C =>
          branchAllowedDim n (RTree.totalWeight C)
            (YdimCandidate n C))).prod
  | [], hcs => by
      simp [childSliceFactors, factorDimProduct]
  | C :: rest, hcs => by
      have hC : RTree.PositiveWeights C := hcs C (by simp)
      have hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hcs D (by simp [hD])
      simp [childSliceFactors, factorDimProduct,
        factorDimProduct_childSliceFactors n rest hrest,
        finrank_Kchild, finrank_recursiveMessageSpace]

theorem factorDimProduct_childSliceFactors_node
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    factorDimProduct (childSliceFactors n cs hcs) =
      YdimCandidate n (RTree.node a cs) := by
  rw [factorDimProduct_childSliceFactors]
  simp [YdimCandidate]

theorem factorDimProduct_childSliceFactors_node_Ydim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    factorDimProduct (childSliceFactors n cs hcs) =
      Ydim n (RTree.node a cs) hT := by
  rw [factorDimProduct_childSliceFactors_node]
  rw [Ydim_eq_YdimCandidate]

theorem card_childFinalAllowed_node
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    Fintype.card (independentAllowed (childSliceFactors n cs hcs)) =
      2 ^ YdimCandidate n (RTree.node a cs) := by
  rw [card_independentAllowed]
  rw [factorDimProduct_childSliceFactors_node]

theorem card_childFinalAllowed_node_Ydim
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs))
    (hcs : ∀ C ∈ cs, RTree.PositiveWeights C) :
    Fintype.card (independentAllowed (childSliceFactors n cs hcs)) =
      2 ^ Ydim n (RTree.node a cs) hT := by
  rw [card_childFinalAllowed_node]
  rw [Ydim_eq_YdimCandidate]

end Imbalance
end TreeGraph
