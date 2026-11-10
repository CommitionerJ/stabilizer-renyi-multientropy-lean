import TreeGraph.Imbalance.OpenNormalBridge
import TreeGraph.Imbalance.PhysicalEdge

namespace TreeGraph
namespace Imbalance

noncomputable def edgeOpenNormalAssignmentCoreEquivClean
    (n a b : Nat) [NeZero n] :
    OpenNormalAssignmentClean n (RTree.node a [RTree.node b []]) ≃
      (EdgeRootContextClean n a → Rep n → F2) where
  toFun A := fun x t => A.nodeField (edgeChildNonRootVertexClean a b)
    (edgeNonRootFieldDomainClean n a b x t)
  invFun φ :=
    { nodeField := fun v dom => by
        have hv : v = edgeChildNonRootVertexClean a b :=
          nonRootVertexClean_edge_eq_child v
        subst v
        exact φ dom.rootCoord dom.diagonal }
  left_inv A := by
    cases A with
    | mk nodeField =>
        rw [OpenNormalAssignmentClean.mk.injEq]
        funext v dom
        have hv : v = edgeChildNonRootVertexClean a b :=
          nonRootVertexClean_edge_eq_child v
        subst v
        change
          nodeField (edgeChildNonRootVertexClean a b)
              (edgeNonRootFieldDomainClean n a b dom.rootCoord dom.diagonal) =
            nodeField (edgeChildNonRootVertexClean a b) dom
        rw [edgeNonRootFieldDomainClean_eta n a b dom]
  right_inv φ := by
    rfl

noncomputable def edgeRootCoreFromCleanRoot
    (n a b : Nat) [NeZero n]
    (root : RootFieldAssignmentClean n (RTree.node a [RTree.node b []])) :
    (Fin b → Rep n) → F2 :=
  fun y => root ((edgeRootFieldDomainCleanEquiv n a b).symm y)

theorem closeOpenNormalAssignmentClean_edge_core
    (n a b : Nat) [NeZero n]
    (root : RootFieldAssignmentClean n (RTree.node a [RTree.node b []]))
    (A : OpenNormalAssignmentClean n (RTree.node a [RTree.node b []])) :
    closeOpenNormalAssignmentClean root A =
      (edgeNormalAssignmentCoreEquivClean n a b).symm
        (edgeRootCoreFromCleanRoot n a b root,
          edgeOpenNormalAssignmentCoreEquivClean n a b A) := by
  cases A with
  | mk nodeField =>
      rw [NormalAssignmentClean.mk.injEq]
      constructor
      · funext rd
        change root rd =
          root ((edgeRootFieldDomainCleanEquiv n a b).symm
            ((edgeRootFieldDomainCleanEquiv n a b) rd))
        exact congrArg root
          ((edgeRootFieldDomainCleanEquiv n a b).left_inv rd).symm
      · funext v dom
        have hv : v = edgeChildNonRootVertexClean a b :=
          nonRootVertexClean_edge_eq_child v
        subst v
        change
          nodeField (edgeChildNonRootVertexClean a b) dom =
            nodeField (edgeChildNonRootVertexClean a b)
              (edgeNonRootFieldDomainClean n a b dom.rootCoord dom.diagonal)
        rw [edgeNonRootFieldDomainClean_eta n a b dom]

noncomputable def edgeOpenNormalCoreSignedSumClean
    (a b n : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2) : ℤ :=
  ∑ φ : EdgeRootContextClean n a → Rep n → F2,
    chi (edgeNormalCorePhaseClean a b n α φ)

theorem openNormalSignedSumClean_edge_eq_fixed_core
    (n a b : Nat) [NeZero n]
    (root : RootFieldAssignmentClean n (RTree.node a [RTree.node b []])) :
    openNormalSignedSumClean n (RTree.node a [RTree.node b []]) root =
      edgeOpenNormalCoreSignedSumClean a b n
        (edgeRootCoreFromCleanRoot n a b root) := by
  classical
  unfold openNormalSignedSumClean edgeOpenNormalCoreSignedSumClean weightClean
  calc
    (∑ A : OpenNormalAssignmentClean n (RTree.node a [RTree.node b []]),
        chi (totalPhaseClean (RTree.node a [RTree.node b []])
          (closeOpenNormalAssignmentClean root A))) =
        ∑ φ : EdgeRootContextClean n a → Rep n → F2,
          chi (totalPhaseClean (RTree.node a [RTree.node b []])
            (closeOpenNormalAssignmentClean root
              ((edgeOpenNormalAssignmentCoreEquivClean n a b).symm φ))) := by
      refine Fintype.sum_equiv
        (edgeOpenNormalAssignmentCoreEquivClean n a b)
        (fun A : OpenNormalAssignmentClean n (RTree.node a [RTree.node b []]) =>
          chi (totalPhaseClean (RTree.node a [RTree.node b []])
            (closeOpenNormalAssignmentClean root A)))
        (fun φ : EdgeRootContextClean n a → Rep n → F2 =>
          chi (totalPhaseClean (RTree.node a [RTree.node b []])
            (closeOpenNormalAssignmentClean root
              ((edgeOpenNormalAssignmentCoreEquivClean n a b).symm φ))))
        ?_
      intro A
      change
        chi (totalPhaseClean (RTree.node a [RTree.node b []])
          (closeOpenNormalAssignmentClean root A)) =
          chi (totalPhaseClean (RTree.node a [RTree.node b []])
            (closeOpenNormalAssignmentClean root
              ((edgeOpenNormalAssignmentCoreEquivClean n a b).symm
                ((edgeOpenNormalAssignmentCoreEquivClean n a b) A))))
      exact congrArg
        (fun A' : OpenNormalAssignmentClean n (RTree.node a [RTree.node b []]) =>
          chi (totalPhaseClean (RTree.node a [RTree.node b []])
            (closeOpenNormalAssignmentClean root A')))
        ((edgeOpenNormalAssignmentCoreEquivClean n a b).left_inv A).symm
    _ = ∑ φ : EdgeRootContextClean n a → Rep n → F2,
          chi (edgeNormalCorePhaseClean a b n
            (edgeRootCoreFromCleanRoot n a b root) φ) := by
      refine Finset.sum_congr rfl ?_
      intro φ _
      rw [closeOpenNormalAssignmentClean_edge_core]
      rw [totalPhaseClean_edge_eq_core]
      exact congrArg
        (fun φ' : EdgeRootContextClean n a → Rep n → F2 =>
          chi (edgeNormalCorePhaseClean a b n
            (edgeRootCoreFromCleanRoot n a b root) φ'))
        ((edgeOpenNormalAssignmentCoreEquivClean n a b).right_inv φ)

noncomputable def edgeDiagCoeffLinear
    (a b n : Nat) [NeZero n] :
    (EdgeRootContextClean n a → Rep n → F2) →ₗ[F2]
      ((Fin b → Rep n) → F2) where
  toFun φ := diagCoeffClean b n (edgeContextSummedConstraintClean a n φ)
  map_add' φ ψ := by
    ext y
    simp [diagCoeffClean]
  map_smul' r φ := by
    ext y
    simp [diagCoeffClean]

@[simp] theorem edgeDiagCoeffLinear_apply
    (a b n : Nat) [NeZero n]
    (φ : EdgeRootContextClean n a → Rep n → F2)
    (y : Fin b → Rep n) :
    edgeDiagCoeffLinear a b n φ y =
      edgeContextSummedConstraintClean a n φ (diag n b y) := rfl

noncomputable def edgeOpenNormalCorePhaseLinear
    (a b n : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2) :
    (EdgeRootContextClean n a → Rep n → F2) →ₗ[F2] F2 :=
  (TreeGraph.dotLinear (Fin b → Rep n) α).comp
    (edgeDiagCoeffLinear a b n)

@[simp] theorem edgeOpenNormalCorePhaseLinear_apply
    (a b n : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2)
    (φ : EdgeRootContextClean n a → Rep n → F2) :
    edgeOpenNormalCorePhaseLinear a b n α φ =
      edgeNormalCorePhaseClean a b n α φ := by
  unfold edgeOpenNormalCorePhaseLinear edgeNormalCorePhaseClean
    edgeDiagCoeffLinear diagCoeffClean
  simp [TreeGraph.dotLinear, mul_comm]

theorem card_edgeOpenNormalCoreFields
    (a n : Nat) [NeZero n] :
    Fintype.card (EdgeRootContextClean n a → Rep n → F2) =
      2 ^ (n ^ (a - 1) * n) := by
  rw [Fintype.card_fun]
  have hctx : Fintype.card (EdgeRootContextClean n a) = n ^ (a - 1) :=
    card_edgeRootContextClean a n
  have hrep : Fintype.card (Rep n → F2) = 2 ^ n := by
    rw [Fintype.card_fun]
    simp [Rep, ZMod.card, F2]
  rw [hctx, hrep]
  calc
    (2 ^ n) ^ n ^ (a - 1) = 2 ^ (n * n ^ (a - 1)) := by
      rw [← Nat.pow_mul]
    _ = 2 ^ (n ^ (a - 1) * n) := by
      rw [Nat.mul_comm]

theorem edgeOpenNormalCoreSignedSumClean_eq_phaseKernel
    (a b n : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2) :
    edgeOpenNormalCoreSignedSumClean a b n α =
      if edgeOpenNormalCorePhaseLinear a b n α = 0 then
        (2 : ℤ) ^ (n ^ (a - 1) * n)
      else 0 := by
  classical
  unfold edgeOpenNormalCoreSignedSumClean
  calc
    (∑ φ : EdgeRootContextClean n a → Rep n → F2,
        chi (edgeNormalCorePhaseClean a b n α φ)) =
        ∑ φ : EdgeRootContextClean n a → Rep n → F2,
          bitSign (edgeOpenNormalCorePhaseLinear a b n α φ) := by
      simp [chi]
    _ = if edgeOpenNormalCorePhaseLinear a b n α = 0 then
          (Fintype.card (EdgeRootContextClean n a → Rep n → F2) : ℤ)
        else 0 := by
      exact sum_bitSign_linear (edgeOpenNormalCorePhaseLinear a b n α)
    _ = if edgeOpenNormalCorePhaseLinear a b n α = 0 then
          (2 : ℤ) ^ (n ^ (a - 1) * n)
        else 0 := by
      rw [card_edgeOpenNormalCoreFields]
      norm_num

theorem edgeOpenNormalCoreSignedSumClean_eq_phaseKernel_closed_exp
    {a b n : Nat} [NeZero n] (ha : 0 < a)
    (α : (Fin b → Rep n) → F2) :
    edgeOpenNormalCoreSignedSumClean a b n α =
      if edgeOpenNormalCorePhaseLinear a b n α = 0 then
        (2 : ℤ) ^ (n ^ a)
      else 0 := by
  rw [edgeOpenNormalCoreSignedSumClean_eq_phaseKernel]
  have hpow : n ^ (a - 1) * n = n ^ a := by
    have ha' : (a - 1) + 1 = a := by omega
    calc
      n ^ (a - 1) * n = n ^ ((a - 1) + 1) := by
        rw [Nat.pow_succ]
      _ = n ^ a := by rw [ha']
  rw [hpow]

end Imbalance
end TreeGraph
