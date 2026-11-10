import TreeGraph.Imbalance.OpenNormalEdgeCheck

namespace TreeGraph
namespace Imbalance

private theorem add_self_eq_zero_F2 (x : F2) : x + x = 0 := by
  fin_cases x <;> decide

noncomputable def edgeRootMessageSpaceCore
    (n b : Nat) [NeZero n] (hb : 0 < b) :
    Submodule F2 (((Fin b → Rep n) → F2)) :=
  LinearMap.ker (cycDiffAfterFiberSum n hb F2)

noncomputable def edgeRootMessageSpaceClean
    (n a b : Nat) [NeZero n] (hb : 0 < b) :
    Submodule F2
      (RootFieldAssignmentClean n (RTree.node a [RTree.node b []])) :=
  transportedSubmodule
    (RootFieldDomainClean n (RTree.node a [RTree.node b []]))
    (Fin b → Rep n)
    F2
    (edgeRootFieldDomainCleanEquiv n a b)
    (edgeRootMessageSpaceCore n b hb)

theorem finrank_edgeRootMessageSpaceCore
    (n b : Nat) [NeZero n] (hb : 0 < b) :
    Module.finrank F2 (edgeRootMessageSpaceCore n b hb) =
      n ^ b - (n - 1) := by
  unfold edgeRootMessageSpaceCore
  rw [finrank_ker_cycDiffAfterFiberSum]
  simp

theorem finrank_edgeRootMessageSpaceClean
    (n a b : Nat) [NeZero n] (hb : 0 < b) :
    Module.finrank F2 (edgeRootMessageSpaceClean n a b hb) =
      n ^ b - (n - 1) := by
  unfold edgeRootMessageSpaceClean
  rw [finrank_transportedSubmodule]
  exact finrank_edgeRootMessageSpaceCore n b hb

theorem Ydim_singleEdge
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    Ydim n (RTree.node a [RTree.node b []]) hT =
      n ^ b - (n - 1) := by
  rw [Ydim_eq_YdimCandidate]
  simp [YdimCandidate, branchAllowedDim, RTree.totalWeight]

theorem finrank_edgeRootMessageSpaceClean_eq_Ydim
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    Module.finrank F2
      (edgeRootMessageSpaceClean n a b (positiveWeights_edge_child hT)) =
        Ydim n (RTree.node a [RTree.node b []]) hT := by
  rw [finrank_edgeRootMessageSpaceClean]
  rw [Ydim_singleEdge]

theorem Xdim_sub_Ydim_singleEdge
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    Xdim n (RTree.node a [RTree.node b []]) -
      Ydim n (RTree.node a [RTree.node b []]) hT = n ^ a := by
  have hb : 0 < b := positiveWeights_edge_child hT
  rw [Xdim_edge_single_leaf (n := n) (a := a) (b := b) hb]
  rw [Ydim_singleEdge]
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hnb : n ≤ n ^ b := by
    simpa using le_self_pow hn (Nat.ne_of_gt hb)
  have hle : n - 1 ≤ n ^ b := le_trans (Nat.sub_le n 1) hnb
  omega

noncomputable def repPoint (n : Nat) [NeZero n] (t : Rep n) :
    Rep n → F2 :=
  Pi.single (M := fun _ : Rep n => F2) t (1 : F2)

theorem sum_repPoint (n : Nat) [NeZero n] (t : Rep n) :
    (∑ x : Rep n, repPoint n t x) = 1 := by
  unfold repPoint
  rw [Fintype.sum_eq_single t]
  · simp
  · intro x hx
    simp [Pi.single_eq_of_ne, hx]

theorem dot_repPoint (n : Nat) [NeZero n]
    (β : Rep n → F2) (t : Rep n) :
    (∑ x : Rep n, repPoint n t x * β x) = β t := by
  unfold repPoint
  rw [Fintype.sum_eq_single t]
  · simp
  · intro x hx
    simp [Pi.single_eq_of_ne, hx]

noncomputable def totalSumLinearF2 (n : Nat) [NeZero n] :
    (Rep n → F2) →ₗ[F2] F2 where
  toFun f := ∑ t : Rep n, f t
  map_add' f g := by
    simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    rw [Finset.smul_sum]
    rfl

@[simp] theorem totalSumLinearF2_apply
    {n : Nat} [NeZero n] (f : Rep n → F2) :
    totalSumLinearF2 n f = ∑ t : Rep n, f t := rfl

theorem totalSumLinearF2_surjective (n : Nat) [NeZero n] :
    Function.Surjective (totalSumLinearF2 n) := by
  intro y
  refine ⟨Pi.single (M := fun _ : Rep n => F2) 0 y, ?_⟩
  rw [totalSumLinearF2_apply]
  rw [Fintype.sum_eq_single (0 : Rep n)]
  · simp
  · intro t ht
    simp [Pi.single_eq_of_ne, ht]

theorem finrank_rep_fun_F2 (n : Nat) [NeZero n] :
    Module.finrank F2 (Rep n → F2) = n := by
  classical
  calc
    Module.finrank F2 (Rep n → F2) =
        ∑ _ : Rep n, Module.finrank F2 F2 := by
      exact Module.finrank_pi_fintype
        (R := F2) (M := fun _ : Rep n => F2)
    _ = n := by
      simp [Rep, ZMod.card]

theorem finrank_ker_totalSumLinearF2 (n : Nat) [NeZero n] :
    Module.finrank F2 (LinearMap.ker (totalSumLinearF2 n)) = n - 1 := by
  let L := totalSumLinearF2 n
  have hsum := LinearMap.finrank_range_add_finrank_ker L
  have hrange : Module.finrank F2 (LinearMap.range L) = 1 := by
    rw [LinearMap.range_eq_top.2 (totalSumLinearF2_surjective n)]
    rw [finrank_top]
    simp
  have hdomain : Module.finrank F2 (Rep n → F2) = n :=
    finrank_rep_fun_F2 n
  have hsum' :
      1 + Module.finrank F2 (LinearMap.ker (totalSumLinearF2 n)) = n := by
    simpa [L, hrange, hdomain] using hsum
  have hpos : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  omega

theorem sum_cycDiff_apply_zero
    {n : Nat} [NeZero n] (f : Rep n → F2) :
    (∑ t : Rep n, cycDiff n F2 f t) = 0 := by
  calc
    (∑ t : Rep n, cycDiff n F2 f t) =
        (∑ t : Rep n, f t) + ∑ t : Rep n, f (t + 1) := by
      simp [cycDiff, Finset.sum_add_distrib]
    _ = (∑ t : Rep n, f t) + ∑ t : Rep n, f t := by
      congr 1
      simpa using (Equiv.sum_comp (Equiv.addRight (1 : Rep n)) f)
    _ = 0 := by
      exact add_self_eq_zero_F2 _

theorem range_cycDiff_eq_ker_totalSumLinearF2
    (n : Nat) [NeZero n] :
    LinearMap.range (cycDiff n F2) =
      LinearMap.ker (totalSumLinearF2 n) := by
  classical
  apply Submodule.eq_of_le_of_finrank_eq
  · intro g hg
    rcases hg with ⟨f, rfl⟩
    exact LinearMap.mem_ker.mpr (sum_cycDiff_apply_zero f)
  · rw [finrank_range_cycDiff]
    rw [finrank_ker_totalSumLinearF2]
    simp

theorem dot_annihilates_range_cycDiff_iff_cycDiff_zero
    {n : Nat} [NeZero n] (β : Rep n → F2) :
    (∀ ψ ∈ LinearMap.range (cycDiff n F2),
        TreeGraph.dotLinear (Rep n) β ψ = 0) ↔
      cycDiff n F2 β = 0 := by
  constructor
  · intro h
    apply (cycDiff_eq_zero_iff_constant_apply F2 β).2
    intro t
    let e : Rep n → F2 := repPoint n t + repPoint n 0
    have he_sum : totalSumLinearF2 n e = 0 := by
      rw [totalSumLinearF2_apply]
      change (∑ x : Rep n, (repPoint n t + repPoint n 0) x) = 0
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib]
      rw [sum_repPoint n t, sum_repPoint n 0]
      exact add_self_eq_zero_F2 1
    have he_range : e ∈ LinearMap.range (cycDiff n F2) := by
      rw [range_cycDiff_eq_ker_totalSumLinearF2]
      exact LinearMap.mem_ker.mpr he_sum
    have hd := h e he_range
    have hdot : TreeGraph.dotLinear (Rep n) β e = β t + β 0 := by
      change (∑ x : Rep n, e x * β x) = β t + β 0
      change
        (∑ x : Rep n, (repPoint n t + repPoint n 0) x * β x) =
          β t + β 0
      simp only [Pi.add_apply, add_mul]
      rw [Finset.sum_add_distrib]
      rw [dot_repPoint n β t, dot_repPoint n β 0]
    have hz : β t + β 0 = 0 := by
      rw [← hdot]
      exact hd
    calc
      β t = β t + 0 := by simp
      _ = β t + (β 0 + β 0) := by rw [add_self_eq_zero_F2]
      _ = (β t + β 0) + β 0 := by abel
      _ = β 0 := by rw [hz]; simp
  · intro hβ ψ hψ
    rcases hψ with ⟨f, rfl⟩
    rcases (cycDiff_eq_zero_iff_exists_constant F2 β).1 hβ with ⟨m, hm⟩
    subst β
    unfold TreeGraph.dotLinear constantFunctionLinear
    calc
      (∑ d : Rep n, cycDiff n F2 f d * m) =
          (∑ d : Rep n, cycDiff n F2 f d) * m := by
        rw [Finset.sum_mul]
      _ = 0 := by
        rw [sum_cycDiff_apply_zero]
        simp

theorem dot_diagCoeffClean_eq_dot_fiberSum
    {b n : Nat} [NeZero n] (hb : 0 < b)
    (α : (Fin b → Rep n) → F2) (ψ : Rep n → F2) :
    TreeGraph.dotLinear (Fin b → Rep n) (diagCoeffClean b n ψ) α =
      TreeGraph.dotLinear (Rep n) (fiberSum n hb F2 α) ψ := by
  classical
  unfold TreeGraph.dotLinear diagCoeffClean
  simp only [fiberSum_apply]
  calc
    (∑ d : Fin b → Rep n, α d * ψ (diag n b d)) =
        ∑ d : Fin b → Rep n,
          ∑ s : Rep n, if diag n b d = s then ψ s * α d else 0 := by
      refine Finset.sum_congr rfl ?_
      intro d _
      rw [Fintype.sum_eq_single (diag n b d)]
      · simp [mul_comm]
      · intro s hs
        have hne : diag n b d ≠ s := fun h => hs h.symm
        simp [hne]
    _ = ∑ s : Rep n, ∑ d : Fin b → Rep n,
          if diag n b d = s then ψ s * α d else 0 := by
      exact Finset.sum_comm
    _ = ∑ s : Rep n,
          (∑ d : Fin b → Rep n, if diag n b d = s then α d else 0) *
            ψ s := by
      refine Finset.sum_congr rfl ?_
      intro s _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro d _
      by_cases h : diag n b d = s <;> simp [h, mul_comm]
    _ = ∑ x : Rep n,
          ψ x * ∑ x_1 : Fin b → Rep n,
            if diag n b x_1 = x then α x_1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro s _
      rw [mul_comm]

instance edgeRootContextClean_nonempty
    (n a : Nat) [NeZero n] (_ha : 0 < a) :
    Nonempty (EdgeRootContextClean n a) := by
  infer_instance

theorem edgeContextSummedConstraintClean_range_eq_cycDiff
    {a n : Nat} [NeZero n] (ha : 0 < a) :
    LinearMap.range (edgeContextSummedConstraintClean a n) =
      LinearMap.range (cycDiff n F2) := by
  letI := edgeRootContextClean_nonempty n a ha
  unfold edgeContextSummedConstraintClean
  exact range_contextSummedCycDiff_eq_range_cycDiff
    (EdgeRootContextClean n a) F2

theorem edgeOpenNormalCorePhaseLinear_zero_iff_cycDiffAfterFiberSum_zero
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b)
    (α : (Fin b → Rep n) → F2) :
    edgeOpenNormalCorePhaseLinear a b n α = 0 ↔
      cycDiffAfterFiberSum n hb F2 α = 0 := by
  constructor
  · intro hzero
    apply (dot_annihilates_range_cycDiff_iff_cycDiff_zero
      (fiberSum n hb F2 α)).1
    intro ψ hψ
    have hψedge : ψ ∈ LinearMap.range (edgeContextSummedConstraintClean a n) := by
      rw [edgeContextSummedConstraintClean_range_eq_cycDiff ha]
      exact hψ
    rcases hψedge with ⟨φ, rfl⟩
    have hφ := congrArg
      (fun L : (EdgeRootContextClean n a → Rep n → F2) →ₗ[F2] F2 => L φ)
      hzero
    change edgeOpenNormalCorePhaseLinear a b n α φ = 0 at hφ
    rw [edgeOpenNormalCorePhaseLinear_apply] at hφ
    rw [← dot_diagCoeffClean_eq_dot_fiberSum hb α
      (edgeContextSummedConstraintClean a n φ)]
    exact hφ
  · intro hcyc
    apply LinearMap.ext
    intro φ
    change edgeOpenNormalCorePhaseLinear a b n α φ = 0
    have hψ : edgeContextSummedConstraintClean a n φ ∈
        LinearMap.range (cycDiff n F2) := by
      rw [← edgeContextSummedConstraintClean_range_eq_cycDiff ha]
      exact ⟨φ, rfl⟩
    have hdot := (dot_annihilates_range_cycDiff_iff_cycDiff_zero
      (fiberSum n hb F2 α)).2 hcyc
      (edgeContextSummedConstraintClean a n φ) hψ
    rw [edgeOpenNormalCorePhaseLinear_apply]
    unfold edgeNormalCorePhaseClean
    rw [dot_diagCoeffClean_eq_dot_fiberSum hb α]
    exact hdot

theorem mem_edgeRootMessageSpaceClean_iff
    (n a b : Nat) [NeZero n] (hb : 0 < b)
    (root : RootFieldAssignmentClean n (RTree.node a [RTree.node b []])) :
    root ∈ edgeRootMessageSpaceClean n a b hb ↔
      cycDiffAfterFiberSum n hb F2
        (edgeRootCoreFromCleanRoot n a b root) = 0 := by
  constructor
  · intro hroot
    rcases (mem_transportedSubmodule_iff
      (RootFieldDomainClean n (RTree.node a [RTree.node b []]))
      (Fin b → Rep n) F2
      (edgeRootFieldDomainCleanEquiv n a b)
      (edgeRootMessageSpaceCore n b hb) root).1 hroot with
      ⟨g, hg, hpre⟩
    have hcore : edgeRootCoreFromCleanRoot n a b root = g := by
      funext y
      have hpre_apply := congrFun hpre
        ((edgeRootFieldDomainCleanEquiv n a b).symm y)
      simpa [edgeRootCoreFromCleanRoot] using hpre_apply.symm
    rw [hcore]
    exact LinearMap.mem_ker.mp hg
  · intro hcore
    apply (mem_transportedSubmodule_iff
      (RootFieldDomainClean n (RTree.node a [RTree.node b []]))
      (Fin b → Rep n) F2
      (edgeRootFieldDomainCleanEquiv n a b)
      (edgeRootMessageSpaceCore n b hb) root).2
    refine ⟨edgeRootCoreFromCleanRoot n a b root, ?_, ?_⟩
    · exact LinearMap.mem_ker.mpr hcore
    · funext rd
      simp [edgeRootCoreFromCleanRoot]

namespace OpenNormalCleanReductionBridge

noncomputable def singleEdge_from_open
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    OpenNormalCleanReductionBridge n (RTree.node a [RTree.node b []]) hT where
  rootMessageSpace :=
    edgeRootMessageSpaceClean n a b (positiveWeights_edge_child hT)
  rootMessageSpace_finrank :=
    finrank_edgeRootMessageSpaceClean_eq_Ydim n a b hT
  open_signed_sum_eq := by
    intro root
    have ha : 0 < a := positiveWeights_edge_root hT
    have hb : 0 < b := positiveWeights_edge_child hT
    rw [openNormalSignedSumClean_edge_eq_fixed_core]
    rw [edgeOpenNormalCoreSignedSumClean_eq_phaseKernel_closed_exp ha]
    have hphase :=
      edgeOpenNormalCorePhaseLinear_zero_iff_cycDiffAfterFiberSum_zero
        (a := a) (b := b) (n := n) ha hb
        (edgeRootCoreFromCleanRoot n a b root)
    have hmem :=
      mem_edgeRootMessageSpaceClean_iff n a b hb root
    have hexp := Xdim_sub_Ydim_singleEdge n a b hT
    by_cases hroot :
        root ∈ edgeRootMessageSpaceClean n a b hb
    · have hzero :
          edgeOpenNormalCorePhaseLinear a b n
            (edgeRootCoreFromCleanRoot n a b root) = 0 := by
        exact hphase.2 (hmem.1 hroot)
      rw [if_pos hzero, if_pos hroot, hexp]
    · have hnonzero :
          edgeOpenNormalCorePhaseLinear a b n
            (edgeRootCoreFromCleanRoot n a b root) ≠ 0 := by
        intro hzero
        exact hroot (hmem.2 (hphase.1 hzero))
      rw [if_neg hnonzero, if_neg hroot]

end OpenNormalCleanReductionBridge

end Imbalance
end TreeGraph
