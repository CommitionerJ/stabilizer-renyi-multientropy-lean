import TreeGraph.Imbalance.CyclicFiberKernel
import TreeGraph.Imbalance.PhysicalRaw

namespace TreeGraph
namespace Imbalance

abbrev EdgeRootContextClean (n a : Nat) [NeZero n] :=
  Fin (a - 1) → Rep n

def edgeChildVertexClean (a b : Nat) :
    Vertex (RTree.node a [RTree.node b []]) :=
  ⟨[0], by
    rw [RTree.addresses_node_single_leaf]
    simp⟩

def edgeChildNonRootVertexClean (a b : Nat) :
    NonRootVertex (RTree.node a [RTree.node b []]) :=
  ⟨edgeChildVertexClean a b, by simp [edgeChildVertexClean]⟩

@[simp] theorem edgeChildNonRootVertexClean_weight (a b : Nat) :
    NonRootVertex.weight (edgeChildNonRootVertexClean a b) = b := by
  rfl

theorem nonRootVertexClean_edge_eq_child {a b : Nat}
    (v : NonRootVertex (RTree.node a [RTree.node b []])) :
    v = edgeChildNonRootVertexClean a b := by
  apply Subtype.ext
  apply Subtype.ext
  have haddr : v.1.1 ∈ [[], [0]] := by
    let p : List Nat := v.1.1
    have hv : p ∈ RTree.addresses (RTree.node a [RTree.node b []]) := v.1.2
    rw [RTree.addresses_node_single_leaf] at hv
    simpa [p] using hv
  rcases List.mem_cons.mp haddr with hroot | htail
  · exact False.elim (v.2 hroot)
  · simpa using htail

theorem otherNonRootVertexClean_edge_false {a b : Nat}
    (u : OtherNonRootVertexClean
      (RTree.node a [RTree.node b []])
      (edgeChildNonRootVertexClean a b)) :
    False := by
  exact u.2 (by rw [nonRootVertexClean_edge_eq_child u.1])

noncomputable def edgeRootFieldDomainCleanEquiv
    (n a b : Nat) [NeZero n] :
    RootFieldDomainClean n (RTree.node a [RTree.node b []]) ≃
      (Fin b → Rep n) where
  toFun rd := fun j => rd (edgeChildNonRootVertexClean a b) j
  invFun y := fun v j => by
    have hv : v = edgeChildNonRootVertexClean a b :=
      nonRootVertexClean_edge_eq_child v
    subst v
    exact y j
  left_inv rd := by
    funext v j
    have hv : v = edgeChildNonRootVertexClean a b :=
      nonRootVertexClean_edge_eq_child v
    subst v
    rfl
  right_inv y := by
    funext j
    rfl

noncomputable def edgeNonRootFieldDomainClean
    (n a b : Nat) [NeZero n]
    (x : EdgeRootContextClean n a) (t : Rep n) :
    NonRootFieldDomainClean n (RTree.node a [RTree.node b []])
      (edgeChildNonRootVertexClean a b) where
  rootCoord := x
  diagonal := t
  otherCoord := fun u => False.elim (otherNonRootVertexClean_edge_false u)

theorem edgeNonRootFieldDomainClean_eta
    (n a b : Nat) [NeZero n]
    (dom : NonRootFieldDomainClean n (RTree.node a [RTree.node b []])
      (edgeChildNonRootVertexClean a b)) :
    edgeNonRootFieldDomainClean n a b dom.rootCoord dom.diagonal = dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      simp only [edgeNonRootFieldDomainClean, RTree.addresses_node, ne_eq,
        NonRootFieldDomainClean.mk.injEq, true_and]
      funext u j
      exact False.elim (otherNonRootVertexClean_edge_false u)

noncomputable def edgeNormalAssignmentCoreEquivClean
    (n a b : Nat) [NeZero n] :
    NormalAssignmentClean n (RTree.node a [RTree.node b []]) ≃
      ((Fin b → Rep n) → F2) ×
        (EdgeRootContextClean n a → Rep n → F2) where
  toFun A :=
    ⟨fun y => A.rootField ((edgeRootFieldDomainCleanEquiv n a b).symm y),
      fun x t => A.nodeField (edgeChildNonRootVertexClean a b)
        (edgeNonRootFieldDomainClean n a b x t)⟩
  invFun P :=
    { rootField := fun rd => P.1 ((edgeRootFieldDomainCleanEquiv n a b) rd)
      nodeField := fun v dom => by
        have hv : v = edgeChildNonRootVertexClean a b :=
          nonRootVertexClean_edge_eq_child v
        subst v
        exact P.2 dom.rootCoord dom.diagonal }
  left_inv A := by
    cases A with
    | mk rootField nodeField =>
        rw [NormalAssignmentClean.mk.injEq]
        constructor
        · funext rd
          change
            rootField
                ((edgeRootFieldDomainCleanEquiv n a b).symm
                  ((edgeRootFieldDomainCleanEquiv n a b) rd)) =
              rootField rd
          exact congrArg rootField
            ((edgeRootFieldDomainCleanEquiv n a b).left_inv rd)
        · funext v dom
          have hv : v = edgeChildNonRootVertexClean a b :=
            nonRootVertexClean_edge_eq_child v
          subst v
          change
            nodeField (edgeChildNonRootVertexClean a b)
                (edgeNonRootFieldDomainClean n a b dom.rootCoord dom.diagonal) =
              nodeField (edgeChildNonRootVertexClean a b) dom
          rw [edgeNonRootFieldDomainClean_eta n a b dom]
  right_inv P := by
    rcases P with ⟨α, φ⟩
    ext y
    · change
        α ((edgeRootFieldDomainCleanEquiv n a b)
          ((edgeRootFieldDomainCleanEquiv n a b).symm y)) = α y
      exact congrArg α
        ((edgeRootFieldDomainCleanEquiv n a b).right_inv y)
    · rfl

noncomputable def edgeNormalSiteCleanEquiv
    (n a b : Nat) [NeZero n] :
    NormalSiteClean n (RTree.node a [RTree.node b []]) ≃
      EdgeRootContextClean n a × (Fin b → Rep n) where
  toFun site :=
    ⟨site.rootCoord, (edgeRootFieldDomainCleanEquiv n a b) site.nonRootCoord⟩
  invFun p :=
    { rootCoord := p.1
      nonRootCoord := (edgeRootFieldDomainCleanEquiv n a b).symm p.2 }
  left_inv site := by
    cases site with
    | mk rootCoord nonRootCoord =>
        simp
  right_inv p := by
    rcases p with ⟨x, y⟩
    simp

theorem phaseAtSiteClean_edge_core
    (n a b : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2)
    (φ : EdgeRootContextClean n a → Rep n → F2)
    (x : EdgeRootContextClean n a) (y : Fin b → Rep n) :
    phaseAtSiteClean (RTree.node a [RTree.node b []])
      ((edgeNormalAssignmentCoreEquivClean n a b).symm (α, φ))
      ((edgeNormalSiteCleanEquiv n a b).symm (x, y)) =
        α y * φ x (diag n b y) +
          α y * φ x (diag n b y + 1) := by
  classical
  let A : NormalAssignmentClean n (RTree.node a [RTree.node b []]) :=
    (edgeNormalAssignmentCoreEquivClean n a b).symm (α, φ)
  let site : NormalSiteClean n (RTree.node a [RTree.node b []]) :=
    (edgeNormalSiteCleanEquiv n a b).symm (x, y)
  change phaseAtSiteClean (RTree.node a [RTree.node b []]) A site =
    α y * φ x (diag n b y) + α y * φ x (diag n b y + 1)
  have hroot :
      ([] : List Nat) ∈ RTree.addresses (RTree.node a [RTree.node b []]) := by
    rw [RTree.addresses_node_single_leaf]
    simp
  have hchild :
      ([0] : List Nat) ∈ RTree.addresses (RTree.node a [RTree.node b []]) := by
    rw [RTree.addresses_node_single_leaf]
    simp
  have hketRoot : ketAtPathClean A site [] = α y := by
    unfold ketAtPathClean
    rw [dif_pos hroot]
    simp [ketAtVertexClean, A, site, edgeNormalAssignmentCoreEquivClean,
      edgeNormalSiteCleanEquiv, edgeRootFieldDomainCleanEquiv]
  have hbraRoot : braAtPathClean A site [] = α y := by
    unfold braAtPathClean
    rw [dif_pos hroot]
    simp [braAtVertexClean, A, site, edgeNormalAssignmentCoreEquivClean,
      edgeNormalSiteCleanEquiv, edgeRootFieldDomainCleanEquiv]
  have hketChild :
      ketAtPathClean A site [0] = φ x (diag n b y) := by
    unfold ketAtPathClean
    rw [dif_pos hchild]
    simp [ketAtVertexClean, nonRootDomainOfSiteClean,
      diagonalClean, A, site, edgeNormalAssignmentCoreEquivClean,
      edgeNormalSiteCleanEquiv, edgeRootFieldDomainCleanEquiv,
      edgeNonRootFieldDomainClean, diag]
    rfl
  have hbraChild :
      braAtPathClean A site [0] = φ x (diag n b y + 1) := by
    unfold braAtPathClean
    rw [dif_pos hchild]
    simp [braAtVertexClean, nonRootDomainOfSiteClean,
      diagonalClean, A, site, edgeNormalAssignmentCoreEquivClean,
      edgeNormalSiteCleanEquiv, edgeRootFieldDomainCleanEquiv,
      edgeNonRootFieldDomainClean, diag]
    rfl
  simp [phaseAtSiteClean, edgePhaseAtSiteClean, hketRoot,
    hbraRoot, hketChild, hbraChild]

noncomputable def diagCoeffClean (b n : Nat) [NeZero n]
    (ψ : Rep n → F2) : (Fin b → Rep n) → F2 :=
  fun y => ψ (diag n b y)

theorem diagCoeffClean_eq_zero_iff {b n : Nat} [NeZero n]
    (hb : 0 < b) (ψ : Rep n → F2) :
    diagCoeffClean b n ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext t
    have ht := congrArg (fun c : (Fin b → Rep n) → F2 =>
      c (diagSection n hb t)) h
    simpa [diagCoeffClean, diag_diagSection] using ht
  · intro h
    subst h
    ext y
    simp [diagCoeffClean]

theorem card_bitFunctions_on_block (b n : Nat) [NeZero n] :
    Fintype.card ((Fin b → Rep n) → F2) = 2 ^ (n ^ b) := by
  rw [Fintype.card_fun]
  have hdom : Fintype.card (Fin b → Rep n) = n ^ b := by
    rw [Fintype.card_fun]
    simp [Rep, ZMod.card]
  rw [hdom]
  simp [F2]

theorem sum_chi_diagCoeffClean_dotLinear
    {b n : Nat} [NeZero n] (hb : 0 < b) (ψ : Rep n → F2) :
    (∑ α : (Fin b → Rep n) → F2,
        chi (TreeGraph.dotLinear (Fin b → Rep n)
          (diagCoeffClean b n ψ) α)) =
      if ψ = 0 then (2 : ℤ) ^ (n ^ b) else 0 := by
  classical
  calc
    (∑ α : (Fin b → Rep n) → F2,
        chi (TreeGraph.dotLinear (Fin b → Rep n)
          (diagCoeffClean b n ψ) α)) =
        if diagCoeffClean b n ψ = 0 then
          (Fintype.card (((Fin b → Rep n) → F2)) : ℤ) else 0 := by
      simpa [chi] using
        TreeGraph.sum_bitSign_dotLinear
          (Fin b → Rep n) (diagCoeffClean b n ψ)
    _ = if ψ = 0 then (2 : ℤ) ^ (n ^ b) else 0 := by
      have hcard :
          (Fintype.card (((Fin b → Rep n) → F2)) : ℤ) =
            (2 : ℤ) ^ (n ^ b) := by
        norm_num [card_bitFunctions_on_block b n]
      by_cases hψ : ψ = 0
      · have hc : diagCoeffClean b n ψ = 0 :=
          (diagCoeffClean_eq_zero_iff hb ψ).2 hψ
        rw [if_pos hc, if_pos hψ]
        exact hcard
      · have hc : diagCoeffClean b n ψ ≠ 0 := by
          intro h
          exact hψ ((diagCoeffClean_eq_zero_iff hb ψ).1 h)
        rw [if_neg hc, if_neg hψ]

noncomputable def edgeContextSummedConstraintClean
    (a n : Nat) [NeZero n] :
    (EdgeRootContextClean n a → Rep n → F2) →ₗ[F2] (Rep n → F2) :=
  contextSummedCycDiff (EdgeRootContextClean n a) n F2

theorem card_edgeRootContextClean (a n : Nat) [NeZero n] :
    Fintype.card (EdgeRootContextClean n a) = n ^ (a - 1) := by
  unfold EdgeRootContextClean
  rw [Fintype.card_fun]
  simp [Rep, ZMod.card]

theorem card_ker_edgeContextSummedConstraintClean
    (a n : Nat) [NeZero n] :
    Nat.card (↥(LinearMap.ker (edgeContextSummedConstraintClean a n))) =
      2 ^ (n ^ (a - 1) * n - (n - 1)) := by
  simpa [edgeContextSummedConstraintClean, card_edgeRootContextClean a n] using
    card_ker_contextSummedCycDiff_F2 (EdgeRootContextClean n a) (n := n)

theorem card_ker_edgeContextSummedConstraintClean_closed
    {a n : Nat} [NeZero n] (ha : 0 < a) :
    Nat.card (↥(LinearMap.ker (edgeContextSummedConstraintClean a n))) =
      2 ^ (n ^ a - (n - 1)) := by
  rw [card_ker_edgeContextSummedConstraintClean]
  have hpow : n ^ (a - 1) * n = n ^ a := by
    have ha' : (a - 1) + 1 = a := by omega
    calc
      n ^ (a - 1) * n = n ^ ((a - 1) + 1) := by
        rw [Nat.pow_succ]
      _ = n ^ a := by rw [ha']
  rw [hpow]

theorem edgeRootConstraintBlocksClean_closed
    {a b n : Nat} [NeZero n] (ha : 0 < a) :
    (2 : ℤ) ^ (n ^ b) *
        (Nat.card
          (↥(LinearMap.ker (edgeContextSummedConstraintClean a n))) : ℤ) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  have hkerNat := card_ker_edgeContextSummedConstraintClean_closed (n := n) ha
  have hkerInt :
      (Nat.card
          (↥(LinearMap.ker (edgeContextSummedConstraintClean a n))) : ℤ) =
        (2 : ℤ) ^ (n ^ a - (n - 1)) := by
    exact_mod_cast hkerNat
  rw [hkerInt]
  rw [← Int.pow_add]
  congr 1
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hna : n ≤ n ^ a := by
    simpa using le_self_pow hn (Nat.ne_of_gt ha)
  have hle : n - 1 ≤ n ^ a := le_trans (Nat.sub_le n 1) hna
  omega

noncomputable def edgeNormalCorePhaseClean (a b n : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2)
    (φ : EdgeRootContextClean n a → Rep n → F2) : F2 :=
  TreeGraph.dotLinear (Fin b → Rep n)
    (diagCoeffClean b n (edgeContextSummedConstraintClean a n φ)) α

noncomputable def edgeNormalCoreSignedSumClean
    (a b n : Nat) [NeZero n] : ℤ :=
  ∑ φ : EdgeRootContextClean n a → Rep n → F2,
    ∑ α : (Fin b → Rep n) → F2,
      chi (edgeNormalCorePhaseClean a b n α φ)

noncomputable def edgeConstraintKernelCleanEquiv
    (a n : Nat) [NeZero n] :
    { φ : EdgeRootContextClean n a → Rep n → F2 //
        edgeContextSummedConstraintClean a n φ = 0 } ≃
      ↥(LinearMap.ker (edgeContextSummedConstraintClean a n)) where
  toFun φ := ⟨φ.1, LinearMap.mem_ker.mpr φ.2⟩
  invFun φ := ⟨φ.1, LinearMap.mem_ker.mp φ.2⟩
  left_inv φ := by
    cases φ
    rfl
  right_inv φ := by
    cases φ
    rfl

theorem card_edgeConstraintClean_zero_subtype
    (a n : Nat) [NeZero n] :
    Fintype.card
        { φ : EdgeRootContextClean n a → Rep n → F2 //
          edgeContextSummedConstraintClean a n φ = 0 } =
      Nat.card (↥(LinearMap.ker (edgeContextSummedConstraintClean a n))) := by
  classical
  have hnat :
      Nat.card
          { φ : EdgeRootContextClean n a → Rep n → F2 //
            edgeContextSummedConstraintClean a n φ = 0 } =
        Nat.card (↥(LinearMap.ker (edgeContextSummedConstraintClean a n))) :=
    Nat.card_congr (edgeConstraintKernelCleanEquiv a n)
  rw [← hnat]
  exact (Nat.card_eq_fintype_card
    (α := { φ : EdgeRootContextClean n a → Rep n → F2 //
      edgeContextSummedConstraintClean a n φ = 0 })).symm

theorem edgeNormalCoreSignedSumClean_closed
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    edgeNormalCoreSignedSumClean a b n =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  classical
  let K : ℤ := (2 : ℤ) ^ (n ^ b)
  calc
    edgeNormalCoreSignedSumClean a b n =
        ∑ φ : EdgeRootContextClean n a → Rep n → F2,
          if edgeContextSummedConstraintClean a n φ = 0 then K else 0 := by
      unfold edgeNormalCoreSignedSumClean edgeNormalCorePhaseClean K
      refine Finset.sum_congr rfl ?_
      intro φ _
      exact sum_chi_diagCoeffClean_dotLinear
        (b := b) (n := n) hb (edgeContextSummedConstraintClean a n φ)
    _ =
        (Fintype.card
          { φ : EdgeRootContextClean n a → Rep n → F2 //
            edgeContextSummedConstraintClean a n φ = 0 } : ℤ) * K := by
      rw [← Finset.sum_filter]
      simp [Fintype.card_subtype, K]
    _ =
        (Nat.card
          (↥(LinearMap.ker (edgeContextSummedConstraintClean a n))) : ℤ) *
          (2 : ℤ) ^ (n ^ b) := by
      rw [card_edgeConstraintClean_zero_subtype a n]
    _ = (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
      rw [mul_comm]
      exact edgeRootConstraintBlocksClean_closed (b := b) (n := n) ha

theorem edgeNormalCorePhaseClean_eq_sum_sites
    (a b n : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2)
    (φ : EdgeRootContextClean n a → Rep n → F2) :
    edgeNormalCorePhaseClean a b n α φ =
      ∑ y : Fin b → Rep n,
        ∑ x : EdgeRootContextClean n a,
          (α y * φ x (diag n b y) +
            α y * φ x (diag n b y + 1)) := by
  classical
  unfold edgeNormalCorePhaseClean diagCoeffClean
    edgeContextSummedConstraintClean contextSummedCycDiff
    contextSumLinear cycDiff
  simp [TreeGraph.dotLinear, Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem edgeNormalCorePhaseClean_eq_sum_sites_comm
    (a b n : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2)
    (φ : EdgeRootContextClean n a → Rep n → F2) :
    edgeNormalCorePhaseClean a b n α φ =
      ∑ x : EdgeRootContextClean n a,
        ∑ y : Fin b → Rep n,
          (α y * φ x (diag n b y) +
            α y * φ x (diag n b y + 1)) := by
  rw [edgeNormalCorePhaseClean_eq_sum_sites]
  exact Finset.sum_comm

theorem totalPhaseClean_edge_eq_core
    (n a b : Nat) [NeZero n]
    (α : (Fin b → Rep n) → F2)
    (φ : EdgeRootContextClean n a → Rep n → F2) :
    totalPhaseClean (RTree.node a [RTree.node b []])
      ((edgeNormalAssignmentCoreEquivClean n a b).symm (α, φ)) =
        edgeNormalCorePhaseClean a b n α φ := by
  classical
  let A : NormalAssignmentClean n (RTree.node a [RTree.node b []]) :=
    (edgeNormalAssignmentCoreEquivClean n a b).symm (α, φ)
  calc
    totalPhaseClean (RTree.node a [RTree.node b []]) A =
        ∑ p : EdgeRootContextClean n a × (Fin b → Rep n),
          phaseAtSiteClean (RTree.node a [RTree.node b []]) A
            ((edgeNormalSiteCleanEquiv n a b).symm p) := by
      unfold totalPhaseClean
      refine Fintype.sum_equiv
        (edgeNormalSiteCleanEquiv n a b)
        (fun site : NormalSiteClean n (RTree.node a [RTree.node b []]) =>
          phaseAtSiteClean (RTree.node a [RTree.node b []]) A site)
        (fun p : EdgeRootContextClean n a × (Fin b → Rep n) =>
          phaseAtSiteClean (RTree.node a [RTree.node b []]) A
            ((edgeNormalSiteCleanEquiv n a b).symm p))
        ?_
      intro site
      change
        phaseAtSiteClean (RTree.node a [RTree.node b []]) A site =
          phaseAtSiteClean (RTree.node a [RTree.node b []]) A
            ((edgeNormalSiteCleanEquiv n a b).symm
              ((edgeNormalSiteCleanEquiv n a b) site))
      exact congrArg
        (phaseAtSiteClean (RTree.node a [RTree.node b []]) A)
        ((edgeNormalSiteCleanEquiv n a b).left_inv site).symm
    _ =
        ∑ x : EdgeRootContextClean n a,
          ∑ y : Fin b → Rep n,
            (α y * φ x (diag n b y) +
              α y * φ x (diag n b y + 1)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro x _
      refine Finset.sum_congr rfl ?_
      intro y _
      exact phaseAtSiteClean_edge_core n a b α φ x y
    _ = edgeNormalCorePhaseClean a b n α φ := by
      exact (edgeNormalCorePhaseClean_eq_sum_sites_comm a b n α φ).symm

theorem normalSignedSumClean_edge_eq_core
    (n a b : Nat) [NeZero n] :
    normalSignedSumClean n (RTree.node a [RTree.node b []]) =
      edgeNormalCoreSignedSumClean a b n := by
  classical
  calc
    normalSignedSumClean n (RTree.node a [RTree.node b []]) =
        ∑ P : ((Fin b → Rep n) → F2) ×
            (EdgeRootContextClean n a → Rep n → F2),
          weightClean (RTree.node a [RTree.node b []])
            ((edgeNormalAssignmentCoreEquivClean n a b).symm P) := by
      unfold normalSignedSumClean
      refine Fintype.sum_equiv
        (edgeNormalAssignmentCoreEquivClean n a b)
        (fun A : NormalAssignmentClean n (RTree.node a [RTree.node b []]) =>
          weightClean (RTree.node a [RTree.node b []]) A)
        (fun P : ((Fin b → Rep n) → F2) ×
            (EdgeRootContextClean n a → Rep n → F2) =>
          weightClean (RTree.node a [RTree.node b []])
            ((edgeNormalAssignmentCoreEquivClean n a b).symm P))
        ?_
      intro A
      change
        weightClean (RTree.node a [RTree.node b []]) A =
          weightClean (RTree.node a [RTree.node b []])
            ((edgeNormalAssignmentCoreEquivClean n a b).symm
              ((edgeNormalAssignmentCoreEquivClean n a b) A))
      exact congrArg (weightClean (RTree.node a [RTree.node b []]))
        ((edgeNormalAssignmentCoreEquivClean n a b).left_inv A).symm
    _ = edgeNormalCoreSignedSumClean a b n := by
      unfold weightClean edgeNormalCoreSignedSumClean
      rw [Fintype.sum_prod_type_right]
      congr with φ
      congr with α
      rw [totalPhaseClean_edge_eq_core]

theorem normalSignedSumClean_edge_closed
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    normalSignedSumClean n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  rw [normalSignedSumClean_edge_eq_core]
  exact edgeNormalCoreSignedSumClean_closed ha hb

theorem Xdim_edge_single_leaf
    {a b n : Nat} [NeZero n] (hb : 0 < b) :
    Xdim n (RTree.node a [RTree.node b []]) =
      n ^ a + n ^ b - (n - 1) := by
  simp [Xdim, XdimCandidate, XdimChildContrib, YdimCandidate,
    branchAllowedDim, RTree.totalWeight]
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hnb : n ≤ n ^ b := by
    simpa using le_self_pow hn (Nat.ne_of_gt hb)
  have hle : n - 1 ≤ n ^ b := le_trans (Nat.sub_le n 1) hnb
  omega

theorem normalSignedSumClean_edge_eq_abstractTreeSignedSum
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    normalSignedSumClean n (RTree.node a [RTree.node b []]) =
      abstractTreeSignedSum n (RTree.node a [RTree.node b []]) hT := by
  have ha : 0 < a := by
    unfold RTree.PositiveWeights at hT
    exact hT.1
  have hb : 0 < b := by
    unfold RTree.PositiveWeights at hT
    have hchild := hT.2 (RTree.node b []) (by simp)
    unfold RTree.PositiveWeights at hchild
    exact hchild.1
  rw [rooted_tree_signed_sum_imbalance_formula]
  rw [normalSignedSumClean_edge_closed ha hb]
  rw [Xdim_edge_single_leaf (n := n) (a := a) (b := b) hb]

theorem positiveWeights_edge_root
    {a b : Nat}
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    0 < a := by
  unfold RTree.PositiveWeights at hT
  exact hT.1

theorem positiveWeights_edge_child
    {a b : Nat}
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    0 < b := by
  unfold RTree.PositiveWeights at hT
  have hchild := hT.2 (RTree.node b []) (by simp)
  unfold RTree.PositiveWeights at hchild
  exact hchild.1

theorem normalFormRawSignedSumClean_edge_closed
    {a b n : Nat} [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    normalFormRawSignedSumClean n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  rw [normalFormRawSignedSumClean_eq_normalSignedSumClean_of_positiveWeights
    (n := n) (T := RTree.node a [RTree.node b []]) hT]
  exact normalSignedSumClean_edge_closed
    (positiveWeights_edge_root hT) (positiveWeights_edge_child hT)

theorem normalFormRawSignedSumClean_edge_eq_abstractTreeSignedSum
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    normalFormRawSignedSumClean n (RTree.node a [RTree.node b []]) =
      abstractTreeSignedSum n (RTree.node a [RTree.node b []]) hT := by
  rw [normalFormRawSignedSumClean_eq_normalSignedSumClean_of_positiveWeights
    (n := n) (T := RTree.node a [RTree.node b []]) hT]
  exact normalSignedSumClean_edge_eq_abstractTreeSignedSum n a b hT

namespace NormalCleanReductionBridge

noncomputable def singleEdge
    (n a b : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [RTree.node b []])) :
    NormalCleanReductionBridge n (RTree.node a [RTree.node b []]) hT where
  normal_signed_sum_eq_abstract :=
    normalSignedSumClean_edge_eq_abstractTreeSignedSum n a b hT

end NormalCleanReductionBridge

end Imbalance
end TreeGraph
