import TreeGraph.RawLinearAlgebra

namespace TreeGraph

namespace RawPrimitive

open RawNormal RawLinearAlgebra

abbrev EdgeRootContext (n a : Nat) [NeZero n] :=
  Fin (a - 1) → ZMod n

def edgeChildVertex (a b : Nat) :
    Vertex (RTree.node a [RTree.node b []]) :=
  ⟨[0], by
    rw [RTree.addresses_node_single_leaf]
    simp⟩

def edgeChildNonRootVertex (a b : Nat) :
    NonRootVertex (RTree.node a [RTree.node b []]) :=
  ⟨edgeChildVertex a b, by simp [edgeChildVertex]⟩

@[simp] theorem edgeChildNonRootVertex_weight (a b : Nat) :
    NonRootVertex.weight (edgeChildNonRootVertex a b) = b := by
  rfl

theorem nonRootVertex_edge_eq_child {a b : Nat}
    (v : NonRootVertex (RTree.node a [RTree.node b []])) :
    v = edgeChildNonRootVertex a b := by
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

theorem otherNonRootVertex_edge_false {a b : Nat}
    (u : OtherNonRootVertex
      (RTree.node a [RTree.node b []]) (edgeChildNonRootVertex a b)) :
    False := by
  exact u.2 (by rw [nonRootVertex_edge_eq_child u.1])

noncomputable def edgeRootFieldDomainEquiv
    (n a b : Nat) [NeZero n] :
    RootFieldDomain n (RTree.node a [RTree.node b []]) ≃
      (Fin b → ZMod n) where
  toFun rd := fun j => rd (edgeChildNonRootVertex a b) j
  invFun y := fun v j => by
    have hv : v = edgeChildNonRootVertex a b :=
      nonRootVertex_edge_eq_child v
    subst v
    exact y j
  left_inv rd := by
    funext v j
    have hv : v = edgeChildNonRootVertex a b :=
      nonRootVertex_edge_eq_child v
    subst v
    rfl
  right_inv y := by
    funext j
    rfl

noncomputable def edgeNonRootFieldDomain
    (n a b : Nat) [NeZero n]
    (x : EdgeRootContext n a) (t : ZMod n) :
    NonRootFieldDomain n (RTree.node a [RTree.node b []])
      (edgeChildNonRootVertex a b) where
  rootCoord := x
  diagonal := t
  otherCoord := fun u => False.elim (otherNonRootVertex_edge_false u)

theorem edgeNonRootFieldDomain_eta
    (n a b : Nat) [NeZero n]
    (dom : NonRootFieldDomain n (RTree.node a [RTree.node b []])
      (edgeChildNonRootVertex a b)) :
    edgeNonRootFieldDomain n a b dom.rootCoord dom.diagonal = dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      simp [edgeNonRootFieldDomain]
      funext u j
      exact False.elim (otherNonRootVertex_edge_false u)

noncomputable def edgeNormalAssignmentCoreEquiv
    (n a b : Nat) [NeZero n] :
    NormalAssignment n (RTree.node a [RTree.node b []]) ≃
      ((Fin b → ZMod n) → F2) ×
        (EdgeRootContext n a → ZMod n → F2) where
  toFun A :=
    ⟨fun y => A.rootField ((edgeRootFieldDomainEquiv n a b).symm y),
      fun x t => A.nodeField (edgeChildNonRootVertex a b)
        (edgeNonRootFieldDomain n a b x t)⟩
  invFun P :=
    { rootField := fun rd => P.1 ((edgeRootFieldDomainEquiv n a b) rd)
      nodeField := fun v dom => by
        have hv : v = edgeChildNonRootVertex a b :=
          nonRootVertex_edge_eq_child v
        subst v
        exact P.2 dom.rootCoord dom.diagonal }
  left_inv A := by
    cases A with
    | mk rootField nodeField =>
        rw [NormalAssignment.mk.injEq]
        constructor
        · funext rd
          change
            rootField
                ((edgeRootFieldDomainEquiv n a b).symm
                  ((edgeRootFieldDomainEquiv n a b) rd)) =
              rootField rd
          exact congrArg rootField
            ((edgeRootFieldDomainEquiv n a b).left_inv rd)
        · funext v dom
          have hv : v = edgeChildNonRootVertex a b :=
            nonRootVertex_edge_eq_child v
          subst v
          change
            nodeField (edgeChildNonRootVertex a b)
                (edgeNonRootFieldDomain n a b dom.rootCoord dom.diagonal) =
              nodeField (edgeChildNonRootVertex a b) dom
          rw [edgeNonRootFieldDomain_eta n a b dom]
  right_inv P := by
    rcases P with ⟨α, φ⟩
    ext y
    · change
        α ((edgeRootFieldDomainEquiv n a b)
          ((edgeRootFieldDomainEquiv n a b).symm y)) = α y
      exact congrArg α
        ((edgeRootFieldDomainEquiv n a b).right_inv y)
    · rfl

noncomputable def edgeNormalSiteEquiv
    (n a b : Nat) [NeZero n] :
    NormalSite n (RTree.node a [RTree.node b []]) ≃
      EdgeRootContext n a × (Fin b → ZMod n) where
  toFun site :=
    ⟨site.rootCoord, (edgeRootFieldDomainEquiv n a b) site.nonRootCoord⟩
  invFun p :=
    { rootCoord := p.1
      nonRootCoord := (edgeRootFieldDomainEquiv n a b).symm p.2 }
  left_inv site := by
    cases site with
    | mk rootCoord nonRootCoord =>
        simp
  right_inv p := by
    rcases p with ⟨x, y⟩
    simp

theorem phaseAtSite_edge_core
    (n a b : Nat) [NeZero n]
    (α : (Fin b → ZMod n) → F2)
    (φ : EdgeRootContext n a → ZMod n → F2)
    (x : EdgeRootContext n a) (y : Fin b → ZMod n) :
    RawNormal.phaseAtSite (RTree.node a [RTree.node b []])
      ((edgeNormalAssignmentCoreEquiv n a b).symm (α, φ))
      ((edgeNormalSiteEquiv n a b).symm (x, y)) =
        α y * φ x (diagSum b n y) +
          α y * φ x (diagSum b n y + 1) := by
  classical
  let A : NormalAssignment n (RTree.node a [RTree.node b []]) :=
    (edgeNormalAssignmentCoreEquiv n a b).symm (α, φ)
  let site : NormalSite n (RTree.node a [RTree.node b []]) :=
    (edgeNormalSiteEquiv n a b).symm (x, y)
  change RawNormal.phaseAtSite (RTree.node a [RTree.node b []]) A site =
    α y * φ x (diagSum b n y) + α y * φ x (diagSum b n y + 1)
  have hroot :
      ([] : List Nat) ∈ RTree.addresses (RTree.node a [RTree.node b []]) := by
    rw [RTree.addresses_node_single_leaf]
    simp
  have hchild :
      ([0] : List Nat) ∈ RTree.addresses (RTree.node a [RTree.node b []]) := by
    rw [RTree.addresses_node_single_leaf]
    simp
  have hketRoot : RawNormal.ketAtPath A site [] = α y := by
    unfold RawNormal.ketAtPath
    rw [dif_pos hroot]
    simp [RawNormal.ketAtVertex, A, site, edgeNormalAssignmentCoreEquiv,
      edgeNormalSiteEquiv, edgeRootFieldDomainEquiv]
  have hbraRoot : RawNormal.braAtPath A site [] = α y := by
    unfold RawNormal.braAtPath
    rw [dif_pos hroot]
    simp [RawNormal.braAtVertex, A, site, edgeNormalAssignmentCoreEquiv,
      edgeNormalSiteEquiv, edgeRootFieldDomainEquiv]
  have hketChild :
      RawNormal.ketAtPath A site [0] = φ x (diagSum b n y) := by
    unfold RawNormal.ketAtPath
    rw [dif_pos hchild]
    simp [RawNormal.ketAtVertex, RawNormal.nonRootDomainOfSite,
      RawNormal.diagonal, A, site, edgeNormalAssignmentCoreEquiv,
      edgeNormalSiteEquiv, edgeRootFieldDomainEquiv,
      edgeNonRootFieldDomain, diagSum]
    rfl
  have hbraChild :
      RawNormal.braAtPath A site [0] = φ x (diagSum b n y + 1) := by
    unfold RawNormal.braAtPath
    rw [dif_pos hchild]
    simp [RawNormal.braAtVertex, RawNormal.nonRootDomainOfSite,
      RawNormal.diagonal, A, site, edgeNormalAssignmentCoreEquiv,
      edgeNormalSiteEquiv, edgeRootFieldDomainEquiv,
      edgeNonRootFieldDomain, diagSum]
    rfl
  simp [RawNormal.phaseAtSite, RawNormal.edgePhaseAtSite, hketRoot,
    hbraRoot, hketChild, hbraChild]

structure RawAssignment (n : Nat) [NeZero n] (T : RTree) where
  ket : Vertex T → NormalSite n T → F2
  bra : Vertex T → NormalSite n T → F2
  deriving Fintype

noncomputable def localEdgePhase {n : Nat} [NeZero n] {T : RTree}
    (A : RawAssignment n T) (site : NormalSite n T)
    (e : List Nat × List Nat) : F2 :=
  let ketAt (p : List Nat) : F2 :=
    if hp : p ∈ RTree.addresses T then A.ket ⟨p, hp⟩ site else 0
  let braAt (p : List Nat) : F2 :=
    if hp : p ∈ RTree.addresses T then A.bra ⟨p, hp⟩ site else 0
  ketAt e.1 * ketAt e.2 + braAt e.1 * braAt e.2

noncomputable def phaseAtSite {n : Nat} [NeZero n] (T : RTree)
    (A : RawAssignment n T) (site : NormalSite n T) : F2 :=
  (RTree.edgeList T).map (localEdgePhase A site) |>.sum

noncomputable def totalPhase {n : Nat} [NeZero n] (T : RTree)
    (A : RawAssignment n T) : F2 :=
  ∑ site : NormalSite n T, phaseAtSite T A site

noncomputable def weight {n : Nat} [NeZero n] (T : RTree)
    (A : RawAssignment n T) : ℤ :=
  bitSign (totalPhase T A)

def RealizedByNormal {n : Nat} [NeZero n] (T : RTree)
    (Araw : RawAssignment n T) : Prop :=
  ∃ Anorm : NormalAssignment n T,
    Araw.ket = (fun v site => ketAtVertex Anorm site v)
      ∧ Araw.bra = (fun v site => braAtVertex Anorm site v)

abbrev NormalFormRawAssignments (n : Nat) [NeZero n] (T : RTree) :=
  { Araw : RawAssignment n T // RealizedByNormal T Araw }

abbrev NonRootContext (n : Nat) [NeZero n] (T : RTree)
    (v : NonRootVertex T) :=
  (Fin (T.rootWeight - 1) → ZMod n) ×
    ((u : OtherNonRootVertex T v) →
      Fin (NonRootVertex.weight u.1) → ZMod n)

noncomputable def nonRootContextExponent (T : RTree)
    (v : NonRootVertex T) : Nat :=
  (T.rootWeight - 1) +
    ∑ u : OtherNonRootVertex T v, NonRootVertex.weight u.1

theorem card_nonRootContext {n : Nat} [NeZero n]
    (T : RTree) (v : NonRootVertex T) :
    Fintype.card (NonRootContext n T v) =
      n ^ nonRootContextExponent T v := by
  classical
  unfold NonRootContext nonRootContextExponent
  rw [Fintype.card_prod]
  have hroot :
      Fintype.card (Fin (T.rootWeight - 1) → ZMod n) =
        n ^ (T.rootWeight - 1) := by
    rw [Fintype.card_fun]
    simp [ZMod.card]
  have hother :
      Fintype.card
          ((u : OtherNonRootVertex T v) →
            Fin (NonRootVertex.weight u.1) → ZMod n) =
        n ^ (∑ u : OtherNonRootVertex T v,
          NonRootVertex.weight u.1) := by
    rw [Fintype.card_pi]
    have hprod :
        (∏ u : OtherNonRootVertex T v,
            n ^ NonRootVertex.weight u.1) =
          n ^ (∑ u : OtherNonRootVertex T v,
            NonRootVertex.weight u.1) := by
      simpa using
        (Finset.prod_pow_eq_pow_sum
          (s := Finset.univ)
          (f := fun u : OtherNonRootVertex T v =>
            NonRootVertex.weight u.1)
          (a := n))
    refine hprod ▸ Finset.prod_congr rfl ?_
    intro u _
    rw [Fintype.card_fun]
    simp [ZMod.card]
  rw [hroot, hother, Nat.pow_add]

abbrev NonRootRawDomain (n : Nat) [NeZero n] (T : RTree)
    (v : NonRootVertex T) :=
  NonRootContext n T v ×
    (Fin (NonRootVertex.weight v) → ZMod n)

theorem card_nonRootRawDomain {n : Nat} [NeZero n]
    (T : RTree) (v : NonRootVertex T) :
    Fintype.card (NonRootRawDomain n T v) =
      n ^ (nonRootContextExponent T v + NonRootVertex.weight v) := by
  classical
  unfold NonRootRawDomain
  rw [Fintype.card_prod, card_nonRootContext]
  have htuple :
      Fintype.card (Fin (NonRootVertex.weight v) → ZMod n) =
        n ^ NonRootVertex.weight v := by
    rw [Fintype.card_fun]
    simp [ZMod.card]
  rw [htuple, Nat.pow_add]

noncomputable def nonRootFieldDomainEquivContextDiagonal
    {n : Nat} [NeZero n] (T : RTree) (v : NonRootVertex T) :
    NonRootFieldDomain n T v ≃ NonRootContext n T v × ZMod n where
  toFun dom := ⟨⟨dom.rootCoord, dom.otherCoord⟩, dom.diagonal⟩
  invFun x :=
    { rootCoord := x.1.1
      diagonal := x.2
      otherCoord := x.1.2 }
  left_inv dom := by
    cases dom
    rfl
  right_inv x := by
    rcases x with ⟨⟨rootCoord, otherCoord⟩, diagonal⟩
    rfl

theorem card_nonRootFieldDomain {n : Nat} [NeZero n]
    (T : RTree) (v : NonRootVertex T) :
    Fintype.card (NonRootFieldDomain n T v) =
      n ^ (nonRootContextExponent T v + 1) := by
  classical
  calc
    Fintype.card (NonRootFieldDomain n T v) =
        Fintype.card (NonRootContext n T v × ZMod n) :=
      Fintype.card_congr
        (nonRootFieldDomainEquivContextDiagonal (n := n) T v)
    _ = n ^ (nonRootContextExponent T v + 1) := by
      rw [Fintype.card_prod, card_nonRootContext, ZMod.card]
      simp [Nat.pow_add]

noncomputable def nonRootConstraintLinearMap
    {n : Nat} [NeZero n] (T : RTree) (v : NonRootVertex T) :
    (NonRootContext n T v →
        (Fin (NonRootVertex.weight v) → ZMod n) → F2) →ₗ[F2]
      (NonRootContext n T v → ZMod n → F2) :=
  (paramCyclicDiff (NonRootContext n T v) n F2).comp
    (paramFiberSum (NonRootContext n T v)
      (NonRootVertex.weight v) n F2)

theorem card_ker_nonRootConstraintLinearMap
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    Nat.card (↥(LinearMap.ker (nonRootConstraintLinearMap (n := n) T v))) =
      2 ^ (Fintype.card (NonRootContext n T v) *
          (n ^ NonRootVertex.weight v * Module.finrank F2 F2) -
        Fintype.card (NonRootContext n T v) *
          ((n - 1) * Module.finrank F2 F2)) := by
  simpa [nonRootConstraintLinearMap] using
    (card_ker_paramCyclicDiff_comp_paramFiberSum
      (NonRootContext n T v)
      (a := NonRootVertex.weight v) (n := n) hvpos F2)

theorem card_ker_nonRootConstraintLinearMap_closed
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    Nat.card (↥(LinearMap.ker (nonRootConstraintLinearMap (n := n) T v))) =
      2 ^ (Fintype.card (NonRootContext n T v) *
          n ^ NonRootVertex.weight v -
        Fintype.card (NonRootContext n T v) * (n - 1)) := by
  simpa [F2, Nat.mul_assoc] using
    card_ker_nonRootConstraintLinearMap (n := n) (T := T) v hvpos

theorem card_ker_nonRootConstraintLinearMap_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (v : NonRootVertex T) :
    Nat.card (↥(LinearMap.ker (nonRootConstraintLinearMap (n := n) T v))) =
      2 ^ (Fintype.card (NonRootContext n T v) *
          n ^ NonRootVertex.weight v -
        Fintype.card (NonRootContext n T v) * (n - 1)) := by
  apply card_ker_nonRootConstraintLinearMap_closed
  simpa [NonRootVertex.weight, Vertex.weight] using
    (RTree.weightAt_positive_of_mem_addresses hT v.1.2)

theorem card_ker_nonRootConstraintLinearMap_weight_closed
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    Nat.card (↥(LinearMap.ker (nonRootConstraintLinearMap (n := n) T v))) =
      2 ^ (n ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
        n ^ nonRootContextExponent T v * (n - 1)) := by
  have h :=
    card_ker_nonRootConstraintLinearMap_closed (n := n) (T := T) v hvpos
  rw [card_nonRootContext] at h
  simpa [Nat.pow_add] using h

theorem card_ker_nonRootConstraintLinearMap_weight_closed_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (v : NonRootVertex T) :
    Nat.card (↥(LinearMap.ker (nonRootConstraintLinearMap (n := n) T v))) =
      2 ^ (n ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
        n ^ nonRootContextExponent T v * (n - 1)) := by
  apply card_ker_nonRootConstraintLinearMap_weight_closed
  simpa [NonRootVertex.weight, Vertex.weight] using
    (RTree.weightAt_positive_of_mem_addresses hT v.1.2)

private theorem nonRootConstraintLinearMap_exponent_le
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    n ^ nonRootContextExponent T v * (n - 1) ≤
      n ^ (nonRootContextExponent T v + NonRootVertex.weight v) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hpow : n ≤ n ^ NonRootVertex.weight v := by
    simpa using le_self_pow hn (Nat.ne_of_gt hvpos)
  have hroot : n - 1 ≤ n ^ NonRootVertex.weight v :=
    le_trans (Nat.sub_le n 1) hpow
  have hmul :=
    Nat.mul_le_mul_left (n ^ nonRootContextExponent T v) hroot
  simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using hmul

private theorem nonRootConstraintLinearMap_exponent_toNat_closed
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    Int.toNat
        ((nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v) =
      n ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
        n ^ nonRootContextExponent T v * (n - 1) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hle := nonRootConstraintLinearMap_exponent_le (n := n) v hvpos
  have hcast :
      ((n ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
        n ^ nonRootContextExponent T v * (n - 1) : Nat) : ℤ) =
        (nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v := by
    rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_sub hn]
    simp [nZ, tZ, Nat.cast_pow]
    ring
  rw [← hcast]
  simp

theorem card_ker_nonRootConstraintLinearMap_eq_two_pow_contextClosed
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    Nat.card (↥(LinearMap.ker (nonRootConstraintLinearMap (n := n) T v))) =
      2 ^ Int.toNat
        ((nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v) := by
  rw [card_ker_nonRootConstraintLinearMap_weight_closed
    (n := n) (T := T) v hvpos]
  rw [← nonRootConstraintLinearMap_exponent_toNat_closed
    (n := n) (T := T) v hvpos]

theorem card_ker_nonRootConstraintLinearMap_eq_two_pow_contextClosed_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (v : NonRootVertex T) :
    Nat.card (↥(LinearMap.ker (nonRootConstraintLinearMap (n := n) T v))) =
      2 ^ Int.toNat
        ((nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v) := by
  apply card_ker_nonRootConstraintLinearMap_eq_two_pow_contextClosed
  simpa [NonRootVertex.weight, Vertex.weight] using
    (RTree.weightAt_positive_of_mem_addresses hT v.1.2)

noncomputable def diagCoeff (b n : Nat) [NeZero n]
    (ψ : ZMod n → F2) : (Fin b → ZMod n) → F2 :=
  fun y => ψ (diagSum b n y)

theorem diagCoeff_eq_zero_iff {b n : Nat} [NeZero n]
    (hb : 0 < b) (ψ : ZMod n → F2) :
    diagCoeff b n ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext t
    have ht :=
      congrArg (fun c : (Fin b → ZMod n) → F2 =>
        c (fiberRep b n hb t)) h
    simpa [diagCoeff, diagSum_fiberRep hb t] using ht
  · intro h
    subst h
    ext y
    simp [diagCoeff]

theorem card_tupleDomain (b n : Nat) [NeZero n] :
    Fintype.card (Fin b → ZMod n) = n ^ b := by
  rw [Fintype.card_fun]
  simp [ZMod.card]

theorem card_bitFunctions_on_tuple (b n : Nat) [NeZero n] :
    Fintype.card ((Fin b → ZMod n) → F2) = 2 ^ (n ^ b) := by
  rw [Fintype.card_fun, card_tupleDomain]
  simp [F2]

theorem sum_bitSign_diagCoeff_dotLinear
    {b n : Nat} [NeZero n] (hb : 0 < b) (ψ : ZMod n → F2) :
    (∑ α : (Fin b → ZMod n) → F2,
        bitSign (dotLinear (Fin b → ZMod n) (diagCoeff b n ψ) α)) =
      if ψ = 0 then (2 : ℤ) ^ (n ^ b) else 0 := by
  classical
  calc
    (∑ α : (Fin b → ZMod n) → F2,
        bitSign (dotLinear (Fin b → ZMod n) (diagCoeff b n ψ) α)) =
        if diagCoeff b n ψ = 0 then
          (Fintype.card ((Fin b → ZMod n) → F2) : ℤ) else 0 :=
      sum_bitSign_dotLinear (Fin b → ZMod n) (diagCoeff b n ψ)
    _ = if ψ = 0 then (2 : ℤ) ^ (n ^ b) else 0 := by
      have hcard :
          (Fintype.card ((Fin b → ZMod n) → F2) : ℤ) =
            (2 : ℤ) ^ (n ^ b) := by
        norm_num [card_bitFunctions_on_tuple b n]
      by_cases hψ : ψ = 0
      · subst ψ
        have hdiag : diagCoeff b n (0 : ZMod n → F2) = 0 := by
          ext y
          simp [diagCoeff]
        simp [hdiag]
      · have hc : diagCoeff b n ψ ≠ 0 := by
          intro h
          exact hψ ((diagCoeff_eq_zero_iff hb ψ).1 h)
        simp [hψ, hc]

theorem card_edgeRootContext (a n : Nat) [NeZero n] :
    Fintype.card (EdgeRootContext n a) = n ^ (a - 1) := by
  unfold EdgeRootContext
  rw [Fintype.card_fun]
  simp [ZMod.card]

noncomputable def edgeContextSummedConstraint (a n : Nat) [NeZero n] :
    (EdgeRootContext n a → ZMod n → F2) →ₗ[F2] (ZMod n → F2) :=
  contextSummedCyclicDiff (EdgeRootContext n a) n F2

theorem card_ker_edgeContextSummedConstraint (a n : Nat) [NeZero n] :
    Nat.card (↥(LinearMap.ker (edgeContextSummedConstraint a n))) =
      2 ^ (n ^ (a - 1) * n - (n - 1)) := by
  simpa [edgeContextSummedConstraint, card_edgeRootContext a n] using
    card_ker_contextSummedCyclicDiff_F2 (EdgeRootContext n a) (n := n)

theorem card_ker_edgeContextSummedConstraint_closed
    {a n : Nat} [NeZero n] (ha : 0 < a) :
    Nat.card (↥(LinearMap.ker (edgeContextSummedConstraint a n))) =
      2 ^ (n ^ a - (n - 1)) := by
  rw [card_ker_edgeContextSummedConstraint]
  have hpow : n ^ (a - 1) * n = n ^ a := by
    have ha' : (a - 1) + 1 = a := by omega
    calc
      n ^ (a - 1) * n = n ^ ((a - 1) + 1) := by
        rw [Nat.pow_succ]
      _ = n ^ a := by rw [ha']
  rw [hpow]

theorem edgeRootConstraintBlocks_closed
    {a b n : Nat} [NeZero n] (ha : 0 < a) :
    (2 : ℤ) ^ (n ^ b) *
        (Nat.card (↥(LinearMap.ker (edgeContextSummedConstraint a n))) : ℤ) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  have hkerNat := card_ker_edgeContextSummedConstraint_closed (n := n) ha
  have hkerInt :
      (Nat.card (↥(LinearMap.ker (edgeContextSummedConstraint a n))) : ℤ) =
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

noncomputable def edgeRootBoundaryConstraint (b n : Nat) [NeZero n] :
    ((Fin b → ZMod n) → F2) →ₗ[F2] (ZMod n → F2) :=
  (cyclicDiff n F2).comp (fiberSum b n F2)

theorem card_ker_edgeRootBoundaryConstraint
    {b n : Nat} [NeZero n] (hb : 0 < b) :
    Nat.card (↥(LinearMap.ker (edgeRootBoundaryConstraint b n))) =
      2 ^ (n ^ b - (n - 1)) := by
  simpa [edgeRootBoundaryConstraint] using
    card_ker_cyclicDiff_comp_fiberSum (a := b) (n := n) hb F2

noncomputable def edgeRootBoundaryConstraintZeroEquiv
    (b n : Nat) [NeZero n] :
    { α : (Fin b → ZMod n) → F2 //
        edgeRootBoundaryConstraint b n α = 0 } ≃
      ↥(LinearMap.ker (edgeRootBoundaryConstraint b n)) where
  toFun α := ⟨α.1, LinearMap.mem_ker.mpr α.2⟩
  invFun α := ⟨α.1, LinearMap.mem_ker.mp α.2⟩
  left_inv α := by
    cases α
    rfl
  right_inv α := by
    cases α
    rfl

theorem card_edgeRootBoundaryConstraint_zero_subtype
    {b n : Nat} [NeZero n] (hb : 0 < b) :
    Fintype.card
        { α : (Fin b → ZMod n) → F2 //
          edgeRootBoundaryConstraint b n α = 0 } =
      2 ^ (n ^ b - (n - 1)) := by
  classical
  have hnat :
      Nat.card
          { α : (Fin b → ZMod n) → F2 //
            edgeRootBoundaryConstraint b n α = 0 } =
        Nat.card (↥(LinearMap.ker (edgeRootBoundaryConstraint b n))) :=
    Nat.card_congr (edgeRootBoundaryConstraintZeroEquiv b n)
  rw [← Nat.card_eq_fintype_card, hnat]
  exact card_ker_edgeRootBoundaryConstraint (b := b) (n := n) hb

noncomputable def edgeNormalCorePhase (a b n : Nat) [NeZero n]
    (α : (Fin b → ZMod n) → F2)
    (φ : EdgeRootContext n a → ZMod n → F2) : F2 :=
  dotLinear (Fin b → ZMod n)
    (diagCoeff b n (edgeContextSummedConstraint a n φ)) α

noncomputable def edgeNormalCoreSignedSum (a b n : Nat) [NeZero n] : ℤ :=
  ∑ φ : EdgeRootContext n a → ZMod n → F2,
    ∑ α : (Fin b → ZMod n) → F2,
      bitSign (edgeNormalCorePhase a b n α φ)

theorem signedSum_edge_reindex_core
    (n a b : Nat) [NeZero n] :
    RawNormal.signedSum n (RTree.node a [RTree.node b []]) =
      ∑ P :
          ((Fin b → ZMod n) → F2) ×
            (EdgeRootContext n a → ZMod n → F2),
        RawNormal.weight (RTree.node a [RTree.node b []])
          ((edgeNormalAssignmentCoreEquiv n a b).symm P) := by
  classical
  unfold RawNormal.signedSum
  refine Fintype.sum_equiv
    (edgeNormalAssignmentCoreEquiv n a b)
    (fun A : NormalAssignment n (RTree.node a [RTree.node b []]) =>
      RawNormal.weight (RTree.node a [RTree.node b []]) A)
    (fun P :
        ((Fin b → ZMod n) → F2) ×
          (EdgeRootContext n a → ZMod n → F2) =>
      RawNormal.weight (RTree.node a [RTree.node b []])
        ((edgeNormalAssignmentCoreEquiv n a b).symm P))
    ?_
  intro A
  change
    RawNormal.weight (RTree.node a [RTree.node b []]) A =
      RawNormal.weight (RTree.node a [RTree.node b []])
        ((edgeNormalAssignmentCoreEquiv n a b).symm
          ((edgeNormalAssignmentCoreEquiv n a b) A))
  exact congrArg (RawNormal.weight (RTree.node a [RTree.node b []]))
    ((edgeNormalAssignmentCoreEquiv n a b).left_inv A).symm

theorem edgeNormalCorePhase_eq_sum_sites
    (a b n : Nat) [NeZero n]
    (α : (Fin b → ZMod n) → F2)
    (φ : EdgeRootContext n a → ZMod n → F2) :
    edgeNormalCorePhase a b n α φ =
      ∑ y : Fin b → ZMod n,
        ∑ x : EdgeRootContext n a,
          (α y * φ x (diagSum b n y) +
            α y * φ x (diagSum b n y + 1)) := by
  classical
  unfold edgeNormalCorePhase dotLinear diagCoeff
    edgeContextSummedConstraint contextSummedCyclicDiff
    contextSumLinear cyclicDiff
  simp [Finset.mul_sum, Finset.sum_add_distrib, mul_add]

theorem edgeNormalCorePhase_eq_sum_sites_comm
    (a b n : Nat) [NeZero n]
    (α : (Fin b → ZMod n) → F2)
    (φ : EdgeRootContext n a → ZMod n → F2) :
    edgeNormalCorePhase a b n α φ =
      ∑ x : EdgeRootContext n a,
        ∑ y : Fin b → ZMod n,
          (α y * φ x (diagSum b n y) +
            α y * φ x (diagSum b n y + 1)) := by
  rw [edgeNormalCorePhase_eq_sum_sites]
  exact Finset.sum_comm

theorem totalPhase_edge_eq_core
    (n a b : Nat) [NeZero n]
    (α : (Fin b → ZMod n) → F2)
    (φ : EdgeRootContext n a → ZMod n → F2) :
    RawNormal.totalPhase (RTree.node a [RTree.node b []])
      ((edgeNormalAssignmentCoreEquiv n a b).symm (α, φ)) =
        edgeNormalCorePhase a b n α φ := by
  classical
  let A : NormalAssignment n (RTree.node a [RTree.node b []]) :=
    (edgeNormalAssignmentCoreEquiv n a b).symm (α, φ)
  calc
    RawNormal.totalPhase (RTree.node a [RTree.node b []]) A =
        ∑ p : EdgeRootContext n a × (Fin b → ZMod n),
          RawNormal.phaseAtSite (RTree.node a [RTree.node b []]) A
            ((edgeNormalSiteEquiv n a b).symm p) := by
      unfold RawNormal.totalPhase
      refine Fintype.sum_equiv
        (edgeNormalSiteEquiv n a b)
        (fun site : NormalSite n (RTree.node a [RTree.node b []]) =>
          RawNormal.phaseAtSite (RTree.node a [RTree.node b []]) A site)
        (fun p : EdgeRootContext n a × (Fin b → ZMod n) =>
          RawNormal.phaseAtSite (RTree.node a [RTree.node b []]) A
            ((edgeNormalSiteEquiv n a b).symm p))
        ?_
      intro site
      change
        RawNormal.phaseAtSite (RTree.node a [RTree.node b []]) A site =
          RawNormal.phaseAtSite (RTree.node a [RTree.node b []]) A
            ((edgeNormalSiteEquiv n a b).symm
              ((edgeNormalSiteEquiv n a b) site))
      exact congrArg
        (RawNormal.phaseAtSite (RTree.node a [RTree.node b []]) A)
        ((edgeNormalSiteEquiv n a b).left_inv site).symm
    _ =
        ∑ x : EdgeRootContext n a,
          ∑ y : Fin b → ZMod n,
            (α y * φ x (diagSum b n y) +
              α y * φ x (diagSum b n y + 1)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro x _
      refine Finset.sum_congr rfl ?_
      intro y _
      exact phaseAtSite_edge_core n a b α φ x y
    _ = edgeNormalCorePhase a b n α φ := by
      exact (edgeNormalCorePhase_eq_sum_sites_comm a b n α φ).symm

noncomputable def edgeConstraintKernelEquiv (a n : Nat) [NeZero n] :
    { φ : EdgeRootContext n a → ZMod n → F2 //
        edgeContextSummedConstraint a n φ = 0 } ≃
      ↥(LinearMap.ker (edgeContextSummedConstraint a n)) where
  toFun φ := ⟨φ.1, LinearMap.mem_ker.mpr φ.2⟩
  invFun φ := ⟨φ.1, LinearMap.mem_ker.mp φ.2⟩
  left_inv φ := by
    cases φ
    rfl
  right_inv φ := by
    cases φ
    rfl

theorem card_edgeConstraint_zero_subtype (a n : Nat) [NeZero n] :
    Fintype.card
        { φ : EdgeRootContext n a → ZMod n → F2 //
          edgeContextSummedConstraint a n φ = 0 } =
      Nat.card (↥(LinearMap.ker (edgeContextSummedConstraint a n))) := by
  classical
  have hnat :
      Nat.card
          { φ : EdgeRootContext n a → ZMod n → F2 //
            edgeContextSummedConstraint a n φ = 0 } =
        Nat.card (↥(LinearMap.ker (edgeContextSummedConstraint a n))) :=
    Nat.card_congr (edgeConstraintKernelEquiv a n)
  rw [← hnat]
  exact (Nat.card_eq_fintype_card
    (α := { φ : EdgeRootContext n a → ZMod n → F2 //
      edgeContextSummedConstraint a n φ = 0 })).symm

theorem edgeNormalCoreSignedSum_closed
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    edgeNormalCoreSignedSum a b n =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  classical
  let K : ℤ := (2 : ℤ) ^ (n ^ b)
  calc
    edgeNormalCoreSignedSum a b n =
        ∑ φ : EdgeRootContext n a → ZMod n → F2,
          if edgeContextSummedConstraint a n φ = 0 then K else 0 := by
      unfold edgeNormalCoreSignedSum edgeNormalCorePhase K
      refine Finset.sum_congr rfl ?_
      intro φ _
      exact sum_bitSign_diagCoeff_dotLinear
        (b := b) (n := n) hb (edgeContextSummedConstraint a n φ)
    _ =
        (Fintype.card
          { φ : EdgeRootContext n a → ZMod n → F2 //
            edgeContextSummedConstraint a n φ = 0 } : ℤ) * K := by
      rw [← Finset.sum_filter]
      simpa [Fintype.card_subtype, K]
    _ =
        (Nat.card
          (↥(LinearMap.ker (edgeContextSummedConstraint a n))) : ℤ) *
          (2 : ℤ) ^ (n ^ b) := by
      rw [card_edgeConstraint_zero_subtype a n]
    _ = (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
      rw [mul_comm]
      exact edgeRootConstraintBlocks_closed (b := b) (n := n) ha

theorem signedSum_edge_eq_core_of_totalPhase
    (n a b : Nat) [NeZero n]
    (hphase :
      ∀ (α : (Fin b → ZMod n) → F2)
        (φ : EdgeRootContext n a → ZMod n → F2),
        RawNormal.totalPhase (RTree.node a [RTree.node b []])
          ((edgeNormalAssignmentCoreEquiv n a b).symm (α, φ)) =
            edgeNormalCorePhase a b n α φ) :
    RawNormal.signedSum n (RTree.node a [RTree.node b []]) =
      edgeNormalCoreSignedSum a b n := by
  classical
  rw [signedSum_edge_reindex_core]
  unfold RawNormal.weight edgeNormalCoreSignedSum
  rw [Fintype.sum_prod_type_right]
  congr with φ
  congr with α
  rw [hphase α φ]

theorem signedSum_edge_eq_core
    (n a b : Nat) [NeZero n] :
    RawNormal.signedSum n (RTree.node a [RTree.node b []]) =
      edgeNormalCoreSignedSum a b n := by
  exact signedSum_edge_eq_core_of_totalPhase n a b
    (fun α φ => totalPhase_edge_eq_core n a b α φ)

theorem signedSum_edge_closed_of_totalPhase
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b)
    (hphase :
      ∀ (α : (Fin b → ZMod n) → F2)
        (φ : EdgeRootContext n a → ZMod n → F2),
        RawNormal.totalPhase (RTree.node a [RTree.node b []])
          ((edgeNormalAssignmentCoreEquiv n a b).symm (α, φ)) =
            edgeNormalCorePhase a b n α φ) :
    RawNormal.signedSum n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  rw [signedSum_edge_eq_core_of_totalPhase n a b hphase]
  exact edgeNormalCoreSignedSum_closed ha hb

theorem signedSum_edge_closed
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    RawNormal.signedSum n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  rw [signedSum_edge_eq_core n a b]
  exact edgeNormalCoreSignedSum_closed ha hb

theorem DeltaTreeModel_edge_closed
    {a b n : Nat} [NeZero n] (ha : 0 < a) (_hb : 0 < b) :
    DeltaTreeModel n (RTree.node a [RTree.node b []]) =
      (2 : ℤ) ^ (n ^ a + n ^ b - (n - 1)) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hna : n ≤ n ^ a := by
    simpa using le_self_pow hn (Nat.ne_of_gt ha)
  have hle : n - 1 ≤ n ^ a + n ^ b := by omega
  have hX :
      Xassign n (RTree.node a [RTree.node b []]) =
        (n : ℤ) ^ a + (n : ℤ) ^ b - ((n : ℤ) - 1) := by
    simp [Xassign, Xpoly, Ypoly, childContribSum, RTree.totalWeight, nZ, tZ]
    ring_nf
  have hcast :
      ((n ^ a + n ^ b - (n - 1) : Nat) : ℤ) =
        (n : ℤ) ^ a + (n : ℤ) ^ b - ((n : ℤ) - 1) := by
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_sub hn]
    ring
  unfold DeltaTreeModel
  rw [hX, ← hcast]
  simp

theorem signedSum_edge_eq_DeltaTreeModel
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    RawNormal.signedSum n (RTree.node a [RTree.node b []]) =
      DeltaTreeModel n (RTree.node a [RTree.node b []]) := by
  rw [signedSum_edge_closed ha hb, DeltaTreeModel_edge_closed ha hb]

noncomputable instance normalFormRawAssignmentsFintype
    (n : Nat) [NeZero n] (T : RTree) :
    Fintype (NormalFormRawAssignments n T) := by
  classical
  infer_instance

noncomputable def normalToRaw {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) : RawAssignment n T where
  ket := fun v site => ketAtVertex A site v
  bra := fun v site => braAtVertex A site v

noncomputable def siteForNonRootDomain {n : Nat} [NeZero n] {T : RTree}
    (hpos : ∀ v : NonRootVertex T, 0 < NonRootVertex.weight v)
    (v : NonRootVertex T) (dom : NonRootFieldDomain n T v) :
    NormalSite n T where
  rootCoord := dom.rootCoord
  nonRootCoord := fun u =>
    if huv : u = v then
      by
        subst u
        exact fiberRep (NonRootVertex.weight v) n (hpos v) dom.diagonal
    else
      by
        have haddr : u.1.1 ≠ v.1.1 := by
          intro haddr
          apply huv
          apply Subtype.ext
          apply Subtype.ext
          exact haddr
        exact dom.otherCoord ⟨u, haddr⟩

theorem nonRootDomainOfSite_siteForNonRootDomain {n : Nat} [NeZero n]
    {T : RTree}
    (hpos : ∀ v : NonRootVertex T, 0 < NonRootVertex.weight v)
    (v : NonRootVertex T) (dom : NonRootFieldDomain n T v) :
    nonRootDomainOfSite (siteForNonRootDomain hpos v dom) v 0 = dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      simp [nonRootDomainOfSite, RawNormal.diagonal, siteForNonRootDomain]
      constructor
      · simpa [diagSum] using
          (diagSum_fiberRep (a := NonRootVertex.weight v) (n := n)
            (hpos v) diagonal)
      · funext u j
        have hne : u.1 ≠ v := by
          intro huv
          exact u.2 (by rw [huv])
        simp [hne]

theorem normalToRaw_realized {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) :
    RealizedByNormal T (normalToRaw A) := by
  exact ⟨A, rfl, rfl⟩

noncomputable def normalToNormalFormRaw {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) : NormalFormRawAssignments n T :=
  ⟨normalToRaw A, normalToRaw_realized A⟩

theorem normalToNormalFormRaw_surjective {n : Nat} [NeZero n] {T : RTree} :
    Function.Surjective
      (normalToNormalFormRaw : NormalAssignment n T → NormalFormRawAssignments n T) := by
  intro B
  rcases B with ⟨Araw, hreal⟩
  rcases hreal with ⟨A, hket, hbra⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  cases Araw with
  | mk ket bra =>
      change normalToRaw A = RawAssignment.mk ket bra
      change ket = (fun v site => ketAtVertex A site v) at hket
      change bra = (fun v site => braAtVertex A site v) at hbra
      cases hket
      cases hbra
      rfl

theorem normalToRaw_injective_of_positive_weight {n : Nat} [NeZero n]
    {T : RTree}
    (hpos : ∀ v : NonRootVertex T, 0 < NonRootVertex.weight v) :
    Function.Injective (normalToRaw : NormalAssignment n T → RawAssignment n T) := by
  intro A B hraw
  cases A with
  | mk Aroot Anode =>
      cases B with
      | mk Broot Bnode =>
          congr
          · funext rd
            let site : NormalSite n T :=
              { rootCoord := fun _ => 0, nonRootCoord := rd }
            have hket :=
              congrArg
                (fun R : RawAssignment n T => R.ket (Vertex.root T) site)
                hraw
            simpa [normalToRaw] using hket
          · funext v dom
            let site := siteForNonRootDomain hpos v dom
            have hket :=
              congrArg (fun R : RawAssignment n T => R.ket v.1 site) hraw
            have hdom :
                nonRootDomainOfSite site v 0 = dom :=
              nonRootDomainOfSite_siteForNonRootDomain hpos v dom
            simpa [normalToRaw, ketAtVertex, v.2, hdom] using hket

theorem normalToRaw_injective_of_positiveWeights {n : Nat} [NeZero n]
    {T : RTree} (hT : RTree.PositiveWeights T) :
    Function.Injective (normalToRaw : NormalAssignment n T → RawAssignment n T) :=
  normalToRaw_injective_of_positive_weight (fun v => by
    simpa [NonRootVertex.weight, Vertex.weight] using
      (RTree.weightAt_positive_of_mem_addresses hT v.1.2))

theorem normalToNormalFormRaw_injective_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    Function.Injective
      (normalToNormalFormRaw : NormalAssignment n T → NormalFormRawAssignments n T) := by
  intro A B hAB
  apply normalToRaw_injective_of_positiveWeights hT
  exact congrArg Subtype.val hAB

theorem normalToNormalFormRaw_bijective_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    Function.Bijective
      (normalToNormalFormRaw : NormalAssignment n T → NormalFormRawAssignments n T) :=
  ⟨normalToNormalFormRaw_injective_of_positiveWeights hT,
    normalToNormalFormRaw_surjective⟩

noncomputable def normalEquivNormalFormRawOfPositiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    NormalAssignment n T ≃ NormalFormRawAssignments n T :=
  Equiv.ofBijective normalToNormalFormRaw
    (normalToNormalFormRaw_bijective_of_positiveWeights hT)

theorem card_normalFormRawAssignments_eq_of_positiveWeights
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    Fintype.card (NormalFormRawAssignments n T)
      = Fintype.card (NormalAssignment n T) := by
  classical
  exact Fintype.card_congr
    (normalEquivNormalFormRawOfPositiveWeights (n := n) hT).symm

theorem localEdgePhase_normalToRaw {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignment n T) (site : NormalSite n T)
    (e : List Nat × List Nat) :
    localEdgePhase (normalToRaw A) site e =
      edgePhaseAtSite A site e := by
  simp [localEdgePhase, normalToRaw, edgePhaseAtSite, ketAtPath, braAtPath]

theorem phaseAtSite_normalToRaw {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignment n T) (site : NormalSite n T) :
    phaseAtSite T (normalToRaw A) site = RawNormal.phaseAtSite T A site := by
  unfold phaseAtSite RawNormal.phaseAtSite
  induction RTree.edgeList T with
  | nil =>
      simp
  | cons e es ih =>
      simp [localEdgePhase_normalToRaw, ih]

theorem totalPhase_normalToRaw {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignment n T) :
    totalPhase T (normalToRaw A) = RawNormal.totalPhase T A := by
  unfold totalPhase RawNormal.totalPhase
  refine Finset.sum_congr rfl ?_
  intro site _
  exact phaseAtSite_normalToRaw T A site

theorem weight_normalToRaw {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignment n T) :
    weight T (normalToRaw A) = RawNormal.weight T A := by
  simp [weight, RawNormal.weight, totalPhase_normalToRaw]

noncomputable def normalFormSignedSum (n : Nat) [NeZero n] (T : RTree) : ℤ :=
  ∑ Araw : NormalFormRawAssignments n T, weight T Araw.1

noncomputable def rawBitStringSignedSum (n : Nat) [NeZero n] (T : RTree) : ℤ :=
  ∑ Araw : NormalFormRawAssignments n T, weight T Araw.1

theorem rawBitStringSignedSum_eq_normalFormSignedSum
    (n : Nat) [NeZero n] (T : RTree) :
    rawBitStringSignedSum n T = normalFormSignedSum n T := rfl

theorem normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    normalFormSignedSum n T = RawNormal.signedSum n T := by
  classical
  have hsum :
      (∑ A : NormalAssignment n T, RawNormal.weight T A) =
        ∑ Araw : NormalFormRawAssignments n T, weight T Araw.1 := by
    refine Fintype.sum_equiv
      (normalEquivNormalFormRawOfPositiveWeights (n := n) hT)
      (fun A : NormalAssignment n T => RawNormal.weight T A)
      (fun Araw : NormalFormRawAssignments n T => weight T Araw.1)
      ?_
    intro A
    simpa [normalEquivNormalFormRawOfPositiveWeights, normalToNormalFormRaw]
      using (weight_normalToRaw T A).symm
  simpa [normalFormSignedSum, RawNormal.signedSum] using hsum.symm

theorem normalFormSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (hmodel : RawNormal.signedSum n T = DeltaTreeModel n T) :
    normalFormSignedSum n T = DeltaTreeModel n T := by
  rw [normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  exact hmodel

theorem normalFormSignedSum_closed_Xpoly_of_signedSum_eq
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (hmodel : RawNormal.signedSum n T = DeltaTreeModel n T) :
    normalFormSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  rw [normalFormSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := T) hT hmodel]
  exact DeltaTreeModel_closed_Xpoly n T

theorem normalFormSignedSum_closed_connected_terms_of_signedSum_eq
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (hmodel : RawNormal.signedSum n T = DeltaTreeModel n T) :
    normalFormSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  rw [normalFormSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := T) hT hmodel]
  exact DeltaTreeModel_closed n T

theorem rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    rawBitStringSignedSum n T = RawNormal.signedSum n T := by
  change normalFormSignedSum n T = RawNormal.signedSum n T
  exact normalFormSignedSum_eq_signedSum_of_positiveWeights (n := n) (T := T) hT

theorem rawBitStringSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (hmodel : RawNormal.signedSum n T = DeltaTreeModel n T) :
    rawBitStringSignedSum n T = DeltaTreeModel n T := by
  change normalFormSignedSum n T = DeltaTreeModel n T
  exact normalFormSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := T) hT hmodel

theorem rawBitStringSignedSum_closed_Xpoly_of_signedSum_eq
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (hmodel : RawNormal.signedSum n T = DeltaTreeModel n T) :
    rawBitStringSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T) := by
  change normalFormSignedSum n T = (2 : ℤ) ^ Int.toNat (Xpoly n T)
  exact normalFormSignedSum_closed_Xpoly_of_signedSum_eq
    (n := n) (T := T) hT hmodel

theorem rawBitStringSignedSum_closed_connected_terms_of_signedSum_eq
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (hmodel : RawNormal.signedSum n T = DeltaTreeModel n T) :
    rawBitStringSignedSum n T =
      (2 : ℤ) ^ Int.toNat (termSum n (allTerms T)) := by
  change normalFormSignedSum n T =
    (2 : ℤ) ^ Int.toNat (termSum n (allTerms T))
  exact normalFormSignedSum_closed_connected_terms_of_signedSum_eq
    (n := n) (T := T) hT hmodel

theorem normalFormSignedSum_leaf_eq_DeltaTreeModel
    (n a : Nat) [NeZero n] (ha : 0 < a) :
    normalFormSignedSum n (RTree.node a []) =
      DeltaTreeModel n (RTree.node a []) := by
  rw [normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := RTree.node a [])
    (hT := by simpa [RTree.PositiveWeights] using ha)]
  exact RawNormal.signedSum_leaf_eq_DeltaTreeModel n a

theorem normalFormSignedSum_edge_eq_DeltaTreeModel
    {a b n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) :
    normalFormSignedSum n (RTree.node a [RTree.node b []]) =
      DeltaTreeModel n (RTree.node a [RTree.node b []]) := by
  rw [normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := RTree.node a [RTree.node b []])
    (hT := by
      simp [RTree.PositiveWeights, ha, hb])]
  exact signedSum_edge_eq_DeltaTreeModel ha hb

end RawPrimitive

end TreeGraph
