import TreeGraph.RawPrimitive
import Core3tree

namespace TreeGraph

namespace RawPrimitive

open RawNormal RawLinearAlgebra

abbrev StarTree (a b c : Nat) : RTree :=
  RTree.node a [RTree.node b [], RTree.node c []]

def starLeftVertex (a b c : Nat) : Vertex (StarTree a b c) :=
  ⟨[0], by
    rw [StarTree, RTree.addresses_node_two_leaf]
    simp⟩

def starRightVertex (a b c : Nat) : Vertex (StarTree a b c) :=
  ⟨[1], by
    rw [StarTree, RTree.addresses_node_two_leaf]
    simp⟩

def starLeftNonRootVertex (a b c : Nat) :
    NonRootVertex (StarTree a b c) :=
  ⟨starLeftVertex a b c, by simp [starLeftVertex]⟩

def starRightNonRootVertex (a b c : Nat) :
    NonRootVertex (StarTree a b c) :=
  ⟨starRightVertex a b c, by simp [starRightVertex]⟩

@[simp] theorem starLeftNonRootVertex_weight (a b c : Nat) :
    NonRootVertex.weight (starLeftNonRootVertex a b c) = b := by
  rfl

@[simp] theorem starRightNonRootVertex_weight (a b c : Nat) :
    NonRootVertex.weight (starRightNonRootVertex a b c) = c := by
  rfl

@[simp] theorem starLeftNonRootVertex_mk (a b c : Nat)
    (haddr : ([0] : List Nat) ∈ RTree.addresses (StarTree a b c))
    (hnot : ([0] : List Nat) ≠ []) :
    (⟨⟨[0], haddr⟩, hnot⟩ : NonRootVertex (StarTree a b c)) =
      starLeftNonRootVertex a b c := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp] theorem starRightNonRootVertex_mk (a b c : Nat)
    (haddr : ([1] : List Nat) ∈ RTree.addresses (StarTree a b c))
    (hnot : ([1] : List Nat) ≠ []) :
    (⟨⟨[1], haddr⟩, hnot⟩ : NonRootVertex (StarTree a b c)) =
      starRightNonRootVertex a b c := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

@[simp] theorem starLeftNonRootVertex_ne_right (a b c : Nat) :
    starLeftNonRootVertex a b c ≠ starRightNonRootVertex a b c := by
  intro h
  have haddr := congrArg
    (fun v : NonRootVertex (StarTree a b c) => v.1.1) h
  simp [starLeftNonRootVertex, starRightNonRootVertex,
    starLeftVertex, starRightVertex] at haddr

@[simp] theorem starRightNonRootVertex_ne_left (a b c : Nat) :
    starRightNonRootVertex a b c ≠ starLeftNonRootVertex a b c := by
  intro h
  exact starLeftNonRootVertex_ne_right a b c h.symm

theorem nonRootVertex_star_eq_left_or_right {a b c : Nat}
    (v : NonRootVertex (StarTree a b c)) :
    v = starLeftNonRootVertex a b c ∨
      v = starRightNonRootVertex a b c := by
  apply Or.imp
    (fun h => by
      apply Subtype.ext
      apply Subtype.ext
      exact h)
    (fun h => by
      apply Subtype.ext
      apply Subtype.ext
      exact h)
  have haddr : v.1.1 ∈ [[], [0], [1]] := by
    let p : List Nat := v.1.1
    have hv : p ∈ RTree.addresses (StarTree a b c) := v.1.2
    rw [StarTree, RTree.addresses_node_two_leaf] at hv
    simpa [p] using hv
  rcases List.mem_cons.mp haddr with hroot | htail
  · exact False.elim (v.2 hroot)
  · rcases List.mem_cons.mp htail with hleft | htail'
    · exact Or.inl hleft
    · exact Or.inr (by simpa using htail')

def starRightOtherOfLeft (a b c : Nat) :
    OtherNonRootVertex (StarTree a b c) (starLeftNonRootVertex a b c) :=
  ⟨starRightNonRootVertex a b c, by
    simp [starLeftNonRootVertex, starRightNonRootVertex,
      starLeftVertex, starRightVertex]⟩

def starLeftOtherOfRight (a b c : Nat) :
    OtherNonRootVertex (StarTree a b c) (starRightNonRootVertex a b c) :=
  ⟨starLeftNonRootVertex a b c, by
    simp [starLeftNonRootVertex, starRightNonRootVertex,
      starLeftVertex, starRightVertex]⟩

@[simp] theorem starRightOtherOfLeft_val (a b c : Nat) :
    (starRightOtherOfLeft a b c).1 = starRightNonRootVertex a b c := by
  rfl

@[simp] theorem starLeftOtherOfRight_val (a b c : Nat) :
    (starLeftOtherOfRight a b c).1 = starLeftNonRootVertex a b c := by
  rfl

theorem otherNonRootVertex_star_left_eq_right {a b c : Nat}
    (u : OtherNonRootVertex (StarTree a b c)
      (starLeftNonRootVertex a b c)) :
    u.1 = starRightNonRootVertex a b c := by
  rcases nonRootVertex_star_eq_left_or_right u.1 with hleft | hright
  · exact False.elim (u.2 (congrArg (fun v : NonRootVertex (StarTree a b c) => v.1.1) hleft))
  · exact hright

theorem otherNonRootVertex_star_right_eq_left {a b c : Nat}
    (u : OtherNonRootVertex (StarTree a b c)
      (starRightNonRootVertex a b c)) :
    u.1 = starLeftNonRootVertex a b c := by
  rcases nonRootVertex_star_eq_left_or_right u.1 with hleft | hright
  · exact hleft
  · exact False.elim (u.2 (congrArg (fun v : NonRootVertex (StarTree a b c) => v.1.1) hright))

theorem otherNonRootVertex_star_left_eq_rightOther {a b c : Nat}
    (u : OtherNonRootVertex (StarTree a b c)
      (starLeftNonRootVertex a b c)) :
    u = starRightOtherOfLeft a b c := by
  apply Subtype.ext
  exact otherNonRootVertex_star_left_eq_right u

theorem otherNonRootVertex_star_right_eq_leftOther {a b c : Nat}
    (u : OtherNonRootVertex (StarTree a b c)
      (starRightNonRootVertex a b c)) :
    u = starLeftOtherOfRight a b c := by
  apply Subtype.ext
  exact otherNonRootVertex_star_right_eq_left u

noncomputable def starRootFieldDomainEquiv
    (n a b c : Nat) [NeZero n] :
    RootFieldDomain n (StarTree a b c) ≃
      No13Migration.ASiteABC b c n where
  toFun rd :=
    ⟨fun j => rd (starLeftNonRootVertex a b c) j,
      fun j => rd (starRightNonRootVertex a b c) j⟩
  invFun yz := fun v j => by
    if hleft : v = starLeftNonRootVertex a b c then
      subst v
      exact yz.1 j
    else
      have hright : v = starRightNonRootVertex a b c := by
        rcases nonRootVertex_star_eq_left_or_right v with h | h
        · exact False.elim (hleft h)
        · exact h
      subst v
      exact yz.2 j
  left_inv rd := by
    funext v j
    rcases nonRootVertex_star_eq_left_or_right v with hleft | hright
    · subst v
      rfl
    · subst v
      rfl
  right_inv yz := by
    rcases yz with ⟨y, z⟩
    apply Prod.ext
    · funext j
      rfl
    · funext j
      rfl

noncomputable def starLeftFieldDomain
    (n a b c : Nat) [NeZero n]
    (x : No13Migration.XCoord a n) (t : ZMod n)
    (z : No13Migration.ZCoord c n) :
    NonRootFieldDomain n (StarTree a b c)
      (starLeftNonRootVertex a b c) where
  rootCoord := x
  diagonal := t
  otherCoord := fun u => by
    have hu : u = starRightOtherOfLeft a b c :=
      otherNonRootVertex_star_left_eq_rightOther u
    subst u
    exact z

noncomputable def starRightFieldDomain
    (n a b c : Nat) [NeZero n]
    (x : No13Migration.XCoord a n)
    (y : No13Migration.YCoord b n) (t : ZMod n) :
    NonRootFieldDomain n (StarTree a b c)
      (starRightNonRootVertex a b c) where
  rootCoord := x
  diagonal := t
  otherCoord := fun u => by
    have hu : u = starLeftOtherOfRight a b c :=
      otherNonRootVertex_star_right_eq_leftOther u
    subst u
    exact y

theorem starLeftFieldDomain_eta
    (n a b c : Nat) [NeZero n]
    (dom : NonRootFieldDomain n (StarTree a b c)
      (starLeftNonRootVertex a b c)) :
    starLeftFieldDomain n a b c dom.rootCoord dom.diagonal
        (fun j => dom.otherCoord (starRightOtherOfLeft a b c) j) =
      dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      simp [starLeftFieldDomain]
      funext u j
      have hu : u = starRightOtherOfLeft a b c :=
        otherNonRootVertex_star_left_eq_rightOther u
      subst u
      rfl

theorem starRightFieldDomain_eta
    (n a b c : Nat) [NeZero n]
    (dom : NonRootFieldDomain n (StarTree a b c)
      (starRightNonRootVertex a b c)) :
    starRightFieldDomain n a b c dom.rootCoord
        (fun j => dom.otherCoord (starLeftOtherOfRight a b c) j)
        dom.diagonal =
      dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      simp [starRightFieldDomain]
      funext u j
      have hu : u = starLeftOtherOfRight a b c :=
        otherNonRootVertex_star_right_eq_leftOther u
      subst u
      rfl

noncomputable def starNormalAssignmentABCEq
    (n a b c : Nat) [NeZero n] :
    NormalAssignment n (StarTree a b c) ≃
      No13Migration.ABCAssignment a b c n where
  toFun A :=
    ⟨fun yz =>
        A.rootField ((starRootFieldDomainEquiv n a b c).symm yz),
      (fun bs =>
        A.nodeField (starLeftNonRootVertex a b c)
          (starLeftFieldDomain n a b c bs.1 bs.2.1 bs.2.2),
      fun cs =>
        A.nodeField (starRightNonRootVertex a b c)
          (starRightFieldDomain n a b c cs.1 cs.2.1 cs.2.2))⟩
  invFun P :=
    { rootField := fun rd => P.1 ((starRootFieldDomainEquiv n a b c) rd)
      nodeField := fun v dom => by
        if hv : v = starLeftNonRootVertex a b c then
          subst v
          exact P.2.1
            (dom.rootCoord, dom.diagonal,
              fun j => dom.otherCoord (starRightOtherOfLeft a b c) j)
        else
          have hright : v = starRightNonRootVertex a b c := by
            rcases nonRootVertex_star_eq_left_or_right v with h | h
            · exact False.elim (hv h)
            · exact h
          subst v
          exact P.2.2
            (dom.rootCoord,
              fun j => dom.otherCoord (starLeftOtherOfRight a b c) j,
              dom.diagonal) }
  left_inv A := by
    cases A with
    | mk rootField nodeField =>
        rw [NormalAssignment.mk.injEq]
        constructor
        · funext rd
          change
            rootField
                ((starRootFieldDomainEquiv n a b c).symm
                  ((starRootFieldDomainEquiv n a b c) rd)) =
              rootField rd
          exact congrArg rootField
            ((starRootFieldDomainEquiv n a b c).left_inv rd)
        · funext v dom
          rcases nonRootVertex_star_eq_left_or_right v with hleft | hright
          · subst v
            change
              nodeField (starLeftNonRootVertex a b c)
                  (starLeftFieldDomain n a b c
                    dom.rootCoord dom.diagonal
                    (fun j =>
                      dom.otherCoord (starRightOtherOfLeft a b c) j)) =
                nodeField (starLeftNonRootVertex a b c) dom
            rw [starLeftFieldDomain_eta n a b c dom]
          · subst v
            change
              nodeField (starRightNonRootVertex a b c)
                  (starRightFieldDomain n a b c
                    dom.rootCoord
                    (fun j =>
                      dom.otherCoord (starLeftOtherOfRight a b c) j)
                    dom.diagonal) =
                nodeField (starRightNonRootVertex a b c) dom
            rw [starRightFieldDomain_eta n a b c dom]
  right_inv P := by
    rcases P with ⟨A, B, C⟩
    apply Prod.ext
    · funext yz
      change
        A ((starRootFieldDomainEquiv n a b c)
          ((starRootFieldDomainEquiv n a b c).symm yz)) = A yz
      exact congrArg A
        ((starRootFieldDomainEquiv n a b c).right_inv yz)
    · apply Prod.ext
      · funext bs
        rfl
      · funext cs
        rfl

noncomputable def starNormalSiteABCEquiv
    (n a b c : Nat) [NeZero n] :
    NormalSite n (StarTree a b c) ≃
      No13Migration.RawSiteABC a b c n where
  toFun site :=
    ⟨site.rootCoord,
      (starRootFieldDomainEquiv n a b c site.nonRootCoord).1,
      (starRootFieldDomainEquiv n a b c site.nonRootCoord).2⟩
  invFun xyz :=
    { rootCoord := xyz.1
      nonRootCoord :=
        (starRootFieldDomainEquiv n a b c).symm
          ⟨xyz.2.1, xyz.2.2⟩ }
  left_inv site := by
    cases site with
    | mk rootCoord nonRootCoord =>
        simp
  right_inv xyz := by
    rcases xyz with ⟨x, y, z⟩
    simp

theorem phaseAtSite_star_abc
    (n a b c : Nat) [NeZero n]
    (nf : No13Migration.ABCAssignment a b c n)
    (xyz : No13Migration.RawSiteABC a b c n) :
    RawNormal.phaseAtSite (StarTree a b c)
      ((starNormalAssignmentABCEq n a b c).symm nf)
      ((starNormalSiteABCEquiv n a b c).symm xyz) =
        No13Migration.rawLocalPhaseBitABC
          (a := a) (b := b) (c := c) (n := n)
          (No13Migration.toRawAssignmentABC nf) xyz := by
  classical
  rcases nf with ⟨A, B, C⟩
  rcases xyz with ⟨x, y, z⟩
  let A0 : NormalAssignment n (StarTree a b c) :=
    (starNormalAssignmentABCEq n a b c).symm (A, B, C)
  let site : NormalSite n (StarTree a b c) :=
    (starNormalSiteABCEquiv n a b c).symm (x, y, z)
  change RawNormal.phaseAtSite (StarTree a b c) A0 site =
    No13Migration.rawLocalPhaseBitABC
      (a := a) (b := b) (c := c) (n := n)
      (No13Migration.toRawAssignmentABC (A, B, C)) (x, y, z)
  have hroot :
      ([] : List Nat) ∈ RTree.addresses (StarTree a b c) := by
    rw [StarTree, RTree.addresses_node_two_leaf]
    simp
  have hleft :
      ([0] : List Nat) ∈ RTree.addresses (StarTree a b c) := by
    rw [StarTree, RTree.addresses_node_two_leaf]
    simp
  have hright :
      ([1] : List Nat) ∈ RTree.addresses (StarTree a b c) := by
    rw [StarTree, RTree.addresses_node_two_leaf]
    simp
  have hleftNot : ([0] : List Nat) ≠ [] := by
    simp
  have hrightNot : ([1] : List Nat) ≠ [] := by
    simp
  have hleftVertex :
      (⟨⟨([0] : List Nat), hleft⟩, hleftNot⟩ :
          NonRootVertex (StarTree a b c)) =
        starLeftNonRootVertex a b c :=
    starLeftNonRootVertex_mk a b c hleft hleftNot
  have hrightVertex :
      (⟨⟨([1] : List Nat), hright⟩, hrightNot⟩ :
          NonRootVertex (StarTree a b c)) =
        starRightNonRootVertex a b c :=
    starRightNonRootVertex_mk a b c hright hrightNot
  have hketRoot : RawNormal.ketAtPath A0 site [] = A (y, z) := by
    unfold RawNormal.ketAtPath
    rw [dif_pos hroot]
    simp [RawNormal.ketAtVertex, A0, site, starNormalAssignmentABCEq,
      starNormalSiteABCEquiv, starRootFieldDomainEquiv]
  have hbraRoot : RawNormal.braAtPath A0 site [] = A (y, z) := by
    unfold RawNormal.braAtPath
    rw [dif_pos hroot]
    simp [RawNormal.braAtVertex, A0, site, starNormalAssignmentABCEq,
      starNormalSiteABCEquiv, starRootFieldDomainEquiv]
  have hketLeft :
      RawNormal.ketAtPath A0 site [0] =
        B (x, No13Migration.sumY y, z) := by
    unfold RawNormal.ketAtPath
    rw [dif_pos hleft]
    unfold RawNormal.ketAtVertex
    rw [dif_neg hleftNot]
    rw [hleftVertex]
    simp [RawNormal.nonRootDomainOfSite,
      RawNormal.diagonal, A0, site, starNormalAssignmentABCEq,
      starNormalSiteABCEquiv, starRootFieldDomainEquiv,
      starLeftFieldDomain, starRightFieldDomain,
      No13Migration.sumY, No13Migration.sumCoord]
    rfl
  have hbraLeft :
      RawNormal.braAtPath A0 site [0] =
        B (x, No13Migration.sumY y + 1, z) := by
    unfold RawNormal.braAtPath
    rw [dif_pos hleft]
    unfold RawNormal.braAtVertex
    rw [dif_neg hleftNot]
    rw [hleftVertex]
    simp [RawNormal.nonRootDomainOfSite,
      RawNormal.diagonal, A0, site, starNormalAssignmentABCEq,
      starNormalSiteABCEquiv, starRootFieldDomainEquiv,
      starLeftFieldDomain, starRightFieldDomain,
      No13Migration.sumY, No13Migration.sumCoord]
    rfl
  have hketRight :
      RawNormal.ketAtPath A0 site [1] =
        C (x, y, No13Migration.sumZ z) := by
    unfold RawNormal.ketAtPath
    rw [dif_pos hright]
    unfold RawNormal.ketAtVertex
    rw [dif_neg hrightNot]
    rw [hrightVertex]
    simp [RawNormal.nonRootDomainOfSite,
      RawNormal.diagonal, A0, site, starNormalAssignmentABCEq,
      starNormalSiteABCEquiv, starRootFieldDomainEquiv,
      starLeftFieldDomain, starRightFieldDomain,
      No13Migration.sumZ, No13Migration.sumCoord]
    rfl
  have hbraRight :
      RawNormal.braAtPath A0 site [1] =
        C (x, y, No13Migration.sumZ z + 1) := by
    unfold RawNormal.braAtPath
    rw [dif_pos hright]
    unfold RawNormal.braAtVertex
    rw [dif_neg hrightNot]
    rw [hrightVertex]
    simp [RawNormal.nonRootDomainOfSite,
      RawNormal.diagonal, A0, site, starNormalAssignmentABCEq,
      starNormalSiteABCEquiv, starRootFieldDomainEquiv,
      starLeftFieldDomain, starRightFieldDomain,
      No13Migration.sumZ, No13Migration.sumCoord]
    rfl
  simp [StarTree, RawNormal.phaseAtSite, RawNormal.edgePhaseAtSite,
    hketRoot, hbraRoot, hketLeft, hbraLeft, hketRight, hbraRight,
    No13Migration.rawLocalPhaseBitABC, No13Migration.toRawAssignmentABC,
    mul_add, add_assoc, add_left_comm, add_comm]

theorem totalPhase_star_abc
    (n a b c : Nat) [NeZero n]
    (nf : No13Migration.ABCAssignment a b c n) :
    RawNormal.totalPhase (StarTree a b c)
      ((starNormalAssignmentABCEq n a b c).symm nf) =
        ∑ xyz : No13Migration.RawSiteABC a b c n,
          No13Migration.rawLocalPhaseBitABC
            (a := a) (b := b) (c := c) (n := n)
            (No13Migration.toRawAssignmentABC nf) xyz := by
  classical
  let A0 : NormalAssignment n (StarTree a b c) :=
    (starNormalAssignmentABCEq n a b c).symm nf
  calc
    RawNormal.totalPhase (StarTree a b c) A0 =
        ∑ xyz : No13Migration.RawSiteABC a b c n,
          RawNormal.phaseAtSite (StarTree a b c) A0
            ((starNormalSiteABCEquiv n a b c).symm xyz) := by
      unfold RawNormal.totalPhase
      refine Fintype.sum_equiv
        (starNormalSiteABCEquiv n a b c)
        (fun site : NormalSite n (StarTree a b c) =>
          RawNormal.phaseAtSite (StarTree a b c) A0 site)
        (fun xyz : No13Migration.RawSiteABC a b c n =>
          RawNormal.phaseAtSite (StarTree a b c) A0
            ((starNormalSiteABCEquiv n a b c).symm xyz))
        ?_
      intro site
      change
        RawNormal.phaseAtSite (StarTree a b c) A0 site =
          RawNormal.phaseAtSite (StarTree a b c) A0
            ((starNormalSiteABCEquiv n a b c).symm
              ((starNormalSiteABCEquiv n a b c) site))
      exact congrArg
        (RawNormal.phaseAtSite (StarTree a b c) A0)
        ((starNormalSiteABCEquiv n a b c).left_inv site).symm
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro xyz _
      exact phaseAtSite_star_abc n a b c nf xyz

theorem weight_star_abc
    (n a b c : Nat) [NeZero n]
    (nf : No13Migration.ABCAssignment a b c n) :
    RawNormal.weight (StarTree a b c)
      ((starNormalAssignmentABCEq n a b c).symm nf) =
      No13Migration.W_abc_real (a := a) (b := b) (c := c) (n := n) nf := by
  classical
  unfold RawNormal.weight
  rw [totalPhase_star_abc]
  let localPhase : No13Migration.RawSiteABC a b c n → F2 :=
    fun xyz : No13Migration.RawSiteABC a b c n =>
      No13Migration.rawLocalPhaseBitABC
        (a := a) (b := b) (c := c) (n := n)
        (No13Migration.toRawAssignmentABC nf) xyz
  change TreeGraph.bitSign
      (∑ xyz : No13Migration.RawSiteABC a b c n, localPhase xyz) =
    No13Migration.W_abc_real (a := a) (b := b) (c := c) (n := n) nf
  have hprod :=
    No13Migration.prod_bitSign_eq_bitSign_sum
      (Finset.univ : Finset (No13Migration.RawSiteABC a b c n)) localPhase
  calc
    TreeGraph.bitSign
        (∑ xyz : No13Migration.RawSiteABC a b c n, localPhase xyz) =
        No13Migration.bitSign
        (∑ xyz : No13Migration.RawSiteABC a b c n, localPhase xyz) := by
      simp [TreeGraph.bitSign, No13Migration.bitSign]
    _ =
        ∏ xyz : No13Migration.RawSiteABC a b c n,
          No13Migration.bitSign (localPhase xyz) := by
      exact hprod.symm
    _ =
        No13Migration.W_abc_raw (a := a) (b := b) (c := c) (n := n)
          (No13Migration.toRawAssignmentABC nf) := by
      rfl
    _ =
        No13Migration.W_abc_real (a := a) (b := b) (c := c) (n := n) nf := by
      exact No13Migration.W_abc_raw_toRawAssignmentABC_eq_W_abc_real
        (a := a) (b := b) (c := c) (n := n) nf

theorem signedSum_star_eq_deltaABCraw_real
    (n a b c : Nat) [NeZero n] :
    RawNormal.signedSum n (StarTree a b c) =
      No13Migration.deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
  classical
  unfold RawNormal.signedSum No13Migration.deltaABCraw_real
  refine Fintype.sum_equiv
    (starNormalAssignmentABCEq n a b c)
    (fun A : NormalAssignment n (StarTree a b c) =>
      RawNormal.weight (StarTree a b c) A)
    (fun nf : No13Migration.ABCAssignment a b c n =>
      No13Migration.W_abc_real (a := a) (b := b) (c := c) (n := n) nf)
    ?_
  intro A
  change
    RawNormal.weight (StarTree a b c) A =
      No13Migration.W_abc_real (a := a) (b := b) (c := c) (n := n)
        ((starNormalAssignmentABCEq n a b c) A)
  rw [← weight_star_abc n a b c ((starNormalAssignmentABCEq n a b c) A)]
  exact congrArg (RawNormal.weight (StarTree a b c))
    ((starNormalAssignmentABCEq n a b c).left_inv A).symm

theorem signedSum_star_closed
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    RawNormal.signedSum n (StarTree a b c) =
      (2 : ℤ) ^
        (n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
          - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2) := by
  rw [signedSum_star_eq_deltaABCraw_real n a b c]
  exact No13Migration.signed_imbalance_abc_real_closed_explicit
    (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem DeltaTreeModel_star_closed
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c) :
    DeltaTreeModel n (StarTree a b c) =
      (2 : ℤ) ^
        (n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
          - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2) := by
  have hnpos : 0 < n := Nat.pos_of_neZero n
  have hn : 1 ≤ n := Nat.succ_le_of_lt hnpos
  have hc_le : c + 1 ≤ a + c := by omega
  have hb_le : b + 1 ≤ a + b := by omega
  have hpow_c : n ^ (c + 1) ≤ n ^ (a + c) :=
    Nat.pow_le_pow_right hnpos hc_le
  have hpow_b : n ^ (b + 1) ≤ n ^ (a + b) :=
    Nat.pow_le_pow_right hnpos hb_le
  let S : Nat := n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
  have hleC : n ^ (c + 1) ≤ S := by
    omega
  have hleB : n ^ (b + 1) ≤ S - n ^ (c + 1) := by
    have hboth : n ^ (c + 1) + n ^ (b + 1) ≤ S := by
      omega
    omega
  have hX :
      Xassign n (StarTree a b c) =
        (n : ℤ) ^ (a + b) + (n : ℤ) ^ (a + c) + (n : ℤ) ^ (b + c)
          - (n : ℤ) ^ (c + 1) - (n : ℤ) ^ (b + 1)
          + (n : ℤ) ^ c + (n : ℤ) ^ b + ((n : ℤ) - 1) ^ 2 := by
    simp [Xassign, Xpoly, Ypoly, childContribSum,
      RTree.totalWeight, nZ, tZ, pow_add]
    ring_nf
  have hcast :
      ((n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
          - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2 : Nat) : ℤ) =
        (n : ℤ) ^ (a + b) + (n : ℤ) ^ (a + c) + (n : ℤ) ^ (b + c)
          - (n : ℤ) ^ (c + 1) - (n : ℤ) ^ (b + 1)
          + (n : ℤ) ^ c + (n : ℤ) ^ b + ((n : ℤ) - 1) ^ 2 := by
    change
      (((S - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2 : Nat) : ℤ) =
        (n : ℤ) ^ (a + b) + (n : ℤ) ^ (a + c) + (n : ℤ) ^ (b + c)
          - (n : ℤ) ^ (c + 1) - (n : ℤ) ^ (b + 1)
          + (n : ℤ) ^ c + (n : ℤ) ^ b + ((n : ℤ) - 1) ^ 2)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add,
      Nat.cast_sub hleB, Nat.cast_sub hleC]
    simp only [S, Nat.cast_add, Nat.cast_pow, Nat.cast_sub hn]
    ring
  have htoNat :
      Int.toNat
        ((n : ℤ) ^ (a + b) + (n : ℤ) ^ (a + c) + (n : ℤ) ^ (b + c)
          - (n : ℤ) ^ (c + 1) - (n : ℤ) ^ (b + 1)
          + (n : ℤ) ^ c + (n : ℤ) ^ b + ((n : ℤ) - 1) ^ 2) =
        n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
          - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2 := by
    have h := congrArg Int.toNat hcast
    simpa using h.symm
  unfold DeltaTreeModel
  rw [hX, htoNat]

theorem signedSum_star_eq_DeltaTreeModel
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    RawNormal.signedSum n (StarTree a b c) =
      DeltaTreeModel n (StarTree a b c) := by
  rw [signedSum_star_closed ha hb hc, DeltaTreeModel_star_closed ha hb hc]

theorem normalFormSignedSum_star_eq_deltaABCraw_real
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    normalFormSignedSum n (StarTree a b c) =
      No13Migration.deltaABCraw_real (a := a) (b := b) (c := c) (n := n) := by
  rw [normalFormSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := StarTree a b c)
    (hT := by
      simp [StarTree, RTree.PositiveWeights, ha, hb, hc])]
  exact signedSum_star_eq_deltaABCraw_real n a b c

theorem normalFormSignedSum_star_closed
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    normalFormSignedSum n (StarTree a b c) =
      (2 : ℤ) ^
        (n ^ (a + b) + n ^ (a + c) + n ^ (b + c)
          - n ^ (c + 1) - n ^ (b + 1)
          + n ^ c + n ^ b + (n - 1) ^ 2) := by
  rw [normalFormSignedSum_star_eq_deltaABCraw_real
    (a := a) (b := b) (c := c) (n := n) ha hb hc]
  exact No13Migration.signed_imbalance_abc_real_closed_explicit
    (a := a) (b := b) (c := c) (n := n) ha hb hc

theorem normalFormSignedSum_star_eq_DeltaTreeModel
    {a b c n : Nat} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    normalFormSignedSum n (StarTree a b c) =
      DeltaTreeModel n (StarTree a b c) := by
  exact normalFormSignedSum_eq_DeltaTreeModel_of_signedSum_eq
    (n := n) (T := StarTree a b c)
    (hT := by
      simp [StarTree, RTree.PositiveWeights, ha, hb, hc])
    (signedSum_star_eq_DeltaTreeModel ha hb hc)

end RawPrimitive

end TreeGraph
