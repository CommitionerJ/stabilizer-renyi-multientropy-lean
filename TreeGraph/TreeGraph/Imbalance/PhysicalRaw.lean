import TreeGraph.Imbalance.PhysicalNormal

namespace TreeGraph
namespace Imbalance

structure RawAssignmentClean (n : Nat) [NeZero n] (T : RTree) where
  ket : Vertex T → NormalSiteClean n T → F2
  bra : Vertex T → NormalSiteClean n T → F2
  deriving Fintype

noncomputable def rawLocalEdgePhaseClean {n : Nat} [NeZero n] {T : RTree}
    (A : RawAssignmentClean n T) (site : NormalSiteClean n T)
    (e : List Nat × List Nat) : F2 :=
  let ketAt (p : List Nat) : F2 :=
    if hp : p ∈ RTree.addresses T then A.ket ⟨p, hp⟩ site else 0
  let braAt (p : List Nat) : F2 :=
    if hp : p ∈ RTree.addresses T then A.bra ⟨p, hp⟩ site else 0
  ketAt e.1 * ketAt e.2 + braAt e.1 * braAt e.2

noncomputable def rawPhaseAtSiteClean {n : Nat} [NeZero n] (T : RTree)
    (A : RawAssignmentClean n T) (site : NormalSiteClean n T) : F2 :=
  (RTree.edgeList T).map (rawLocalEdgePhaseClean A site) |>.sum

noncomputable def rawTotalPhaseClean {n : Nat} [NeZero n] (T : RTree)
    (A : RawAssignmentClean n T) : F2 :=
  ∑ site : NormalSiteClean n T, rawPhaseAtSiteClean T A site

noncomputable def rawWeightClean {n : Nat} [NeZero n] (T : RTree)
    (A : RawAssignmentClean n T) : ℤ :=
  chi (rawTotalPhaseClean T A)

def RealizedByNormalClean {n : Nat} [NeZero n] (T : RTree)
    (Araw : RawAssignmentClean n T) : Prop :=
  ∃ Anorm : NormalAssignmentClean n T,
    Araw.ket = (fun v site => ketAtVertexClean Anorm site v) ∧
      Araw.bra = (fun v site => braAtVertexClean Anorm site v)

abbrev NormalFormRawAssignmentsClean (n : Nat) [NeZero n] (T : RTree) :=
  { Araw : RawAssignmentClean n T // RealizedByNormalClean T Araw }

noncomputable instance normalFormRawAssignmentsCleanFintype
    (n : Nat) [NeZero n] (T : RTree) :
    Fintype (NormalFormRawAssignmentsClean n T) := by
  classical
  infer_instance

noncomputable def normalToRawClean {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) : RawAssignmentClean n T where
  ket := fun v site => ketAtVertexClean A site v
  bra := fun v site => braAtVertexClean A site v

noncomputable def diagonalWitnessClean (a n : Nat) [NeZero n]
    (ha : 0 < a) (t : Rep n) : Fin a → Rep n :=
  fun j => if j = ⟨0, ha⟩ then t else 0

@[simp] theorem diagonalWitnessClean_sum (a n : Nat) [NeZero n]
    (ha : 0 < a) (t : Rep n) :
    (∑ j : Fin a, diagonalWitnessClean a n ha t j) = t := by
  classical
  simp [diagonalWitnessClean]

noncomputable def siteForNonRootDomainClean {n : Nat} [NeZero n] {T : RTree}
    (hpos : ∀ v : NonRootVertex T, 0 < NonRootVertex.weight v)
    (v : NonRootVertex T) (dom : NonRootFieldDomainClean n T v) :
    NormalSiteClean n T where
  rootCoord := dom.rootCoord
  nonRootCoord := fun u =>
    if huv : u = v then
      by
        subst u
        exact diagonalWitnessClean (NonRootVertex.weight v) n (hpos v)
          dom.diagonal
    else
      by
        have haddr : u.1.1 ≠ v.1.1 := by
          intro haddr
          apply huv
          apply Subtype.ext
          apply Subtype.ext
          exact haddr
        exact dom.otherCoord ⟨u, haddr⟩

theorem nonRootDomainOfSiteClean_siteForNonRootDomainClean
    {n : Nat} [NeZero n] {T : RTree}
    (hpos : ∀ v : NonRootVertex T, 0 < NonRootVertex.weight v)
    (v : NonRootVertex T) (dom : NonRootFieldDomainClean n T v) :
    nonRootDomainOfSiteClean (siteForNonRootDomainClean hpos v dom) v 0 =
      dom := by
  cases dom with
  | mk rootCoord diagonal otherCoord =>
      simp only [nonRootDomainOfSiteClean, siteForNonRootDomainClean, ne_eq,
        diagonalClean, ↓reduceDIte, diagonalWitnessClean_sum, add_zero,
        NonRootFieldDomainClean.mk.injEq, true_and]
      funext u j
      have hne : u.1 ≠ v := by
        intro huv
        exact u.2 (by rw [huv])
      simp [hne]

theorem normalToRawClean_realized {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) :
    RealizedByNormalClean T (normalToRawClean A) := by
  exact ⟨A, rfl, rfl⟩

noncomputable def normalToNormalFormRawClean {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) : NormalFormRawAssignmentsClean n T :=
  ⟨normalToRawClean A, normalToRawClean_realized A⟩

theorem normalToNormalFormRawClean_surjective
    {n : Nat} [NeZero n] {T : RTree} :
    Function.Surjective
      (normalToNormalFormRawClean :
        NormalAssignmentClean n T → NormalFormRawAssignmentsClean n T) := by
  intro B
  rcases B with ⟨Araw, hreal⟩
  rcases hreal with ⟨A, hket, hbra⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  cases Araw with
  | mk ket bra =>
      change normalToRawClean A = RawAssignmentClean.mk ket bra
      change ket = (fun v site => ketAtVertexClean A site v) at hket
      change bra = (fun v site => braAtVertexClean A site v) at hbra
      cases hket
      cases hbra
      rfl

theorem normalToRawClean_injective_of_positive_weight
    {n : Nat} [NeZero n] {T : RTree}
    (hpos : ∀ v : NonRootVertex T, 0 < NonRootVertex.weight v) :
    Function.Injective
      (normalToRawClean : NormalAssignmentClean n T → RawAssignmentClean n T) := by
  intro A B hraw
  cases A with
  | mk Aroot Anode =>
      cases B with
      | mk Broot Bnode =>
          congr
          · funext rd
            let site : NormalSiteClean n T :=
              { rootCoord := fun _ => 0, nonRootCoord := rd }
            have hket :=
              congrArg
                (fun R : RawAssignmentClean n T => R.ket (Vertex.root T) site)
                hraw
            simpa [normalToRawClean] using hket
          · funext v dom
            let site := siteForNonRootDomainClean hpos v dom
            have hket :=
              congrArg (fun R : RawAssignmentClean n T => R.ket v.1 site) hraw
            have hdom :
                nonRootDomainOfSiteClean site v 0 = dom :=
              nonRootDomainOfSiteClean_siteForNonRootDomainClean hpos v dom
            simpa [normalToRawClean, ketAtVertexClean, v.2, hdom] using hket

theorem normalToRawClean_injective_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    Function.Injective
      (normalToRawClean : NormalAssignmentClean n T → RawAssignmentClean n T) :=
  normalToRawClean_injective_of_positive_weight (fun v => by
    simpa [NonRootVertex.weight, Vertex.weight] using
      (RTree.weightAt_positive_of_mem_addresses hT v.1.2))

theorem normalToNormalFormRawClean_injective_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    Function.Injective
      (normalToNormalFormRawClean :
        NormalAssignmentClean n T → NormalFormRawAssignmentsClean n T) := by
  intro A B hAB
  apply normalToRawClean_injective_of_positiveWeights hT
  exact congrArg Subtype.val hAB

theorem normalToNormalFormRawClean_bijective_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    Function.Bijective
      (normalToNormalFormRawClean :
        NormalAssignmentClean n T → NormalFormRawAssignmentsClean n T) :=
  ⟨normalToNormalFormRawClean_injective_of_positiveWeights hT,
    normalToNormalFormRawClean_surjective⟩

noncomputable def normalEquivNormalFormRawCleanOfPositiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    NormalAssignmentClean n T ≃ NormalFormRawAssignmentsClean n T :=
  Equiv.ofBijective normalToNormalFormRawClean
    (normalToNormalFormRawClean_bijective_of_positiveWeights hT)

theorem rawLocalEdgePhaseClean_normalToRawClean
    {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (e : List Nat × List Nat) :
    rawLocalEdgePhaseClean (normalToRawClean A) site e =
      edgePhaseAtSiteClean A site e := by
  simp [rawLocalEdgePhaseClean, normalToRawClean, edgePhaseAtSiteClean,
    ketAtPathClean, braAtPathClean]

theorem rawPhaseAtSiteClean_normalToRawClean
    {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T) :
    rawPhaseAtSiteClean T (normalToRawClean A) site =
      phaseAtSiteClean T A site := by
  unfold rawPhaseAtSiteClean phaseAtSiteClean
  induction RTree.edgeList T with
  | nil =>
      simp
  | cons e es ih =>
      simp [rawLocalEdgePhaseClean_normalToRawClean, ih]

theorem rawTotalPhaseClean_normalToRawClean
    {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) :
    rawTotalPhaseClean T (normalToRawClean A) = totalPhaseClean T A := by
  unfold rawTotalPhaseClean totalPhaseClean
  refine Finset.sum_congr rfl ?_
  intro site _
  exact rawPhaseAtSiteClean_normalToRawClean T A site

theorem rawWeightClean_normalToRawClean
    {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) :
    rawWeightClean T (normalToRawClean A) = weightClean T A := by
  simp [rawWeightClean, weightClean, rawTotalPhaseClean_normalToRawClean]

noncomputable def normalFormRawSignedSumClean
    (n : Nat) [NeZero n] (T : RTree) : ℤ :=
  ∑ Araw : NormalFormRawAssignmentsClean n T, rawWeightClean T Araw.1

theorem normalFormRawSignedSumClean_eq_signedCharacterSum
    (n : Nat) [NeZero n] (T : RTree) :
    normalFormRawSignedSumClean n T =
      signedCharacterSum (NormalFormRawAssignmentsClean n T)
        (fun Araw => rawTotalPhaseClean T Araw.1) := by
  rfl

theorem normalFormRawSignedSumClean_eq_normalSignedSumClean_of_positiveWeights
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    normalFormRawSignedSumClean n T = normalSignedSumClean n T := by
  classical
  have hsum :
      (∑ A : NormalAssignmentClean n T, weightClean T A) =
        ∑ Araw : NormalFormRawAssignmentsClean n T, rawWeightClean T Araw.1 := by
    refine Fintype.sum_equiv
      (normalEquivNormalFormRawCleanOfPositiveWeights (n := n) hT)
      (fun A : NormalAssignmentClean n T => weightClean T A)
      (fun Araw : NormalFormRawAssignmentsClean n T => rawWeightClean T Araw.1)
      ?_
    intro A
    simpa [normalEquivNormalFormRawCleanOfPositiveWeights,
      normalToNormalFormRawClean] using
        (rawWeightClean_normalToRawClean T A).symm
  simpa [normalFormRawSignedSumClean, normalSignedSumClean] using hsum.symm

namespace NormalCleanReductionBridge

noncomputable def toRealizedRawSignedReductionBridge
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    (B : NormalCleanReductionBridge n T hT) :
    SignedReductionBridge n T hT (NormalFormRawAssignmentsClean n T) where
  rawPhase := fun Araw => rawTotalPhaseClean T Araw.1
  raw_signed_sum_eq_abstract := by
    rw [← normalFormRawSignedSumClean_eq_signedCharacterSum]
    rw [normalFormRawSignedSumClean_eq_normalSignedSumClean_of_positiveWeights
      (n := n) (T := T) hT]
    exact B.normal_signed_sum_eq_abstract

end NormalCleanReductionBridge

end Imbalance
end TreeGraph
