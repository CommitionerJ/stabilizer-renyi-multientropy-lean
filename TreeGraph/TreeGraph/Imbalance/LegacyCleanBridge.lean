import TreeGraph.RawPrimitive
import TreeGraph.Imbalance.PhysicalRaw

namespace TreeGraph
namespace Imbalance

namespace LegacyCleanBridge

noncomputable def normalSiteEquiv
    (n : Nat) [NeZero n] (T : RTree) :
    RawNormal.NormalSite n T ≃ NormalSiteClean n T where
  toFun site :=
    { rootCoord := site.rootCoord
      nonRootCoord := site.nonRootCoord }
  invFun site :=
    { rootCoord := site.rootCoord
      nonRootCoord := site.nonRootCoord }
  left_inv site := by
    cases site
    rfl
  right_inv site := by
    cases site
    rfl

noncomputable def nonRootFieldDomainEquiv
    (n : Nat) [NeZero n] (T : RTree) (v : NonRootVertex T) :
    RawNormal.NonRootFieldDomain n T v ≃ NonRootFieldDomainClean n T v where
  toFun dom :=
    { rootCoord := dom.rootCoord
      diagonal := dom.diagonal
      otherCoord := dom.otherCoord }
  invFun dom :=
    { rootCoord := dom.rootCoord
      diagonal := dom.diagonal
      otherCoord := dom.otherCoord }
  left_inv dom := by
    cases dom
    rfl
  right_inv dom := by
    cases dom
    rfl

noncomputable def normalAssignmentEquiv
    (n : Nat) [NeZero n] (T : RTree) :
    RawNormal.NormalAssignment n T ≃ NormalAssignmentClean n T where
  toFun A :=
    { rootField := fun rd => A.rootField rd
      nodeField := fun v dom =>
        A.nodeField v ((nonRootFieldDomainEquiv n T v).symm dom) }
  invFun A :=
    { rootField := fun rd => A.rootField rd
      nodeField := fun v dom =>
        A.nodeField v ((nonRootFieldDomainEquiv n T v) dom) }
  left_inv A := by
    cases A with
    | mk rootField nodeField =>
        simp [nonRootFieldDomainEquiv]
  right_inv A := by
    cases A with
    | mk rootField nodeField =>
        simp [nonRootFieldDomainEquiv]

@[simp] theorem diagonalClean_normalSiteEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (site : RawNormal.NormalSite n T) (v : NonRootVertex T) :
    diagonalClean ((normalSiteEquiv n T) site) v =
      RawNormal.diagonal site v := by
  rfl

@[simp] theorem nonRootDomainOfSiteClean_normalSiteEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (site : RawNormal.NormalSite n T) (v : NonRootVertex T)
    (shift : Rep n) :
    nonRootDomainOfSiteClean ((normalSiteEquiv n T) site) v shift =
      (nonRootFieldDomainEquiv n T v)
        (RawNormal.nonRootDomainOfSite site v shift) := by
  rfl

@[simp] theorem nonRootFieldDomainEquiv_symm_nonRootDomainOfSiteClean
    {n : Nat} [NeZero n] {T : RTree}
    (site : RawNormal.NormalSite n T) (v : NonRootVertex T)
    (shift : Rep n) :
    (nonRootFieldDomainEquiv n T v).symm
        (nonRootDomainOfSiteClean ((normalSiteEquiv n T) site) v shift) =
      RawNormal.nonRootDomainOfSite site v shift := by
  rw [nonRootDomainOfSiteClean_normalSiteEquiv]
  exact (nonRootFieldDomainEquiv n T v).left_inv
    (RawNormal.nonRootDomainOfSite site v shift)

@[simp] theorem ketAtVertexClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (A : RawNormal.NormalAssignment n T)
    (site : RawNormal.NormalSite n T) (v : Vertex T) :
    ketAtVertexClean ((normalAssignmentEquiv n T) A)
        ((normalSiteEquiv n T) site) v =
      RawNormal.ketAtVertex A site v := by
  by_cases hroot : v.1 = []
  · simp [ketAtVertexClean, RawNormal.ketAtVertex, hroot, normalSiteEquiv,
      normalAssignmentEquiv]
  · simp [ketAtVertexClean, RawNormal.ketAtVertex, hroot,
      normalAssignmentEquiv]

@[simp] theorem braAtVertexClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (A : RawNormal.NormalAssignment n T)
    (site : RawNormal.NormalSite n T) (v : Vertex T) :
    braAtVertexClean ((normalAssignmentEquiv n T) A)
        ((normalSiteEquiv n T) site) v =
      RawNormal.braAtVertex A site v := by
  by_cases hroot : v.1 = []
  · simp [braAtVertexClean, RawNormal.braAtVertex, hroot, normalSiteEquiv,
      normalAssignmentEquiv]
  · simp [braAtVertexClean, RawNormal.braAtVertex, hroot,
      normalAssignmentEquiv]

@[simp] theorem ketAtPathClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (A : RawNormal.NormalAssignment n T)
    (site : RawNormal.NormalSite n T) (p : List Nat) :
    ketAtPathClean ((normalAssignmentEquiv n T) A)
        ((normalSiteEquiv n T) site) p =
      RawNormal.ketAtPath A site p := by
  unfold ketAtPathClean RawNormal.ketAtPath
  split <;> simp

@[simp] theorem braAtPathClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (A : RawNormal.NormalAssignment n T)
    (site : RawNormal.NormalSite n T) (p : List Nat) :
    braAtPathClean ((normalAssignmentEquiv n T) A)
        ((normalSiteEquiv n T) site) p =
      RawNormal.braAtPath A site p := by
  unfold braAtPathClean RawNormal.braAtPath
  split <;> simp

@[simp] theorem edgePhaseAtSiteClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] {T : RTree}
    (A : RawNormal.NormalAssignment n T)
    (site : RawNormal.NormalSite n T) (e : List Nat × List Nat) :
    edgePhaseAtSiteClean ((normalAssignmentEquiv n T) A)
        ((normalSiteEquiv n T) site) e =
      RawNormal.edgePhaseAtSite A site e := by
  simp [edgePhaseAtSiteClean, RawNormal.edgePhaseAtSite]

theorem phaseAtSiteClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] (T : RTree)
    (A : RawNormal.NormalAssignment n T)
    (site : RawNormal.NormalSite n T) :
    phaseAtSiteClean T ((normalAssignmentEquiv n T) A)
        ((normalSiteEquiv n T) site) =
      RawNormal.phaseAtSite T A site := by
  unfold phaseAtSiteClean RawNormal.phaseAtSite
  induction RTree.edgeList T with
  | nil =>
      simp
  | cons e es ih =>
      simp [ih]

theorem totalPhaseClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] (T : RTree)
    (A : RawNormal.NormalAssignment n T) :
    totalPhaseClean T ((normalAssignmentEquiv n T) A) =
      RawNormal.totalPhase T A := by
  classical
  let e := normalSiteEquiv n T
  calc
    totalPhaseClean T ((normalAssignmentEquiv n T) A) =
        ∑ site : RawNormal.NormalSite n T,
          phaseAtSiteClean T ((normalAssignmentEquiv n T) A) (e site) := by
      unfold totalPhaseClean
      exact (Equiv.sum_comp e
        (fun site : NormalSiteClean n T =>
          phaseAtSiteClean T ((normalAssignmentEquiv n T) A) site)).symm
    _ = ∑ site : RawNormal.NormalSite n T,
          RawNormal.phaseAtSite T A site := by
      refine Finset.sum_congr rfl ?_
      intro site _
      exact phaseAtSiteClean_normalAssignmentEquiv T A site
    _ = RawNormal.totalPhase T A := by
      rfl

theorem weightClean_normalAssignmentEquiv
    {n : Nat} [NeZero n] (T : RTree)
    (A : RawNormal.NormalAssignment n T) :
    weightClean T ((normalAssignmentEquiv n T) A) =
      RawNormal.weight T A := by
  simp [weightClean, RawNormal.weight, chi,
    totalPhaseClean_normalAssignmentEquiv]

theorem normalSignedSumClean_eq_legacy_signedSum
    (n : Nat) [NeZero n] (T : RTree) :
    normalSignedSumClean n T = RawNormal.signedSum n T := by
  classical
  let e := normalAssignmentEquiv n T
  calc
    normalSignedSumClean n T =
        ∑ A : RawNormal.NormalAssignment n T, weightClean T (e A) := by
      unfold normalSignedSumClean
      exact (Equiv.sum_comp e
        (fun A : NormalAssignmentClean n T => weightClean T A)).symm
    _ = ∑ A : RawNormal.NormalAssignment n T, RawNormal.weight T A := by
      refine Finset.sum_congr rfl ?_
      intro A _
      exact weightClean_normalAssignmentEquiv T A
    _ = RawNormal.signedSum n T := by
      rfl

theorem legacy_signedSum_eq_normalSignedSumClean
    (n : Nat) [NeZero n] (T : RTree) :
    RawNormal.signedSum n T = normalSignedSumClean n T :=
  (normalSignedSumClean_eq_legacy_signedSum n T).symm

theorem rawBitStringSignedSum_eq_normalSignedSumClean_of_positiveWeights
    (n : Nat) [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T) :
    RawPrimitive.rawBitStringSignedSum n T = normalSignedSumClean n T := by
  rw [RawPrimitive.rawBitStringSignedSum_eq_signedSum_of_positiveWeights
    (n := n) (T := T) hT]
  exact legacy_signedSum_eq_normalSignedSumClean n T

end LegacyCleanBridge

end Imbalance
end TreeGraph
