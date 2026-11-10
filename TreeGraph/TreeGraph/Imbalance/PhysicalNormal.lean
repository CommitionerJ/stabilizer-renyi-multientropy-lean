import TreeGraph.Imbalance.SignedReductionBridge
import TreeGraph.Addresses

namespace TreeGraph
namespace Imbalance

abbrev RootFieldDomainClean (n : Nat) [NeZero n] (T : RTree) :=
  (v : NonRootVertex T) → Fin (NonRootVertex.weight v) → Rep n

abbrev OtherNonRootVertexClean (T : RTree) (v : NonRootVertex T) :=
  { u : NonRootVertex T // u.1.1 ≠ v.1.1 }

structure NonRootFieldDomainClean (n : Nat) [NeZero n] (T : RTree)
    (v : NonRootVertex T) where
  rootCoord : Fin (T.rootWeight - 1) → Rep n
  diagonal : Rep n
  otherCoord :
    (u : OtherNonRootVertexClean T v) →
      Fin (NonRootVertex.weight u.1) → Rep n
  deriving DecidableEq, Fintype

structure NormalSiteClean (n : Nat) [NeZero n] (T : RTree) where
  rootCoord : Fin (T.rootWeight - 1) → Rep n
  nonRootCoord : RootFieldDomainClean n T
  deriving DecidableEq, Fintype

structure NormalAssignmentClean (n : Nat) [NeZero n] (T : RTree) where
  rootField : RootFieldDomainClean n T → F2
  nodeField :
    (v : NonRootVertex T) →
      NonRootFieldDomainClean n T v → F2
  deriving Fintype

abbrev RootFieldAssignmentClean (n : Nat) [NeZero n] (T : RTree) :=
  RootFieldDomainClean n T → F2

abbrev NodeFieldAssignmentClean (n : Nat) [NeZero n] (T : RTree) :=
  (v : NonRootVertex T) → NonRootFieldDomainClean n T v → F2

noncomputable def normalAssignmentCleanEquivRootNodeFields
    (n : Nat) [NeZero n] (T : RTree) :
    NormalAssignmentClean n T ≃
      RootFieldAssignmentClean n T × NodeFieldAssignmentClean n T where
  toFun A := (A.rootField, A.nodeField)
  invFun P := { rootField := P.1, nodeField := P.2 }
  left_inv A := by
    cases A
    rfl
  right_inv P := by
    cases P
    rfl

theorem sum_normalAssignmentClean_eq_sum_root_nodeFields
    {n : Nat} [NeZero n] (T : RTree)
    (F : NormalAssignmentClean n T → ℤ) :
    (∑ A : NormalAssignmentClean n T, F A) =
      ∑ P : RootFieldAssignmentClean n T × NodeFieldAssignmentClean n T,
        F ((normalAssignmentCleanEquivRootNodeFields n T).symm P) := by
  classical
  exact (Equiv.sum_comp
    (normalAssignmentCleanEquivRootNodeFields n T).symm F).symm

noncomputable def diagonalClean {n : Nat} [NeZero n] {T : RTree}
    (site : NormalSiteClean n T) (v : NonRootVertex T) : Rep n :=
  ∑ j : Fin (NonRootVertex.weight v), site.nonRootCoord v j

noncomputable def nonRootDomainOfSiteClean {n : Nat} [NeZero n] {T : RTree}
    (site : NormalSiteClean n T) (v : NonRootVertex T)
    (shift : Rep n) : NonRootFieldDomainClean n T v where
  rootCoord := site.rootCoord
  diagonal := diagonalClean site v + shift
  otherCoord := fun u => site.nonRootCoord u.1

noncomputable def ketAtVertexClean {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (v : Vertex T) : F2 :=
  if hv : v.1 = [] then
    A.rootField site.nonRootCoord
  else
    A.nodeField ⟨v, hv⟩ (nonRootDomainOfSiteClean site ⟨v, hv⟩ 0)

noncomputable def braAtVertexClean {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (v : Vertex T) : F2 :=
  if hv : v.1 = [] then
    A.rootField site.nonRootCoord
  else
    A.nodeField ⟨v, hv⟩ (nonRootDomainOfSiteClean site ⟨v, hv⟩ 1)

noncomputable def ketAtPathClean {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (p : List Nat) : F2 :=
  if hp : p ∈ RTree.addresses T then
    ketAtVertexClean A site ⟨p, hp⟩
  else
    0

noncomputable def braAtPathClean {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (p : List Nat) : F2 :=
  if hp : p ∈ RTree.addresses T then
    braAtVertexClean A site ⟨p, hp⟩
  else
    0

noncomputable def edgePhaseAtSiteClean {n : Nat} [NeZero n] {T : RTree}
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T)
    (e : List Nat × List Nat) : F2 :=
  ketAtPathClean A site e.1 * ketAtPathClean A site e.2 +
    braAtPathClean A site e.1 * braAtPathClean A site e.2

noncomputable def phaseAtSiteClean {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) (site : NormalSiteClean n T) : F2 :=
  (RTree.edgeList T).map (edgePhaseAtSiteClean A site) |>.sum

noncomputable def totalPhaseClean {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) : F2 :=
  ∑ site : NormalSiteClean n T, phaseAtSiteClean T A site

noncomputable def weightClean {n : Nat} [NeZero n] (T : RTree)
    (A : NormalAssignmentClean n T) : ℤ :=
  chi (totalPhaseClean T A)

noncomputable def normalSignedSumClean
    (n : Nat) [NeZero n] (T : RTree) : ℤ :=
  ∑ A : NormalAssignmentClean n T, weightClean T A

@[simp] theorem phaseAtSiteClean_leaf {n a : Nat} [NeZero n]
    (A : NormalAssignmentClean n (RTree.node a []))
    (site : NormalSiteClean n (RTree.node a [])) :
    phaseAtSiteClean (RTree.node a []) A site = 0 := by
  simp [phaseAtSiteClean]

@[simp] theorem totalPhaseClean_leaf {n a : Nat} [NeZero n]
    (A : NormalAssignmentClean n (RTree.node a [])) :
    totalPhaseClean (RTree.node a []) A = 0 := by
  simp [totalPhaseClean]

@[simp] theorem weightClean_leaf {n a : Nat} [NeZero n]
    (A : NormalAssignmentClean n (RTree.node a [])) :
    weightClean (RTree.node a []) A = 1 := by
  simp [weightClean]

theorem normalSignedSumClean_leaf (n a : Nat) [NeZero n] :
    normalSignedSumClean n (RTree.node a []) =
      (Fintype.card (NormalAssignmentClean n (RTree.node a [])) : ℤ) := by
  unfold normalSignedSumClean
  simp [weightClean]

theorem nonRootVertexClean_leaf_false {a : Nat}
    (v : NonRootVertex (RTree.node a [])) : False := by
  let p : List Nat := v.1.1
  have hmem : p ∈ RTree.addresses (RTree.node a []) := v.1.2
  change p ∈ ([[]] : List (List Nat)) at hmem
  have haddr : p = [] := List.mem_singleton.mp hmem
  exact v.2 haddr

instance rootFieldDomainCleanLeafSubsingleton
    (n a : Nat) [NeZero n] :
    Subsingleton (RootFieldDomainClean n (RTree.node a [])) where
  allEq f g := by
    funext v
    exact False.elim (nonRootVertexClean_leaf_false v)

def rootFieldDomainCleanLeafDefault
    (n a : Nat) [NeZero n] :
    RootFieldDomainClean n (RTree.node a []) :=
  fun v => False.elim (nonRootVertexClean_leaf_false v)

noncomputable def normalAssignmentCleanLeafEquiv
    (n a : Nat) [NeZero n] :
    NormalAssignmentClean n (RTree.node a []) ≃ F2 where
  toFun A := A.rootField (rootFieldDomainCleanLeafDefault n a)
  invFun b :=
    { rootField := fun _ => b
      nodeField := fun v => False.elim (nonRootVertexClean_leaf_false v) }
  left_inv A := by
    cases A with
    | mk rootField nodeField =>
        rw [NormalAssignmentClean.mk.injEq]
        constructor
        · funext rd
          exact congrArg rootField
            (Subsingleton.elim (rootFieldDomainCleanLeafDefault n a) rd)
        · funext v dom
          exact False.elim (nonRootVertexClean_leaf_false v)
  right_inv b := by
    rfl

theorem card_normalAssignmentClean_leaf
    (n a : Nat) [NeZero n] :
    Fintype.card (NormalAssignmentClean n (RTree.node a [])) = 2 := by
  classical
  calc
    Fintype.card (NormalAssignmentClean n (RTree.node a [])) =
        Fintype.card F2 :=
      Fintype.card_congr (normalAssignmentCleanLeafEquiv n a)
    _ = 2 := by
      simp [F2]

theorem normalSignedSumClean_leaf_eq_abstractTreeSignedSum
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    normalSignedSumClean n (RTree.node a []) =
      abstractTreeSignedSum n (RTree.node a []) hT := by
  rw [rooted_tree_signed_sum_imbalance_formula]
  rw [normalSignedSumClean_leaf]
  rw [card_normalAssignmentClean_leaf]
  simp

theorem normalSignedSumClean_eq_signedCharacterSum
    (n : Nat) [NeZero n] (T : RTree) :
    normalSignedSumClean n T =
      signedCharacterSum (NormalAssignmentClean n T)
        (fun A => totalPhaseClean T A) := by
  rfl

structure NormalCleanReductionBridge
    (n : Nat) [NeZero n] (T : RTree) (hT : RTree.PositiveWeights T) where
  normal_signed_sum_eq_abstract :
    normalSignedSumClean n T = abstractTreeSignedSum n T hT

namespace NormalCleanReductionBridge

noncomputable def leaf
    (n a : Nat) [NeZero n]
    (hT : RTree.PositiveWeights (RTree.node a [])) :
    NormalCleanReductionBridge n (RTree.node a []) hT where
  normal_signed_sum_eq_abstract :=
    normalSignedSumClean_leaf_eq_abstractTreeSignedSum n a hT

noncomputable def toSignedReductionBridge
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    (B : NormalCleanReductionBridge n T hT) :
    SignedReductionBridge n T hT (NormalAssignmentClean n T) where
  rawPhase := fun A => totalPhaseClean T A
  raw_signed_sum_eq_abstract := by
    rw [← normalSignedSumClean_eq_signedCharacterSum]
    exact B.normal_signed_sum_eq_abstract

theorem rooted_tree_imbalance_formula
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    (B : NormalCleanReductionBridge n T hT) :
    normalSignedSumClean n T = (2 : ℤ) ^ Xdim n T := by
  rw [B.normal_signed_sum_eq_abstract]
  exact rooted_tree_signed_sum_imbalance_formula n T hT

theorem rooted_tree_imbalance_formula_allTerms
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    (B : NormalCleanReductionBridge n T hT) :
    ∃ X : Nat,
      normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact B.rooted_tree_imbalance_formula
  · exact Xdim_cast_eq_allTerms n T hT

theorem rooted_tree_imbalance_formula_Xpoly
    {n : Nat} [NeZero n] {T : RTree} {hT : RTree.PositiveWeights T}
    (B : NormalCleanReductionBridge n T hT) :
    ∃ X : Nat,
      normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T := by
  refine ⟨Xdim n T, ?_, ?_⟩
  · exact B.rooted_tree_imbalance_formula
  · exact Xdim_cast_eq_Xpoly n T hT

end NormalCleanReductionBridge

end Imbalance
end TreeGraph
