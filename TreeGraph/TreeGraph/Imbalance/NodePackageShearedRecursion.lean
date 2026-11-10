import TreeGraph.Imbalance.NodePackageShearedOpenPackage
import TreeGraph.Imbalance.CanonicalPackage

namespace TreeGraph
namespace Imbalance

private lemma numVertices_le_sum_of_mem {T : RTree} {ts : List RTree}
    (h : T ∈ ts) :
    RTree.numVertices T ≤ (ts.map RTree.numVertices).sum := by
  induction ts with
  | nil =>
      cases h
  | cons U us ih =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h
        simp
      · have hle := ih h
        simp
        omega

private lemma numVertices_lt_node_of_mem
    {C : RTree} {a : Nat} {cs : List RTree} (h : C ∈ cs) :
    RTree.numVertices C < RTree.numVertices (RTree.node a cs) := by
  have hle := numVertices_le_sum_of_mem h
  simp [RTree.numVertices]
  omega

noncomputable def canonicalShearedStepCertificateOfCanonicalChildren
    (n a : Nat) [NeZero n] :
    (cs : List RTree) →
      (hT : RTree.PositiveWeights (RTree.node a cs)) →
      (childPackage :
        ∀ C, (hCmem : C ∈ cs) →
          OpenNormalCleanPackage n C
            (child_positive_of_node hT C hCmem)) →
      (∀ C (hCmem : C ∈ cs), (childPackage C hCmem).IsCanonical) →
      NodeShearedOpenPackageStepCertificate n a cs hT
        (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
          n a cs hT childPackage)
  | [], hT, childPackage, _hcanon => by
      refine { open_signed_sum_eq := ?_ }
      intro root
      rw [openNormalSignedSumClean_leaf]
      rw [if_pos
        (mem_packageShearedAllowedRootFieldSpace_nil n a hT
          (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
            n a [] hT childPackage) root)]
      have hX : Xdim n (RTree.node a []) = 1 := Xdim_leaf n a
      have hY : Ydim n (RTree.node a []) hT = 1 := by
        rw [Ydim_eq_YdimCandidate, YdimCandidate_leaf]
      rw [hX, hY]
      norm_num
  | RTree.node b ds :: rest, hT, childPackage, hcanon => by
      let C : RTree := RTree.node b ds
      let hTail : RTree.PositiveWeights (RTree.node a rest) :=
        positiveWeights_node_tail_of_cons hT
      let tailChildPackage :
          ∀ D, (hDmem : D ∈ rest) →
            OpenNormalCleanPackage n D
              (child_positive_of_node hTail D hDmem) :=
        fun D hDmem => childPackage D (by simp [hDmem])
      have hcanonTail :
          ∀ D (hDmem : D ∈ rest),
            (tailChildPackage D hDmem).IsCanonical := by
        intro D hDmem
        simpa [tailChildPackage] using
          hcanon D (by simp [hDmem])
      let Wtail0 :
          NodeShearedOpenPackageStepCertificate n a rest hTail
            (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
              n a rest hTail tailChildPackage) :=
        canonicalShearedStepCertificateOfCanonicalChildren
          n a rest hTail tailChildPackage hcanonTail
      have Wtail :
          NodeShearedOpenPackageStepCertificate n a rest hTail
            (nodeTailInputsOfCons n a C rest hT
              (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
                n a (C :: rest) hT childPackage)) := by
        simpa [C, hTail, tailChildPackage, nodeTailInputsOfCons,
          NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages,
          NodeOpenPackageStepInputs.ofChildPackagesCanonical,
          NodeOpenPackageStepInputs.withCanonicalParentBridge] using Wtail0
      refine { open_signed_sum_eq := ?_ }
      intro root
      simpa [C] using
        canonical_openNormalSignedSumClean_node_cons_eq_if_packageShearedAllowed
          n a b ds rest hT childPackage Wtail
          (hcanon (RTree.node b ds) (by simp)) root

noncomputable def canonicalShearedOpenPackageWithCanonical
    (n : Nat) [NeZero n] :
    (T : RTree) → (hT : RTree.PositiveWeights T) →
      { P : OpenNormalCleanPackage n T hT // P.IsCanonical } := by
  classical
  refine WellFounded.fix (measure RTree.numVertices).wf
    (C := fun T => ∀ hT : RTree.PositiveWeights T,
      { P : OpenNormalCleanPackage n T hT // P.IsCanonical }) ?_
  intro T rec hT
  cases T with
  | node a cs =>
      let childPackage :
          ∀ C, (hCmem : C ∈ cs) →
            OpenNormalCleanPackage n C
              (child_positive_of_node hT C hCmem) :=
        fun C hCmem =>
          (rec C (numVertices_lt_node_of_mem hCmem)
            (child_positive_of_node hT C hCmem)).1
      have hcanon :
          ∀ C (hCmem : C ∈ cs), (childPackage C hCmem).IsCanonical := by
        intro C hCmem
        exact
          (rec C (numVertices_lt_node_of_mem hCmem)
            (child_positive_of_node hT C hCmem)).2
      let W :
          NodeShearedOpenPackageStepCertificate n a cs hT
            (NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages
              n a cs hT childPackage) :=
        canonicalShearedStepCertificateOfCanonicalChildren
          n a cs hT childPackage hcanon
      exact
        ⟨(W.toOpenPackageStepTheorem).parentPackage, by
          dsimp [NodeShearedOpenPackageStepCertificate.toOpenPackageStepTheorem,
            OpenNormalCleanPackage.IsCanonical,
            NodeOpenPackageStepInputs.canonicalNodeInputsOfPackages,
            NodeOpenPackageStepInputs.ofChildPackagesCanonical,
            NodeOpenPackageStepInputs.withCanonicalParentBridge]
          rfl⟩

noncomputable def canonicalShearedOpenPackageOfTree
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    OpenNormalCleanPackage n T hT :=
  (canonicalShearedOpenPackageWithCanonical n T hT).1

@[simp] theorem canonicalShearedOpenPackageOfTree_isCanonical
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    (canonicalShearedOpenPackageOfTree n T hT).IsCanonical :=
  (canonicalShearedOpenPackageWithCanonical n T hT).2

open Classical in
theorem canonicalShearedOpenPackageOfTree_open_signed_sum_eq
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T)
    (root : RootFieldAssignmentClean n T) :
    openNormalSignedSumClean n T root =
      if root ∈
          (canonicalShearedOpenPackageOfTree n T hT).openBridge.rootMessageSpace then
        (2 : ℤ) ^ (Xdim n T - Ydim n T hT)
      else 0 :=
  (canonicalShearedOpenPackageOfTree n T hT).openBridge.open_signed_sum_eq root

noncomputable def canonicalShearedOpenBridgeOfTree
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    OpenNormalCleanReductionBridge n T hT :=
  (canonicalShearedOpenPackageOfTree n T hT).openBridge

noncomputable def canonicalShearedClosedBridgeOfTree
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    NormalCleanReductionBridge n T hT :=
  (canonicalShearedOpenBridgeOfTree n T hT).toNormalCleanReductionBridge

theorem canonicalSheared_normalSignedSumClean_eq_abstractTreeSignedSum
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalSignedSumClean n T = abstractTreeSignedSum n T hT :=
  (canonicalShearedClosedBridgeOfTree n T hT).normal_signed_sum_eq_abstract

theorem canonicalSheared_normalSignedSumClean_eq_two_pow_Xdim
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    normalSignedSumClean n T = (2 : ℤ) ^ Xdim n T :=
  (canonicalShearedClosedBridgeOfTree n T hT).rooted_tree_imbalance_formula

theorem canonicalSheared_normalSignedSumClean_eq_two_pow_allTerms
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = termSum n (allTerms T) :=
  (canonicalShearedClosedBridgeOfTree n T hT).rooted_tree_imbalance_formula_allTerms

theorem canonicalSheared_normalSignedSumClean_eq_two_pow_Xpoly
    (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ∃ X : Nat,
      normalSignedSumClean n T = (2 : ℤ) ^ X ∧
        ((X : Nat) : ℤ) = Xpoly n T :=
  (canonicalShearedClosedBridgeOfTree n T hT).rooted_tree_imbalance_formula_Xpoly

end Imbalance
end TreeGraph
