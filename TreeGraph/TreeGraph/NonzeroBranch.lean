import TreeGraph.FinalTheorem

namespace TreeGraph

namespace RawPrimitive

namespace NonzeroBranch

abbrev CoreRule : Prop :=
  ChildOpenRootFourierKernelBoundaryNonzeroBranchNontrivialRule

abbrev AdjacentCodimCoreRule : Prop :=
  ChildBoundaryAdjacentSliceRangeCodimNontrivialRule

abbrev InternalKernelConstantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs),
        ∃ K : ℤ,
          ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            childOpenRootInternalKernelAt
              (n := n) (a := a) cs i φ = K

abbrev InternalKernelTopInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs),
        ChildOpenRootInternalKernelInvariantSubmoduleAt a cs n i ⊤

abbrev InvariantSupKerCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        ∃ S :
          Submodule F2
            (RawNormal.NodeChildRootFieldDomain n a cs i → F2),
          ChildOpenRootInternalKernelInvariantSubmoduleAt
              a cs n i S ∧
            ChildBoundaryLinearFormSubmoduleSupKerAt a cs n R i S

abbrev WitnessShiftCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        ChildOpenRootFourierKernelBoundaryWitnessShiftAt a cs n R i

abbrev ShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        ChildOpenRootFourierKernelBoundaryShiftInvariantAt a cs n R i

abbrev VisibleSingletonShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        ChildOpenRootFourierKernelBoundaryVisibleSingletonShiftInvariantAt
          a cs n R i

abbrev VisibleSingletonWitnessCoreRule : Prop :=
  ChildOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftNontrivialRule

abbrev BoundaryFlipEquivCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          ∃ e :
            (RawNormal.NodeChildRootFieldDomain n a cs i → F2) ≃
              (RawNormal.NodeChildRootFieldDomain n a cs i → F2),
            (∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
              childOpenRootInternalKernelAt
                  (n := n) (a := a) cs i (e φ) =
                childOpenRootInternalKernelAt
                  (n := n) (a := a) cs i φ) ∧
            ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
              childBoundaryLinearFormAt (n := n) (a := a) cs R i
                  (e φ) =
              childBoundaryLinearFormAt (n := n) (a := a) cs R i φ + 1

abbrev DiagonalShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (shift : ZMod n)
        (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        childOpenRootInternalKernelAt (n := n) (a := a) cs i
            (nodeChildRootFieldFunctionDiagonalShiftLinearEquiv
              (n := n) (b := a) cs i shift φ) =
          childOpenRootInternalKernelAt (n := n) (a := a) cs i φ

abbrev DiagonalFlipCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          ∃ shift : ZMod n,
            ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
              childBoundaryLinearFormAt (n := n) (a := a) cs R i
                  (nodeChildRootFieldFunctionDiagonalShiftLinearEquiv
                    (n := n) (b := a) cs i shift φ) =
                childBoundaryLinearFormAt
                  (n := n) (a := a) cs R i φ + 1

abbrev OddModulusCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      Odd n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            bitSign
              (childBoundaryLinearFormAt
                (n := n) (a := a) cs R i φ) *
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ) = 0

abbrev EvenModulusCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      Even n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            bitSign
              (childBoundaryLinearFormAt
                (n := n) (a := a) cs R i φ) *
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ) = 0

abbrev OddFiberCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            bitSign
              (childBoundaryLinearFormAt
                (n := n) (a := a) cs R i φ) *
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ) = 0

abbrev EvenFiberCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Even
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            bitSign
              (childBoundaryLinearFormAt
                (n := n) (a := a) cs R i φ) *
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ) = 0

abbrev EvenModulusHeavyCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      Even n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        1 < NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) →
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            bitSign
              (childBoundaryLinearFormAt
                (n := n) (a := a) cs R i φ) *
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ) = 0

abbrev OddFiberVisibleWitnessCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        ChildOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt
          a cs n R i

abbrev EvenHeavyVisibleWitnessCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      Even n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        1 < NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) →
        ChildOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt
          a cs n R i

abbrev LeafChildrenCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    (∀ i : ChildIdx cs, ∃ b : Nat, childAt cs i = RTree.node b []) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            bitSign
              (childBoundaryLinearFormAt
                (n := n) (a := a) cs R i φ) *
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ) = 0

abbrev LeafChildrenInternalKernelTopInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    (∀ i : ChildIdx cs, ∃ b : Nat, childAt cs i = RTree.node b []) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ i : ChildIdx cs,
        ChildOpenRootInternalKernelInvariantSubmoduleAt a cs n i ⊤

abbrev LeafChildrenVisibleWitnessCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    (∀ i : ChildIdx cs, ∃ b : Nat, childAt cs i = RTree.node b []) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        ChildOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt
          a cs n R i

abbrev VerifiedShapeCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    VerifiedShape (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            bitSign
              (childBoundaryLinearFormAt
                (n := n) (a := a) cs R i φ) *
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ) = 0

abbrev VerifiedShapeInternalKernelTopInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    VerifiedShape (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ i : ChildIdx cs,
        ChildOpenRootInternalKernelInvariantSubmoduleAt a cs n i ⊤

abbrev VerifiedShapeVisibleWitnessCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    VerifiedShape (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        ChildOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt
          a cs n R i

abbrev VerifiedShapeAdjacentCodimCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    VerifiedShape (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      Module.finrank F2
          (LinearMap.range
            (cyclicChildRootBoundaryAdjacentSliceProjectionLinearMap
              (n := n) (b := a) cs)) +
        independentBranchDimension n cs =
      Fintype.card (RawNormal.RootFieldDomain n (RTree.node a cs))

noncomputable def nodeChildRootBoundaryBranchMessageMap
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs) :
    (RawNormal.NodeChildRootFieldDomain n a cs i → F2) →ₗ[F2]
      (NonRootContext n (RTree.node a cs)
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) →
        (Fin
          (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)) →
            ZMod n) → F2) where
  toFun δ :=
    fun c x =>
      δ
        (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := a) cs i c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
          0)
  map_add' δ η := by
    ext c x
    simp [Pi.add_apply]
  map_smul' r δ := by
    ext c x
    simp [Pi.smul_apply]

@[simp] theorem nodeChildRootBoundaryBranchMessageMap_apply
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (c : NonRootContext n (RTree.node a cs)
      (RawNormal.childRootAtAsNonRootInNode (a := a) i))
    (x :
      Fin
        (NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)) →
        ZMod n) :
    nodeChildRootBoundaryBranchMessageMap
        (n := n) (a := a) cs i δ c x =
      δ
        (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := a) cs i c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
          0) := rfl

noncomputable def nodeChildRootBoundaryBranchConstraintMap
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs) :
    (RawNormal.NodeChildRootFieldDomain n a cs i → F2) →ₗ[F2]
      (ZMod n →
        NonRootContext n (RTree.node a cs)
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) → F2) :=
  (nonRootBranchConstraintMap (RTree.node a cs)
      (RawNormal.childRootAtAsNonRootInNode (a := a) i)).comp
    (nodeChildRootBoundaryBranchMessageMap (n := n) (a := a) cs i)

@[simp] theorem nodeChildRootBoundaryBranchConstraintMap_apply
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (t : ZMod n)
    (c : NonRootContext n (RTree.node a cs)
      (RawNormal.childRootAtAsNonRootInNode (a := a) i)) :
    nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i δ t c =
      nonRootBranchConstraintMap (RTree.node a cs)
        (RawNormal.childRootAtAsNonRootInNode (a := a) i)
        (fun c x =>
          δ
            (rootBoundarySelectedNodeChildRootFieldDomain
              (n := n) (b := a) cs i c.1
              (rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
              0)) t c := rfl

theorem nodeChildRootBoundaryBranchConstraintMap_contextTuple_apply
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (t : ZMod n)
    (c : NonRootContext n (RTree.node a cs)
      (RawNormal.childRootAtAsNonRootInNode (a := a) i)) :
    nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i δ t c =
      (∑ x : { x : Fin (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n //
          RawLinearAlgebra.diagSum
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i)) n x = t },
        δ (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := a) cs i c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x.1)
          0)) +
      (∑ x : { x : Fin (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n //
          RawLinearAlgebra.diagSum
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i)) n x =
            t + 1 },
        δ (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := a) cs i c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x.1)
          0)) := by
  rw [nodeChildRootBoundaryBranchConstraintMap_apply]
  exact
    nodeChildRootBranchConstraintMap_contextTuple_apply
      (n := n) (b := a) cs i δ t c

theorem nodeChildRootBoundaryBranchConstraintMap_contextTuple_eq_zero
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0)
    (t : ZMod n)
    (c : NonRootContext n (RTree.node a cs)
      (RawNormal.childRootAtAsNonRootInNode (a := a) i)) :
      (∑ x : { x : Fin (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n //
          RawLinearAlgebra.diagSum
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i)) n x = t },
        δ (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := a) cs i c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x.1)
          0)) +
      (∑ x : { x : Fin (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n //
          RawLinearAlgebra.diagSum
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i)) n x =
            t + 1 },
        δ (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := a) cs i c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x.1)
          0)) = 0 := by
  have hpoint := congrFun (congrFun hδ t) c
  rw [nodeChildRootBoundaryBranchConstraintMap_contextTuple_apply] at hpoint
  simpa using hpoint

theorem nodeChildRootBranchFiberBoundaryMessageSum_eq_zero_of_boundaryBranchConstraintMap
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (rd : RawNormal.RootFieldDomain n (RTree.node a cs))
    (t : ZMod n)
    (hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0) :
    nodeChildRootBranchFiberBoundaryMessageSum
        (n := n) (b := a) cs i δ rd t = 0 := by
  apply
    nodeChildRootBranchFiberBoundaryMessageSum_eq_zero_of_branchConstraintMap
      (n := n) (b := a) cs i δ rd t
  simpa [nodeChildRootBoundaryBranchConstraintMap] using hδ

theorem nodeChildRootBranchFiberBoundaryMessageSum_add_eq_left_of_right_boundaryBranchConstraintMap
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (rd : RawNormal.RootFieldDomain n (RTree.node a cs))
    (t : ZMod n)
    (hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0) :
    nodeChildRootBranchFiberBoundaryMessageSum
        (n := n) (b := a) cs i (φ + δ) rd t =
      nodeChildRootBranchFiberBoundaryMessageSum
        (n := n) (b := a) cs i φ rd t := by
  classical
  rw [
    nodeChildRootBranchFiberBoundaryMessageSum_eq_sum_rootCoord_branchConstraint
      (n := n) (b := a) cs i (φ + δ) rd t,
    nodeChildRootBranchFiberBoundaryMessageSum_eq_sum_rootCoord_branchConstraint
      (n := n) (b := a) cs i φ rd t]
  refine Finset.sum_congr rfl ?_
  intro rootCoord _hrootCoord
  let c :
      NonRootContext n (RTree.node a cs)
        (RawNormal.childRootAtAsNonRootInNode (a := a) i) :=
    rootBoundarySelectedNonRootContext
      (n := n) (T := RTree.node a cs)
      (RawNormal.childRootAtAsNonRootInNode (a := a) i)
      rootCoord rd
  have hpoint :
      nonRootBranchConstraintMap (RTree.node a cs)
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)
          (fun c x =>
            δ (rootBoundarySelectedNodeChildRootFieldDomain
              (n := n) (b := a) cs i c.1
              (rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
              0)) t c = 0 := by
    have hpoint := congrFun (congrFun hδ t) c
    simpa [nodeChildRootBoundaryBranchConstraintMap_apply] using hpoint
  have hmap :
      nonRootBranchConstraintMap (RTree.node a cs)
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)
          (fun c x =>
            (φ + δ) (rootBoundarySelectedNodeChildRootFieldDomain
              (n := n) (b := a) cs i c.1
              (rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
              0)) t c =
        nonRootBranchConstraintMap (RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)
            (fun c x =>
              φ (rootBoundarySelectedNodeChildRootFieldDomain
                (n := n) (b := a) cs i c.1
                (rootFieldDomainOfNonRootContextTuple
                  (n := n) (T := RTree.node a cs)
                  (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
                0)) t c +
          nonRootBranchConstraintMap (RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)
            (fun c x =>
              δ (rootBoundarySelectedNodeChildRootFieldDomain
                (n := n) (b := a) cs i c.1
                (rootFieldDomainOfNonRootContextTuple
                  (n := n) (T := RTree.node a cs)
                  (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
                0)) t c := by
    have hmap :=
      congrFun
        (congrFun
          ((nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i).map_add φ δ) t) c
    simpa [nodeChildRootBoundaryBranchConstraintMap_apply] using hmap
  rw [hmap, hpoint]
  simp [c]

theorem nodeChildRootBranchFiberBoundaryMessageSum_eq_of_boundaryBranchConstraintMap_eq
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (rd : RawNormal.RootFieldDomain n (RTree.node a cs))
    (t : ZMod n)
    (hmap :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i φ =
        nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) :
    nodeChildRootBranchFiberBoundaryMessageSum
        (n := n) (b := a) cs i φ rd t =
      nodeChildRootBranchFiberBoundaryMessageSum
        (n := n) (b := a) cs i ψ rd t := by
  classical
  let δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2 := φ + ψ
  have hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 := by
    rw [show δ = φ + ψ by rfl]
    rw [
      (nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i).map_add,
      hmap]
    ext t c
    exact
      add_self_eq_zero_of_module_F2
        ((nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) t c)
  have hshift :=
    nodeChildRootBranchFiberBoundaryMessageSum_add_eq_left_of_right_boundaryBranchConstraintMap
      (n := n) (a := a) (cs := cs) i ψ δ rd t hδ
  have hsum :
      ψ + δ = φ := by
    funext d
    calc
      ψ d + δ d = ψ d + (φ d + ψ d) := rfl
      _ = φ d + (ψ d + ψ d) := by ac_rfl
      _ = φ d + 0 := by
        rw [add_self_eq_zero_of_module_F2 (ψ d)]
      _ = φ d := by simp
  simpa [hsum] using hshift

theorem nodeChildRootBoundaryBranchConstraintMap_add_eq_left_of_right_eq_zero
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0) :
    nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i (φ + δ) =
      nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i φ := by
  rw [
    (nodeChildRootBoundaryBranchConstraintMap
      (n := n) (a := a) cs i).map_add,
    hδ]
  simp

theorem rootBoundaryChildMessageSumAt_single_selected_self
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (rd : RawNormal.RootFieldDomain n (RTree.node b ds))
    (shift : ZMod n) :
    rootBoundaryChildMessageSumAt (n := n) (b := b) ds j
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
          (rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := b) ds j rootCoord rd shift)
          (1 : F2))
        rd shift = 1 := by
  classical
  rw [rootBoundaryChildMessageSumAt_eq_selected]
  rw [Fintype.sum_eq_single rootCoord]
  · simp
  · intro rootCoord' hne
    have hselected_ne :
        rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := b) ds j rootCoord' rd shift ≠
          rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := b) ds j rootCoord rd shift := by
      intro hselected
      have hparts :=
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord' rd shift
          (rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := b) ds j rootCoord rd shift)).1 hselected
      exact hne hparts.1
    simp [Pi.single_eq_of_ne hselected_ne]

theorem rootBoundaryChildMessageSumAt_single_selected_comm
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (rd : RawNormal.RootFieldDomain n (RTree.node b ds))
    (s t : ZMod n) :
    rootBoundaryChildMessageSumAt (n := n) (b := b) ds j
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
          (rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := b) ds j rootCoord rd s)
          (1 : F2))
        rd t =
      rootBoundaryChildMessageSumAt (n := n) (b := b) ds j
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
          (rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := b) ds j rootCoord rd t)
          (1 : F2))
        rd s := by
  classical
  rw [rootBoundaryChildMessageSumAt_eq_selected]
  rw [rootBoundaryChildMessageSumAt_eq_selected]
  refine Finset.sum_congr rfl ?_
  intro rootCoord' _hrootCoord'
  let ds0 := rootBoundarySelectedNodeChildRootFieldDomain
    (n := n) (b := b) ds j rootCoord rd s
  let dt0 := rootBoundarySelectedNodeChildRootFieldDomain
    (n := n) (b := b) ds j rootCoord rd t
  let xs := rootBoundarySelectedNodeChildRootFieldDomain
    (n := n) (b := b) ds j rootCoord' rd s
  let xt := rootBoundarySelectedNodeChildRootFieldDomain
    (n := n) (b := b) ds j rootCoord' rd t
  have hswap : xt = ds0 ↔ xs = dt0 := by
    constructor
    · intro h
      have hxt :=
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord' rd t ds0).1 h
      have hds :=
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord rd s ds0).1 rfl
      have hdt :=
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord rd t dt0).1 rfl
      refine
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord' rd s dt0).2 ?_
      refine ⟨hxt.1, ?_, hxt.2.2⟩
      exact (hds.2.1.trans hxt.2.1.symm).trans hdt.2.1
    · intro h
      have hxs :=
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord' rd s dt0).1 h
      have hds :=
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord rd s ds0).1 rfl
      have hdt :=
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord rd t dt0).1 rfl
      refine
        (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
          (n := n) (b := b) ds j rootCoord' rd t ds0).2 ?_
      refine ⟨hxs.1, ?_, hxs.2.2⟩
      exact (hdt.2.1.trans hxs.2.1.symm).trans hds.2.1
  by_cases hxt : xt = ds0
  · have hxs : xs = dt0 := hswap.1 hxt
    change
      Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
          ds0 (1 : F2) xt =
        Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
          dt0 (1 : F2) xs
    rw [hxt, hxs]
    simp
  · have hxs : xs ≠ dt0 := by
      intro h
      exact hxt (hswap.2 h)
    simp [ds0, dt0, xs, xt, hxt, hxs]

@[simp] theorem rootBoundaryChildMessageSumAt_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (rd : RawNormal.RootFieldDomain n (RTree.node b ds))
    (shift : ZMod n) :
    rootBoundaryChildMessageSumAt (n := n) (b := b) ds j
        (0 : RawNormal.NodeChildRootFieldDomain n b ds j → F2)
        rd shift = 0 := by
  simp [rootBoundaryChildMessageSumAt]

abbrev BranchSingletonConstraintVisibleAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i) : Prop :=
  nodeChildRootBoundaryBranchConstraintMap (n := n) (a := a) cs i
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2)) ≠ 0

abbrev BranchSingletonConstraintInvisibleAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i) : Prop :=
  nodeChildRootBoundaryBranchConstraintMap (n := n) (a := a) cs i
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2)) = 0

abbrev BoundarySingletonVisibleAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (R : RawNormal.NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i) : Prop :=
  childBoundaryLinearFormAt (n := n) (a := a) cs R i
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2)) = 1

theorem exists_boundarySingletonVisibleAt_of_childBoundaryLinearFormAt_ne_zero
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : RawNormal.NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs)
    (hnonzero :
      childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0) :
    ∃ d : RawNormal.NodeChildRootFieldDomain n a cs i,
      BoundarySingletonVisibleAt (n := n) (a := a) cs R i d :=
  exists_single_childBoundaryLinearFormAt_eq_one_of_ne_zero
    (n := n) (a := a) cs R i hnonzero

theorem exists_boundary_and_branchSingletonVisibleAt_odd_fiber
    {n a : Nat} [NeZero n] {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C)
    (R : RawNormal.NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs)
    (hodd :
      Odd
        (n ^
          (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)))
    (hnonzero :
      childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0) :
    ∃ d : RawNormal.NodeChildRootFieldDomain n a cs i,
      BoundarySingletonVisibleAt (n := n) (a := a) cs R i d ∧
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d := by
  exact
    exists_single_childBoundaryLinearFormAt_eq_one_and_branchConstraintMap_ne_zero_odd_fiberCard
      (n := n) (b := a) cs R i
      (childRootAtAsNonRootInNode_weight_pos_of_childCert
        (b := a) (ds := cs) hchildren i)
      hodd hnonzero

abbrev OddFiberBoundaryBranchSingletonCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          ∃ d : RawNormal.NodeChildRootFieldDomain n a cs i,
            BoundarySingletonVisibleAt (n := n) (a := a) cs R i d ∧
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d

theorem oddFiberBoundaryBranchSingletonCore_proved :
    OddFiberBoundaryBranchSingletonCoreRule := by
  intro a cs _ha hchildren n _ _hn R i hodd hnonzero
  exact
    exists_boundary_and_branchSingletonVisibleAt_odd_fiber
      (n := n) (a := a) (cs := cs) hchildren R i hodd hnonzero

abbrev EvenHeavyBoundaryBranchSingletonCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      Even n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        1 < NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) →
        childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0 →
          ∃ d : RawNormal.NodeChildRootFieldDomain n a cs i,
            BoundarySingletonVisibleAt (n := n) (a := a) cs R i d ∧
              ((∀ b : Nat, childAt cs i ≠ RTree.node b []) →
                BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d)

theorem sum_fiber_single_rootBoundarySelectedNodeChildRootFieldDomain
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (d : RawNormal.NodeChildRootFieldDomain n b ds j)
    (c : NonRootContext n (RTree.node b ds)
      (RawNormal.childRootAtAsNonRootInNode (a := b) j))
    (t : ZMod n) :
    (∑ x : { x : Fin (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := b) j)) → ZMod n //
          RawLinearAlgebra.diagSum
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := b) j)) n x = t },
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
        d (1 : F2))
        (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := b) ds j c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node b ds)
            (RawNormal.childRootAtAsNonRootInNode (a := b) j) c x.1)
          0)) =
      Fintype.card
          { x : Fin (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := b) j)) → ZMod n //
            RawLinearAlgebra.diagSum
              (NonRootVertex.weight
                (RawNormal.childRootAtAsNonRootInNode (a := b) j)) n x = t } •
        (if c.1 = d.rootCoord ∧ t = d.diagonal ∧
            ∀ (u : RawNormal.OtherNonRootVertex (RTree.node b ds)
                  (RawNormal.childRootAtAsNonRootInNode (a := b) j))
              (k : Fin (NonRootVertex.weight u.1)),
              c.2 u k = d.otherCoord u k
          then (1 : F2) else 0) := by
  classical
  let v := RawNormal.childRootAtAsNonRootInNode (a := b) j
  let α :=
    { x : Fin (NonRootVertex.weight v) → ZMod n //
      RawLinearAlgebra.diagSum (NonRootVertex.weight v) n x = t }
  let value : F2 :=
    if c.1 = d.rootCoord ∧ t = d.diagonal ∧
        ∀ (u : RawNormal.OtherNonRootVertex (RTree.node b ds) v)
          (k : Fin (NonRootVertex.weight u.1)),
          c.2 u k = d.otherCoord u k
      then 1 else 0
  have hpoint :
      ∀ x : α,
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
          d (1 : F2))
          (rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := b) ds j c.1
            (rootFieldDomainOfNonRootContextTuple
              (n := n) (T := RTree.node b ds) v c x.1)
            0) = value := by
    intro x
    rw [pi_single_rootBoundarySelectedNodeChildRootFieldDomain_eq_if]
    dsimp [value, α, v] at x ⊢
    congr 1
    apply propext
    constructor
    · rintro ⟨hroot, hdiag, hother⟩
      refine ⟨hroot, ?_, ?_⟩
      · have hxself :
            rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node b ds) v c x.1 v =
              x.1 := by
          funext k
          simp [v]
        have hdiag' :
            RawLinearAlgebra.diagSum (NonRootVertex.weight v) n x.1 =
              d.diagonal := by
          simpa [hxself, v] using hdiag
        exact x.2.symm.trans hdiag'
      · intro u k
        simpa using hother u k
    · rintro ⟨hroot, hdiag, hother⟩
      refine ⟨hroot, ?_, ?_⟩
      · have hxself :
            rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node b ds) v c x.1 v =
              x.1 := by
          funext k
          simp [v]
        exact by
          simpa [hxself, v] using x.2.trans hdiag
      · intro u k
        simpa using hother u k
  calc
    (∑ x : α,
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j => F2)
        d (1 : F2))
        (rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := b) ds j c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node b ds) v c x.1)
          0)) =
        ∑ _x : α, value := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact hpoint x
    _ = Fintype.card α • value := by
          simp

theorem branchSingletonConstraintMap_eq_zero_of_even_fiberCard
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (d : RawNormal.NodeChildRootFieldDomain n b ds j)
    (hpos :
      0 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := b) j))
    (hevenFiber :
      Even
        (n ^
          (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := b) j) - 1))) :
    nonRootBranchConstraintMap (RTree.node b ds)
        (RawNormal.childRootAtAsNonRootInNode (a := b) j)
        (fun c x =>
          (Pi.single
            (M := fun _ : RawNormal.NodeChildRootFieldDomain n b ds j =>
              F2)
            d (1 : F2))
            (rootBoundarySelectedNodeChildRootFieldDomain
              (n := n) (b := b) ds j c.1
              (rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node b ds)
                (RawNormal.childRootAtAsNonRootInNode (a := b) j) c x)
              0)) = 0 := by
  classical
  funext t c
  rw [nodeChildRootBranchConstraintMap_contextTuple_apply]
  rw [sum_fiber_single_rootBoundarySelectedNodeChildRootFieldDomain
      (n := n) (b := b) ds j d c t,
    sum_fiber_single_rootBoundarySelectedNodeChildRootFieldDomain
      (n := n) (b := b) ds j d c (t + 1)]
  have hcard_t :
      Even
        (Fintype.card
          { x : Fin (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := b) j)) → ZMod n //
            RawLinearAlgebra.diagSum
              (NonRootVertex.weight
                (RawNormal.childRootAtAsNonRootInNode (a := b) j)) n x =
                t }) := by
    rw [RawLinearAlgebra.diagSum_fiber_card
      (a := NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := b) j))
      (n := n) hpos t]
    exact hevenFiber
  have hcard_succ :
      Even
        (Fintype.card
          { x : Fin (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := b) j)) → ZMod n //
            RawLinearAlgebra.diagSum
              (NonRootVertex.weight
                (RawNormal.childRootAtAsNonRootInNode (a := b) j)) n x =
                t + 1 }) := by
    rw [RawLinearAlgebra.diagSum_fiber_card
      (a := NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := b) j))
      (n := n) hpos (t + 1)]
    exact hevenFiber
  rw [RawLinearAlgebra.nsmul_eq_zero_of_even_module_F2 hcard_t]
  rw [RawLinearAlgebra.nsmul_eq_zero_of_even_module_F2 hcard_succ]
  simp

theorem branchSingletonConstraintInvisibleAt_of_even_fiberCard
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hpos :
      0 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := a) i))
    (hevenFiber :
      Even
        (n ^
          (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1))) :
    BranchSingletonConstraintInvisibleAt (n := n) (a := a) cs i d :=
  branchSingletonConstraintMap_eq_zero_of_even_fiberCard
    (n := n) (b := a) cs i d hpos hevenFiber

theorem not_branchSingletonConstraintVisibleAt_of_even_fiberCard
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hpos :
      0 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := a) i))
    (hevenFiber :
      Even
        (n ^
          (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1))) :
    ¬ BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d := by
  intro hvisible
  exact hvisible
    (branchSingletonConstraintMap_eq_zero_of_even_fiberCard
      (n := n) (b := a) cs i d hpos hevenFiber)

theorem not_branchSingletonConstraintVisibleAt_of_even_modulus_heavy
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (heven : Even n)
    (hweight :
      1 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := a) i)) :
    ¬ BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d := by
  exact
    not_branchSingletonConstraintVisibleAt_of_even_fiberCard
      (n := n) (a := a) (cs := cs) i d
      (by omega)
      (by
        rw [Nat.even_pow]
        exact ⟨heven, by omega⟩)

theorem branchSingletonConstraintInvisibleAt_of_even_modulus_heavy
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (heven : Even n)
    (hweight :
      1 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := a) i)) :
    BranchSingletonConstraintInvisibleAt (n := n) (a := a) cs i d := by
  exact
    branchSingletonConstraintInvisibleAt_of_even_fiberCard
      (n := n) (a := a) (cs := cs) i d
      (by omega)
      (by
        rw [Nat.even_pow]
        exact ⟨heven, by omega⟩)

theorem evenHeavyBoundaryBranchSingletonCore_no_nonleaf_nonzero
    (hrule : EvenHeavyBoundaryBranchSingletonCoreRule)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a)
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C)
    (n : Nat) [NeZero n]
    (hn : 1 < n)
    (heven : Even n)
    (R : RawNormal.NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs)
    (hweight :
      1 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := a) i))
    (hnonleaf : ∀ b : Nat, childAt cs i ≠ RTree.node b [])
    (hnonzero :
      childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0) :
    False := by
  rcases hrule ha hchildren n hn heven R i hweight hnonzero with
    ⟨d, _hboundary, hbranch_if_nonleaf⟩
  exact
    not_branchSingletonConstraintVisibleAt_of_even_modulus_heavy
      (n := n) (a := a) (cs := cs) i d heven hweight
      (hbranch_if_nonleaf hnonleaf)

theorem childBoundaryLinearFormAt_singleton_heavy_edge_child_n_two_ne_zero :
    ∃ R : RawNormal.NodeRootFieldAssignment 2 1
        [RTree.node 2 [RTree.node 1 []]],
      childBoundaryLinearFormAt (n := 2) (a := 1)
        [RTree.node 2 [RTree.node 1 []]] R
        (0 : ChildIdx [RTree.node 2 [RTree.node 1 []]]) ≠ 0 := by
  classical
  let cs : List RTree := [RTree.node 2 [RTree.node 1 []]]
  let i : ChildIdx cs := 0
  let rd : RawNormal.RootFieldDomain 2 (RTree.node 1 cs) := fun _ _ => 0
  let R : RawNormal.NodeRootFieldAssignment 2 1 cs :=
    Pi.single rd (1 : F2)
  let d : RawNormal.NodeChildRootFieldDomain 2 1 cs i :=
    rootBoundarySelectedNodeChildRootFieldDomain
      (n := 2) (b := 1) cs i (fun _ => 0) rd 0
  refine ⟨R, ?_⟩
  change childBoundaryLinearFormAt (n := 2) (a := 1) cs R i ≠ 0
  have hone :
      childBoundaryLinearFormAt (n := 2) (a := 1) cs R i
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain 2 1 cs i => F2)
          d 1) = 1 := by
    dsimp [R]
    rw [childBoundaryLinearFormAt_pi_single_eq_messageSums]
    rw [rootBoundaryChildMessageSumAt_eq_selected]
    rw [rootBoundaryChildMessageSumAt_eq_selected]
    have hrootCoord_unique :
        ∀ rootCoord : Fin ((RTree.node 1 cs).rootWeight - 1) → ZMod 2,
          rootCoord = fun _ => 0 := by
      intro rootCoord
      funext k
      fin_cases k
    have hsum0 :
        (∑ rootCoord :
          Fin ((RTree.node 1 cs).rootWeight - 1) → ZMod 2,
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain 2 1 cs i => F2)
            d 1
            (rootBoundarySelectedNodeChildRootFieldDomain
              (n := 2) (b := 1) cs i rootCoord rd 0)) = 1 := by
      rw [Fintype.sum_eq_single
        (fun _ : Fin ((RTree.node 1 cs).rootWeight - 1) =>
          (0 : ZMod 2))]
      · dsimp [d]
        simp
      · intro rootCoord hne
        exact False.elim (hne (hrootCoord_unique rootCoord))
    have hsum1 :
        (∑ rootCoord :
          Fin ((RTree.node 1 cs).rootWeight - 1) → ZMod 2,
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain 2 1 cs i => F2)
            d 1
            (rootBoundarySelectedNodeChildRootFieldDomain
              (n := 2) (b := 1) cs i rootCoord rd 1)) = 0 := by
      rw [Fintype.sum_eq_single
        (fun _ : Fin ((RTree.node 1 cs).rootWeight - 1) =>
          (0 : ZMod 2))]
      · have hne :
            rootBoundarySelectedNodeChildRootFieldDomain
                (n := 2) (b := 1) cs i (fun _ => 0) rd 1 ≠
              rootBoundarySelectedNodeChildRootFieldDomain
                (n := 2) (b := 1) cs i (fun _ => 0) rd 0 := by
          intro h
          have hparts1 :=
            (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
              (n := 2) (b := 1) cs i (fun _ => 0) rd (1 : ZMod 2)
              (rootBoundarySelectedNodeChildRootFieldDomain
                (n := 2) (b := 1) cs i
                (fun _ => 0) rd 0)).1 h
          rcases hparts1 with ⟨_, hdiag1, _⟩
          have hparts0 :=
            (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
              (n := 2) (b := 1) cs i (fun _ => 0) rd (0 : ZMod 2)
              (rootBoundarySelectedNodeChildRootFieldDomain
                (n := 2) (b := 1) cs i
                (fun _ => 0) rd 0)).1 rfl
          rcases hparts0 with ⟨_, hdiag0, _⟩
          rw [← hdiag0] at hdiag1
          simp [rd] at hdiag1
        dsimp [d]
        simp [Pi.single_eq_of_ne hne]
      · intro rootCoord hne
        exact False.elim (hne (hrootCoord_unique rootCoord))
    rw [hsum0, hsum1]
    simp
  intro hzero
  have hlinzero :
      childBoundaryLinearFormAt (n := 2) (a := 1) cs R i
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain 2 1 cs i => F2)
          d 1) = 0 := by
    rw [hzero]
    rfl
  rw [hone] at hlinzero
  exact one_ne_zero hlinzero

theorem not_evenHeavyBoundaryBranchSingletonCoreRule :
    ¬ EvenHeavyBoundaryBranchSingletonCoreRule := by
  intro hrule
  rcases childBoundaryLinearFormAt_singleton_heavy_edge_child_n_two_ne_zero with
    ⟨R, hnonzero⟩
  let cs : List RTree := [RTree.node 2 [RTree.node 1 []]]
  let i : ChildIdx cs := 0
  have hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C := by
    intro C hC
    have hCeq : C = RTree.node 2 [RTree.node 1 []] := by
      simpa [cs] using hC
    rw [hCeq]
    exact RawExpandedOpenRootSubtreeCert.edge (by norm_num) (by norm_num)
  have hweight :
      1 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := 1) i) := by
    dsimp [i, cs]
    rw [RawNormal.childRootAtAsNonRootInNode_weight]
    norm_num [childAt, RTree.rootWeight]
  have hnonleaf : ∀ b : Nat, childAt cs i ≠ RTree.node b [] := by
    intro b h
    dsimp [i, cs] at h
    simp [childAt] at h
  exact
    evenHeavyBoundaryBranchSingletonCore_no_nonleaf_nonzero
      hrule (ha := by norm_num) hchildren (n := 2) (hn := by norm_num)
      (heven := by norm_num) R i hweight hnonleaf hnonzero

theorem f2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_apply_eq_one_of_ne_zero
    {α : Type} (f : α → F2) (hf : f ≠ 0) :
    ∃ a : α, f a = 1 := by
  classical
  by_contra h
  apply hf
  funext a
  rcases f2_eq_zero_or_one (f a) with hzero | hone
  · exact hzero
  · exact False.elim (h ⟨a, hone⟩)

theorem exists_apply₂_eq_one_of_ne_zero
    {α : Type} {β : α → Type}
    (f : (a : α) → β a → F2) (hf : f ≠ 0) :
    ∃ a : α, ∃ b : β a, f a b = 1 := by
  classical
  by_contra h
  apply hf
  funext a b
  rcases f2_eq_zero_or_one (f a b) with hzero | hone
  · exact hzero
  · exact False.elim (h ⟨a, b, hone⟩)

theorem exists_eq_one_of_sum_univ_eq_one
    {α : Type} [Fintype α] (f : α → F2)
    (h : (∑ x : α, f x) = 1) :
    ∃ x : α, f x = 1 := by
  classical
  by_contra hnone
  have hzero : ∀ x : α, f x = 0 := by
    intro x
    rcases f2_eq_zero_or_one (f x) with hx | hx
    · exact hx
    · exact False.elim (hnone ⟨x, hx⟩)
  have hsum : (∑ x : α, f x) = 0 := by
    simp [hzero]
  rw [hsum] at h
  exact zero_ne_one h

theorem f2_eq_one_or_eq_one_of_add_eq_one
    {x y : F2} (h : x + y = 1) :
    x = 1 ∨ y = 1 := by
  rcases f2_eq_zero_or_one x with hx | hx <;>
    rcases f2_eq_zero_or_one y with hy | hy <;>
    simp [hx, hy] at h ⊢

theorem branchSingletonConstraintVisibleAt_exists_apply_eq_one
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hvisible :
      BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d) :
    ∃ t : ZMod n,
      ∃ c : NonRootContext n (RTree.node a cs)
          (RawNormal.childRootAtAsNonRootInNode (a := a) i),
        nonRootBranchConstraintMap (RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i)
            (fun c x =>
              (Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2))
                (rootBoundarySelectedNodeChildRootFieldDomain
                  (n := n) (b := a) cs i c.1
                  (rootFieldDomainOfNonRootContextTuple
                    (n := n) (T := RTree.node a cs)
                    (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
                  0)) t c = 1 := by
  exact
    exists_apply₂_eq_one_of_ne_zero
      (fun t c =>
        nonRootBranchConstraintMap (RTree.node a cs)
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)
          (fun c x =>
            (Pi.single
              (M := fun _ :
                RawNormal.NodeChildRootFieldDomain n a cs i => F2)
              d (1 : F2))
              (rootBoundarySelectedNodeChildRootFieldDomain
                (n := n) (b := a) cs i c.1
                (rootFieldDomainOfNonRootContextTuple
                  (n := n) (T := RTree.node a cs)
                  (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
                0)) t c)
      hvisible

theorem branchSingletonConstraintVisibleAt_exists_selected_eq
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hvisible :
      BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d) :
    ∃ c : NonRootContext n (RTree.node a cs)
        (RawNormal.childRootAtAsNonRootInNode (a := a) i),
      ∃ x :
        Fin (NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n,
        rootBoundarySelectedNodeChildRootFieldDomain
          (n := n) (b := a) cs i c.1
          (rootFieldDomainOfNonRootContextTuple
            (n := n) (T := RTree.node a cs)
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
          0 = d := by
  classical
  rcases branchSingletonConstraintVisibleAt_exists_apply_eq_one
      (n := n) (a := a) (cs := cs) i d hvisible with
    ⟨t, c, htc⟩
  have hmap :=
    nodeChildRootBranchConstraintMap_contextTuple_apply
      (n := n) (b := a) cs i
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2)) t c
  rw [htc] at hmap
  have hsums := hmap.symm
  rcases f2_eq_one_or_eq_one_of_add_eq_one hsums with hleft | hright
  · rcases exists_eq_one_of_sum_univ_eq_one _ hleft with ⟨x, hx⟩
    refine ⟨c, x.1, ?_⟩
    by_contra hne
    have hzero :
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
          (rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := a) cs i c.1
            (rootFieldDomainOfNonRootContextTuple
              (n := n) (T := RTree.node a cs)
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x.1)
            0) = 0 := by
      simp [Pi.single_eq_of_ne hne]
    rw [hzero] at hx
    exact zero_ne_one hx
  · rcases exists_eq_one_of_sum_univ_eq_one _ hright with ⟨x, hx⟩
    refine ⟨c, x.1, ?_⟩
    by_contra hne
    have hzero :
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
          (rootBoundarySelectedNodeChildRootFieldDomain
            (n := n) (b := a) cs i c.1
            (rootFieldDomainOfNonRootContextTuple
              (n := n) (T := RTree.node a cs)
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x.1)
            0) = 0 := by
      simp [Pi.single_eq_of_ne hne]
    rw [hzero] at hx
    exact zero_ne_one hx

theorem branchSingletonConstraintVisibleAt_exists_selected_decompose
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hvisible :
      BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d) :
    ∃ c : NonRootContext n (RTree.node a cs)
        (RawNormal.childRootAtAsNonRootInNode (a := a) i),
      ∃ x :
        Fin (NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n,
        nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d =
          nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i
            (rootBoundarySelectedNodeChildRootFieldDomain
              (n := n) (b := a) cs i c.1
              (rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
              0) := by
  rcases branchSingletonConstraintVisibleAt_exists_selected_eq
      (n := n) (a := a) (cs := cs) i d hvisible with
    ⟨c, x, hselected⟩
  refine ⟨c, x, ?_⟩
  rw [hselected]

theorem branchSingletonConstraintVisibleAt_exists_selected_components
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hvisible :
      BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d) :
    ∃ c : NonRootContext n (RTree.node a cs)
        (RawNormal.childRootAtAsNonRootInNode (a := a) i),
      ∃ x :
        Fin (NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n,
        c.1 = d.rootCoord ∧
          RawLinearAlgebra.diagSum
              (NonRootVertex.weight
                (RawNormal.childRootAtAsNonRootInNode (a := a) i))
              n x = d.diagonal ∧
          ∀ (u : RawNormal.OtherNonRootVertex (RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i))
            (k : Fin (NonRootVertex.weight u.1)),
            rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x
                u.1 k =
              d.otherCoord u k := by
  rcases branchSingletonConstraintVisibleAt_exists_selected_eq
      (n := n) (a := a) (cs := cs) i d hvisible with
    ⟨c, x, hselected⟩
  refine ⟨c, x, ?_⟩
  have hcomponents :=
    (rootBoundarySelectedNodeChildRootFieldDomain_eq_iff
      (n := n) (b := a) cs i c.1
      (rootFieldDomainOfNonRootContextTuple
        (n := n) (T := RTree.node a cs)
        (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x)
      (0 : ZMod n) d).1 hselected
  rcases hcomponents with ⟨hroot, hdiag, hother⟩
  refine ⟨hroot, ?_, hother⟩
  have hchildRootTuple :
      rootFieldDomainOfNonRootContextTuple
          (n := n) (T := RTree.node a cs)
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) =
        x := by
    funext k
    simp
  simpa [hchildRootTuple] using hdiag

theorem branchSingletonConstraintVisibleAt_exists_structured_components
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hvisible :
      BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d) :
    ∃ c : NonRootContext n (RTree.node a cs)
        (RawNormal.childRootAtAsNonRootInNode (a := a) i),
      ∃ x :
        Fin (NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)) → ZMod n,
        (nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1.rootCoord = c.1 ∧
          (nodeChildRootFieldDomainStructuredEquiv
              (n := n) (a := a) (cs := cs) i d).1.childRootDiagonal =
            RawLinearAlgebra.diagSum
              (NonRootVertex.weight
                (RawNormal.childRootAtAsNonRootInNode (a := a) i))
              n x ∧
          (∀ (p : ChildSiblingVertex cs i)
              (k : Fin (Vertex.weight p.1.2)),
            (nodeChildRootFieldDomainStructuredEquiv
                (n := n) (a := a) (cs := cs) i d).1.siblingCoord p k =
              rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x
                (childSiblingVertexAsOtherRoot (a := a) i p).1
                (by
                  simpa [childSiblingVertexAsOtherRoot_weight] using k)) ∧
          ∀ (v : NonRootVertex (childAt cs i))
              (k : Fin (NonRootVertex.weight v)),
            (nodeChildRootFieldDomainStructuredEquiv
                (n := n) (a := a) (cs := cs) i d).2 v k =
              rootFieldDomainOfNonRootContextTuple
                (n := n) (T := RTree.node a cs)
                (RawNormal.childRootAtAsNonRootInNode (a := a) i) c x
                (childNonRootVertexAsOtherRoot (a := a) i v).1
                (by
                  simpa [childNonRootVertexAsOtherRoot_weight] using k) := by
  rcases branchSingletonConstraintVisibleAt_exists_selected_components
      (n := n) (a := a) (cs := cs) i d hvisible with
    ⟨c, x, hroot, hdiag, hother⟩
  refine ⟨c, x, ?_, ?_, ?_, ?_⟩
  · simpa [nodeChildRootFieldDomainStructuredEquiv] using hroot.symm
  · simpa [nodeChildRootFieldDomainStructuredEquiv] using hdiag.symm
  · intro p k
    have h :=
      hother (childSiblingVertexAsOtherRoot (a := a) i p)
        (by simpa [childSiblingVertexAsOtherRoot_weight] using k)
    simpa [nodeChildRootFieldDomainStructuredEquiv] using h.symm
  · intro v k
    have h :=
      hother (childNonRootVertexAsOtherRoot (a := a) i v)
        (by simpa [childNonRootVertexAsOtherRoot_weight] using k)
    simpa [nodeChildRootFieldDomainStructuredEquiv] using h.symm

abbrev InternalKernelSingletonShiftInvariantAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i) : Prop :=
  ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
    childOpenRootInternalKernelAt (n := n) (a := a) cs i
        (φ +
          Pi.single
            (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
            d (1 : F2)) =
      childOpenRootInternalKernelAt (n := n) (a := a) cs i φ

abbrev BranchConstraintKernelShiftInvariantLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 →
        ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
          childOpenRootInternalKernelAt
              (n := n) (a := a) cs i (φ + δ) =
            childOpenRootInternalKernelAt (n := n) (a := a) cs i φ

abbrev BranchConstraintImageKernelDependsLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i φ =
        nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ →
        childOpenRootInternalKernelAt
            (n := n) (a := a) cs i φ =
          childOpenRootInternalKernelAt
            (n := n) (a := a) cs i ψ

abbrev BranchConstraintImageKernelDependsCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i φ =
          nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i ψ →
          childOpenRootInternalKernelAt
              (n := n) (a := a) cs i φ =
            childOpenRootInternalKernelAt
              (n := n) (a := a) cs i ψ

theorem branchConstraintKernelShiftInvariantLocalRule_of_imageKernelDepends
    (hdepends : BranchConstraintImageKernelDependsLocalRule) :
    BranchConstraintKernelShiftInvariantLocalRule := by
  intro n a _ cs i δ hδ φ
  exact
    hdepends (n := n) (a := a) (cs := cs) i (φ + δ) φ
      (nodeChildRootBoundaryBranchConstraintMap_add_eq_left_of_right_eq_zero
        (n := n) (a := a) (cs := cs) i φ δ hδ)

theorem branchConstraintImageKernelDependsLocalRule_of_kernelShiftInvariant
    (hkernel : BranchConstraintKernelShiftInvariantLocalRule) :
    BranchConstraintImageKernelDependsLocalRule := by
  intro n a _ cs i φ ψ hmap
  let δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2 := φ + ψ
  have hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 := by
    rw [show δ = φ + ψ by rfl]
    rw [
      (nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i).map_add,
      hmap]
    ext t c
    exact
      add_self_eq_zero_of_module_F2
        ((nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) t c)
  have hshift :=
    hkernel (n := n) (a := a) (cs := cs) i δ hδ ψ
  have hsum :
      ψ + δ = φ := by
    funext d
    calc
      ψ d + δ d = ψ d + (φ d + ψ d) := rfl
      _ = φ d + (ψ d + ψ d) := by ac_rfl
      _ = φ d + 0 := by
        rw [add_self_eq_zero_of_module_F2 (ψ d)]
      _ = φ d := by simp
  simpa [hsum] using hshift

theorem branchConstraintImageKernelDependsLocalRule_iff_kernelShiftInvariant :
    BranchConstraintImageKernelDependsLocalRule ↔
      BranchConstraintKernelShiftInvariantLocalRule :=
  ⟨branchConstraintKernelShiftInvariantLocalRule_of_imageKernelDepends,
    branchConstraintImageKernelDependsLocalRule_of_kernelShiftInvariant⟩

abbrev BranchConstraintKernelShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
            childOpenRootInternalKernelAt
                (n := n) (a := a) cs i (φ + δ) =
              childOpenRootInternalKernelAt
                (n := n) (a := a) cs i φ

theorem branchConstraintKernelShiftInvariantCoreRule_of_imageKernelDependsCore
    (hdepends : BranchConstraintImageKernelDependsCoreRule) :
    BranchConstraintKernelShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ φ
  exact
    hdepends ha hchildren n hn i (φ + δ) φ
      (nodeChildRootBoundaryBranchConstraintMap_add_eq_left_of_right_eq_zero
        (n := n) (a := a) (cs := cs) i φ δ hδ)

theorem branchConstraintImageKernelDependsCoreRule_of_kernelShiftInvariantCore
    (hkernel : BranchConstraintKernelShiftInvariantCoreRule) :
    BranchConstraintImageKernelDependsCoreRule := by
  intro a cs ha hchildren n _ hn i φ ψ hmap
  let δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2 := φ + ψ
  have hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 := by
    rw [show δ = φ + ψ by rfl]
    rw [
      (nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i).map_add,
      hmap]
    ext t c
    exact
      add_self_eq_zero_of_module_F2
        ((nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) t c)
  have hshift :=
    hkernel ha hchildren n hn i δ hδ ψ
  have hsum :
      ψ + δ = φ := by
    funext d
    calc
      ψ d + δ d = ψ d + (φ d + ψ d) := rfl
      _ = φ d + (ψ d + ψ d) := by ac_rfl
      _ = φ d + 0 := by
        rw [add_self_eq_zero_of_module_F2 (ψ d)]
      _ = φ d := by simp
  simpa [hsum] using hshift

theorem branchConstraintImageKernelDependsCoreRule_iff_kernelShiftInvariantCore :
    BranchConstraintImageKernelDependsCoreRule ↔
      BranchConstraintKernelShiftInvariantCoreRule :=
  ⟨branchConstraintKernelShiftInvariantCoreRule_of_imageKernelDependsCore,
    branchConstraintImageKernelDependsCoreRule_of_kernelShiftInvariantCore⟩

theorem branchConstraintKernelShiftInvariantCoreRule_of_local
    (hlocal : BranchConstraintKernelShiftInvariantLocalRule) :
    BranchConstraintKernelShiftInvariantCoreRule := by
  intro a cs _ha _hchildren n _ _hn i δ hδ φ
  exact hlocal (n := n) (a := a) (cs := cs) i δ hδ φ

theorem branchConstraintImageKernelDependsCoreRule_of_local
    (hlocal : BranchConstraintImageKernelDependsLocalRule) :
    BranchConstraintImageKernelDependsCoreRule := by
  intro a cs _ha _hchildren n _ _hn i φ ψ hmap
  exact hlocal (n := n) (a := a) (cs := cs) i φ ψ hmap

theorem branchConstraintImageKernelDependsAt_of_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childOpenRootInternalKernelAt
        (n := n) (a := a) cs i φ =
      childOpenRootInternalKernelAt
        (n := n) (a := a) cs i ψ := by
  rw [
    childOpenRootInternalKernelAt_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild φ,
    childOpenRootInternalKernelAt_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild ψ]

theorem branchConstraintKernelShiftInvariantAt_of_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
      childOpenRootInternalKernelAt
          (n := n) (a := a) cs i (φ + δ) =
        childOpenRootInternalKernelAt
          (n := n) (a := a) cs i φ := by
  intro φ
  exact
    branchConstraintImageKernelDependsAt_of_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild (φ + δ) φ

abbrev BranchInvisibleSingletonShiftInvariantLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i),
      BranchSingletonConstraintInvisibleAt (n := n) (a := a) cs i d →
        InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d

theorem branchInvisibleSingletonShiftInvariantLocalRule_of_branchConstraintKernelShiftInvariant
    (hkernel : BranchConstraintKernelShiftInvariantLocalRule) :
    BranchInvisibleSingletonShiftInvariantLocalRule := by
  intro n a _ cs i d hinvisible φ
  exact
    hkernel (n := n) (a := a) (cs := cs) i
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2))
      hinvisible φ

theorem branchInvisibleSingletonShiftInvariantLocalRule_of_imageKernelDepends
    (hdepends : BranchConstraintImageKernelDependsLocalRule) :
    BranchInvisibleSingletonShiftInvariantLocalRule :=
  branchInvisibleSingletonShiftInvariantLocalRule_of_branchConstraintKernelShiftInvariant
    (branchConstraintKernelShiftInvariantLocalRule_of_imageKernelDepends
      hdepends)

theorem evenHeavyVisibleWitnessCore_of_branchInvisibleSingletonShiftInvariantLocal
    (hinv : BranchInvisibleSingletonShiftInvariantLocalRule) :
    EvenHeavyVisibleWitnessCoreRule := by
  intro a cs _ha _hchildren n _ _hn heven R i hweight hnonzero
  rcases
      exists_boundarySingletonVisibleAt_of_childBoundaryLinearFormAt_ne_zero
        (n := n) (a := a) (cs := cs) R i hnonzero with
    ⟨d, hboundary⟩
  refine ⟨d, hboundary, ?_⟩
  exact
    hinv (n := n) (a := a) (cs := cs) i d
      (branchSingletonConstraintInvisibleAt_of_even_modulus_heavy
        (n := n) (a := a) (cs := cs) i d heven hweight)

theorem evenHeavyVisibleWitnessCore_of_branchConstraintImageKernelDependsCore
    (hdepends : BranchConstraintImageKernelDependsCoreRule) :
    EvenHeavyVisibleWitnessCoreRule := by
  intro a cs ha hchildren n _ hn heven R i hweight hnonzero
  rcases
      exists_boundarySingletonVisibleAt_of_childBoundaryLinearFormAt_ne_zero
        (n := n) (a := a) (cs := cs) R i hnonzero with
    ⟨d, hboundary⟩
  refine ⟨d, hboundary, ?_⟩
  intro φ
  exact
    hdepends ha hchildren n hn i
      (φ +
        Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
      φ
      (nodeChildRootBoundaryBranchConstraintMap_add_eq_left_of_right_eq_zero
        (n := n) (a := a) (cs := cs) i φ
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
        (branchSingletonConstraintInvisibleAt_of_even_modulus_heavy
          (n := n) (a := a) (cs := cs) i d heven hweight))

theorem evenHeavyVisibleWitnessCore_of_branchConstraintKernelShiftInvariantCore
    (hkernel : BranchConstraintKernelShiftInvariantCoreRule) :
    EvenHeavyVisibleWitnessCoreRule :=
  evenHeavyVisibleWitnessCore_of_branchConstraintImageKernelDependsCore
    (branchConstraintImageKernelDependsCoreRule_of_kernelShiftInvariantCore
      hkernel)

abbrev LeafChildrenBranchSingleShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    (∀ i : ChildIdx cs, ∃ b : Nat, childAt cs i = RTree.node b []) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (_R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs)
        (d : RawNormal.NodeChildRootFieldDomain n a cs i),
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
          InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d

abbrev VerifiedShapeBranchSingleShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    VerifiedShape (RTree.node a cs) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (_R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs)
        (d : RawNormal.NodeChildRootFieldDomain n a cs i),
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
          InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d

abbrev ChildInternalNonRootFieldFamily
    (n a : Nat) [NeZero n] (cs : List RTree) (i : ChildIdx cs) :=
  (v : NonRootVertex (childAt cs i)) →
    RawNormal.NodeChildNonRootFieldDomain n a cs i v → F2

abbrev ChildExternalNodeFieldFamily
    (n a : Nat) [NeZero n] (cs : List RTree) (i : ChildIdx cs) :=
  ChildExternalCoordinate n a cs i →
    RawNormal.NodeFieldAssignment n (childAt cs i)

noncomputable def childExternalNodeFieldSingle
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0) :
    ChildExternalNodeFieldFamily n a cs i :=
  Pi.single
    (M := fun _ : ChildExternalCoordinate n a cs i =>
      RawNormal.NodeFieldAssignment n (childAt cs i))
    ext0
    (Pi.single
      (M := fun v : NonRootVertex (childAt cs i) =>
        RawNormal.NonRootFieldDomain n (childAt cs i) v → F2)
      v0
      (Pi.single
        (M := fun _ : RawNormal.NonRootFieldDomain n (childAt cs i) v0 => F2)
        d0 (1 : F2)))

@[simp] theorem childExternalNodeFieldSingle_apply_self
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0) :
    childExternalNodeFieldSingle
        (n := n) (a := a) (cs := cs) i ext0 v0 d0
        ext0 v0 d0 = 1 := by
  classical
  simp [childExternalNodeFieldSingle]

@[simp] theorem childExternalNodeFieldSingle_apply_ne_ext
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 ext : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (v : NonRootVertex (childAt cs i))
    (d : RawNormal.NonRootFieldDomain n (childAt cs i) v)
    (h : ext ≠ ext0) :
    childExternalNodeFieldSingle
        (n := n) (a := a) (cs := cs) i ext0 v0 d0
        ext v d = 0 := by
  classical
  simp [childExternalNodeFieldSingle, h]

@[simp] theorem childExternalNodeFieldSingle_apply_ne_vertex
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 v : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (d : RawNormal.NonRootFieldDomain n (childAt cs i) v)
    (h : v ≠ v0) :
    childExternalNodeFieldSingle
        (n := n) (a := a) (cs := cs) i ext0 v0 d0
        ext0 v d = 0 := by
  classical
  simp [childExternalNodeFieldSingle, h]

@[simp] theorem childExternalNodeFieldSingle_apply_ne_domain
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 d : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (h : d ≠ d0) :
    childExternalNodeFieldSingle
        (n := n) (a := a) (cs := cs) i ext0 v0 d0
        ext0 v0 d = 0 := by
  classical
  simp [childExternalNodeFieldSingle, h]

noncomputable def childExternalNodeFieldSingleToggleEquiv
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0) :
    ChildExternalNodeFieldFamily n a cs i ≃
      ChildExternalNodeFieldFamily n a cs i :=
  Equiv.addRight
    (childExternalNodeFieldSingle
      (n := n) (a := a) (cs := cs) i ext0 v0 d0)

@[simp] theorem childExternalNodeFieldSingleToggleEquiv_apply
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 ext : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (v : NonRootVertex (childAt cs i))
    (d : RawNormal.NonRootFieldDomain n (childAt cs i) v)
    (Ψ : ChildExternalNodeFieldFamily n a cs i) :
    childExternalNodeFieldSingleToggleEquiv
        (n := n) (a := a) (cs := cs) i ext0 v0 d0 Ψ ext v d =
      Ψ ext v d +
        childExternalNodeFieldSingle
          (n := n) (a := a) (cs := cs) i ext0 v0 d0 ext v d := rfl

@[simp] theorem childExternalNodeFieldSingleToggleEquiv_apply_self
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (Ψ : ChildExternalNodeFieldFamily n a cs i) :
    childExternalNodeFieldSingleToggleEquiv
        (n := n) (a := a) (cs := cs) i ext0 v0 d0 Ψ
        ext0 v0 d0 =
      Ψ ext0 v0 d0 + 1 := by
  simp

@[simp] theorem childExternalNodeFieldSingleToggleEquiv_apply_ne_ext
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 ext : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (v : NonRootVertex (childAt cs i))
    (d : RawNormal.NonRootFieldDomain n (childAt cs i) v)
    (Ψ : ChildExternalNodeFieldFamily n a cs i)
    (h : ext ≠ ext0) :
    childExternalNodeFieldSingleToggleEquiv
        (n := n) (a := a) (cs := cs) i ext0 v0 d0 Ψ
        ext v d =
      Ψ ext v d := by
  simp [h]

@[simp] theorem childExternalNodeFieldSingleToggleEquiv_apply_ne_vertex
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 v : NonRootVertex (childAt cs i))
    (d0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (d : RawNormal.NonRootFieldDomain n (childAt cs i) v)
    (Ψ : ChildExternalNodeFieldFamily n a cs i)
    (h : v ≠ v0) :
    childExternalNodeFieldSingleToggleEquiv
        (n := n) (a := a) (cs := cs) i ext0 v0 d0 Ψ
        ext0 v d =
      Ψ ext0 v d := by
  simp [h]

@[simp] theorem childExternalNodeFieldSingleToggleEquiv_apply_ne_domain
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (d0 d : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (Ψ : ChildExternalNodeFieldFamily n a cs i)
    (h : d ≠ d0) :
    childExternalNodeFieldSingleToggleEquiv
        (n := n) (a := a) (cs := cs) i ext0 v0 d0 Ψ
        ext0 v0 d =
      Ψ ext0 v0 d := by
  simp [h]

@[simp] theorem nodeChildNonRootFieldFamilyAtExternalEquiv_symm_singleToggle_self
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (nd0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (Ψ : ChildExternalNodeFieldFamily n a cs i) :
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm
        (childExternalNodeFieldSingleToggleEquiv
          (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ))
      v0
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v0).symm
        (ext0, nd0)) =
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm Ψ)
      v0
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v0).symm
        (ext0, nd0)) + 1 := by
  simp [nodeChildNonRootFieldFamilyAtExternalEquiv]

@[simp] theorem nodeChildNonRootFieldFamilyAtExternalEquiv_symm_singleToggle_ne_ext
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (ext0 ext : ChildExternalCoordinate n a cs i)
    (v0 v : NonRootVertex (childAt cs i))
    (nd0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (nd : RawNormal.NonRootFieldDomain n (childAt cs i) v)
    (Ψ : ChildExternalNodeFieldFamily n a cs i)
    (h : ext ≠ ext0) :
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm
        (childExternalNodeFieldSingleToggleEquiv
          (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ))
      v
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v).symm
        (ext, nd)) =
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm Ψ)
      v
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v).symm
        (ext, nd)) := by
  simp [nodeChildNonRootFieldFamilyAtExternalEquiv, h]

@[simp] theorem nodeChildNonRootFieldFamilyAtExternalEquiv_symm_singleToggle_ne_vertex
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 v : NonRootVertex (childAt cs i))
    (nd0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (nd : RawNormal.NonRootFieldDomain n (childAt cs i) v)
    (Ψ : ChildExternalNodeFieldFamily n a cs i)
    (h : v ≠ v0) :
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm
        (childExternalNodeFieldSingleToggleEquiv
          (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ))
      v
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v).symm
        (ext0, nd)) =
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm Ψ)
      v
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v).symm
        (ext0, nd)) := by
  simp [nodeChildNonRootFieldFamilyAtExternalEquiv, h]

@[simp] theorem nodeChildNonRootFieldFamilyAtExternalEquiv_symm_singleToggle_ne_domain
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (nd0 nd : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (Ψ : ChildExternalNodeFieldFamily n a cs i)
    (h : nd ≠ nd0) :
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm
        (childExternalNodeFieldSingleToggleEquiv
          (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ))
      v0
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v0).symm
        (ext0, nd)) =
    ((nodeChildNonRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot).symm Ψ)
      v0
      ((nodeChildNonRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i hchildRoot v0).symm
        (ext0, nd)) := by
  simp [nodeChildNonRootFieldFamilyAtExternalEquiv, h]

@[simp] theorem nodeChildRootFieldFamilyAtExternalEquiv_add_single_self
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i
        (φ +
          Pi.single
            (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
            d (1 : F2)))
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2 =
    (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i φ)
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2 + 1 := by
  classical
  simp [nodeChildRootFieldFamilyAtExternalEquiv]

theorem nodeChildRootFieldDomainStructuredEquiv_symm_pair_ne_of_ext_ne
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (ext : ChildExternalCoordinate n a cs i)
    (rd : RawNormal.RootFieldDomain n (childAt cs i))
    (h :
      ext ≠
        (nodeChildRootFieldDomainStructuredEquiv
          (n := n) (a := a) (cs := cs) i d).1) :
    (nodeChildRootFieldDomainStructuredEquiv
      (n := n) (a := a) (cs := cs) i).symm (ext, rd) ≠ d := by
  intro heq
  have hp :=
    congrArg
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i) heq
  exact h (by simpa using congrArg Prod.fst hp)

theorem nodeChildRootFieldDomainStructuredEquiv_symm_pair_ne_of_root_ne
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (ext : ChildExternalCoordinate n a cs i)
    (rd : RawNormal.RootFieldDomain n (childAt cs i))
    (h :
      rd ≠
        (nodeChildRootFieldDomainStructuredEquiv
          (n := n) (a := a) (cs := cs) i d).2) :
    (nodeChildRootFieldDomainStructuredEquiv
      (n := n) (a := a) (cs := cs) i).symm (ext, rd) ≠ d := by
  intro heq
  have hp :=
    congrArg
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i) heq
  exact h (by simpa using congrArg Prod.snd hp)

@[simp] theorem nodeChildRootFieldFamilyAtExternalEquiv_add_single_ne_ext
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (ext : ChildExternalCoordinate n a cs i)
    (rd : RawNormal.RootFieldDomain n (childAt cs i))
    (h :
      ext ≠
        (nodeChildRootFieldDomainStructuredEquiv
          (n := n) (a := a) (cs := cs) i d).1) :
    (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i
        (φ +
          Pi.single
            (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
            d (1 : F2))) ext rd =
      (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i φ) ext rd := by
  classical
  have hne :=
    nodeChildRootFieldDomainStructuredEquiv_symm_pair_ne_of_ext_ne
      (n := n) (a := a) (cs := cs) i d ext rd h
  simp [nodeChildRootFieldFamilyAtExternalEquiv, hne]

@[simp] theorem nodeChildRootFieldFamilyAtExternalEquiv_add_single_ne_root
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (ext : ChildExternalCoordinate n a cs i)
    (rd : RawNormal.RootFieldDomain n (childAt cs i))
    (h :
      rd ≠
        (nodeChildRootFieldDomainStructuredEquiv
          (n := n) (a := a) (cs := cs) i d).2) :
    (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i
        (φ +
          Pi.single
            (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
            d (1 : F2))) ext rd =
      (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i φ) ext rd := by
  classical
  have hne :=
    nodeChildRootFieldDomainStructuredEquiv_symm_pair_ne_of_root_ne
      (n := n) (a := a) (cs := cs) i d ext rd h
  simp [nodeChildRootFieldFamilyAtExternalEquiv, hne]

noncomputable def childExternalNodeFieldFamilyBaseCyclicEquiv
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) :
    ChildExternalNodeFieldFamily n a cs i ≃
      (ChildExternalBaseCoordinate n a cs i →
        ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i)) where
  toFun Ψ base d :=
    Ψ ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i).symm (base, d))
  invFun Ψ ext :=
    let bd :=
      childExternalCoordinateEquivBaseDiag
        (n := n) (a := a) (cs := cs) i ext
    Ψ bd.1 bd.2
  left_inv := by
    intro Ψ
    funext ext v nd
    cases ext
    rfl
  right_inv := by
    intro Ψ
    funext base d v nd
    cases base
    rfl

@[simp] theorem childExternalNodeFieldFamilyBaseCyclicEquiv_apply
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (Ψ : ChildExternalNodeFieldFamily n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i) (d : ZMod n)
    (v : NonRootVertex (childAt cs i))
    (nd : RawNormal.NonRootFieldDomain n (childAt cs i) v) :
    childExternalNodeFieldFamilyBaseCyclicEquiv
        (n := n) (a := a) (cs := cs) i Ψ base d v nd =
      Ψ ((childExternalCoordinateEquivBaseDiag
        (n := n) (a := a) (cs := cs) i).symm (base, d)) v nd :=
  rfl

noncomputable def fixedRootCyclicNodeFieldSum
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) : ℤ :=
  ∑ N : ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i),
    bitSign
      (cyclicRootTwistedPhaseForRootNode
        (n := n) (a := a) (cs := cs) i Rcyc N)

theorem nonRootVertex_leaf_false {b : Nat}
    (v : NonRootVertex (RTree.node b [])) : False := by
  have haddr : v.1.1 ∈ RTree.addresses (RTree.node b []) := v.1.2
  have hnil : v.1.1 = [] := by
    change v.1.1 ∈ ([[]] : List (List Nat)) at haddr
    simpa using haddr
  exact v.2 hnil

theorem fixedRootCyclicNodeFieldSum_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) :
    fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i Rcyc = 1 := by
  classical
  simp [fixedRootCyclicNodeFieldSum, cyclicRootTwistedPhaseForRootNode,
    cyclicRootTwistedPhaseForBase, hchild]
  have hprod :
      (∏ x : NonRootVertex (RTree.node b []),
        (2 : ℤ) ^
          Fintype.card (RawNormal.NonRootFieldDomain n (RTree.node b []) x)) =
        1 := by
    refine Finset.prod_eq_one ?_
    intro x _hx
    exact False.elim (nonRootVertex_leaf_false x)
  calc
    ((∏ x : NonRootVertex (RTree.node b []),
      (2 : ℤ) ^ Fintype.card
        (RawNormal.NonRootFieldDomain n (RTree.node b []) x)) ^ n) =
        (1 : ℤ) ^ n := by
          exact congrArg (fun m : ℤ => m ^ n) hprod
    _ = 1 := by
          simp

theorem fixedRootCyclicNodeFieldSum_shiftInvariant_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (R S :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i (R + S) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i R := by
  rw [
    fixedRootCyclicNodeFieldSum_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild (R + S),
    fixedRootCyclicNodeFieldSum_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild R]

theorem fixedRootCyclicNodeFieldSum_node_eq_sum_linearForm
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc =
      ∑ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        bitSign
          (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
              (fun d => castRootFieldAssignment hchild (Rcyc d)) +
            cyclicNodeInternalPhase (n := n) (b := b) ds N) := by
  classical
  unfold fixedRootCyclicNodeFieldSum
  refine Fintype.sum_equiv
    (castCyclicNodeFieldFamilyEquiv (n := n) hchild)
    (fun N : ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i) =>
      bitSign
        (cyclicRootTwistedPhaseForRootNode
          (n := n) (a := a) (cs := cs) i Rcyc N))
    (fun N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds =>
      bitSign
        (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
            (fun d => castRootFieldAssignment hchild (Rcyc d)) +
          cyclicNodeInternalPhase (n := n) (b := b) ds N))
    ?_
  intro N
  change
    bitSign
        (cyclicRootTwistedPhaseForRootNode
          (n := n) (a := a) (cs := cs) i Rcyc N) =
      bitSign
        (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
            (fun d => castNodeFieldAssignment hchild (N d))
            (fun d => castRootFieldAssignment hchild (Rcyc d)) +
          cyclicNodeInternalPhase (n := n) (b := b) ds
            (fun d => castNodeFieldAssignment hchild (N d)))
  rw [cyclicRootTwistedPhaseForRootNode_node_eq_linearForm_add_internal
    (n := n) (a := a) (b := b) (cs := cs) i hchild Rcyc N]

noncomputable def cyclicNodeFixedRootFieldSum
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) : ℤ :=
  ∑ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
    bitSign
      (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
        cyclicNodeInternalPhase (n := n) (b := b) ds N)

theorem cyclicNodeFixedRootFieldSum_eq_of_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R S : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) ≃
        (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds))
    (hphase :
      ∀ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds (e N) S +
            cyclicNodeInternalPhase (n := n) (b := b) ds (e N) =
          cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
            cyclicNodeInternalPhase (n := n) (b := b) ds N) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds S =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R := by
  classical
  unfold cyclicNodeFixedRootFieldSum
  symm
  refine
    Fintype.sum_equiv e
      (fun N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds =>
        bitSign
          (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
            cyclicNodeInternalPhase (n := n) (b := b) ds N))
      (fun N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds =>
        bitSign
          (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N S +
            cyclicNodeInternalPhase (n := n) (b := b) ds N))
      ?_
  intro N
  exact (congrArg bitSign (hphase N)).symm

theorem fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d => castRootFieldAssignment hchild (Rcyc d)) := by
  rw [fixedRootCyclicNodeFieldSum_node_eq_sum_linearForm
    (n := n) (a := a) (b := b) (cs := cs) i hchild Rcyc]
  rfl

theorem fixedRootCyclicNodeFieldSum_node_eq_of_reindex
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (R S :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (e :
      (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) ≃
        (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds))
    (hphase :
      ∀ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds (e N)
              (fun d => castRootFieldAssignment hchild (S d)) +
            cyclicNodeInternalPhase (n := n) (b := b) ds (e N) =
          cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
              (fun d => castRootFieldAssignment hchild (R d)) +
            cyclicNodeInternalPhase (n := n) (b := b) ds N) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i S =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i R := by
  rw [
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild S,
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild R]
  exact
    cyclicNodeFixedRootFieldSum_eq_of_reindex
      (n := n) (b := b) ds
      (fun d => castRootFieldAssignment hchild (R d))
      (fun d => castRootFieldAssignment hchild (S d))
      e hphase

theorem cyclicNodeFixedRootFieldSum_eq_sum_childDataFamily
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R =
      ∑ H : ZMod n → RawNormal.NodeChildDataFamily n b ds,
        bitSign
          (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
              (fun d =>
                RawNormal.nodeFieldFromChildDataFamily
                  (n := n) (a := b) (cs := ds) (H d)) R +
            cyclicNodeInternalPhase (n := n) (b := b) ds
              (fun d =>
                RawNormal.nodeFieldFromChildDataFamily
                  (n := n) (a := b) (cs := ds) (H d))) := by
  classical
  unfold cyclicNodeFixedRootFieldSum
  refine Fintype.sum_equiv
    (cyclicNodeFieldFamilyEquivChildDataFamily n b ds)
    (fun N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds =>
      bitSign
        (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
          cyclicNodeInternalPhase (n := n) (b := b) ds N))
    (fun H : ZMod n → RawNormal.NodeChildDataFamily n b ds =>
      bitSign
        (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
            (fun d =>
              RawNormal.nodeFieldFromChildDataFamily
                (n := n) (a := b) (cs := ds) (H d)) R +
          cyclicNodeInternalPhase (n := n) (b := b) ds
            (fun d =>
              RawNormal.nodeFieldFromChildDataFamily
                (n := n) (a := b) (cs := ds) (H d))))
    ?_
  intro N
  let H := cyclicNodeFieldFamilyEquivChildDataFamily n b ds N
  have hN :
      (fun d =>
        RawNormal.nodeFieldFromChildDataFamily
          (n := n) (a := b) (cs := ds) (H d)) = N := by
    funext d
    change
      (nodeChildDataFamilyEquivNodeField n b ds)
          ((cyclicNodeFieldFamilyEquivChildDataFamily n b ds) N d) =
        N d
    exact (nodeChildDataFamilyEquivNodeField n b ds).right_inv (N d)
  simp [H, hN]

theorem cyclicNodeFixedRootFieldSum_shiftInvariant_of_boundaryShift_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R S : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (hS :
      ∀ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N S = 0) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds (R + S) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R := by
  classical
  unfold cyclicNodeFixedRootFieldSum
  refine Finset.sum_congr rfl ?_
  intro N _
  have hlin :
      cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N (R + S) =
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R := by
    rw [(cyclicNodeRootBoundaryLinearForm
      (n := n) (b := b) ds N).map_add, hS N]
    simp
  rw [hlin]

theorem sum_bitSign_mul_eq_sum_of_oneFiber_sum_eq_zero
    {α : Type} [Fintype α]
    (c : α → F2) (f : α → ℤ)
    (hone : (∑ x : α, if c x = 1 then f x else 0) = 0) :
    (∑ x : α, bitSign (c x) * f x) = ∑ x : α, f x := by
  classical
  have hpoint :
      ∀ x : α,
        bitSign (c x) * f x =
          f x - 2 * (if c x = 1 then f x else 0) := by
    intro x
    have hcases : c x = 0 ∨ c x = 1 := by
      generalize hc : c x = y
      fin_cases y
      · left
        rfl
      · right
        rfl
    rcases hcases with h0 | h1
    · simp [h0]
    · simp [h1]
      ring_nf
  calc
    (∑ x : α, bitSign (c x) * f x) =
        ∑ x : α, (f x - 2 * (if c x = 1 then f x else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          exact hpoint x
    _ =
        (∑ x : α, f x) -
          2 * (∑ x : α, if c x = 1 then f x else 0) := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = ∑ x : α, f x := by
          rw [hone]
          simp

theorem cyclicNodeRootBoundaryLinearForm_add_single
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
        cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q := by
  classical
  let L := cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
  let S : ZMod n → RawNormal.NodeRootFieldAssignment n b ds :=
    fun d rd =>
      Pi.single
        (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
        q (1 : F2) (d, rd)
  change L (R + S) =
    L R + cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q
  rw [L.map_add]
  rw [cyclicNodeRootBoundaryCoefficient_apply]

theorem cyclicNodeRootBoundaryLinearForm_eq_dot_coeff
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N)
        (fun q : CyclicNodeRootBoundaryDomain n b ds => R q.1 q.2) := by
  change
    cyclicNodeRootBoundaryLinearFormProduct (n := n) (b := b) ds N
        (fun q : CyclicNodeRootBoundaryDomain n b ds => R q.1 q.2) =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N)
        (fun q : CyclicNodeRootBoundaryDomain n b ds => R q.1 q.2)
  rw [
    linearFunctional_eq_dotLinear_coeff
      (CyclicNodeRootBoundaryDomain n b ds)
      (cyclicNodeRootBoundaryLinearFormProduct (n := n) (b := b) ds N)]
  rfl

theorem cyclicNodeRootBoundaryLinearForm_eq_zero_of_forall_dot_summand_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (hzero : ∀ q : CyclicNodeRootBoundaryDomain n b ds,
      R q.1 q.2 *
        cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q = 0) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R = 0 := by
  rw [cyclicNodeRootBoundaryLinearForm_eq_dot_coeff]
  rw [dotLinear_apply]
  exact Finset.sum_eq_zero (fun q _ => hzero q)

theorem cyclicNodeRootBoundaryLinearForm_eq_zero_of_coefficient_eq_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (hcoeff :
      cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N = 0) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R = 0 := by
  have hlin :
      cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N = 0 :=
    (cyclicNodeRootBoundaryLinearForm_eq_zero_iff_coefficient
      (n := n) (b := b) ds N).2 hcoeff
  have hval := congrArg
    (fun L : (ZMod n → RawNormal.NodeRootFieldAssignment n b ds) →ₗ[F2] F2 => L R)
    hlin
  simpa using hval

theorem cyclicNodeRootBoundaryLinearForm_eq_zero_of_forall_coefficient_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (hcoeff :
      ∀ q : CyclicNodeRootBoundaryDomain n b ds,
        cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q = 0) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R = 0 := by
  exact
    cyclicNodeRootBoundaryLinearForm_eq_zero_of_coefficient_eq_zero
      (n := n) (b := b) ds N R
      ((cyclicNodeRootBoundaryCoefficient_eq_zero_iff_forall
        (n := n) (b := b) ds N).2 hcoeff)

theorem cyclicNodeRootBoundaryLinearForm_eq_zero_of_layers_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (hlayers :
      ∀ (d : ZMod n)
        (rd : RawNormal.RootFieldDomain n (RTree.node b ds)),
        cyclicNodeRootBoundaryLayer0 (n := n) (b := b) ds N d rd +
          cyclicNodeRootBoundaryLayer1 (n := n) (b := b) ds N (d - 1) rd =
            0) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R = 0 := by
  exact
    cyclicNodeRootBoundaryLinearForm_eq_zero_of_forall_coefficient_zero
      (n := n) (b := b) ds N R
      ((cyclicNodeRootBoundaryCoefficient_zero_iff_layers
        (n := n) (b := b) ds N).2 hlayers)

theorem cyclicNodeRootBoundaryLinearForm_eq_sum_layers
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R =
      ∑ q : CyclicNodeRootBoundaryDomain n b ds,
        R q.1 q.2 *
          (cyclicNodeRootBoundaryLayer0 (n := n) (b := b) ds N q.1 q.2 +
            cyclicNodeRootBoundaryLayer1 (n := n) (b := b) ds N (q.1 - 1)
              q.2) := by
  rw [cyclicNodeRootBoundaryLinearForm_eq_dot_coeff]
  rw [dotLinear_apply]
  refine Finset.sum_congr rfl ?_
  intro q _hq
  rcases q with ⟨d, rd⟩
  rw [cyclicNodeRootBoundaryCoefficient_eq_layers]

theorem cyclicNodeRootBoundaryLinearForm_childDataFamily_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (H : ZMod n → RawNormal.NodeChildDataFamily n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
        (fun d =>
          RawNormal.nodeFieldFromChildDataFamily
            (n := n) (a := b) (cs := ds) (H d)) R =
      ∑ d : ZMod n,
        ∑ site : RawNormal.NormalSite n (RTree.node b ds),
          ∑ j : ChildIdx ds,
            (R d site.nonRootCoord *
                (H d j).1
                  (by
                    simpa [RawNormal.NodeChildRootFieldDomain] using
                      RawNormal.nonRootDomainOfSite site
                        (RawNormal.childRootAtAsNonRootInNode (a := b) j)
                        0) +
              R (d + 1) site.nonRootCoord *
                (H d j).1
                  (by
                    simpa [RawNormal.NodeChildRootFieldDomain] using
                      RawNormal.nonRootDomainOfSite site
                        (RawNormal.childRootAtAsNonRootInNode (a := b) j)
                        1)) := by
  rw [cyclicNodeRootBoundaryLinearForm_apply]
  simp only [RawNormal.nodeFieldFromChildDataFamily_childRootAt]

theorem cyclicNodeRootBoundaryCoefficient_childDataFamily_eq_cyclicChildRootBoundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (H : ZMod n → RawNormal.NodeChildDataFamily n b ds)
    (d : ZMod n)
    (rd : RawNormal.RootFieldDomain n (RTree.node b ds)) :
    cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds
        (fun d =>
          RawNormal.nodeFieldFromChildDataFamily
            (n := n) (a := b) (cs := ds) (H d))
        (d, rd) =
      cyclicChildRootBoundaryMap (n := n) (b := b) ds
        (fun j d => (H d j).1) d rd := by
  rw [cyclicNodeRootBoundaryCoefficient_eq_layers]
  rw [
    cyclicNodeRootBoundaryLayer0_eq_sum_child,
    cyclicNodeRootBoundaryLayer1_eq_sum_child]
  rw [cyclicChildRootBoundaryMap_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [
    cyclicNodeRootBoundaryLayer0At_childDataFamily_message,
    cyclicNodeRootBoundaryLayer1At_childDataFamily_message]
  rfl

theorem cyclicNodeRootBoundaryLinearForm_childDataFamily_eq_dot_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (H : ZMod n → RawNormal.NodeChildDataFamily n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
        (fun d =>
          RawNormal.nodeFieldFromChildDataFamily
            (n := n) (a := b) (cs := ds) (H d))
        R =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (fun j d => (H d j).1) q.1 q.2)
        (fun q : CyclicNodeRootBoundaryDomain n b ds => R q.1 q.2) := by
  rw [cyclicNodeRootBoundaryLinearForm_eq_dot_coeff]
  have hcoeff :
      cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds
          (fun d =>
            RawNormal.nodeFieldFromChildDataFamily
              (n := n) (a := b) (cs := ds) (H d)) =
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (fun j d => (H d j).1) q.1 q.2) := by
    funext q
    rcases q with ⟨d, rd⟩
    exact
      cyclicNodeRootBoundaryCoefficient_childDataFamily_eq_cyclicChildRootBoundaryMap
        (n := n) (b := b) ds H d rd
  rw [hcoeff]

theorem cyclicNodeFixedRootFieldSum_eq_sum_childDataFamily_product_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R =
      ∑ H : ZMod n → RawNormal.NodeChildDataFamily n b ds,
        (∏ i : ChildIdx ds,
          bitSign
            (cyclicNodeChildInternalPhaseAt (n := n) (b := b) ds i
              (fun d =>
                RawNormal.nodeFieldFromChildDataFamily
                  (n := n) (a := b) (cs := ds) (H d)))) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (fun j d => (H d j).1) q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)) := by
  classical
  rw [cyclicNodeFixedRootFieldSum_eq_sum_childDataFamily
    (n := n) (b := b) ds R]
  refine Finset.sum_congr rfl ?_
  intro H _hH
  rw [
    cyclicNodeRootBoundaryLinearForm_childDataFamily_eq_dot_boundaryMap
      (n := n) (b := b) ds H R,
    bitSign_add]
  rw [
    bitSign_cyclicNodeInternalPhase_eq_prod_childInternal
      (n := n) (b := b) ds
      (fun d =>
        RawNormal.nodeFieldFromChildDataFamily
          (n := n) (a := b) (cs := ds) (H d))]
  ac_rfl

theorem cyclicNodeFixedRootFieldSum_eq_sum_childDataSplit_product_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R =
      ∑ K : CyclicNodeChildDataSplit n b ds,
        (∏ i : ChildIdx ds,
          bitSign
            (cyclicNodeChildInternalPhaseAt (n := n) (b := b) ds i
              (fun d =>
                RawNormal.nodeFieldFromChildDataFamily
                  (n := n) (a := b) (cs := ds)
                  (fun j => ((K j).1 d, (K j).2 d))))) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (fun j d => (K j).1 d) q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)) := by
  classical
  rw [cyclicNodeFixedRootFieldSum_eq_sum_childDataFamily_product_boundaryMap
    (n := n) (b := b) ds R]
  refine Fintype.sum_equiv
    (cyclicNodeChildDataFamilySplitEquiv n b ds)
    (fun H : ZMod n → RawNormal.NodeChildDataFamily n b ds =>
      (∏ i : ChildIdx ds,
        bitSign
          (cyclicNodeChildInternalPhaseAt (n := n) (b := b) ds i
            (fun d =>
              RawNormal.nodeFieldFromChildDataFamily
                (n := n) (a := b) (cs := ds) (H d)))) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (fun j d => (H d j).1) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2)))
    (fun K : CyclicNodeChildDataSplit n b ds =>
      (∏ i : ChildIdx ds,
        bitSign
          (cyclicNodeChildInternalPhaseAt (n := n) (b := b) ds i
            (fun d =>
              RawNormal.nodeFieldFromChildDataFamily
                (n := n) (a := b) (cs := ds)
                (fun j => ((K j).1 d, (K j).2 d))))) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (fun j d => (K j).1 d) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2)))
    ?_
  intro H
  simp [cyclicNodeChildDataFamilySplitEquiv]

theorem cyclicNodeFixedRootFieldSum_eq_sum_childDataSplit_local_product_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R =
      ∑ K : CyclicNodeChildDataSplit n b ds,
        (∏ i : ChildIdx ds,
          bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds i (K i).1 (K i).2)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (fun j d => (K j).1 d) q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)) := by
  classical
  rw [cyclicNodeFixedRootFieldSum_eq_sum_childDataSplit_product_boundaryMap
    (n := n) (b := b) ds R]
  refine Finset.sum_congr rfl ?_
  intro K _hK
  have hprod :
      (∏ i : ChildIdx ds,
        bitSign
          (cyclicNodeChildInternalPhaseAt (n := n) (b := b) ds i
            (fun d =>
              RawNormal.nodeFieldFromChildDataFamily
                (n := n) (a := b) (cs := ds)
                (fun j => ((K j).1 d, (K j).2 d))))) =
        ∏ i : ChildIdx ds,
          bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds i (K i).1 (K i).2) := by
    refine Finset.prod_congr rfl ?_
    intro i _hi
    rw [cyclicNodeChildInternalPhaseAt_split_eq_data
      (n := n) (b := b) ds K i]
  rw [hprod]

theorem cyclicNodeFixedRootFieldSum_eq_sum_childRootNonRootFamily_product_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R =
      ∑ P :
        CyclicNodeChildRootFamily n b ds ×
          CyclicNodeChildNonRootFamily n b ds,
        (∏ i : ChildIdx ds,
          bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds i (P.1 i) (P.2 i))) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  P.1 q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)) := by
  classical
  rw [cyclicNodeFixedRootFieldSum_eq_sum_childDataSplit_local_product_boundaryMap
    (n := n) (b := b) ds R]
  refine Fintype.sum_equiv
    (cyclicNodeChildDataSplitRootNonRootEquiv n b ds)
    (fun K : CyclicNodeChildDataSplit n b ds =>
      (∏ i : ChildIdx ds,
        bitSign
          (cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds i (K i).1 (K i).2)) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (fun j d => (K j).1 d) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2)))
    (fun P :
        CyclicNodeChildRootFamily n b ds ×
          CyclicNodeChildNonRootFamily n b ds =>
      (∏ i : ChildIdx ds,
        bitSign
          (cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds i (P.1 i) (P.2 i))) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                P.1 q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2)))
    ?_
  intro K
  simp [cyclicNodeChildDataSplitRootNonRootEquiv]

theorem cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSums_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R =
      ∑ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ i : ChildIdx ds,
          ∑ ψ :
            ZMod n → (v : NonRootVertex (childAt ds i)) →
              RawNormal.NodeChildNonRootFieldDomain n b ds i v → F2,
            bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds i (Φ i) ψ)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)) := by
  classical
  rw [cyclicNodeFixedRootFieldSum_eq_sum_childRootNonRootFamily_product_boundaryMap
    (n := n) (b := b) ds R]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro Φ _hΦ
  let c : ℤ :=
    bitSign
      (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            Φ q.1 q.2)
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          R q.1 q.2))
  calc
    (∑ Ψ : CyclicNodeChildNonRootFamily n b ds,
      (∏ i : ChildIdx ds,
        bitSign
          (cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds i (Φ i) (Ψ i))) * c) =
        (∑ Ψ : CyclicNodeChildNonRootFamily n b ds,
          ∏ i : ChildIdx ds,
            bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds i (Φ i) (Ψ i))) * c := by
          rw [Finset.sum_mul]
    _ =
        (∏ i : ChildIdx ds,
          ∑ ψ :
            ZMod n → (v : NonRootVertex (childAt ds i)) →
              RawNormal.NodeChildNonRootFieldDomain n b ds i v → F2,
            bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds i (Φ i) ψ)) * c := by
          rw [sum_pi_product_dep
            (ι := ChildIdx ds)
            (R := ℤ)
            (α := fun i : ChildIdx ds =>
              ZMod n → (v : NonRootVertex (childAt ds i)) →
                RawNormal.NodeChildNonRootFieldDomain n b ds i v → F2)
            (fun i ψ =>
              bitSign
                (cyclicNodeChildInternalPhaseAtData
                  (n := n) (b := b) ds i (Φ i) ψ))]
    _ =
        (∏ i : ChildIdx ds,
          ∑ ψ :
            ZMod n → (v : NonRootVertex (childAt ds i)) →
              RawNormal.NodeChildNonRootFieldDomain n b ds i v → F2,
            bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds i (Φ i) ψ)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)) := by
          rfl

theorem cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R =
      ∑ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ i : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds i (Φ i)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)) := by
  simpa [cyclicNodeChildNonRootSumAtRootFamily] using
    cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSums_boundaryMap
      (n := n) (b := b) ds R

theorem cyclicNodeChildNonRootSumAtRootFamily_eq_of_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (φ ψ :
      ZMod n → RawNormal.NodeChildRootFieldDomain n b ds j → F2)
    (e :
      (ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2) ≃
      (ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2))
    (hphase :
      ∀ Ψ :
        ZMod n → (v : NonRootVertex (childAt ds j)) →
          RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
        cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j ψ (e Ψ) =
          cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j φ Ψ) :
    cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j ψ =
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j φ := by
  classical
  unfold cyclicNodeChildNonRootSumAtRootFamily
  symm
  refine
    Fintype.sum_equiv e
      (fun Ψ =>
        bitSign
          (cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j φ Ψ))
      (fun Ψ =>
        bitSign
          (cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j ψ Ψ))
      ?_
  intro Ψ
  change
    bitSign
        (cyclicNodeChildInternalPhaseAtData
          (n := n) (b := b) ds j φ Ψ) =
      bitSign
        (cyclicNodeChildInternalPhaseAtData
          (n := n) (b := b) ds j ψ (e Ψ))
  rw [hphase Ψ]

theorem cyclicNodeChildNonRootSumAtRootFamily_eq_neg_of_reindex_flip
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (φ ψ :
      ZMod n → RawNormal.NodeChildRootFieldDomain n b ds j → F2)
    (e :
      (ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2) ≃
      (ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2))
    (hphase :
      ∀ Ψ :
        ZMod n → (v : NonRootVertex (childAt ds j)) →
          RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
        cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j ψ (e Ψ) =
          cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j φ Ψ + 1) :
    cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j ψ =
      -cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j φ := by
  classical
  unfold cyclicNodeChildNonRootSumAtRootFamily
  calc
    (∑ Ψ :
      ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
      bitSign
        (cyclicNodeChildInternalPhaseAtData
          (n := n) (b := b) ds j ψ Ψ)) =
        ∑ Ψ :
          ZMod n → (v : NonRootVertex (childAt ds j)) →
            RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
          bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds j ψ (e Ψ)) := by
          exact
            (Equiv.sum_comp e
              (fun Ψ =>
                bitSign
                  (cyclicNodeChildInternalPhaseAtData
                    (n := n) (b := b) ds j ψ Ψ))).symm
    _ =
        ∑ Ψ :
          ZMod n → (v : NonRootVertex (childAt ds j)) →
            RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
          -bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds j φ Ψ) := by
          refine Finset.sum_congr rfl ?_
          intro Ψ _hΨ
          have hsign :
              bitSign
                  (cyclicNodeChildInternalPhaseAtData
                    (n := n) (b := b) ds j ψ (e Ψ)) =
                -bitSign
                  (cyclicNodeChildInternalPhaseAtData
                    (n := n) (b := b) ds j φ Ψ) := by
            simp [hphase Ψ, bitSign_add, mul_comm]
          exact hsign
    _ =
        -(∑ Ψ :
          ZMod n → (v : NonRootVertex (childAt ds j)) →
            RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
          bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds j φ Ψ)) := by
          rw [Finset.sum_neg_distrib]

theorem cyclicNodeChildNonRootSumAtRootFamily_eq_mul_bitSign_of_reindex_phase
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j : ChildIdx ds)
    (φ ψ :
      ZMod n → RawNormal.NodeChildRootFieldDomain n b ds j → F2)
    (ε : F2)
    (e :
      (ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2) ≃
      (ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2))
    (hphase :
      ∀ Ψ :
        ZMod n → (v : NonRootVertex (childAt ds j)) →
          RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
        cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j ψ (e Ψ) =
          cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j φ Ψ + ε) :
    cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j ψ =
      cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j φ *
        bitSign ε := by
  classical
  unfold cyclicNodeChildNonRootSumAtRootFamily
  calc
    (∑ Ψ :
      ZMod n → (v : NonRootVertex (childAt ds j)) →
        RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
      bitSign
        (cyclicNodeChildInternalPhaseAtData
          (n := n) (b := b) ds j ψ Ψ)) =
        ∑ Ψ :
          ZMod n → (v : NonRootVertex (childAt ds j)) →
            RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
          bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds j ψ (e Ψ)) := by
          exact
            (Equiv.sum_comp e
              (fun Ψ =>
                bitSign
                  (cyclicNodeChildInternalPhaseAtData
                    (n := n) (b := b) ds j ψ Ψ))).symm
    _ =
        ∑ Ψ :
          ZMod n → (v : NonRootVertex (childAt ds j)) →
            RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
          bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds j φ Ψ) *
            bitSign ε := by
          refine Finset.sum_congr rfl ?_
          intro Ψ _hΨ
          rw [hphase Ψ]
          simp [bitSign_add]
    _ =
        (∑ Ψ :
          ZMod n → (v : NonRootVertex (childAt ds j)) →
            RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2,
          bitSign
            (cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds j φ Ψ)) *
          bitSign ε := by
          rw [Finset.sum_mul]

theorem cyclicNodeChildNonRootSumProduct_eq_mul_bitSign_of_reindex_phase
    {n b : Nat} [NeZero n] (ds : List RTree)
    (φ ψ : CyclicNodeChildRootFamily n b ds)
    (ε : F2)
    (e :
      CyclicNodeChildNonRootFamily n b ds ≃
        CyclicNodeChildNonRootFamily n b ds)
    (hphase :
      ∀ Ψ : CyclicNodeChildNonRootFamily n b ds,
        (∑ j : ChildIdx ds,
          cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j (ψ j) ((e Ψ) j)) =
          (∑ j : ChildIdx ds,
            cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds j (φ j) (Ψ j)) + ε) :
    (∏ j : ChildIdx ds,
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j (ψ j)) =
      (∏ j : ChildIdx ds,
        cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j (φ j)) *
        bitSign ε := by
  classical
  have hprod :
      ∀ Θ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Θ j)) =
          ∑ Ψ : CyclicNodeChildNonRootFamily n b ds,
            ∏ j : ChildIdx ds,
              bitSign
                (cyclicNodeChildInternalPhaseAtData
                  (n := n) (b := b) ds j (Θ j) (Ψ j)) := by
    intro Θ
    unfold cyclicNodeChildNonRootSumAtRootFamily
    rw [← sum_pi_product_dep
      (ι := ChildIdx ds)
      (R := ℤ)
      (α := fun j : ChildIdx ds =>
        ZMod n → (v : NonRootVertex (childAt ds j)) →
          RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2)
      (fun j Ψ =>
        bitSign
          (cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j (Θ j) Ψ))]
  rw [hprod ψ, hprod φ]
  calc
    (∑ Ψ : CyclicNodeChildNonRootFamily n b ds,
      ∏ j : ChildIdx ds,
        bitSign
          (cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j (ψ j) (Ψ j))) =
        ∑ Ψ : CyclicNodeChildNonRootFamily n b ds,
          ∏ j : ChildIdx ds,
            bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds j (ψ j) ((e Ψ) j)) := by
          exact
            (Equiv.sum_comp e
              (fun Ψ : CyclicNodeChildNonRootFamily n b ds =>
                ∏ j : ChildIdx ds,
                  bitSign
                    (cyclicNodeChildInternalPhaseAtData
                      (n := n) (b := b) ds j (ψ j) (Ψ j)))).symm
    _ =
        ∑ Ψ : CyclicNodeChildNonRootFamily n b ds,
          (∏ j : ChildIdx ds,
            bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds j (φ j) (Ψ j))) *
            bitSign ε := by
          refine Finset.sum_congr rfl ?_
          intro Ψ _hΨ
          calc
            (∏ j : ChildIdx ds,
              bitSign
                (cyclicNodeChildInternalPhaseAtData
                  (n := n) (b := b) ds j (ψ j) ((e Ψ) j))) =
                bitSign
                  (∑ j : ChildIdx ds,
                    cyclicNodeChildInternalPhaseAtData
                      (n := n) (b := b) ds j (ψ j) ((e Ψ) j)) := by
                  exact
                    prod_bitSign_eq_bitSign_sum
                      (Finset.univ : Finset (ChildIdx ds))
                      (fun j =>
                        cyclicNodeChildInternalPhaseAtData
                          (n := n) (b := b) ds j (ψ j) ((e Ψ) j))
            _ =
                bitSign
                  ((∑ j : ChildIdx ds,
                    cyclicNodeChildInternalPhaseAtData
                      (n := n) (b := b) ds j (φ j) (Ψ j)) + ε) := by
                  rw [hphase Ψ]
            _ =
                bitSign
                    (∑ j : ChildIdx ds,
                      cyclicNodeChildInternalPhaseAtData
                        (n := n) (b := b) ds j (φ j) (Ψ j)) *
                  bitSign ε := by
                  rw [bitSign_add]
            _ =
                (∏ j : ChildIdx ds,
                  bitSign
                    (cyclicNodeChildInternalPhaseAtData
                      (n := n) (b := b) ds j (φ j) (Ψ j))) *
                  bitSign ε := by
                  rw [prod_bitSign_eq_bitSign_sum
                    (Finset.univ : Finset (ChildIdx ds))]
    _ =
        (∑ Ψ : CyclicNodeChildNonRootFamily n b ds,
          ∏ j : ChildIdx ds,
            bitSign
              (cyclicNodeChildInternalPhaseAtData
                (n := n) (b := b) ds j (φ j) (Ψ j))) *
          bitSign ε := by
          rw [Finset.sum_mul]

theorem cyclicNodeChildNonRootSumProduct_eq_one_of_all_leaf_children
    {n b : Nat} [NeZero n] (ds : List RTree)
    (hleaf :
      ∀ j : ChildIdx ds, ∃ c : Nat, childAt ds j = RTree.node c [])
    (Φ : CyclicNodeChildRootFamily n b ds) :
    (∏ j : ChildIdx ds,
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j (Φ j)) = 1 := by
  classical
  refine Finset.prod_eq_one ?_
  intro j _hj
  rcases hleaf j with ⟨c, hchild⟩
  exact
    cyclicNodeChildNonRootSumAtRootFamily_leaf_child
      (n := n) (b := b) (c := c) ds j hchild (Φ j)

theorem fixedRootCyclicNodeFieldSum_node_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc =
      ∑ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                castRootFieldAssignment hchild (Rcyc q.1) q.2)) := by
  rw [fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
    (n := n) (a := a) (b := b) (cs := cs) i hchild Rcyc]
  exact
    cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (b := b) ds
      (fun d => castRootFieldAssignment hchild (Rcyc d))

theorem fixedRootCyclicNodeFieldSum_node_eq_of_boundaryMap_dot_eq
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (R S :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (S q.1) q.2) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (R q.1) q.2)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i S =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i R := by
  classical
  rw [
    fixedRootCyclicNodeFieldSum_node_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (a := a) (b := b) (cs := cs) i hchild S,
    fixedRootCyclicNodeFieldSum_node_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (a := a) (b := b) (cs := cs) i hchild R]
  refine Finset.sum_congr rfl ?_
  intro Φ _hΦ
  rw [hdot Φ]

theorem fixedRootCyclicNodeFieldSum_node_eq_of_childRootFamily_reindex
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (R S :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hweight :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (S q.1) q.2) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (R q.1) q.2)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i S =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i R := by
  classical
  rw [
    fixedRootCyclicNodeFieldSum_node_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (a := a) (b := b) (cs := cs) i hchild S,
    fixedRootCyclicNodeFieldSum_node_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (a := a) (b := b) (cs := cs) i hchild R]
  symm
  refine
    Fintype.sum_equiv e
      (fun Φ : CyclicNodeChildRootFamily n b ds =>
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                castRootFieldAssignment hchild (R q.1) q.2)))
      (fun Φ : CyclicNodeChildRootFamily n b ds =>
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                castRootFieldAssignment hchild (S q.1) q.2)))
      ?_
  intro Φ
  change
    (∏ j : ChildIdx ds,
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j (Φ j)) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (R q.1) q.2)) =
      (∏ j : ChildIdx ds,
        cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j ((e Φ) j)) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (S q.1) q.2))
  rw [hweight Φ, hdot Φ]

theorem fixedRootCyclicNodeFieldSum_shiftInvariant_of_childRootFamily_reindex
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (R S :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hweight :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild ((R + S) q.1) q.2) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (R q.1) q.2)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i (R + S) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i R :=
  fixedRootCyclicNodeFieldSum_node_eq_of_childRootFamily_reindex
    (n := n) (a := a) (b := b) (cs := cs) i hchild
    R (R + S) e hweight hdot

theorem cyclicNodeFixedRootFieldSum_eq_of_childRootFamily_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R S : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hweight :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              S q.1 q.2) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2)) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds S =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R := by
  classical
  rw [
    cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (b := b) ds S,
    cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (b := b) ds R]
  symm
  refine
    Fintype.sum_equiv e
      (fun Φ : CyclicNodeChildRootFamily n b ds =>
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)))
      (fun Φ : CyclicNodeChildRootFamily n b ds =>
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                S q.1 q.2)))
      ?_
  intro Φ
  change
    (∏ j : ChildIdx ds,
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j (Φ j)) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2)) =
      (∏ j : ChildIdx ds,
        cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j ((e Φ) j)) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              S q.1 q.2))
  rw [hweight Φ, hdot Φ]

theorem cyclicNodeFixedRootFieldSum_eq_of_childRootFamily_summand_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R S : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hsummand :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    (e Φ) q.1 q.2)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  S q.1 q.2)) =
          (∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    Φ q.1 q.2)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  R q.1 q.2))) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds S =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R := by
  classical
  rw [
    cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (b := b) ds S,
    cyclicNodeFixedRootFieldSum_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
      (n := n) (b := b) ds R]
  symm
  refine
    Fintype.sum_equiv e
      (fun Φ : CyclicNodeChildRootFamily n b ds =>
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                R q.1 q.2)))
      (fun Φ : CyclicNodeChildRootFamily n b ds =>
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign
            (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  Φ q.1 q.2)
              (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                S q.1 q.2)))
      ?_
  intro Φ
  change
    (∏ j : ChildIdx ds,
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j (Φ j)) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2)) =
      (∏ j : ChildIdx ds,
        cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j ((e Φ) j)) *
        bitSign
          (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              S q.1 q.2))
  exact (hsummand Φ).symm

theorem cyclicNodeFixedRootFieldSum_eq_of_childRootFamily_signFlip_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (R S : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          -(∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              S q.1 q.2) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ q.1 q.2)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              R q.1 q.2) + 1) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds S =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_eq_of_childRootFamily_summand_reindex
    (n := n) (b := b) ds R S e
    (by
      intro Φ
      rw [hprod Φ, hdot Φ]
      simp [bitSign_add, mul_comm, mul_left_comm, mul_assoc])

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hweight :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              R p.1 p.2 +
                Pi.single
                  (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
                  q (1 : F2) p) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              R p.1 p.2)) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_eq_of_childRootFamily_reindex
    (n := n) (b := b) ds R
    (fun d rd =>
      R d rd +
        Pi.single
          (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
          q (1 : F2) (d, rd))
      e hweight hdot

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_summand_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hsummand :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    (e Φ) p.1 p.2)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  R p.1 p.2 +
                    Pi.single
                      (M := fun _ :
                        CyclicNodeRootBoundaryDomain n b ds => F2)
                      q (1 : F2) p)) =
          (∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    Φ p.1 p.2)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  R p.1 p.2))) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_eq_of_childRootFamily_summand_reindex
    (n := n) (b := b) ds R
    (fun d rd =>
      R d rd +
        Pi.single
          (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
          q (1 : F2) (d, rd))
    e hsummand

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_signFlip_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          -(∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              R p.1 p.2 +
                Pi.single
                  (M := fun _ :
                    CyclicNodeRootBoundaryDomain n b ds => F2)
                  q (1 : F2) p) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              R p.1 p.2) + 1) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_eq_of_childRootFamily_signFlip_reindex
    (n := n) (b := b) ds R
    (fun d rd =>
      R d rd +
        Pi.single
          (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
          q (1 : F2) (d, rd))
    e hprod hdot

noncomputable def cyclicNodeChildRootFamilySingle
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0) :
    CyclicNodeChildRootFamily n b ds :=
  fun j d rd =>
    if hj : j = j0 then
      by
        subst j
        exact
          if hd : d = d0 then
            by
              subst d
              exact
                Pi.single
                  (M := fun _ :
                    RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
                  rd0 (1 : F2) rd
          else 0
    else 0

@[simp] theorem cyclicNodeChildRootFamilySingle_apply_self
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0) :
    cyclicNodeChildRootFamilySingle
        (n := n) (b := b) ds j0 d0 rd0 j0 d0 rd0 = 1 := by
  classical
  simp [cyclicNodeChildRootFamilySingle]

@[simp] theorem cyclicNodeChildRootFamilySingle_apply_ne_child
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 j : ChildIdx ds)
    (d0 d : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (rd : RawNormal.NodeChildRootFieldDomain n b ds j)
    (h : j ≠ j0) :
    cyclicNodeChildRootFamilySingle
        (n := n) (b := b) ds j0 d0 rd0 j d rd = 0 := by
  classical
  simp [cyclicNodeChildRootFamilySingle, h]

@[simp] theorem cyclicNodeChildRootFamilySingle_apply_ne_time
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 d : ZMod n)
    (rd0 rd : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (h : d ≠ d0) :
    cyclicNodeChildRootFamilySingle
        (n := n) (b := b) ds j0 d0 rd0 j0 d rd = 0 := by
  classical
  simp [cyclicNodeChildRootFamilySingle, h]

@[simp] theorem cyclicNodeChildRootFamilySingle_apply_ne_domain
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 rd : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (h : rd ≠ rd0) :
    cyclicNodeChildRootFamilySingle
        (n := n) (b := b) ds j0 d0 rd0 j0 d0 rd = 0 := by
  classical
  simp [cyclicNodeChildRootFamilySingle, h]

theorem cyclicNodeChildRootFamilySingle_component_eq_zero_of_ne_child
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 j : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (h : j ≠ j0) :
    cyclicNodeChildRootFamilySingle
        (n := n) (b := b) ds j0 d0 rd0 j = 0 := by
  funext d rd
  exact
    cyclicNodeChildRootFamilySingle_apply_ne_child
      (n := n) (b := b) ds j0 j d0 d rd0 rd h

noncomputable def cyclicNodeChildRootFamilyTranslationEquiv
    {n b : Nat} [NeZero n] (ds : List RTree)
    (τ : CyclicNodeChildRootFamily n b ds) :
    CyclicNodeChildRootFamily n b ds ≃
      CyclicNodeChildRootFamily n b ds :=
  Equiv.addRight τ

@[simp] theorem cyclicNodeChildRootFamilyTranslationEquiv_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (τ : CyclicNodeChildRootFamily n b ds)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (j : ChildIdx ds)
    (d : ZMod n)
    (rd : RawNormal.NodeChildRootFieldDomain n b ds j) :
    cyclicNodeChildRootFamilyTranslationEquiv
        (n := n) (b := b) ds τ Φ j d rd =
      Φ j d rd + τ j d rd := rfl

noncomputable def cyclicNodeChildRootFamilySingleToggleEquiv
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0) :
    CyclicNodeChildRootFamily n b ds ≃
      CyclicNodeChildRootFamily n b ds :=
  cyclicNodeChildRootFamilyTranslationEquiv
    (n := n) (b := b) ds
    (cyclicNodeChildRootFamilySingle
      (n := n) (b := b) ds j0 d0 rd0)

@[simp] theorem cyclicNodeChildRootFamilySingleToggleEquiv_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 j : ChildIdx ds)
    (d0 d : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (rd : RawNormal.NodeChildRootFieldDomain n b ds j)
    (Φ : CyclicNodeChildRootFamily n b ds) :
    cyclicNodeChildRootFamilySingleToggleEquiv
        (n := n) (b := b) ds j0 d0 rd0 Φ j d rd =
      Φ j d rd +
        cyclicNodeChildRootFamilySingle
          (n := n) (b := b) ds j0 d0 rd0 j d rd := rfl

noncomputable def cyclicNodeChildRootFamilyPair
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (j1 : ChildIdx ds)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j1) :
    CyclicNodeChildRootFamily n b ds :=
  cyclicNodeChildRootFamilySingle
      (n := n) (b := b) ds j0 d0 rd0 +
    cyclicNodeChildRootFamilySingle
      (n := n) (b := b) ds j1 d1 rd1

theorem cyclicNodeChildRootFamilyPair_component_eq_zero_of_ne_child
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (j1 : ChildIdx ds)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j1)
    (j : ChildIdx ds)
    (h0 : j ≠ j0)
    (h1 : j ≠ j1) :
    cyclicNodeChildRootFamilyPair
        (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1 j = 0 := by
  funext d rd
  simp [cyclicNodeChildRootFamilyPair,
    cyclicNodeChildRootFamilySingle_component_eq_zero_of_ne_child,
    h0, h1]

theorem cyclicChildRootBoundaryMap_childRootFamilySingle
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (d : ZMod n)
    (rd : RawNormal.RootFieldDomain n (RTree.node b ds)) :
    cyclicChildRootBoundaryMap (n := n) (b := b) ds
        (cyclicNodeChildRootFamilySingle
          (n := n) (b := b) ds j0 d0 rd0) d rd =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 rd
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 d,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (d - 1)) := by
  classical
  rw [cyclicChildRootBoundaryMap_apply]
  rw [Fintype.sum_eq_single j0]
  · intro j hj
    have hfun :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j = 0 :=
      cyclicNodeChildRootFamilySingle_component_eq_zero_of_ne_child
        (n := n) (b := b) ds j0 j d0 rd0 hj
    simp [childBoundaryPairLinearFormAt_apply, hfun,
      rootBoundaryChildMessageSumAt, nodeChildRootFieldAsMessage,
      nonRootFieldDomainFunctionAsMessage]

theorem cyclicChildRootBoundaryMap_childRootFamilyPair
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (j1 : ChildIdx ds)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j1)
    (d : ZMod n)
    (rd : RawNormal.RootFieldDomain n (RTree.node b ds)) :
    cyclicChildRootBoundaryMap (n := n) (b := b) ds
        (cyclicNodeChildRootFamilyPair
          (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1) d rd =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 rd
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 d,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (d - 1)) +
        childBoundaryPairLinearFormAt (n := n) (b := b) ds j1 rd
          (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 d,
            cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 (d - 1)) := by
  rw [cyclicNodeChildRootFamilyPair]
  change
    cyclicChildRootBoundaryLinearMap (n := n) (b := b) ds
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 +
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j1 d1 rd1) d rd =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 rd
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 d,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (d - 1)) +
        childBoundaryPairLinearFormAt (n := n) (b := b) ds j1 rd
          (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 d,
            cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 (d - 1))
  rw [LinearMap.map_add]
  change
    cyclicChildRootBoundaryMap (n := n) (b := b) ds
        (cyclicNodeChildRootFamilySingle
          (n := n) (b := b) ds j0 d0 rd0) d rd +
      cyclicChildRootBoundaryMap (n := n) (b := b) ds
        (cyclicNodeChildRootFamilySingle
          (n := n) (b := b) ds j1 d1 rd1) d rd =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 rd
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 d,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (d - 1)) +
        childBoundaryPairLinearFormAt (n := n) (b := b) ds j1 rd
          (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 d,
            cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 (d - 1))
  rw [
    cyclicChildRootBoundaryMap_childRootFamilySingle,
    cyclicChildRootBoundaryMap_childRootFamilySingle]

noncomputable def cyclicNodeChildRootFamilyPairToggleEquiv
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (j1 : ChildIdx ds)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j1) :
    CyclicNodeChildRootFamily n b ds ≃
      CyclicNodeChildRootFamily n b ds :=
  cyclicNodeChildRootFamilyTranslationEquiv
    (n := n) (b := b) ds
    (cyclicNodeChildRootFamilyPair
      (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1)

@[simp] theorem cyclicNodeChildRootFamilyPairToggleEquiv_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 j1 j : ChildIdx ds)
    (d0 d1 d : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j1)
    (rd : RawNormal.NodeChildRootFieldDomain n b ds j)
    (Φ : CyclicNodeChildRootFamily n b ds) :
    cyclicNodeChildRootFamilyPairToggleEquiv
        (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1 Φ j d rd =
      Φ j d rd +
        cyclicNodeChildRootFamilyPair
          (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1 j d rd := rfl

noncomputable def f2ShearEquiv
    (V : Type) [AddCommGroup V] [Module F2 V]
    (ℓ : V →ₗ[F2] F2)
    (τ : V)
    (hτ : ℓ τ = 0) :
    V ≃ V where
  toFun v := v + ℓ v • τ
  invFun v := v + ℓ v • τ
  left_inv v := by
    have hlin : ℓ (v + ℓ v • τ) = ℓ v := by
      rw [LinearMap.map_add, LinearMap.map_smul, hτ]
      simp
    calc
      (v + ℓ v • τ) + ℓ (v + ℓ v • τ) • τ =
          (v + ℓ v • τ) + ℓ v • τ := by rw [hlin]
      _ = v + (ℓ v • τ + ℓ v • τ) := by ac_rfl
      _ = v := by
            rw [add_self_eq_zero_of_module_F2 (ℓ v • τ)]
            simp
  right_inv v := by
    have hlin : ℓ (v + ℓ v • τ) = ℓ v := by
      rw [LinearMap.map_add, LinearMap.map_smul, hτ]
      simp
    calc
      (v + ℓ v • τ) + ℓ (v + ℓ v • τ) • τ =
          (v + ℓ v • τ) + ℓ v • τ := by rw [hlin]
      _ = v + (ℓ v • τ + ℓ v • τ) := by ac_rfl
      _ = v := by
            rw [add_self_eq_zero_of_module_F2 (ℓ v • τ)]
            simp

@[simp] theorem f2ShearEquiv_apply
    (V : Type) [AddCommGroup V] [Module F2 V]
    (ℓ : V →ₗ[F2] F2)
    (τ : V)
    (hτ : ℓ τ = 0)
    (v : V) :
    f2ShearEquiv V ℓ τ hτ v = v + ℓ v • τ := rfl

theorem f2_eq_zero_or_one_nonzeroBranch (x : F2) :
    x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

abbrev CyclicNodeChildNonRootFieldAt
    (n b : Nat) [NeZero n] (ds : List RTree) (j : ChildIdx ds) :=
  ZMod n → (v : NonRootVertex (childAt ds j)) →
    RawNormal.NodeChildNonRootFieldDomain n b ds j v → F2

theorem cyclicNodeChildInternalReindexPhase_of_evalOne
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (σ : F2)
    (hOne :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ = 1 →
          ∃ e :
            CyclicNodeChildNonRootFieldAt n b ds j0 ≃
              CyclicNodeChildNonRootFieldAt n b ds j0,
            ∀ Ψ : CyclicNodeChildNonRootFieldAt n b ds j0,
              cyclicNodeChildInternalPhaseAtData
                  (n := n) (b := b) ds j0
                  ((f2ShearEquiv
                    (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j0)
                  (e Ψ) =
                cyclicNodeChildInternalPhaseAtData
                    (n := n) (b := b) ds j0 (Φ j0) Ψ +
                  (σ + 1))
    (Φ : CyclicNodeChildRootFamily n b ds) :
    ∃ e :
      CyclicNodeChildNonRootFieldAt n b ds j0 ≃
        CyclicNodeChildNonRootFieldAt n b ds j0,
      ∀ Ψ : CyclicNodeChildNonRootFieldAt n b ds j0,
        cyclicNodeChildInternalPhaseAtData
            (n := n) (b := b) ds j0
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j0)
            (e Ψ) =
          cyclicNodeChildInternalPhaseAtData
              (n := n) (b := b) ds j0 (Φ j0) Ψ +
            (ℓ Φ * (σ + 1)) := by
  by_cases hzero : ℓ Φ = 0
  · refine ⟨Equiv.refl _, ?_⟩
    intro Ψ
    simp [f2ShearEquiv_apply, hzero]
  · have hone : ℓ Φ = 1 :=
      (f2_eq_zero_or_one_nonzeroBranch (ℓ Φ)).resolve_left hzero
    rcases hOne Φ hone with ⟨e, he⟩
    refine ⟨e, ?_⟩
    intro Ψ
    simpa [hone] using he Ψ

theorem cyclicNodeChildNonRootSumAtRootFamily_f2Shear_eq_mul_bitSign_of_evalOne
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (σ : F2)
    (hOne :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ = 1 →
          cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j0
              ((f2ShearEquiv
                (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j0) =
            cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j0 (Φ j0) *
              bitSign (σ + 1))
    (Φ : CyclicNodeChildRootFamily n b ds) :
    cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j0
        ((f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j0) =
      cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j0 (Φ j0) *
        bitSign (ℓ Φ * (σ + 1)) := by
  by_cases hzero : ℓ Φ = 0
  · have hcomponent :
        ((f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j0) = Φ j0 := by
      funext d rd
      simp [f2ShearEquiv_apply, hzero]
    rw [hcomponent]
    simp [hzero]
  · have hone : ℓ Φ = 1 :=
      (f2_eq_zero_or_one_nonzeroBranch (ℓ Φ)).resolve_left hzero
    simpa [hone] using hOne Φ hone

theorem cyclicNodeChildNonRootSumProduct_f2Shear_eq_mul_bitSign_of_evalOne
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (σ : F2)
    (hOne :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ = 1 →
          (∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j
              ((f2ShearEquiv
                (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
            (∏ j : ChildIdx ds,
              cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j (Φ j)) *
              bitSign (σ + 1))
    (Φ : CyclicNodeChildRootFamily n b ds) :
    (∏ j : ChildIdx ds,
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j
        ((f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
      (∏ j : ChildIdx ds,
        cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j (Φ j)) *
        bitSign (ℓ Φ * (σ + 1)) := by
  by_cases hzero : ℓ Φ = 0
  · have hshear :
        f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ = Φ := by
      funext j d rd
      simp [f2ShearEquiv_apply, hzero]
    rw [hshear]
    simp [hzero]
  · have hone : ℓ Φ = 1 :=
      (f2_eq_zero_or_one_nonzeroBranch (ℓ Φ)).resolve_left hzero
    simpa [hone] using hOne Φ hone

theorem cyclicNodeChildNonRootSumProduct_f2Shear_eq_mul_bitSign_one_of_all_leaf_children
    {n b : Nat} [NeZero n] (ds : List RTree)
    (hleaf :
      ∀ j : ChildIdx ds, ∃ c : Nat, childAt ds j = RTree.node c [])
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (Φ : CyclicNodeChildRootFamily n b ds) :
    (∏ j : ChildIdx ds,
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j
        ((f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
      (∏ j : ChildIdx ds,
        cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j (Φ j)) *
        bitSign (ℓ Φ * ((1 : F2) + 1)) := by
  rw [
    cyclicNodeChildNonRootSumProduct_eq_one_of_all_leaf_children
      (n := n) (b := b) ds hleaf
      (fun j =>
        (f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j),
    cyclicNodeChildNonRootSumProduct_eq_one_of_all_leaf_children
      (n := n) (b := b) ds hleaf Φ]
  have htwo : (1 : F2) + 1 = 0 :=
    add_self_eq_zero_of_module_F2 (1 : F2)
  rw [htwo]
  simp

theorem cyclicNodeChildNonRootSumAtRootFamily_f2Shear_eq_of_component_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (j : ChildIdx ds)
    (hτj : τ j = 0) :
    cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j
        ((f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j) =
      cyclicNodeChildNonRootSumAtRootFamily
        (n := n) (b := b) ds j (Φ j) := by
  have hcomponent :
      ((f2ShearEquiv
        (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j) = Φ j := by
    funext d rd
    simp [f2ShearEquiv_apply, hτj]
  rw [hcomponent]

noncomputable def cyclicChildRootBoundaryPairLinearMap
    {n b : Nat} [NeZero n] (ds : List RTree) :
    CyclicNodeChildRootFamily n b ds →ₗ[F2]
      (CyclicNodeRootBoundaryDomain n b ds → F2) where
  toFun Φ := fun q =>
    cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2
  map_add' Φ Ψ := by
    funext q
    change
      cyclicChildRootBoundaryLinearMap (n := n) (b := b) ds
          (Φ + Ψ) q.1 q.2 =
        (cyclicChildRootBoundaryLinearMap
          (n := n) (b := b) ds Φ +
          cyclicChildRootBoundaryLinearMap
            (n := n) (b := b) ds Ψ) q.1 q.2
    exact
      congrFun
        (congrFun
          ((cyclicChildRootBoundaryLinearMap
            (n := n) (b := b) ds).map_add Φ Ψ) q.1) q.2
  map_smul' r Φ := by
    funext q
    change
      cyclicChildRootBoundaryLinearMap (n := n) (b := b) ds
          (r • Φ) q.1 q.2 =
        (r • cyclicChildRootBoundaryLinearMap
          (n := n) (b := b) ds Φ) q.1 q.2
    exact
      congrFun
        (congrFun
          ((cyclicChildRootBoundaryLinearMap
            (n := n) (b := b) ds).map_smul r Φ) q.1) q.2

@[simp] theorem cyclicChildRootBoundaryPairLinearMap_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicChildRootBoundaryPairLinearMap
        (n := n) (b := b) ds Φ q =
      cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2 := rfl

noncomputable def cyclicChildRootBoundaryEvalLinearMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    CyclicNodeChildRootFamily n b ds →ₗ[F2] F2 where
  toFun Φ := cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2
  map_add' Φ Ψ := by
    change
      cyclicChildRootBoundaryLinearMap (n := n) (b := b) ds
          (Φ + Ψ) q.1 q.2 =
        (cyclicChildRootBoundaryLinearMap
          (n := n) (b := b) ds Φ +
          cyclicChildRootBoundaryLinearMap
            (n := n) (b := b) ds Ψ) q.1 q.2
    exact
      congrFun
        (congrFun
          ((cyclicChildRootBoundaryLinearMap
            (n := n) (b := b) ds).map_add Φ Ψ) q.1) q.2
  map_smul' r Φ := by
    change
      cyclicChildRootBoundaryLinearMap (n := n) (b := b) ds
          (r • Φ) q.1 q.2 =
        (r • cyclicChildRootBoundaryLinearMap
          (n := n) (b := b) ds Φ) q.1 q.2
    exact
      congrFun
        (congrFun
          ((cyclicChildRootBoundaryLinearMap
            (n := n) (b := b) ds).map_smul r Φ) q.1) q.2

@[simp] theorem cyclicChildRootBoundaryEvalLinearMap_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (Φ : CyclicNodeChildRootFamily n b ds) :
    cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds q Φ =
      cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2 := rfl

theorem cyclicChildRootBoundaryEvalLinearMap_childRootFamilySingle
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q
        (cyclicNodeChildRootFamilySingle
          (n := n) (b := b) ds j0 d0 rd0) =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 q.1,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (q.1 - 1)) := by
  simpa [cyclicChildRootBoundaryEvalLinearMap_apply] using
    cyclicChildRootBoundaryMap_childRootFamilySingle
      (n := n) (b := b) ds j0 d0 rd0 q.1 q.2

theorem cyclicChildRootBoundaryEvalLinearMap_childRootFamilyPair
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (j1 : ChildIdx ds)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j1)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q
        (cyclicNodeChildRootFamilyPair
          (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1) =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 q.1,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (q.1 - 1)) +
        childBoundaryPairLinearFormAt (n := n) (b := b) ds j1 q.2
          (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 q.1,
            cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1 j1 (q.1 - 1)) := by
  simpa [cyclicChildRootBoundaryEvalLinearMap_apply] using
    cyclicChildRootBoundaryMap_childRootFamilyPair
      (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1 q.1 q.2

theorem cyclicChildRootBoundaryEvalLinearMap_childRootFamilyPair_sameChild
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q
        (cyclicNodeChildRootFamilyPair
          (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1) =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 q.1,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (q.1 - 1)) +
        childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
          (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j0 d1 rd1 j0 q.1,
            cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j0 d1 rd1 j0 (q.1 - 1)) := by
  simpa using
    cyclicChildRootBoundaryEvalLinearMap_childRootFamilyPair
      (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1 q

theorem cyclicChildRootBoundaryEvalLinearMap_childRootFamilyPair_sameChild_eq_zero_of_eq
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (heq :
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 q.1,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 d0 rd0 j0 (q.1 - 1)) =
        childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
          (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j0 d1 rd1 j0 q.1,
            cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j0 d1 rd1 j0 (q.1 - 1))) :
    cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q
        (cyclicNodeChildRootFamilyPair
          (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1) = 0 := by
  rw [cyclicChildRootBoundaryEvalLinearMap_childRootFamilyPair_sameChild]
  rw [heq, add_self_eq_zero_of_module_F2]

theorem cyclicChildRootBoundaryEvalLinearMap_selectedAdjacentPair_eq_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q
        (cyclicNodeChildRootFamilyPair
          (n := n) (b := b) ds
          j0 q.1
            (rootBoundarySelectedNodeChildRootFieldDomain
              (n := n) (b := b) ds j0 rootCoord q.2 0)
          j0 (q.1 - 1)
            (rootBoundarySelectedNodeChildRootFieldDomain
              (n := n) (b := b) ds j0 rootCoord q.2 1)) = 0 := by
  apply
    cyclicChildRootBoundaryEvalLinearMap_childRootFamilyPair_sameChild_eq_zero_of_eq
      (n := n) (b := b) ds j0
      q.1
      (rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 0)
      (q.1 - 1)
      (rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 1)
      q
  let rd0 :=
    rootBoundarySelectedNodeChildRootFieldDomain
      (n := n) (b := b) ds j0 rootCoord q.2 0
  let rd1 :=
    rootBoundarySelectedNodeChildRootFieldDomain
      (n := n) (b := b) ds j0 rootCoord q.2 1
  change
    childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 q.1 rd0 j0 q.1,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 q.1 rd0 j0 (q.1 - 1)) =
      childBoundaryPairLinearFormAt (n := n) (b := b) ds j0 q.2
        (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 (q.1 - 1) rd1 j0 q.1,
          cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 (q.1 - 1) rd1 j0 (q.1 - 1))
  by_cases htime : q.1 - 1 = q.1
  · have hcomm :
        rootBoundaryChildMessageSumAt (n := n) (b := b) ds j0
            (Pi.single
              (M := fun _ :
                RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
              rd0
              (1 : F2))
            q.2 1 =
          rootBoundaryChildMessageSumAt (n := n) (b := b) ds j0
            (Pi.single
              (M := fun _ :
                RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
              rd1
              (1 : F2))
            q.2 0 := by
        exact
          rootBoundaryChildMessageSumAt_single_selected_comm
            (n := n) (b := b) ds j0 rootCoord q.2 0 1
    have h00 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 q.1 rd0 j0 q.1 =
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
            rd0 (1 : F2) := by
      funext rd
      simp [cyclicNodeChildRootFamilySingle]
    have h01 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 q.1 rd0 j0 (q.1 - 1) =
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
            rd0 (1 : F2) := by
      rw [htime]
      exact h00
    have h10 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 (q.1 - 1) rd1 j0 q.1 =
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
            rd1 (1 : F2) := by
      rw [htime]
      funext rd
      simp [cyclicNodeChildRootFamilySingle]
    have h11 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 (q.1 - 1) rd1 j0 (q.1 - 1) =
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
            rd1 (1 : F2) := by
      funext rd
      simp [cyclicNodeChildRootFamilySingle]
    rw [childBoundaryPairLinearFormAt_apply, h00, h01, h10, h11]
    simp [rd0, rd1, rootBoundaryChildMessageSumAt_single_selected_self,
      hcomm, add_comm]
  · have htime' : q.1 ≠ q.1 - 1 := by
      intro h
      exact htime h.symm
    have h00 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 q.1 rd0 j0 q.1 =
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
            rd0 (1 : F2) := by
      funext rd
      simp [cyclicNodeChildRootFamilySingle]
    have h01 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 q.1 rd0 j0 (q.1 - 1) =
          0 := by
      funext rd
      simp [cyclicNodeChildRootFamilySingle, htime]
    have h10 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 (q.1 - 1) rd1 j0 q.1 =
          0 := by
      funext rd
      simp [cyclicNodeChildRootFamilySingle, htime']
    have h11 :
        cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j0 (q.1 - 1) rd1 j0 (q.1 - 1) =
          Pi.single
            (M := fun _ :
              RawNormal.NodeChildRootFieldDomain n b ds j0 => F2)
            rd1 (1 : F2) := by
      funext rd
      simp [cyclicNodeChildRootFamilySingle]
    rw [childBoundaryPairLinearFormAt_apply, h00, h01, h10, h11]
    simp [rd0, rd1, rootBoundaryChildMessageSumAt_single_selected_self]

theorem selectedAdjacentPair_evalShearDotWitness
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2) :
    ∃ d0 : ZMod n,
    ∃ rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0,
    ∃ d1 : ZMod n,
    ∃ rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0,
    let τ : CyclicNodeChildRootFamily n b ds :=
      cyclicNodeChildRootFamilyPair
        (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1
    ∃ _hτ : cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds q τ = 0,
    ∃ σ : F2,
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            τ p.1 p.2)
        R = σ := by
  refine ⟨q.1, ?_, q.1 - 1, ?_, ?_⟩
  · exact
      rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 0
  · exact
      rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 1
  · refine ⟨?_, ?_⟩
    · exact
        cyclicChildRootBoundaryEvalLinearMap_selectedAdjacentPair_eq_zero
          (n := n) (b := b) ds j0 rootCoord q
    · refine ⟨dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (cyclicNodeChildRootFamilyPair
              (n := n) (b := b) ds j0 q.1
                (rootBoundarySelectedNodeChildRootFieldDomain
                  (n := n) (b := b) ds j0 rootCoord q.2 0)
                j0 (q.1 - 1)
                (rootBoundarySelectedNodeChildRootFieldDomain
                  (n := n) (b := b) ds j0 rootCoord q.2 1))
            p.1 p.2)
        R, rfl⟩

theorem selectedAdjacentPair_supportedEvalShearDotWitness
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2) :
    ∃ d0 : ZMod n,
    ∃ rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0,
    ∃ d1 : ZMod n,
    ∃ rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0,
    let τ : CyclicNodeChildRootFamily n b ds :=
      cyclicNodeChildRootFamilyPair
        (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1
    ∃ _hτ : cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds q τ = 0,
    ∃ σ : F2,
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            τ p.1 p.2)
        R = σ ∧
      (∀ j : ChildIdx ds, j ≠ j0 → τ j = 0) := by
  rcases
    selectedAdjacentPair_evalShearDotWitness
      (n := n) (b := b) ds j0 rootCoord q R with
    ⟨d0, rd0, d1, rd1, hτ, σ, hdot⟩
  refine ⟨d0, rd0, d1, rd1, hτ, σ, hdot, ?_⟩
  intro j hj
  exact
    cyclicNodeChildRootFamilyPair_component_eq_zero_of_ne_child
      (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1 j hj hj

noncomputable def selectedAdjacentPairRootFamily
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    CyclicNodeChildRootFamily n b ds :=
  cyclicNodeChildRootFamilyPair
    (n := n) (b := b) ds
    j0 q.1
      (rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 0)
    j0 (q.1 - 1)
      (rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 1)

theorem selectedAdjacentPairRootFamily_eval_eq_zero
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q
        (selectedAdjacentPairRootFamily
          (n := n) (b := b) ds j0 rootCoord q) = 0 := by
  simpa [selectedAdjacentPairRootFamily] using
    cyclicChildRootBoundaryEvalLinearMap_selectedAdjacentPair_eq_zero
      (n := n) (b := b) ds j0 rootCoord q

theorem selectedAdjacentPairRootFamily_component_eq_zero_of_ne_child
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (j : ChildIdx ds)
    (hj : j ≠ j0) :
    selectedAdjacentPairRootFamily
        (n := n) (b := b) ds j0 rootCoord q j = 0 := by
  simpa [selectedAdjacentPairRootFamily] using
    cyclicNodeChildRootFamilyPair_component_eq_zero_of_ne_child
      (n := n) (b := b) ds j0 q.1
      (rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 0)
      j0 (q.1 - 1)
      (rootBoundarySelectedNodeChildRootFieldDomain
        (n := n) (b := b) ds j0 rootCoord q.2 1)
      j hj hj

noncomputable def dotLinearLeftLinearMap
    (α : Type) [Fintype α] (R : α → F2) :
    (α → F2) →ₗ[F2] F2 where
  toFun P := dotLinear α P R
  map_add' P Q := by
    simp [dotLinear, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp [dotLinear, Pi.smul_apply, Finset.mul_sum, mul_assoc,
      mul_left_comm, mul_comm]

@[simp] theorem dotLinearLeftLinearMap_apply
    (α : Type) [Fintype α] (R : α → F2) (P : α → F2) :
    dotLinearLeftLinearMap α R P = dotLinear α P R := rfl

theorem dotLinear_add_singleton_right
    (α : Type) [Fintype α] [DecidableEq α]
    (P R : α → F2) (q : α) :
    dotLinear α P
        (fun p => R p +
          Pi.single (M := fun _ : α => F2) q (1 : F2) p) =
      dotLinear α P R + P q := by
  classical
  rw [dotLinear_apply, dotLinear_apply]
  calc
    (∑ p : α,
        (R p + Pi.single (M := fun _ : α => F2) q (1 : F2) p) *
          P p) =
        ∑ p : α,
          (R p * P p +
            Pi.single (M := fun _ : α => F2) q (1 : F2) p * P p) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          rw [add_mul]
    _ =
        (∑ p : α, R p * P p) +
          ∑ p : α,
            Pi.single (M := fun _ : α => F2) q (1 : F2) p * P p := by
          rw [Finset.sum_add_distrib]
    _ = (∑ p : α, R p * P p) + P q := by
          congr 1
          simpa using
            (Finset.sum_eq_single
              (s := Finset.univ) (a := q)
              (f := fun p : α =>
                Pi.single (M := fun _ : α => F2) q (1 : F2) p *
                  P p)
              (by
                intro p _hp hp
                simp [Pi.single_eq_of_ne hp])
              (by
                intro hq
                simp at hq))

theorem dotLinear_cyclicChildRootBoundaryMap_childRootFamilyPair
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (j1 : ChildIdx ds)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j1)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2) :
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (cyclicNodeChildRootFamilyPair
              (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1)
            p.1 p.2)
        R =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j0 d0 rd0)
            p.1 p.2)
        R +
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j1 d1 rd1)
            p.1 p.2)
        R := by
  let B := cyclicChildRootBoundaryPairLinearMap (n := n) (b := b) ds
  let D := dotLinearLeftLinearMap (CyclicNodeRootBoundaryDomain n b ds) R
  change
    D (B
      (cyclicNodeChildRootFamilyPair
        (n := n) (b := b) ds j0 d0 rd0 j1 d1 rd1)) =
      D (B
        (cyclicNodeChildRootFamilySingle
          (n := n) (b := b) ds j0 d0 rd0)) +
        D (B
          (cyclicNodeChildRootFamilySingle
            (n := n) (b := b) ds j1 d1 rd1))
  rw [cyclicNodeChildRootFamilyPair, B.map_add, D.map_add]

theorem dotLinear_cyclicChildRootBoundaryMap_childRootFamilyPair_sameChild_eq_zero_of_eq
    {n b : Nat} [NeZero n] (ds : List RTree)
    (j0 : ChildIdx ds)
    (d0 : ZMod n)
    (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (d1 : ZMod n)
    (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2)
    (heq :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j0 d0 rd0)
            p.1 p.2)
        R =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (cyclicNodeChildRootFamilySingle
              (n := n) (b := b) ds j0 d1 rd1)
            p.1 p.2)
        R) :
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (cyclicNodeChildRootFamilyPair
              (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1)
            p.1 p.2)
        R = 0 := by
  rw [dotLinear_cyclicChildRootBoundaryMap_childRootFamilyPair]
  rw [heq, add_self_eq_zero_of_module_F2]

theorem cyclicChildRootBoundaryMap_f2ShearEquiv_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    cyclicChildRootBoundaryMap (n := n) (b := b) ds
        (f2ShearEquiv (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ)
        q.1 q.2 =
      cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2 +
        ℓ Φ •
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2 := by
  change
    cyclicChildRootBoundaryLinearMap (n := n) (b := b) ds
        (Φ + ℓ Φ • τ) q.1 q.2 =
      cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2 +
        ℓ Φ •
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2
  rw [LinearMap.map_add, LinearMap.map_smul]
  rfl

theorem dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2) :
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (f2ShearEquiv (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ)
            q.1 q.2)
        R =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
          (fun q : CyclicNodeRootBoundaryDomain n b ds =>
            cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2)
          R +
        ℓ Φ •
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun q : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2)
            R := by
  let B := cyclicChildRootBoundaryPairLinearMap (n := n) (b := b) ds
  let D := dotLinearLeftLinearMap (CyclicNodeRootBoundaryDomain n b ds) R
  change D (B (Φ + ℓ Φ • τ)) = D (B Φ) + ℓ Φ • D (B τ)
  rw [B.map_add, B.map_smul, D.map_add, D.map_smul]

theorem dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv_add_singleton
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2)
    (q : CyclicNodeRootBoundaryDomain n b ds) :
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (f2ShearEquiv (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ)
            p.1 p.2)
        (fun p =>
          R p +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) p) =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
          (fun p : CyclicNodeRootBoundaryDomain n b ds =>
            cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ p.1 p.2)
          R +
        ℓ Φ •
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
            R +
        cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2 +
        ℓ Φ •
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2 := by
  classical
  rw [dotLinear_add_singleton_right]
  rw [dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv]
  rw [cyclicChildRootBoundaryMap_f2ShearEquiv_apply]
  ac_rfl

theorem dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv_add_singleton_cancel
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (hℓ :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ =
          cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2)
    (heval :
      cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2 = 0)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        R = 1)
    (Φ : CyclicNodeChildRootFamily n b ds) :
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (f2ShearEquiv (CyclicNodeChildRootFamily n b ds)
              ℓ τ hτ Φ)
            p.1 p.2)
        (fun p =>
          R p +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) p) =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
          (fun p : CyclicNodeRootBoundaryDomain n b ds =>
            cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ p.1 p.2)
          R := by
  classical
  rw [dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv_add_singleton]
  rw [hdot, heval, ← hℓ Φ]
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
  rw [add_assoc, add_self_eq_zero_of_module_F2 (ℓ Φ), add_zero]

theorem dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv_add_singleton_extra
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : CyclicNodeRootBoundaryDomain n b ds → F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (σ : F2)
    (hℓ :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ =
          cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2)
    (heval :
      cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2 = 0)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        R = σ)
    (Φ : CyclicNodeChildRootFamily n b ds) :
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (f2ShearEquiv (CyclicNodeChildRootFamily n b ds)
              ℓ τ hτ Φ)
            p.1 p.2)
        (fun p =>
          R p +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) p) =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
          (fun p : CyclicNodeRootBoundaryDomain n b ds =>
            cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ p.1 p.2)
          R +
        ℓ Φ * (σ + 1) := by
  classical
  rw [dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv_add_singleton]
  rw [hdot, heval, ← hℓ Φ]
  simp only [smul_eq_mul, mul_zero, add_zero]
  ring_nf

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_shear
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (hℓ :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ =
          cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2)
    (heval :
      cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2 = 0)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds => R p.1 p.2) = 1)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_reindex
    (n := n) (b := b) ds q R
    (f2ShearEquiv (CyclicNodeChildRootFamily n b ds) ℓ τ hτ)
    hprod
    (by
      intro Φ
      exact
        dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv_add_singleton_cancel
          (n := n) (b := b) ds ℓ q
          (fun p : CyclicNodeRootBoundaryDomain n b ds => R p.1 p.2)
          τ hτ
          (hℓ := hℓ)
          (heval := heval)
          (hdot := hdot)
          Φ)

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_shearSign
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (σ : F2)
    (hℓ :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ =
          cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ q.1 q.2)
    (heval :
      cyclicChildRootBoundaryMap (n := n) (b := b) ds τ q.1 q.2 = 0)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds => R p.1 p.2) = σ)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
          (∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) *
            bitSign (ℓ Φ * (σ + 1))) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_summand_reindex
    (n := n) (b := b) ds q R
    (f2ShearEquiv (CyclicNodeChildRootFamily n b ds) ℓ τ hτ)
    (by
      intro Φ
      let P : ℤ :=
        ∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)
      let D : F2 :=
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
          (fun p : CyclicNodeRootBoundaryDomain n b ds =>
            cyclicChildRootBoundaryMap (n := n) (b := b) ds
              Φ p.1 p.2)
          (fun p : CyclicNodeRootBoundaryDomain n b ds => R p.1 p.2)
      let E : F2 := ℓ Φ * (σ + 1)
      have hdotExtra :=
        dotLinear_cyclicChildRootBoundaryMap_f2ShearEquiv_add_singleton_extra
          (n := n) (b := b) ds ℓ q
          (fun p : CyclicNodeRootBoundaryDomain n b ds => R p.1 p.2)
          τ hτ σ
          (hℓ := hℓ)
          (heval := heval)
          (hdot := hdot)
          Φ
      have hdotExtra' :
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (f2ShearEquiv (CyclicNodeChildRootFamily n b ds)
                    ℓ τ hτ Φ)
                  p.1 p.2)
              (fun p =>
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  R p.1 p.2) p +
                  Pi.single
                    (M := fun _ :
                      CyclicNodeRootBoundaryDomain n b ds => F2)
                    q (1 : F2) p) =
            D + E := by
        simpa [D, E] using hdotExtra
      have hsign : bitSign E * bitSign E = 1 := by
        rcases f2_eq_zero_or_one E with hextra | hextra <;>
          simp [hextra]
      rw [hprod Φ, hdotExtra']
      change (P * bitSign E) * bitSign (D + E) = P * bitSign D
      rw [bitSign_add]
      calc
        (P * bitSign E) * (bitSign D * bitSign E) =
            P * bitSign D * (bitSign E * bitSign E) := by ring
        _ = P * bitSign D * 1 := by rw [hsign]
        _ = P * bitSign D := by ring)

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSign
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q τ = 0)
    (σ : F2)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds => R p.1 p.2) = σ)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds)
              (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q)
              τ hτ Φ) j)) =
          (∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) *
            bitSign
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ * (σ + 1))) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_shearSign
    (n := n) (b := b) ds q R
    (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q)
    τ hτ σ
    (by intro Φ; rfl)
    hτ hdot hprod

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShear
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q τ = 0)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds => R p.1 p.2) = 1)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds)
              (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q)
              τ hτ Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_shear
    (n := n) (b := b) ds q R
    (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q)
    τ hτ
    (by
      intro Φ
      rfl)
    (by
      simpa [cyclicChildRootBoundaryEvalLinearMap_apply] using hτ)
    hdot hprod

theorem cyclicNodeRootBoundaryLinearForm_eq_childDataFamily
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R =
      cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
        (fun d =>
          RawNormal.nodeFieldFromChildDataFamily
            (n := n) (a := b) (cs := ds)
            ((cyclicNodeFieldFamilyEquivChildDataFamily n b ds N) d))
        R := by
  have hN :
      N =
        fun d =>
          RawNormal.nodeFieldFromChildDataFamily
            (n := n) (a := b) (cs := ds)
            ((cyclicNodeFieldFamilyEquivChildDataFamily n b ds N) d) := by
    funext d
    change
      N d =
        (nodeChildDataFamilyEquivNodeField n b ds)
          ((cyclicNodeFieldFamilyEquivChildDataFamily n b ds N) d)
    exact ((nodeChildDataFamilyEquivNodeField n b ds).right_inv (N d)).symm
  exact congrArg (fun M => cyclicNodeRootBoundaryLinearForm
    (n := n) (b := b) ds M R) hN

theorem cyclicNodeRootBoundaryLinearForm_eq_dot_boundaryMap
    {n b : Nat} [NeZero n] (ds : List RTree)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R =
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (fun j d =>
              ((cyclicNodeFieldFamilyEquivChildDataFamily n b ds N) d j).1)
            q.1 q.2)
        (fun q : CyclicNodeRootBoundaryDomain n b ds => R q.1 q.2) := by
  rw [cyclicNodeRootBoundaryLinearForm_eq_childDataFamily]
  exact
    cyclicNodeRootBoundaryLinearForm_childDataFamily_eq_dot_boundaryMap
      (n := n) (b := b) ds
      (cyclicNodeFieldFamilyEquivChildDataFamily n b ds N) R

theorem cyclicNodeRootBoundaryLinearForm_nil
    {n b : Nat} [NeZero n]
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b [])
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b []) :
    cyclicNodeRootBoundaryLinearForm (n := n) (b := b) [] N R = 0 := by
  rw [cyclicNodeRootBoundaryLinearForm_apply]
  simp [ChildIdx]

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_oneFiber
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (hcancel :
      (∑ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        if cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q = 1
        then
          bitSign
            (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
              cyclicNodeInternalPhase (n := n) (b := b) ds N)
        else 0) = 0) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R := by
  classical
  unfold cyclicNodeFixedRootFieldSum
  calc
    (∑ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
      bitSign
        (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
            (fun d rd =>
              R d rd +
                Pi.single
                  (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
                  q (1 : F2) (d, rd)) +
          cyclicNodeInternalPhase (n := n) (b := b) ds N)) =
        ∑ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
          bitSign
              (cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q) *
            bitSign
              (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
                cyclicNodeInternalPhase (n := n) (b := b) ds N) := by
          refine Finset.sum_congr rfl ?_
          intro N _
          rw [cyclicNodeRootBoundaryLinearForm_add_single
            (n := n) (b := b) ds N R q]
          simp [bitSign_add, add_assoc, add_left_comm, add_comm,
            mul_comm, mul_left_comm, mul_assoc]
    _ =
        ∑ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
          bitSign
            (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
              cyclicNodeInternalPhase (n := n) (b := b) ds N) := by
          exact
            sum_bitSign_mul_eq_sum_of_oneFiber_sum_eq_zero
              (fun N : ZMod n →
                  RawNormal.NodeNonRootFieldAssignment n b ds =>
                cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q)
              (fun N : ZMod n →
                  RawNormal.NodeNonRootFieldAssignment n b ds =>
                bitSign
                  (cyclicNodeRootBoundaryLinearForm
                      (n := n) (b := b) ds N R +
                    cyclicNodeInternalPhase (n := n) (b := b) ds N))
              hcancel

abbrev CyclicNodeFixedRootOneFiberCancellationCoreRule : Prop :=
  ∀ {b : Nat} {ds : List RTree},
    RawExpandedOpenRootSubtreeCert (RTree.node b ds) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (q : CyclicNodeRootBoundaryDomain n b ds)
        (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds),
        (∑ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
          if cyclicNodeRootBoundaryCoefficient (n := n) (b := b) ds N q = 1
          then
            bitSign
              (cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
                cyclicNodeInternalPhase (n := n) (b := b) ds N)
          else 0) = 0

theorem childExternalNormalAssignmentOfRootNodeField_eq_baseCyclic
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (Ψcyc :
      ChildExternalBaseCoordinate n a cs i →
        ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i)) :
    childExternalNormalAssignmentOfRootNodeField
        (n := n) (a := a) (cs := cs) i φ
        ((childExternalNodeFieldFamilyBaseCyclicEquiv
          (n := n) (a := a) (cs := cs) i).symm Ψcyc) =
      (externalAssignmentsEquivBaseCyclic
        (n := n) (a := a) (cs := cs) i).symm
        (fun base d =>
          { rootField :=
              (nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i φ)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, d))
            nodeField := Ψcyc base d }) := by
  funext ext
  rw [RawNormal.NormalAssignment.mk.injEq]
  constructor
  · funext rd
    cases ext
    rfl
  · funext v nd
    cases ext
    rfl

abbrev FixedRootCyclicNodeFieldSumConstantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs),
        ∃ K : ℤ,
          ∀ Rcyc :
            ZMod n → RawNormal.RootFieldAssignment n (childAt cs i),
            fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i Rcyc = K

abbrev FixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs),
        ∀ q :
          ZMod n × RawNormal.RootFieldDomain n (childAt cs i),
          ∀ Rcyc :
            ZMod n → RawNormal.RootFieldAssignment n (childAt cs i),
            fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i
              (fun d rd =>
                Rcyc d rd +
                  Pi.single
                    (M := fun _ :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) =>
                      F2)
                    q (1 : F2) (d, rd)) =
            fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i Rcyc

def castRootFieldDomain
    {n : Nat} [NeZero n] {T U : RTree} (h : T = U)
    (rd : RawNormal.RootFieldDomain n T) :
    RawNormal.RootFieldDomain n U :=
  match h with
  | rfl => rd

theorem selectedAdjacentPair_supportedEvalShearDotWitness_cast
    {n b : Nat} [NeZero n] {cs ds : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b ds)
    (j0 : ChildIdx ds)
    (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (R : CyclicNodeRootBoundaryDomain n b ds → F2) :
    ∃ d0 : ZMod n,
    ∃ rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0,
    ∃ d1 : ZMod n,
    ∃ rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0,
    let τ : CyclicNodeChildRootFamily n b ds :=
      cyclicNodeChildRootFamilyPair
        (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1
    ∃ _hτ :
      cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds
        (q.1, castRootFieldDomain hchild q.2) τ = 0,
    ∃ σ : F2,
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            τ p.1 p.2)
        R = σ ∧
      (∀ j : ChildIdx ds, j ≠ j0 → τ j = 0) :=
  selectedAdjacentPair_supportedEvalShearDotWitness
    (n := n) (b := b) ds j0 rootCoord
    (q.1, castRootFieldDomain hchild q.2) R

theorem castRootFieldAssignment_add
    {n : Nat} [NeZero n] {T U : RTree} (h : T = U)
    (R S : RawNormal.RootFieldAssignment n T) :
    castRootFieldAssignment h (R + S) =
      castRootFieldAssignment h R + castRootFieldAssignment h S := by
  cases h
  rfl

theorem castRootFieldAssignment_add_single
    {n : Nat} [NeZero n] {T U : RTree} (h : T = U)
    (R : RawNormal.RootFieldAssignment n T)
    (q : ZMod n × RawNormal.RootFieldDomain n T)
    (d : ZMod n) :
    castRootFieldAssignment h
      (fun rd =>
        R rd +
          Pi.single
            (M := fun _ : ZMod n × RawNormal.RootFieldDomain n T => F2)
            q (1 : F2) (d, rd)) =
      fun rd =>
        castRootFieldAssignment h R rd +
          Pi.single
            (M := fun _ : ZMod n × RawNormal.RootFieldDomain n U => F2)
            (q.1, castRootFieldDomain h q.2) (1 : F2) (d, rd) := by
  cases h
  cases q
  rfl

theorem fixedRootCyclicNodeFieldSum_shiftInvariant_of_boundaryShift_zero
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (R S : ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (hS :
      ∀ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
          (fun d => castRootFieldAssignment hchild (S d)) = 0) :
    fixedRootCyclicNodeFieldSum (n := n) (a := a) (cs := cs) i (R + S) =
      fixedRootCyclicNodeFieldSum (n := n) (a := a) (cs := cs) i R := by
  rw [
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild (R + S),
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild R]
  let Rnode : ZMod n → RawNormal.NodeRootFieldAssignment n b ds :=
    fun d => castRootFieldAssignment hchild (R d)
  let Snode : ZMod n → RawNormal.NodeRootFieldAssignment n b ds :=
    fun d => castRootFieldAssignment hchild (S d)
  have hcast :
      (fun d => castRootFieldAssignment hchild ((R + S) d)) =
        Rnode + Snode := by
    funext d rd
    have h :=
      congrFun (castRootFieldAssignment_add hchild (R d) (S d)) rd
    simpa [Rnode, Snode, Pi.add_apply] using h
  rw [hcast]
  exact
    cyclicNodeFixedRootFieldSum_shiftInvariant_of_boundaryShift_zero
      (n := n) (b := b) ds Rnode Snode hS

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_reindex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (e :
      (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) ≃
        (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds))
    (hphase :
      ∀ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds (e N)
              (fun d rd =>
                R d rd +
                  Pi.single
                    (M := fun _ : CyclicNodeRootBoundaryDomain n b ds =>
                      F2)
                    q (1 : F2) (d, rd)) +
            cyclicNodeInternalPhase (n := n) (b := b) ds (e N) =
          cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N R +
            cyclicNodeInternalPhase (n := n) (b := b) ds N) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_eq_of_reindex
    (n := n) (b := b) ds R
    (fun d rd =>
      R d rd +
        Pi.single
          (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
          q (1 : F2) (d, rd))
    e hphase

noncomputable def cyclicNodeNonRootFieldSingle
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0) :
    ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds :=
  fun d =>
    if hd : d = d0 then
      by
        subst d
        exact
          Pi.single
            (M := fun v : NonRootVertex (RTree.node b ds) =>
              RawNormal.NonRootFieldDomain n (RTree.node b ds) v → F2)
            v0
            (Pi.single
              (M := fun _ :
                RawNormal.NonRootFieldDomain n (RTree.node b ds) v0 => F2)
              nd0 (1 : F2))
    else 0

@[simp] theorem cyclicNodeNonRootFieldSingle_apply_self
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0) :
    cyclicNodeNonRootFieldSingle
        (n := n) (b := b) ds d0 v0 nd0 d0 v0 nd0 = 1 := by
  classical
  simp [cyclicNodeNonRootFieldSingle]

@[simp] theorem cyclicNodeNonRootFieldSingle_apply_ne_time
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 d : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (v : NonRootVertex (RTree.node b ds))
    (nd : RawNormal.NonRootFieldDomain n (RTree.node b ds) v)
    (h : d ≠ d0) :
    cyclicNodeNonRootFieldSingle
        (n := n) (b := b) ds d0 v0 nd0 d v nd = 0 := by
  classical
  simp [cyclicNodeNonRootFieldSingle, h]

@[simp] theorem cyclicNodeNonRootFieldSingle_apply_ne_vertex
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 v : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (nd : RawNormal.NonRootFieldDomain n (RTree.node b ds) v)
    (h : v ≠ v0) :
    cyclicNodeNonRootFieldSingle
        (n := n) (b := b) ds d0 v0 nd0 d0 v nd = 0 := by
  classical
  simp [cyclicNodeNonRootFieldSingle, h]

@[simp] theorem cyclicNodeNonRootFieldSingle_apply_ne_domain
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 nd : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (h : nd ≠ nd0) :
    cyclicNodeNonRootFieldSingle
        (n := n) (b := b) ds d0 v0 nd0 d0 v0 nd = 0 := by
  classical
  simp [cyclicNodeNonRootFieldSingle, h]

noncomputable def cyclicNodeNonRootFieldSingleToggleEquiv
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0) :
    (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) ≃
      (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) :=
  Equiv.addRight
    (cyclicNodeNonRootFieldSingle
      (n := n) (b := b) ds d0 v0 nd0)

@[simp] theorem cyclicNodeNonRootFieldSingleToggleEquiv_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 d : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (v : NonRootVertex (RTree.node b ds))
    (nd : RawNormal.NonRootFieldDomain n (RTree.node b ds) v)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) :
    cyclicNodeNonRootFieldSingleToggleEquiv
        (n := n) (b := b) ds d0 v0 nd0 N d v nd =
      N d v nd +
        cyclicNodeNonRootFieldSingle
          (n := n) (b := b) ds d0 v0 nd0 d v nd := rfl

@[simp] theorem cyclicNodeNonRootFieldSingleToggleEquiv_apply_self
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) :
    cyclicNodeNonRootFieldSingleToggleEquiv
        (n := n) (b := b) ds d0 v0 nd0 N d0 v0 nd0 =
      N d0 v0 nd0 + 1 := by
  simp

noncomputable def cyclicNodeNonRootFieldTranslationEquiv
    {n b : Nat} [NeZero n] (ds : List RTree)
    (τ : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) :
    (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) ≃
      (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) :=
  Equiv.addRight τ

@[simp] theorem cyclicNodeNonRootFieldTranslationEquiv_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (τ : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds)
    (d : ZMod n)
    (v : NonRootVertex (RTree.node b ds))
    (nd : RawNormal.NonRootFieldDomain n (RTree.node b ds) v) :
    cyclicNodeNonRootFieldTranslationEquiv
        (n := n) (b := b) ds τ N d v nd =
      N d v nd + τ d v nd := rfl

noncomputable def cyclicNodeNonRootFieldPair
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (d1 : ZMod n)
    (v1 : NonRootVertex (RTree.node b ds))
    (nd1 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v1) :
    ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds :=
  cyclicNodeNonRootFieldSingle (n := n) (b := b) ds d0 v0 nd0 +
    cyclicNodeNonRootFieldSingle (n := n) (b := b) ds d1 v1 nd1

noncomputable def cyclicNodeNonRootFieldPairToggleEquiv
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (d1 : ZMod n)
    (v1 : NonRootVertex (RTree.node b ds))
    (nd1 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v1) :
    (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) ≃
      (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) :=
  cyclicNodeNonRootFieldTranslationEquiv
    (n := n) (b := b) ds
    (cyclicNodeNonRootFieldPair (n := n) (b := b) ds
      d0 v0 nd0 d1 v1 nd1)

@[simp] theorem cyclicNodeNonRootFieldPairToggleEquiv_apply
    {n b : Nat} [NeZero n] (ds : List RTree)
    (d0 d1 d : ZMod n)
    (v0 : NonRootVertex (RTree.node b ds))
    (nd0 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v0)
    (v1 : NonRootVertex (RTree.node b ds))
    (nd1 : RawNormal.NonRootFieldDomain n (RTree.node b ds) v1)
    (v : NonRootVertex (RTree.node b ds))
    (nd : RawNormal.NonRootFieldDomain n (RTree.node b ds) v)
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) :
    cyclicNodeNonRootFieldPairToggleEquiv
        (n := n) (b := b) ds d0 v0 nd0 d1 v1 nd1 N d v nd =
      N d v nd +
        cyclicNodeNonRootFieldPair
          (n := n) (b := b) ds d0 v0 nd0 d1 v1 nd1 d v nd := rfl

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (hroot :
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
          (fun d rd =>
            castRootFieldAssignment hchild (Rcyc d) rd +
              Pi.single
                (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
                (q.1, castRootFieldDomain hchild q.2) (1 : F2)
                (d, rd)) =
        cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
          (fun d => castRootFieldAssignment hchild (Rcyc d))) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc := by
  rw [
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild,
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild]
  have hshift :
      (fun d =>
        castRootFieldAssignment hchild
          (fun rd =>
            Rcyc d rd +
              Pi.single
                (M := fun _ :
                  ZMod n ×
                    RawNormal.RootFieldDomain n (childAt cs i) =>
                    F2)
                q (1 : F2) (d, rd))) =
        (fun d rd =>
          castRootFieldAssignment hchild (Rcyc d) rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              (q.1, castRootFieldDomain hchild q.2) (1 : F2)
              (d, rd)) := by
    funext d
    exact castRootFieldAssignment_add_single hchild (Rcyc d) q d
  rw [hshift]
  exact hroot

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_nodeReindex
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (e :
      (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds) ≃
        (ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds))
    (hphase :
      ∀ N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b ds,
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds (e N)
              (fun d rd =>
                castRootFieldAssignment hchild (Rcyc d) rd +
                  Pi.single
                    (M := fun _ : CyclicNodeRootBoundaryDomain n b ds =>
                      F2)
                    (q.1, castRootFieldDomain hchild q.2) (1 : F2)
                    (d, rd)) +
            cyclicNodeInternalPhase (n := n) (b := b) ds (e N) =
          cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds N
              (fun d => castRootFieldAssignment hchild (Rcyc d)) +
            cyclicNodeInternalPhase (n := n) (b := b) ds N) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_reindex
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      e hphase)

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_childRootFamily_reindex
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hweight :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (Rcyc p.1) p.2 +
                Pi.single
                  (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
                  (q.1, castRootFieldDomain hchild q.2) (1 : F2) p) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (Rcyc p.1) p.2)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_reindex
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      e hweight hdot)

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_childRootFamily_summand_reindex
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hsummand :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    (e Φ) p.1 p.2)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  castRootFieldAssignment hchild (Rcyc p.1) p.2 +
                    Pi.single
                      (M := fun _ :
                        CyclicNodeRootBoundaryDomain n b ds => F2)
                      (q.1, castRootFieldDomain hchild q.2)
                      (1 : F2) p)) =
          (∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    Φ p.1 p.2)
                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                  castRootFieldAssignment hchild (Rcyc p.1) p.2))) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_summand_reindex
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      e hsummand)

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_childRootFamily_shear
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (hℓ :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ℓ Φ =
          cyclicChildRootBoundaryMap (n := n) (b := b) ds Φ
            q.1 (castRootFieldDomain hchild q.2))
    (heval :
      cyclicChildRootBoundaryMap (n := n) (b := b) ds τ
        q.1 (castRootFieldDomain hchild q.2) = 0)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          castRootFieldAssignment hchild (Rcyc p.1) p.2) = 1)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_shear
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      ℓ τ hτ hℓ heval hdot hprod)

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShear
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ :
      cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds
        (q.1, castRootFieldDomain hchild q.2) τ = 0)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          castRootFieldAssignment hchild (Rcyc p.1) p.2) = 1)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds)
              (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds
                (q.1, castRootFieldDomain hchild q.2))
              τ hτ Φ) j)) =
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShear
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      τ hτ hdot hprod)

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSign
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ :
      cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds
        (q.1, castRootFieldDomain hchild q.2) τ = 0)
    (σ : F2)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          castRootFieldAssignment hchild (Rcyc p.1) p.2) = σ)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds)
              (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds
                (q.1, castRootFieldDomain hchild q.2))
              τ hτ Φ) j)) =
          (∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)) *
            bitSign
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds
                (q.1, castRootFieldDomain hchild q.2) Φ * (σ + 1))) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSign
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      τ hτ σ hdot hprod)

theorem cyclicNodeChildNonRootSumProduct_shearSign_of_single_factor
    {n b : Nat} [NeZero n] (ds : List RTree)
    (ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ : ℓ τ = 0)
    (σ : F2)
    (j0 : ChildIdx ds)
    (hother :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ∀ j : ChildIdx ds,
          j ≠ j0 →
            cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j
                ((f2ShearEquiv
                  (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j) =
              cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j (Φ j))
    (hselected :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j0
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j0) =
          cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j0 (Φ j0) *
            bitSign (ℓ Φ * (σ + 1))) :
    ∀ Φ : CyclicNodeChildRootFamily n b ds,
      (∏ j : ChildIdx ds,
        cyclicNodeChildNonRootSumAtRootFamily
          (n := n) (b := b) ds j
          ((f2ShearEquiv
            (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Φ j)) *
          bitSign (ℓ Φ * (σ + 1)) := by
  classical
  intro Φ
  let F : ChildIdx ds → ℤ := fun j =>
    cyclicNodeChildNonRootSumAtRootFamily
      (n := n) (b := b) ds j
      ((f2ShearEquiv
        (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)
  let G : ChildIdx ds → ℤ := fun j =>
    cyclicNodeChildNonRootSumAtRootFamily
      (n := n) (b := b) ds j (Φ j)
  have hF :
      (∏ j : ChildIdx ds, F j) =
        F j0 * Finset.prod (Finset.univ.erase j0) F := by
    rw [← Finset.prod_insert (by simp)]
    congr
    ext j
    simp
  have hG :
      (∏ j : ChildIdx ds, G j) =
        G j0 * Finset.prod (Finset.univ.erase j0) G := by
    rw [← Finset.prod_insert (by simp)]
    congr
    ext j
    simp
  have htail :
      Finset.prod (Finset.univ.erase j0) F =
        Finset.prod (Finset.univ.erase j0) G := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    exact hother Φ j (by simpa using hj)
  have hsel : F j0 = G j0 * bitSign (ℓ Φ * (σ + 1)) := by
    exact hselected Φ
  change (∏ j : ChildIdx ds, F j) =
    (∏ j : ChildIdx ds, G j) * bitSign (ℓ Φ * (σ + 1))
  rw [hF, hG, htail, hsel]
  ring

theorem cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSignSingleFactor
    {n b : Nat} [NeZero n] (ds : List RTree)
    (q : CyclicNodeRootBoundaryDomain n b ds)
    (R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds)
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ :
      cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q τ = 0)
    (σ : F2)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          R p.1 p.2) = σ)
    (j0 : ChildIdx ds)
    (hother :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ∀ j : ChildIdx ds,
          j ≠ j0 →
            cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j
                ((f2ShearEquiv
                  (CyclicNodeChildRootFamily n b ds)
                  (cyclicChildRootBoundaryEvalLinearMap
                    (n := n) (b := b) ds q)
                  τ hτ Φ) j) =
              cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j (Φ j))
    (hselected :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j0
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds)
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q)
              τ hτ Φ) j0) =
          cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j0 (Φ j0) *
            bitSign
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ * (σ + 1))) :
    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
        (fun d rd =>
          R d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              q (1 : F2) (d, rd)) =
      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds R :=
  cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSign
    (n := n) (b := b) ds q R τ hτ σ hdot
    (cyclicNodeChildNonRootSumProduct_shearSign_of_single_factor
      (n := n) (b := b) ds
      (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q)
      τ hτ σ j0 hother hselected)

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSignSingleFactor
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (τ : CyclicNodeChildRootFamily n b ds)
    (hτ :
      cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds
        (q.1, castRootFieldDomain hchild q.2) τ = 0)
    (σ : F2)
    (hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          castRootFieldAssignment hchild (Rcyc p.1) p.2) = σ)
    (j0 : ChildIdx ds)
    (hother :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        ∀ j : ChildIdx ds,
          j ≠ j0 →
            cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j
                ((f2ShearEquiv
                  (CyclicNodeChildRootFamily n b ds)
                  (cyclicChildRootBoundaryEvalLinearMap
                    (n := n) (b := b) ds
                    (q.1, castRootFieldDomain hchild q.2))
                  τ hτ Φ) j) =
              cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j (Φ j))
    (hselected :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j0
            ((f2ShearEquiv
              (CyclicNodeChildRootFamily n b ds)
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds
                (q.1, castRootFieldDomain hchild q.2))
              τ hτ Φ) j0) =
          cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j0 (Φ j0) *
            bitSign
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds
                (q.1, castRootFieldDomain hchild q.2) Φ * (σ + 1))) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSignSingleFactor
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      τ hτ σ hdot j0 hother hselected)

theorem fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_childRootFamily_signFlip_reindex
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i))
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (e :
      CyclicNodeChildRootFamily n b ds ≃
        CyclicNodeChildRootFamily n b ds)
    (hprod :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        (∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j ((e Φ) j)) =
          -(∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Φ j)))
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                (e Φ) p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (Rcyc p.1) p.2 +
                Pi.single
                  (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
                  (q.1, castRootFieldDomain hchild q.2)
                  (1 : F2) p) =
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap (n := n) (b := b) ds
                Φ p.1 p.2)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              castRootFieldAssignment hchild (Rcyc p.1) p.2) + 1) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd =>
          Rcyc d rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (d, rd)) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
    (n := n) (a := a) (b := b) (cs := cs) i hchild q Rcyc
    (cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_signFlip_reindex
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun d => castRootFieldAssignment hchild (Rcyc d))
      e hprod hdot)

theorem fixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCore_of_oneFiber
    (hcancel : CyclicNodeFixedRootOneFiberCancellationCoreRule) :
    FixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCoreRule := by
  classical
  intro a cs _ha hchildren n _ hn i q Rcyc
  obtain ⟨b, ds, hchild⟩ :
      ∃ b ds, childAt cs i = RTree.node b ds := by
    cases h : childAt cs i with
    | node b ds => exact ⟨b, ds, rfl⟩
  have hcert : RawExpandedOpenRootSubtreeCert (RTree.node b ds) := by
    simpa [hchild] using
      RawExpandedOpenRootSubtreeCert.childAt_of_children
        (cs := cs) hchildren i
  rw [
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild,
    fixedRootCyclicNodeFieldSum_node_eq_cyclicNodeFixedRootFieldSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild]
  let qnode : CyclicNodeRootBoundaryDomain n b ds :=
    (q.1, castRootFieldDomain hchild q.2)
  let Rnode : ZMod n → RawNormal.NodeRootFieldAssignment n b ds :=
    fun d => castRootFieldAssignment hchild (Rcyc d)
  have hshift :
      (fun d =>
        castRootFieldAssignment hchild
          (fun rd =>
            Rcyc d rd +
              Pi.single
                (M := fun _ :
                  ZMod n ×
                    RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
                q (1 : F2) (d, rd))) =
        (fun d rd =>
          Rnode d rd +
            Pi.single
              (M := fun _ : CyclicNodeRootBoundaryDomain n b ds => F2)
              qnode (1 : F2) (d, rd)) := by
    funext d
    exact castRootFieldAssignment_add_single hchild (Rcyc d) q d
  rw [hshift]
  exact
    cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_oneFiber
      (n := n) (b := b) ds qnode Rnode
      (hcancel hcert n hn qnode Rnode)

theorem childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childOpenRootInternalKernelAt (n := n) (a := a) cs i φ =
      ∏ base : ChildExternalBaseCoordinate n a cs i,
        fixedRootCyclicNodeFieldSum
          (n := n) (a := a) (cs := cs) i
          (fun d =>
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm (base, d))) := by
  classical
  rw [
    childOpenRootInternalKernelAt_eq_externalNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot φ]
  unfold childOpenRootInternalExternalNodeFieldSum
  let e :=
    childExternalNodeFieldFamilyBaseCyclicEquiv
      (n := n) (a := a) (cs := cs) i
  let Rcyc :
      ChildExternalBaseCoordinate n a cs i →
        ZMod n → RawNormal.RootFieldAssignment n (childAt cs i) :=
    fun base d =>
      (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i φ)
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, d))
  calc
    (∑ Ψ : ChildExternalNodeFieldFamily n a cs i,
      bitSign
        (childInternalPhaseGivenRootDataAt
          (n := n) (a := a) cs
          (0 : RawNormal.NodeRootFieldAssignment n a cs) i
          ((nodeChildDataAtStructuredEquivExternalNormalAssignments
            (n := n) (a := a) (cs := cs) i hchildRoot).symm
            (childExternalNormalAssignmentOfRootNodeField
              (n := n) (a := a) (cs := cs) i φ Ψ)))) =
        ∑ Ψcyc :
          ChildExternalBaseCoordinate n a cs i →
            ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i),
          bitSign
            (childInternalPhaseGivenRootDataAt
              (n := n) (a := a) cs
              (0 : RawNormal.NodeRootFieldAssignment n a cs) i
              ((nodeChildDataAtStructuredEquivExternalNormalAssignments
                (n := n) (a := a) (cs := cs) i hchildRoot).symm
                (childExternalNormalAssignmentOfRootNodeField
                  (n := n) (a := a) (cs := cs) i φ (e.symm Ψcyc)))) := by
          exact
            Fintype.sum_equiv e
              (fun Ψ : ChildExternalNodeFieldFamily n a cs i =>
                bitSign
                  (childInternalPhaseGivenRootDataAt
                    (n := n) (a := a) cs
                    (0 : RawNormal.NodeRootFieldAssignment n a cs) i
                    ((nodeChildDataAtStructuredEquivExternalNormalAssignments
                      (n := n) (a := a) (cs := cs) i hchildRoot).symm
                      (childExternalNormalAssignmentOfRootNodeField
                        (n := n) (a := a) (cs := cs) i φ Ψ))))
              (fun Ψcyc :
                  ChildExternalBaseCoordinate n a cs i →
                    ZMod n →
                      RawNormal.NodeFieldAssignment n (childAt cs i) =>
                bitSign
                  (childInternalPhaseGivenRootDataAt
                    (n := n) (a := a) cs
                    (0 : RawNormal.NodeRootFieldAssignment n a cs) i
                    ((nodeChildDataAtStructuredEquivExternalNormalAssignments
                      (n := n) (a := a) (cs := cs) i hchildRoot).symm
                      (childExternalNormalAssignmentOfRootNodeField
                        (n := n) (a := a) (cs := cs) i φ
                        (e.symm Ψcyc)))))
              (by
                intro Ψ
                rfl)
    _ =
        ∑ Ψcyc :
          ChildExternalBaseCoordinate n a cs i →
            ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i),
          ∏ base : ChildExternalBaseCoordinate n a cs i,
            bitSign
              (cyclicRootTwistedPhaseForRootNode
                (n := n) (a := a) (cs := cs) i
                (Rcyc base) (Ψcyc base)) := by
          refine Finset.sum_congr rfl ?_
          intro Ψcyc _
          rw [
            childExternalNormalAssignmentOfRootNodeField_eq_baseCyclic
              (n := n) (a := a) (cs := cs) i φ Ψcyc]
          have hphase :=
            childInternalPhaseGivenRootDataAt_zero_eq_sum_base_cyclicPhase
              (n := n) (a := a) (cs := cs) i hchildRoot
              (fun base d =>
                { rootField := Rcyc base d
                  nodeField := Ψcyc base d })
          rw [hphase]
          simpa [cyclicRootTwistedPhaseForRootNode] using
            (prod_bitSign_eq_bitSign_sum
              (Finset.univ : Finset (ChildExternalBaseCoordinate n a cs i))
              (fun base =>
                cyclicRootTwistedPhaseForRootNode
                  (n := n) (a := a) (cs := cs) i
                  (Rcyc base) (Ψcyc base))).symm
    _ =
        ∏ base : ChildExternalBaseCoordinate n a cs i,
          ∑ N : ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i),
            bitSign
              (cyclicRootTwistedPhaseForRootNode
                (n := n) (a := a) (cs := cs) i (Rcyc base) N) := by
          simpa using
            (sum_pi_product_dep
              (ι := ChildExternalBaseCoordinate n a cs i)
              (α := fun _base =>
                ZMod n → RawNormal.NodeFieldAssignment n (childAt cs i))
              (R := ℤ)
              (fun base N =>
                bitSign
                  (cyclicRootTwistedPhaseForRootNode
                    (n := n) (a := a) (cs := cs) i (Rcyc base) N)))
    _ =
        ∏ base : ChildExternalBaseCoordinate n a cs i,
          fixedRootCyclicNodeFieldSum
            (n := n) (a := a) (cs := cs) i (Rcyc base) := by
          rfl

theorem childOpenRootInternalKernelAt_eq_sum_base_childRootFamily_boundaryMap
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childOpenRootInternalKernelAt (n := n) (a := a) cs i φ =
      ∑ Γ :
        ChildExternalBaseCoordinate n a cs i →
          CyclicNodeChildRootFamily n b ds,
        ∏ base : ChildExternalBaseCoordinate n a cs i,
          ((∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Γ base j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    (Γ base) q.1 q.2)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  castRootFieldAssignment hchild
                    ((nodeChildRootFieldFamilyAtExternalEquiv
                      (n := n) (a := a) (cs := cs) i φ)
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i).symm
                        (base, q.1))) q.2))) := by
  classical
  rw [childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
    (n := n) (a := a) (cs := cs) i hchildRoot φ]
  have hfactor :
      ∀ base : ChildExternalBaseCoordinate n a cs i,
        fixedRootCyclicNodeFieldSum
            (n := n) (a := a) (cs := cs) i
            (fun d =>
              (nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i φ)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm
                  (base, d))) =
          ∑ Φ : CyclicNodeChildRootFamily n b ds,
            (∏ j : ChildIdx ds,
              cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j (Φ j)) *
              bitSign
                (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                  (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                    cyclicChildRootBoundaryMap (n := n) (b := b) ds
                      Φ q.1 q.2)
                  (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                    castRootFieldAssignment hchild
                      ((nodeChildRootFieldFamilyAtExternalEquiv
                        (n := n) (a := a) (cs := cs) i φ)
                        ((childExternalCoordinateEquivBaseDiag
                          (n := n) (a := a) (cs := cs) i).symm
                          (base, q.1))) q.2)) := by
    intro base
    exact
      fixedRootCyclicNodeFieldSum_node_eq_sum_childRootFamily_product_nonRootSumAt_boundaryMap
        (n := n) (a := a) (b := b) (cs := cs) i hchild
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (base, d)))
  calc
    (∏ base : ChildExternalBaseCoordinate n a cs i,
      fixedRootCyclicNodeFieldSum
          (n := n) (a := a) (cs := cs) i
          (fun d =>
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm
                (base, d)))) =
        ∏ base : ChildExternalBaseCoordinate n a cs i,
          ∑ Φ : CyclicNodeChildRootFamily n b ds,
            (∏ j : ChildIdx ds,
              cyclicNodeChildNonRootSumAtRootFamily
                (n := n) (b := b) ds j (Φ j)) *
              bitSign
                (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                  (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                    cyclicChildRootBoundaryMap (n := n) (b := b) ds
                      Φ q.1 q.2)
                  (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                    castRootFieldAssignment hchild
                      ((nodeChildRootFieldFamilyAtExternalEquiv
                        (n := n) (a := a) (cs := cs) i φ)
                        ((childExternalCoordinateEquivBaseDiag
                          (n := n) (a := a) (cs := cs) i).symm
                          (base, q.1))) q.2)) := by
          refine Finset.prod_congr rfl ?_
          intro base _hbase
          exact hfactor base
    _ =
      ∑ Γ :
        ChildExternalBaseCoordinate n a cs i →
          CyclicNodeChildRootFamily n b ds,
        ∏ base : ChildExternalBaseCoordinate n a cs i,
          ((∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Γ base j)) *
            bitSign
              (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    (Γ base) q.1 q.2)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  castRootFieldAssignment hchild
                    ((nodeChildRootFieldFamilyAtExternalEquiv
                      (n := n) (a := a) (cs := cs) i φ)
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i).symm
                        (base, q.1))) q.2))) := by
          rw [← sum_pi_product_dep
            (ι := ChildExternalBaseCoordinate n a cs i)
            (R := ℤ)
            (α := fun _base : ChildExternalBaseCoordinate n a cs i =>
              CyclicNodeChildRootFamily n b ds)
            (fun base Φ =>
              (∏ j : ChildIdx ds,
                cyclicNodeChildNonRootSumAtRootFamily
                  (n := n) (b := b) ds j (Φ j)) *
                bitSign
                  (dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                    (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                      cyclicChildRootBoundaryMap (n := n) (b := b) ds
                        Φ q.1 q.2)
                    (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                      castRootFieldAssignment hchild
                        ((nodeChildRootFieldFamilyAtExternalEquiv
                          (n := n) (a := a) (cs := cs) i φ)
                        ((childExternalCoordinateEquivBaseDiag
                            (n := n) (a := a) (cs := cs) i).symm
                            (base, q.1))) q.2)))]

theorem childOpenRootInternalKernelAt_eq_sum_base_childRootFamily_boundaryMap_bitSignSum
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childOpenRootInternalKernelAt (n := n) (a := a) cs i φ =
      ∑ Γ :
        ChildExternalBaseCoordinate n a cs i →
          CyclicNodeChildRootFamily n b ds,
        (∏ base : ChildExternalBaseCoordinate n a cs i,
          ∏ j : ChildIdx ds,
            cyclicNodeChildNonRootSumAtRootFamily
              (n := n) (b := b) ds j (Γ base j)) *
          bitSign
            (∑ base : ChildExternalBaseCoordinate n a cs i,
              dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  cyclicChildRootBoundaryMap (n := n) (b := b) ds
                    (Γ base) q.1 q.2)
                (fun q : CyclicNodeRootBoundaryDomain n b ds =>
                  castRootFieldAssignment hchild
                    ((nodeChildRootFieldFamilyAtExternalEquiv
                      (n := n) (a := a) (cs := cs) i φ)
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i).symm
                        (base, q.1))) q.2)) := by
  classical
  rw [childOpenRootInternalKernelAt_eq_sum_base_childRootFamily_boundaryMap
    (n := n) (a := a) (b := b) (cs := cs) i hchild hchildRoot φ]
  refine Finset.sum_congr rfl ?_
  intro Γ _hΓ
  rw [Finset.prod_mul_distrib]
  rw [prod_bitSign_eq_bitSign_sum
    (Finset.univ : Finset (ChildExternalBaseCoordinate n a cs i))
    (fun base =>
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds
            (Γ base) q.1 q.2)
        (fun q : CyclicNodeRootBoundaryDomain n b ds =>
          castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm
                (base, q.1))) q.2))]

noncomputable def childRootBoundaryMapExponentAt
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (Γ :
      ChildExternalBaseCoordinate n a cs i →
        CyclicNodeChildRootFamily n b ds)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) : F2 :=
  ∑ base : ChildExternalBaseCoordinate n a cs i,
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
      (fun q : CyclicNodeRootBoundaryDomain n b ds =>
        cyclicChildRootBoundaryMap (n := n) (b := b) ds
          (Γ base) q.1 q.2)
      (fun q : CyclicNodeRootBoundaryDomain n b ds =>
        castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (base, q.1))) q.2)

noncomputable def childRootBoundaryMapDotAt
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) : F2 :=
  dotLinear (CyclicNodeRootBoundaryDomain n b ds)
    (fun q : CyclicNodeRootBoundaryDomain n b ds =>
      cyclicChildRootBoundaryMap (n := n) (b := b) ds
        Φ q.1 q.2)
    (fun q : CyclicNodeRootBoundaryDomain n b ds =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, q.1))) q.2)

theorem childRootBoundaryMapDotAt_eq_linearForm
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ φ =
      cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
        (fun d =>
          RawNormal.nodeFieldFromChildDataFamily
            (n := n) (a := b) (cs := ds)
            (fun j => (Φ j d, 0)))
        (fun d =>
          castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm
                (base, d)))) := by
  classical
  unfold childRootBoundaryMapDotAt
  let H : ZMod n → RawNormal.NodeChildDataFamily n b ds :=
    fun d j => (Φ j d, 0)
  let R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds :=
    fun d =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, d)))
  have hlin :=
    cyclicNodeRootBoundaryLinearForm_childDataFamily_eq_dot_boundaryMap
      (n := n) (b := b) ds H R
  simpa [H, R] using hlin.symm

theorem childRootBoundaryMapDotAt_eq_zero_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b [])
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs)
        i hchild base Φ δ = 0 := by
  simp [childRootBoundaryMapDotAt, cyclicChildRootBoundaryMap, ChildIdx]

theorem fixedRootCyclicNodeFieldSum_eq_of_childRootBoundaryMapDotAt_eq
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hdot :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        childRootBoundaryMapDotAt
            (n := n) (a := a) (b := b) (cs := cs)
            i hchild base Φ φ =
          childRootBoundaryMapDotAt
            (n := n) (a := a) (b := b) (cs := cs)
            i hchild base Φ ψ) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (base, d))) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i ψ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (base, d))) := by
  classical
  exact
    fixedRootCyclicNodeFieldSum_node_eq_of_boundaryMap_dot_eq
      (n := n) (a := a) (b := b) (cs := cs) i hchild
      (fun d =>
        (nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i ψ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, d)))
      (fun d =>
        (nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, d)))
      (by
        intro Φ
        exact
          hdot Φ)

theorem childRootBoundaryMapDotAt_add
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ
        (φ + ψ) =
      childRootBoundaryMapDotAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ φ +
        childRootBoundaryMapDotAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ ψ := by
  classical
  unfold childRootBoundaryMapDotAt
  let L : (CyclicNodeRootBoundaryDomain n b ds → F2) →ₗ[F2] F2 :=
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
      (fun q : CyclicNodeRootBoundaryDomain n b ds =>
        cyclicChildRootBoundaryMap (n := n) (b := b) ds
          Φ q.1 q.2)
  let A : CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun q =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, q.1))) q.2
  let B : CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun q =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i ψ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, q.1))) q.2
  let C : CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun q =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i (φ + ψ))
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, q.1))) q.2
  change L C = L A + L B
  have hC : C = A + B := by
    funext q
    dsimp [A, B, C]
    let ext : ChildExternalCoordinate n a cs i :=
      (childExternalCoordinateEquivBaseDiag
        (n := n) (a := a) (cs := cs) i).symm (base, q.1)
    have hfam :
        (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i (φ + ψ)) ext =
          (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ) ext +
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i ψ) ext := by
      funext rd
      rfl
    calc
      castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i (φ + ψ)) ext) q.2
          =
        castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ) ext +
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i ψ) ext) q.2 := by
            rw [hfam]
      _ =
        castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ) ext) q.2 +
          castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i ψ) ext) q.2 := by
            simpa [Pi.add_apply] using
              congrArg (fun F => F q.2)
                (castRootFieldAssignment_add (n := n) hchild
                  ((nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i φ) ext)
                  ((nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i ψ) ext))
  rw [hC]
  exact LinearMap.map_add L A B

theorem childRootBoundaryMapDotAt_eq_of_add_eq_zero
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hzero :
      childRootBoundaryMapDotAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ
          (φ + ψ) = 0) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ φ =
      childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ ψ := by
  let X :=
    childRootBoundaryMapDotAt
      (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ φ
  let Y :=
    childRootBoundaryMapDotAt
      (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ ψ
  have hadd :
      childRootBoundaryMapDotAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ
          (φ + ψ) =
        X + Y := by
    simpa [X, Y] using
      childRootBoundaryMapDotAt_add
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ φ ψ
  have hXY : X + Y = 0 := by
    simpa [hzero] using hadd.symm
  calc
    X = X + 0 := by simp
    _ = X + (Y + Y) := by
      rw [add_self_eq_zero_of_module_F2 Y]
    _ = (X + Y) + Y := by ac_rfl
    _ = Y := by simp [hXY]

theorem fixedRootCyclicNodeFieldSum_eq_of_childRootBoundaryMapDotAt_add_eq_zero
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hzero :
      ∀ Φ : CyclicNodeChildRootFamily n b ds,
        childRootBoundaryMapDotAt
            (n := n) (a := a) (b := b) (cs := cs)
            i hchild base Φ (φ + ψ) = 0) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (base, d))) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i ψ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (base, d))) := by
  exact
    fixedRootCyclicNodeFieldSum_eq_of_childRootBoundaryMapDotAt_eq
      (n := n) (a := a) (b := b) (cs := cs) i hchild base φ ψ
      (fun Φ =>
        childRootBoundaryMapDotAt_eq_of_add_eq_zero
          (n := n) (a := a) (b := b) (cs := cs)
          i hchild base Φ φ ψ (hzero Φ))

theorem childRootBoundaryMapExponentAt_add
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (Γ :
      ChildExternalBaseCoordinate n a cs i →
        CyclicNodeChildRootFamily n b ds)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childRootBoundaryMapExponentAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild Γ
        (φ + ψ) =
      childRootBoundaryMapExponentAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ +
        childRootBoundaryMapExponentAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild Γ ψ := by
  classical
  unfold childRootBoundaryMapExponentAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro base _hbase
  let L : (CyclicNodeRootBoundaryDomain n b ds → F2) →ₗ[F2] F2 :=
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
      (fun q : CyclicNodeRootBoundaryDomain n b ds =>
        cyclicChildRootBoundaryMap (n := n) (b := b) ds
          (Γ base) q.1 q.2)
  let A : CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun q =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, q.1))) q.2
  let B : CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun q =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i ψ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, q.1))) q.2
  let C : CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun q =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i (φ + ψ))
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (base, q.1))) q.2
  change L C = L A + L B
  have hC : C = A + B := by
    funext q
    dsimp [A, B, C]
    let ext : ChildExternalCoordinate n a cs i :=
      (childExternalCoordinateEquivBaseDiag
        (n := n) (a := a) (cs := cs) i).symm (base, q.1)
    have hfam :
        (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i (φ + ψ)) ext =
          (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ) ext +
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i ψ) ext := by
      funext rd
      rfl
    calc
      castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i (φ + ψ)) ext) q.2
          =
        castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ) ext +
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i ψ) ext) q.2 := by
            rw [hfam]
      _ =
        castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ) ext) q.2 +
          castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i ψ) ext) q.2 := by
            simpa [Pi.add_apply] using
              congrArg (fun F => F q.2)
                (castRootFieldAssignment_add (n := n) hchild
                  ((nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i φ) ext)
                  ((nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i ψ) ext))
  rw [hC]
  exact LinearMap.map_add L A B

theorem childRootBoundaryMapExponentAt_eq_of_add_eq_zero
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (Γ :
      ChildExternalBaseCoordinate n a cs i →
        CyclicNodeChildRootFamily n b ds)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hzero :
      childRootBoundaryMapExponentAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild Γ
          (φ + ψ) = 0) :
    childRootBoundaryMapExponentAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ =
      childRootBoundaryMapExponentAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild Γ ψ := by
  let X :=
    childRootBoundaryMapExponentAt
      (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ
  let Y :=
    childRootBoundaryMapExponentAt
      (n := n) (a := a) (b := b) (cs := cs) i hchild Γ ψ
  have hadd :
      childRootBoundaryMapExponentAt
          (n := n) (a := a) (b := b) (cs := cs) i hchild Γ
          (φ + ψ) =
        X + Y := by
    simpa [X, Y] using
      childRootBoundaryMapExponentAt_add
        (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ ψ
  have hXY : X + Y = 0 := by
    simpa [hzero] using hadd.symm
  calc
    X = X + 0 := by simp
    _ = X + (Y + Y) := by
      rw [add_self_eq_zero_of_module_F2 Y]
    _ = (X + Y) + Y := by ac_rfl
    _ = Y := by simp [hXY]

theorem childRootBoundaryMapExponentAt_eq_sum_base_linearForm
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (Γ :
      ChildExternalBaseCoordinate n a cs i →
        CyclicNodeChildRootFamily n b ds)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childRootBoundaryMapExponentAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ =
      ∑ base : ChildExternalBaseCoordinate n a cs i,
        cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
          (fun d =>
            RawNormal.nodeFieldFromChildDataFamily
              (n := n) (a := b) (cs := ds)
              (fun j => (Γ base j d, 0)))
          (fun d =>
            castRootFieldAssignment hchild
              ((nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i φ)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm
                  (base, d)))) := by
  classical
  unfold childRootBoundaryMapExponentAt
  refine Finset.sum_congr rfl ?_
  intro base _hbase
  let H : ZMod n → RawNormal.NodeChildDataFamily n b ds :=
    fun d j => (Γ base j d, 0)
  let R : ZMod n → RawNormal.NodeRootFieldAssignment n b ds :=
    fun d =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, d)))
  have hlin :=
    cyclicNodeRootBoundaryLinearForm_childDataFamily_eq_dot_boundaryMap
      (n := n) (b := b) ds H R
  simpa [H, R] using hlin.symm

theorem childOpenRootInternalKernelAt_eq_of_boundaryMapExponent_eq
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hexp :
      ∀ Γ :
        ChildExternalBaseCoordinate n a cs i →
          CyclicNodeChildRootFamily n b ds,
        childRootBoundaryMapExponentAt
            (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ =
          childRootBoundaryMapExponentAt
            (n := n) (a := a) (b := b) (cs := cs) i hchild Γ ψ) :
    childOpenRootInternalKernelAt (n := n) (a := a) cs i φ =
      childOpenRootInternalKernelAt (n := n) (a := a) cs i ψ := by
  classical
  rw [
    childOpenRootInternalKernelAt_eq_sum_base_childRootFamily_boundaryMap_bitSignSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild hchildRoot φ,
    childOpenRootInternalKernelAt_eq_sum_base_childRootFamily_boundaryMap_bitSignSum
      (n := n) (a := a) (b := b) (cs := cs) i hchild hchildRoot ψ]
  refine Finset.sum_congr rfl ?_
  intro Γ _hΓ
  change
    ((∏ base : ChildExternalBaseCoordinate n a cs i,
        ∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Γ base j)) *
        bitSign
          (childRootBoundaryMapExponentAt
            (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ)) =
      ((∏ base : ChildExternalBaseCoordinate n a cs i,
        ∏ j : ChildIdx ds,
          cyclicNodeChildNonRootSumAtRootFamily
            (n := n) (b := b) ds j (Γ base j)) *
        bitSign
          (childRootBoundaryMapExponentAt
            (n := n) (a := a) (b := b) (cs := cs) i hchild Γ ψ))
  rw [hexp Γ]

abbrev BranchConstraintImageBoundaryMapExponentDependsCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i φ =
          nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i ψ →
          ∀ {b : Nat} {ds : List RTree}
            (hchild : childAt cs i = RTree.node b ds)
            (Γ :
              ChildExternalBaseCoordinate n a cs i →
                CyclicNodeChildRootFamily n b ds),
            childRootBoundaryMapExponentAt
                (n := n) (a := a) (b := b) (cs := cs)
                i hchild Γ φ =
              childRootBoundaryMapExponentAt
                (n := n) (a := a) (b := b) (cs := cs)
                i hchild Γ ψ

abbrev BranchConstraintKernelBoundaryMapExponentZeroCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          ∀ {b : Nat} {ds : List RTree}
            (hchild : childAt cs i = RTree.node b ds)
            (Γ :
              ChildExternalBaseCoordinate n a cs i →
                CyclicNodeChildRootFamily n b ds),
            childRootBoundaryMapExponentAt
                (n := n) (a := a) (b := b) (cs := cs)
                i hchild Γ δ = 0

abbrev BranchConstraintKernelBoundaryLinearFormZeroCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          ∀ {b : Nat} {ds : List RTree}
            (hchild : childAt cs i = RTree.node b ds)
            (base : ChildExternalBaseCoordinate n a cs i)
            (Γ :
              ChildExternalBaseCoordinate n a cs i →
                CyclicNodeChildRootFamily n b ds),
            cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
              (fun d =>
                RawNormal.nodeFieldFromChildDataFamily
                  (n := n) (a := b) (cs := ds)
                  (fun j => (Γ base j d, 0)))
              (fun d =>
                castRootFieldAssignment hchild
                  ((nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i δ)
                    ((childExternalCoordinateEquivBaseDiag
                      (n := n) (a := a) (cs := cs) i).symm
                      (base, d)))) = 0

abbrev BranchConstraintKernelBoundaryMapDotZeroCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          ∀ {b : Nat} {ds : List RTree}
            (hchild : childAt cs i = RTree.node b ds)
            (base : ChildExternalBaseCoordinate n a cs i)
            (Φ : CyclicNodeChildRootFamily n b ds),
            childRootBoundaryMapDotAt
                (n := n) (a := a) (b := b) (cs := cs)
                i hchild base Φ δ = 0

abbrev BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
            ∀ {b : Nat} {ds : List RTree}
              (hchild : childAt cs i = RTree.node b ds)
              (base : ChildExternalBaseCoordinate n a cs i)
              (Φ : CyclicNodeChildRootFamily n b ds),
              childRootBoundaryMapDotAt
                  (n := n) (a := a) (b := b) (cs := cs)
                  i hchild base Φ δ = 0

theorem branchConstraintKernelBoundaryMapDotZeroCoreRule_of_nonLeaf
    (hnonleaf :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule) :
    BranchConstraintKernelBoundaryMapDotZeroCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ b ds hchild base Φ
  by_cases hleaf : ∃ b0 : Nat, childAt cs i = RTree.node b0 []
  · rcases hleaf with ⟨b0, hleafChild⟩
    have hnode : RTree.node b ds = RTree.node b0 [] :=
      hchild.symm.trans hleafChild
    cases hnode
    exact
      childRootBoundaryMapDotAt_eq_zero_leaf_child
        (n := n) (a := a) (b := b) (cs := cs)
        i hchild base Φ δ
  · exact
      hnonleaf ha hchildren n hn i δ hδ
        (by
          intro b0 hchild0
          exact hleaf ⟨b0, hchild0⟩)
        hchild base Φ

theorem branchConstraintKernelBoundaryLinearFormZeroCoreRule_of_dotZero
    (hdot : BranchConstraintKernelBoundaryMapDotZeroCoreRule) :
    BranchConstraintKernelBoundaryLinearFormZeroCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ b ds hchild base Γ
  rw [
    ← childRootBoundaryMapDotAt_eq_linearForm
      (n := n) (a := a) (b := b) (cs := cs)
      i hchild base (Γ base) δ]
  exact hdot ha hchildren n hn i δ hδ hchild base (Γ base)

theorem branchConstraintKernelBoundaryMapExponentZeroCoreRule_of_linearFormZero
    (hlinear : BranchConstraintKernelBoundaryLinearFormZeroCoreRule) :
    BranchConstraintKernelBoundaryMapExponentZeroCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ b ds hchild Γ
  rw [
    childRootBoundaryMapExponentAt_eq_sum_base_linearForm
      (n := n) (a := a) (b := b) (cs := cs) i hchild Γ δ]
  simp [hlinear ha hchildren n hn i δ hδ hchild]

theorem branchConstraintKernelBoundaryMapExponentZeroCoreRule_of_dotZero
    (hdot : BranchConstraintKernelBoundaryMapDotZeroCoreRule) :
    BranchConstraintKernelBoundaryMapExponentZeroCoreRule :=
  branchConstraintKernelBoundaryMapExponentZeroCoreRule_of_linearFormZero
    (branchConstraintKernelBoundaryLinearFormZeroCoreRule_of_dotZero hdot)

theorem branchConstraintImageBoundaryMapExponentDependsCoreRule_of_kernelZero
    (hzero : BranchConstraintKernelBoundaryMapExponentZeroCoreRule) :
    BranchConstraintImageBoundaryMapExponentDependsCoreRule := by
  intro a cs ha hchildren n _ hn i φ ψ hmap b ds hchild Γ
  let δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2 := φ + ψ
  have hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 := by
    rw [show δ = φ + ψ by rfl]
    rw [
      (nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i).map_add,
      hmap]
    ext t c
    exact
      add_self_eq_zero_of_module_F2
        ((nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) t c)
  exact
    childRootBoundaryMapExponentAt_eq_of_add_eq_zero
      (n := n) (a := a) (b := b) (cs := cs) i hchild Γ φ ψ
      (by
        simpa [δ] using
          hzero ha hchildren n hn i δ hδ hchild Γ)

theorem branchConstraintImageKernelDependsCoreRule_of_boundaryMapExponent
    (hexp : BranchConstraintImageBoundaryMapExponentDependsCoreRule) :
    BranchConstraintImageKernelDependsCoreRule := by
  intro a cs ha hchildren n _ hn i φ ψ hmap
  obtain ⟨b, ds, hchild⟩ :
      ∃ b ds, childAt cs i = RTree.node b ds := by
    cases h : childAt cs i with
    | node b ds => exact ⟨b, ds, rfl⟩
  exact
    childOpenRootInternalKernelAt_eq_of_boundaryMapExponent_eq
      (n := n) (a := a) (b := b) (cs := cs) i hchild
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      φ ψ
      (hexp ha hchildren n hn i φ ψ hmap hchild)

theorem branchConstraintImageKernelDependsCoreRule_of_boundaryLinearFormZero
    (hlinear : BranchConstraintKernelBoundaryLinearFormZeroCoreRule) :
    BranchConstraintImageKernelDependsCoreRule :=
  branchConstraintImageKernelDependsCoreRule_of_boundaryMapExponent
    (branchConstraintImageBoundaryMapExponentDependsCoreRule_of_kernelZero
      (branchConstraintKernelBoundaryMapExponentZeroCoreRule_of_linearFormZero
        hlinear))

theorem branchConstraintImageKernelDependsCoreRule_of_boundaryMapDotZero
    (hdot : BranchConstraintKernelBoundaryMapDotZeroCoreRule) :
    BranchConstraintImageKernelDependsCoreRule :=
  branchConstraintImageKernelDependsCoreRule_of_boundaryLinearFormZero
    (branchConstraintKernelBoundaryLinearFormZeroCoreRule_of_dotZero hdot)

theorem childRootBoundaryMapDotAt_eq_zero_of_boundaryLinearFormZeroCore
    (hlinear : BranchConstraintKernelBoundaryLinearFormZeroCoreRule)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a)
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C)
    (n : Nat) [NeZero n]
    (hn : 1 < n)
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0)
    {b : Nat} {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs)
        i hchild base Φ δ = 0 := by
  rw [
    childRootBoundaryMapDotAt_eq_linearForm
      (n := n) (a := a) (b := b) (cs := cs)
      i hchild base Φ δ]
  exact
    hlinear ha hchildren n hn i δ hδ hchild base
      (fun _base : ChildExternalBaseCoordinate n a cs i => Φ)

theorem childOpenRootInternalKernelAt_eq_of_branchConstraintMap_eq_of_fixedRootFactor
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (_hmap :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i φ =
        nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ)
    (hfactor :
      ∀ base : ChildExternalBaseCoordinate n a cs i,
        fixedRootCyclicNodeFieldSum
            (n := n) (a := a) (cs := cs) i
            (fun d =>
              (nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i φ)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, d))) =
          fixedRootCyclicNodeFieldSum
            (n := n) (a := a) (cs := cs) i
            (fun d =>
              (nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i ψ)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, d)))) :
    childOpenRootInternalKernelAt (n := n) (a := a) cs i φ =
      childOpenRootInternalKernelAt (n := n) (a := a) cs i ψ := by
  classical
  rw [
    childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot φ,
    childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot ψ]
  refine Finset.prod_congr rfl ?_
  intro base _hbase
  exact hfactor base

theorem fixedRootCyclicNodeFieldSum_eq_of_branchConstraintMap_eq_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (_hmap :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i φ =
        nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ)
    (base : ChildExternalBaseCoordinate n a cs i) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, d))) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i ψ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, d))) := by
  rw [
    fixedRootCyclicNodeFieldSum_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild,
    fixedRootCyclicNodeFieldSum_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild]

theorem internalKernelSingletonShiftInvariantAt_of_fixedRootFactorSingletonShift
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (hfactor :
      ∀ (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
        (base : ChildExternalBaseCoordinate n a cs i),
        fixedRootCyclicNodeFieldSum
            (n := n) (a := a) (cs := cs) i
            (fun t =>
              (nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i
                (φ +
                  Pi.single
                    (M := fun _ :
                      RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                    d (1 : F2)))
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, t))) =
          fixedRootCyclicNodeFieldSum
            (n := n) (a := a) (cs := cs) i
            (fun t =>
              (nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i φ)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, t)))) :
    InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d := by
  classical
  intro φ
  rw [
    childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot
      (φ +
        Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2)),
    childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot φ]
  refine Finset.prod_congr rfl ?_
  intro base _hbase
  exact hfactor φ base

abbrev BranchConstraintImageFixedRootFactorDependsCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i φ =
          nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i ψ →
          ∀ base : ChildExternalBaseCoordinate n a cs i,
            fixedRootCyclicNodeFieldSum
                (n := n) (a := a) (cs := cs) i
                (fun d =>
                  (nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i φ)
                    ((childExternalCoordinateEquivBaseDiag
                      (n := n) (a := a) (cs := cs) i).symm
                      (base, d))) =
              fixedRootCyclicNodeFieldSum
                (n := n) (a := a) (cs := cs) i
                (fun d =>
                  (nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i ψ)
                    ((childExternalCoordinateEquivBaseDiag
                      (n := n) (a := a) (cs := cs) i).symm
                      (base, d)))

abbrev BranchConstraintImageFixedRootFactorDependsNonLeafCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i φ =
          nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i ψ →
          ∀ base : ChildExternalBaseCoordinate n a cs i,
            fixedRootCyclicNodeFieldSum
                (n := n) (a := a) (cs := cs) i
                (fun d =>
                  (nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i φ)
                    ((childExternalCoordinateEquivBaseDiag
                      (n := n) (a := a) (cs := cs) i).symm
                      (base, d))) =
              fixedRootCyclicNodeFieldSum
                (n := n) (a := a) (cs := cs) i
                (fun d =>
                  (nodeChildRootFieldFamilyAtExternalEquiv
                    (n := n) (a := a) (cs := cs) i ψ)
                    ((childExternalCoordinateEquivBaseDiag
                      (n := n) (a := a) (cs := cs) i).symm
                      (base, d)))

theorem branchConstraintImageFixedRootFactorDependsCoreRule_of_nonLeaf
    (hnonleaf :
      BranchConstraintImageFixedRootFactorDependsNonLeafCoreRule) :
    BranchConstraintImageFixedRootFactorDependsCoreRule := by
  intro a cs ha hchildren n _ hn i φ ψ hmap base
  by_cases hleaf : ∃ b : Nat, childAt cs i = RTree.node b []
  · rcases hleaf with ⟨b, hchild⟩
    exact
      fixedRootCyclicNodeFieldSum_eq_of_branchConstraintMap_eq_leaf_child
        (n := n) (a := a) (b := b) (cs := cs) i hchild φ ψ hmap base
  · exact
      hnonleaf ha hchildren n hn i φ ψ
        (by
          intro b hchild
          exact hleaf ⟨b, hchild⟩)
        hmap base

theorem branchConstraintImageFixedRootFactorDependsCoreRule_of_boundaryLinearFormZero
    (hlinear : BranchConstraintKernelBoundaryLinearFormZeroCoreRule) :
    BranchConstraintImageFixedRootFactorDependsCoreRule := by
  intro a cs ha hchildren n _ hn i φ ψ hmap base
  obtain ⟨b, ds, hchild⟩ :
      ∃ b ds, childAt cs i = RTree.node b ds := by
    cases h : childAt cs i with
    | node b ds => exact ⟨b, ds, rfl⟩
  let δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2 := φ + ψ
  have hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 := by
    rw [show δ = φ + ψ by rfl]
    rw [
      (nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i).map_add,
      hmap]
    ext t c
    exact
      add_self_eq_zero_of_module_F2
        ((nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) t c)
  exact
    fixedRootCyclicNodeFieldSum_eq_of_childRootBoundaryMapDotAt_add_eq_zero
      (n := n) (a := a) (b := b) (cs := cs) i hchild base φ ψ
      (fun Φ =>
        childRootBoundaryMapDotAt_eq_zero_of_boundaryLinearFormZeroCore
          hlinear ha hchildren n hn i δ hδ hchild base Φ)

theorem branchConstraintImageFixedRootFactorDependsCoreRule_of_boundaryMapDotZero
    (hdot : BranchConstraintKernelBoundaryMapDotZeroCoreRule) :
    BranchConstraintImageFixedRootFactorDependsCoreRule :=
  branchConstraintImageFixedRootFactorDependsCoreRule_of_boundaryLinearFormZero
    (branchConstraintKernelBoundaryLinearFormZeroCoreRule_of_dotZero hdot)

theorem branchConstraintKernelBoundaryLinearFormZeroCoreRule_of_dotZeroNonLeaf
    (hdot :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule) :
    BranchConstraintKernelBoundaryLinearFormZeroCoreRule :=
  branchConstraintKernelBoundaryLinearFormZeroCoreRule_of_dotZero
    (branchConstraintKernelBoundaryMapDotZeroCoreRule_of_nonLeaf hdot)

theorem branchConstraintImageKernelDependsCoreRule_of_boundaryMapDotZeroNonLeaf
    (hdot :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule) :
    BranchConstraintImageKernelDependsCoreRule :=
  branchConstraintImageKernelDependsCoreRule_of_boundaryMapDotZero
    (branchConstraintKernelBoundaryMapDotZeroCoreRule_of_nonLeaf hdot)

theorem branchConstraintImageFixedRootFactorDependsCoreRule_of_boundaryMapDotZeroNonLeaf
    (hdot :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule) :
    BranchConstraintImageFixedRootFactorDependsCoreRule :=
  branchConstraintImageFixedRootFactorDependsCoreRule_of_boundaryMapDotZero
    (branchConstraintKernelBoundaryMapDotZeroCoreRule_of_nonLeaf hdot)

theorem branchConstraintImageFixedRootFactorDependsNonLeafCoreRule_of_boundaryMapDotZeroNonLeaf
    (hdot :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule) :
    BranchConstraintImageFixedRootFactorDependsNonLeafCoreRule := by
  intro a cs ha hchildren n _ hn i φ ψ hnonleaf hmap base
  obtain ⟨b, ds, hchild⟩ :
      ∃ b ds, childAt cs i = RTree.node b ds := by
    cases h : childAt cs i with
    | node b ds => exact ⟨b, ds, rfl⟩
  let δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2 := φ + ψ
  have hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 := by
    rw [show δ = φ + ψ by rfl]
    rw [
      (nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i).map_add,
      hmap]
    ext t c
    exact
      add_self_eq_zero_of_module_F2
        ((nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) t c)
  exact
    fixedRootCyclicNodeFieldSum_eq_of_childRootBoundaryMapDotAt_add_eq_zero
      (n := n) (a := a) (b := b) (cs := cs) i hchild base φ ψ
      (fun Φ =>
        hdot ha hchildren n hn i δ hδ hnonleaf hchild base Φ)

theorem branchConstraintKernelShiftInvariantCoreRule_of_boundaryMapDotZeroNonLeaf
    (hdot :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule) :
    BranchConstraintKernelShiftInvariantCoreRule :=
  branchConstraintKernelShiftInvariantCoreRule_of_imageKernelDependsCore
    (branchConstraintImageKernelDependsCoreRule_of_boundaryMapDotZeroNonLeaf
      hdot)

theorem branchConstraintImageKernelDependsCoreRule_of_fixedRootFactorDependsCore
    (hfactor : BranchConstraintImageFixedRootFactorDependsCoreRule) :
    BranchConstraintImageKernelDependsCoreRule := by
  intro a cs ha hchildren n _ hn i φ ψ hmap
  exact
    childOpenRootInternalKernelAt_eq_of_branchConstraintMap_eq_of_fixedRootFactor
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      φ ψ hmap
      (hfactor ha hchildren n hn i φ ψ hmap)

noncomputable def nodeChildRootFieldShiftAtExternalBase
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (base : ChildExternalBaseCoordinate n a cs i) :
    ZMod n → RawNormal.RootFieldAssignment n (childAt cs i) :=
  fun d rd =>
    δ
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i).symm
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, d), rd))

@[simp] theorem nodeChildRootFieldShiftAtExternalBase_apply
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (base : ChildExternalBaseCoordinate n a cs i)
    (d : ZMod n)
    (rd : RawNormal.RootFieldDomain n (childAt cs i)) :
    nodeChildRootFieldShiftAtExternalBase
        (n := n) (a := a) (cs := cs) i δ base d rd =
      δ
        ((nodeChildRootFieldDomainStructuredEquiv
          (n := n) (a := a) (cs := cs) i).symm
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, d), rd)) :=
  rfl

theorem nodeChildRootFieldShiftAtExternalBase_single_eq_root_single_of_base
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i)
    (hbase :
      base =
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1) :
    nodeChildRootFieldShiftAtExternalBase
        (n := n) (a := a) (cs := cs) i
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
        base =
      fun t rd =>
        Pi.single
          (M := fun _ :
            ZMod n × RawNormal.RootFieldDomain n (childAt cs i) => F2)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i
            ((nodeChildRootFieldDomainStructuredEquiv
              (n := n) (a := a) (cs := cs) i d).1)).2,
            (nodeChildRootFieldDomainStructuredEquiv
              (n := n) (a := a) (cs := cs) i d).2)
          (1 : F2) (t, rd) := by
  classical
  let e := nodeChildRootFieldDomainStructuredEquiv
    (n := n) (a := a) (cs := cs) i
  let bd := childExternalCoordinateEquivBaseDiag
    (n := n) (a := a) (cs := cs) i (e d).1
  let q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    (bd.2, (e d).2)
  funext t rd
  change
    nodeChildRootFieldShiftAtExternalBase
        (n := n) (a := a) (cs := cs) i
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
        base t rd =
      Pi.single
        (M := fun _ :
          ZMod n × RawNormal.RootFieldDomain n (childAt cs i) => F2)
        q (1 : F2) (t, rd)
  by_cases hp : (t, rd) = q
  · have ht : t = bd.2 := by
      simpa [q] using congrArg Prod.fst hp
    have hrd : rd = (e d).2 := by
      simpa [q] using congrArg Prod.snd hp
    have hbd : (base, t) = bd := by
      exact Prod.ext hbase ht
    have hext :
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, t) =
          (e d).1 := by
      rw [hbd]
      exact
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm_apply_apply
          (e d).1
    have hpair :
        ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
          e d := by
      exact Prod.ext hext hrd
    have hdomain :
        e.symm
          ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
          d := by
      rw [hpair]
      exact e.symm_apply_apply d
    unfold nodeChildRootFieldShiftAtExternalBase
    rw [hdomain, hp]
    simp
  · have hdomain_ne :
        e.symm
          ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t), rd) ≠
          d := by
      intro hdomain
      apply hp
      have hpair :
          ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
            e d := by
        exact (e.symm_apply_eq).1 hdomain
      have hext :
          (childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, t) =
            (e d).1 := by
        simpa using congrArg Prod.fst hpair
      have hrd : rd = (e d).2 := by
        simpa using congrArg Prod.snd hpair
      have hbd :
          (base, t) = bd := by
        have happ :=
          congrArg
            (childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i) hext
        simpa [bd] using happ
      exact Prod.ext
        (by simpa [q] using congrArg Prod.snd hbd)
        (by simpa [q] using hrd)
    unfold nodeChildRootFieldShiftAtExternalBase
    rw [Pi.single_eq_of_ne hdomain_ne, Pi.single_eq_of_ne hp]

theorem nodeChildRootFieldShiftAtExternalBase_single_eq_zero_of_ne_base
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i)
    (hbase :
      base ≠
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1) :
    nodeChildRootFieldShiftAtExternalBase
        (n := n) (a := a) (cs := cs) i
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
        base = 0 := by
  classical
  let e := nodeChildRootFieldDomainStructuredEquiv
    (n := n) (a := a) (cs := cs) i
  let bd := childExternalCoordinateEquivBaseDiag
    (n := n) (a := a) (cs := cs) i (e d).1
  funext t rd
  unfold nodeChildRootFieldShiftAtExternalBase
  apply Pi.single_eq_of_ne
  intro hdomain
  have hpair :
      ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
        e d := by
    exact (e.symm_apply_eq).1 hdomain
  have hext :
      (childExternalCoordinateEquivBaseDiag
        (n := n) (a := a) (cs := cs) i).symm (base, t) =
        (e d).1 := by
    simpa using congrArg Prod.fst hpair
  have hbd :
      (base, t) = bd := by
    have happ :=
      congrArg
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i) hext
    simpa [bd] using happ
  exact hbase (by simpa [bd] using congrArg Prod.fst hbd)

theorem fixedRootCyclicNodeFieldSum_singletonShiftAtExternalBase_eq_rootSingleton
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (hbase :
      base =
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (Rcyc +
          nodeChildRootFieldShiftAtExternalBase
            (n := n) (a := a) (cs := cs) i
            (Pi.single
              (M := fun _ :
                RawNormal.NodeChildRootFieldDomain n a cs i => F2)
              d (1 : F2))
            base) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t rd =>
          Rcyc t rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i
                ((nodeChildRootFieldDomainStructuredEquiv
                  (n := n) (a := a) (cs := cs) i d).1)).2,
                (nodeChildRootFieldDomainStructuredEquiv
                  (n := n) (a := a) (cs := cs) i d).2)
              (1 : F2) (t, rd)) := by
  have hshift :=
    nodeChildRootFieldShiftAtExternalBase_single_eq_root_single_of_base
      (n := n) (a := a) (cs := cs) i d base hbase
  congr 1
  funext t rd
  rw [hshift]
  rfl

theorem fixedRootCyclicNodeFieldSum_singletonShiftAtExternalBase_ne
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i))
    (hbase :
      base ≠
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (Rcyc +
          nodeChildRootFieldShiftAtExternalBase
            (n := n) (a := a) (cs := cs) i
            (Pi.single
              (M := fun _ :
                RawNormal.NodeChildRootFieldDomain n a cs i => F2)
              d (1 : F2))
            base) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc := by
  have hzero :=
    nodeChildRootFieldShiftAtExternalBase_single_eq_zero_of_ne_base
      (n := n) (a := a) (cs := cs) i d base hbase
  congr 1
  funext t rd
  rw [hzero]
  simp

theorem fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_add_eq_shiftAtBase
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (base : ChildExternalBaseCoordinate n a cs i) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i (φ + δ))
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t))) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        ((fun t =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t))) +
          nodeChildRootFieldShiftAtExternalBase
            (n := n) (a := a) (cs := cs) i δ base) := by
  congr 1

theorem fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_singletonShift_ne_base
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i)
    (hbase :
      base ≠
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i
            (φ +
              Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2)))
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t))) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t))) := by
  rw [
    fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_add_eq_shiftAtBase
      (n := n) (a := a) (cs := cs) i φ
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2))
      base]
  exact
    fixedRootCyclicNodeFieldSum_singletonShiftAtExternalBase_ne
      (n := n) (a := a) (cs := cs) i d base
      (fun t =>
        (nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, t)))
      hbase

theorem fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_singletonShift_eq_rootSingleton
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i)
    (hbase :
      base =
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i
            (φ +
              Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2)))
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t))) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t rd =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t)) rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i
                ((nodeChildRootFieldDomainStructuredEquiv
                  (n := n) (a := a) (cs := cs) i d).1)).2,
                (nodeChildRootFieldDomainStructuredEquiv
                  (n := n) (a := a) (cs := cs) i d).2)
              (1 : F2) (t, rd)) := by
  rw [
    fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_add_eq_shiftAtBase
      (n := n) (a := a) (cs := cs) i φ
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2))
      base]
  exact
    fixedRootCyclicNodeFieldSum_singletonShiftAtExternalBase_eq_rootSingleton
      (n := n) (a := a) (cs := cs) i d base
      (fun t =>
        (nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, t)))
      hbase

theorem fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_singletonShift_of_selectedRootSingleton
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (base : ChildExternalBaseCoordinate n a cs i)
    (hroot :
      fixedRootCyclicNodeFieldSum
          (n := n) (a := a) (cs := cs) i
          (fun t rd =>
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i
                  ((nodeChildRootFieldDomainStructuredEquiv
                    (n := n) (a := a) (cs := cs) i d).1)).1, t)) rd +
              Pi.single
                (M := fun _ :
                  ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                    F2)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i
                  ((nodeChildRootFieldDomainStructuredEquiv
                    (n := n) (a := a) (cs := cs) i d).1)).2,
                  (nodeChildRootFieldDomainStructuredEquiv
                    (n := n) (a := a) (cs := cs) i d).2)
                (1 : F2) (t, rd)) =
        fixedRootCyclicNodeFieldSum
          (n := n) (a := a) (cs := cs) i
          (fun t =>
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i
                  ((nodeChildRootFieldDomainStructuredEquiv
                    (n := n) (a := a) (cs := cs) i d).1)).1, t)))) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i
            (φ +
              Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2)))
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t))) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun t =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t))) := by
  classical
  by_cases hbase :
      base =
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1
  · subst base
    rw [
      fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_singletonShift_eq_rootSingleton
        (n := n) (a := a) (cs := cs) i φ d
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1)
        rfl]
    exact hroot
  · exact
      fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_singletonShift_ne_base
        (n := n) (a := a) (cs := cs) i φ d base hbase

theorem childRootBoundaryMapDotAt_eq_linearForm_shiftAtBase
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ δ =
      cyclicNodeRootBoundaryLinearForm (n := n) (b := b) ds
        (fun d =>
          RawNormal.nodeFieldFromChildDataFamily
            (n := n) (a := b) (cs := ds)
            (fun j => (Φ j d, 0)))
        (fun d =>
          castRootFieldAssignment hchild
            (nodeChildRootFieldShiftAtExternalBase
              (n := n) (a := a) (cs := cs) i δ base d)) := by
  rw [
    childRootBoundaryMapDotAt_eq_linearForm
      (n := n) (a := a) (b := b) (cs := cs)
      i hchild base Φ δ]
  rfl

theorem childRootBoundaryMapDotAt_eq_sum_sliceProjection_shiftAtBase
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ δ =
      ∑ d : ZMod n,
        dotLinear (RawNormal.RootFieldDomain n (RTree.node b ds))
          (cyclicChildRootBoundarySliceProjectionLinearMap
            (n := n) (b := b) ds
            (cyclicChildRootTwistedDiffSlice
              (n := n) (b := b) ds Φ d))
          (fun rd =>
            castRootFieldAssignment hchild
              (nodeChildRootFieldShiftAtExternalBase
                (n := n) (a := a) (cs := cs) i δ base d) rd) := by
  classical
  unfold childRootBoundaryMapDotAt
  rw [dotLinear_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro d _hd
  rw [dotLinear_apply]
  refine Finset.sum_congr rfl ?_
  intro rd _hrd
  rw [
    cyclicChildRootBoundaryMap_apply_eq_sliceProjection_twistedDiff
      (n := n) (b := b) ds Φ d rd]
  rfl

theorem childRootBoundaryMapDotAt_eq_zero_of_forall_sliceProjection_dot_zero
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs) {ds : List RTree}
    (hchild : childAt cs i = RTree.node b ds)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Φ : CyclicNodeChildRootFamily n b ds)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hzero :
      ∀ d : ZMod n,
        dotLinear (RawNormal.RootFieldDomain n (RTree.node b ds))
          (cyclicChildRootBoundarySliceProjectionLinearMap
            (n := n) (b := b) ds
            (cyclicChildRootTwistedDiffSlice
              (n := n) (b := b) ds Φ d))
          (fun rd =>
            castRootFieldAssignment hchild
              (nodeChildRootFieldShiftAtExternalBase
                (n := n) (a := a) (cs := cs) i δ base d) rd) = 0) :
    childRootBoundaryMapDotAt
        (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ δ = 0 := by
  rw [
    childRootBoundaryMapDotAt_eq_sum_sliceProjection_shiftAtBase
      (n := n) (a := a) (b := b) (cs := cs) i hchild base Φ δ]
  exact Finset.sum_eq_zero (fun d _hd => hzero d)

@[simp] theorem nodeChildRootFieldFamilyAtExternalEquiv_add_baseDiag
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (φ δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (base : ChildExternalBaseCoordinate n a cs i)
    (d : ZMod n)
    (rd : RawNormal.RootFieldDomain n (childAt cs i)) :
    (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i (φ + δ))
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, d)) rd =
      (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i φ)
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, d)) rd +
      nodeChildRootFieldShiftAtExternalBase
        (n := n) (a := a) (cs := cs) i δ base d rd :=
  rfl

theorem childOpenRootInternalKernelAt_shiftInvariant_of_baseFixedRootShiftInvariant
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hbase :
      ∀ base : ChildExternalBaseCoordinate n a cs i,
        ∀ Rcyc : ZMod n →
            RawNormal.RootFieldAssignment n (childAt cs i),
          fixedRootCyclicNodeFieldSum (n := n) (a := a) (cs := cs) i
              (Rcyc +
                nodeChildRootFieldShiftAtExternalBase
                  (n := n) (a := a) (cs := cs) i δ base) =
            fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i Rcyc) :
    ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
      childOpenRootInternalKernelAt (n := n) (a := a) cs i (φ + δ) =
        childOpenRootInternalKernelAt (n := n) (a := a) cs i φ := by
  classical
  intro φ
  rw [
    childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot (φ + δ),
    childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot φ]
  refine Finset.prod_congr rfl ?_
  intro base _
  let Rcyc : ZMod n → RawNormal.RootFieldAssignment n (childAt cs i) :=
    fun d =>
      (nodeChildRootFieldFamilyAtExternalEquiv
        (n := n) (a := a) (cs := cs) i φ)
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i).symm (base, d))
  have hfun :
      (fun d =>
        (nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i (φ + δ))
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, d))) =
        Rcyc +
          nodeChildRootFieldShiftAtExternalBase
            (n := n) (a := a) (cs := cs) i δ base := by
    funext d rd
    exact
      nodeChildRootFieldFamilyAtExternalEquiv_add_baseDiag
        (n := n) (a := a) (cs := cs) i φ δ base d rd
  calc
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i (φ + δ))
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, d))) =
        fixedRootCyclicNodeFieldSum
          (n := n) (a := a) (cs := cs) i
          (Rcyc +
            nodeChildRootFieldShiftAtExternalBase
              (n := n) (a := a) (cs := cs) i δ base) := by
          rw [hfun]
    _ =
        fixedRootCyclicNodeFieldSum
          (n := n) (a := a) (cs := cs) i Rcyc :=
          hbase base Rcyc
    _ =
        fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
          (fun d =>
            (nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, d))) := rfl

theorem childOpenRootInternalKernelAt_eq_of_branchConstraintMap_eq_of_baseFixedRootShiftInvariant
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ ψ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hmap :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i φ =
        nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ)
    (hbase :
      ∀ base : ChildExternalBaseCoordinate n a cs i,
        ∀ Rcyc :
            ZMod n → RawNormal.RootFieldAssignment n (childAt cs i),
          fixedRootCyclicNodeFieldSum (n := n) (a := a) (cs := cs) i
              (Rcyc +
                nodeChildRootFieldShiftAtExternalBase
                  (n := n) (a := a) (cs := cs) i (φ + ψ) base) =
            fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i Rcyc) :
    childOpenRootInternalKernelAt (n := n) (a := a) cs i φ =
      childOpenRootInternalKernelAt (n := n) (a := a) cs i ψ := by
  let δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2 := φ + ψ
  have hδ :
      nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i δ = 0 := by
    rw [show δ = φ + ψ by rfl]
    rw [
      (nodeChildRootBoundaryBranchConstraintMap
        (n := n) (a := a) cs i).map_add,
      hmap]
    ext t c
    exact
      add_self_eq_zero_of_module_F2
        ((nodeChildRootBoundaryBranchConstraintMap
          (n := n) (a := a) cs i ψ) t c)
  have hbaseδ :
      ∀ base : ChildExternalBaseCoordinate n a cs i,
        ∀ Rcyc :
            ZMod n → RawNormal.RootFieldAssignment n (childAt cs i),
          fixedRootCyclicNodeFieldSum (n := n) (a := a) (cs := cs) i
              (Rcyc +
                nodeChildRootFieldShiftAtExternalBase
                  (n := n) (a := a) (cs := cs) i δ base) =
            fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i Rcyc := by
    simpa [δ] using hbase
  have hshift :=
    childOpenRootInternalKernelAt_shiftInvariant_of_baseFixedRootShiftInvariant
      (n := n) (a := a) (cs := cs) i hchildRoot δ hbaseδ ψ
  have hsum :
      ψ + δ = φ := by
    funext d
    calc
      ψ d + δ d = ψ d + (φ d + ψ d) := rfl
      _ = φ d + (ψ d + ψ d) := by ac_rfl
      _ = φ d + 0 := by
        rw [add_self_eq_zero_of_module_F2 (ψ d)]
      _ = φ d := by simp
  simpa [hsum] using hshift

theorem childOpenRootInternalKernelAt_shiftInvariant_of_baseBoundaryShift_zero
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (hbaseZero :
      ∀ base : ChildExternalBaseCoordinate n a cs i,
        ∀ {b : Nat} {ds : List RTree}
          (hchild : childAt cs i = RTree.node b ds),
          ∀ N : ZMod n →
              RawNormal.NodeNonRootFieldAssignment n b ds,
            cyclicNodeRootBoundaryLinearForm
                (n := n) (b := b) ds N
                (fun d =>
                  castRootFieldAssignment hchild
                    (nodeChildRootFieldShiftAtExternalBase
                      (n := n) (a := a) (cs := cs) i δ base d)) =
              0) :
    ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
      childOpenRootInternalKernelAt (n := n) (a := a) cs i (φ + δ) =
        childOpenRootInternalKernelAt (n := n) (a := a) cs i φ :=
  childOpenRootInternalKernelAt_shiftInvariant_of_baseFixedRootShiftInvariant
    (n := n) (a := a) (cs := cs) i hchildRoot δ
    (by
      intro base Rcyc
      let b := (childAt cs i).rootWeight
      let ds := (childAt cs i).children
      have hchild : childAt cs i = RTree.node b ds := by
        cases hT : childAt cs i with
        | node b' ds' =>
            simp [b, ds, hT, RTree.rootWeight, RTree.children]
      exact
        fixedRootCyclicNodeFieldSum_shiftInvariant_of_boundaryShift_zero
          (n := n) (a := a) (b := b) (cs := cs) i hchild Rcyc
            (nodeChildRootFieldShiftAtExternalBase
              (n := n) (a := a) (cs := cs) i δ base)
            (hbaseZero base hchild))

theorem branchConstraintBaseBoundaryShiftZero_at_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (base : ChildExternalBaseCoordinate n a cs i)
    (hchild : childAt cs i = RTree.node b [])
    (N : ZMod n → RawNormal.NodeNonRootFieldAssignment n b []) :
    cyclicNodeRootBoundaryLinearForm
        (n := n) (b := b) [] N
        (fun d =>
          castRootFieldAssignment hchild
            (nodeChildRootFieldShiftAtExternalBase
              (n := n) (a := a) (cs := cs) i δ base d)) = 0 :=
  cyclicNodeRootBoundaryLinearForm_nil
    (n := n) (b := b) N
    (fun d =>
      castRootFieldAssignment hchild
        (nodeChildRootFieldShiftAtExternalBase
          (n := n) (a := a) (cs := cs) i δ base d))

abbrev BranchConstraintBaseFixedRootShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          ∀ base : ChildExternalBaseCoordinate n a cs i,
            ∀ Rcyc :
                ZMod n → RawNormal.RootFieldAssignment n (childAt cs i),
              fixedRootCyclicNodeFieldSum (n := n) (a := a) (cs := cs) i
                  (Rcyc +
                    nodeChildRootFieldShiftAtExternalBase
                      (n := n) (a := a) (cs := cs) i δ base) =
                fixedRootCyclicNodeFieldSum
                  (n := n) (a := a) (cs := cs) i Rcyc

theorem branchConstraintBaseFixedRootShiftInvariantAt_of_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (base : ChildExternalBaseCoordinate n a cs i)
    (Rcyc :
      ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) :
    fixedRootCyclicNodeFieldSum (n := n) (a := a) (cs := cs) i
        (Rcyc +
          nodeChildRootFieldShiftAtExternalBase
            (n := n) (a := a) (cs := cs) i δ base) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i Rcyc :=
  fixedRootCyclicNodeFieldSum_shiftInvariant_leaf_child
    (n := n) (a := a) (b := b) (cs := cs) i hchild Rcyc
    (nodeChildRootFieldShiftAtExternalBase
      (n := n) (a := a) (cs := cs) i δ base)

theorem branchConstraintKernelShiftInvariantCoreRule_of_baseFixedRootShiftInvariantCore
    (hbase : BranchConstraintBaseFixedRootShiftInvariantCoreRule) :
    BranchConstraintKernelShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ φ
  exact
    childOpenRootInternalKernelAt_shiftInvariant_of_baseFixedRootShiftInvariant
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      δ
      (hbase ha hchildren n hn i δ hδ)
      φ

theorem branchConstraintImageKernelDependsCoreRule_of_baseFixedRootShiftInvariantCore
    (hbase : BranchConstraintBaseFixedRootShiftInvariantCoreRule) :
    BranchConstraintImageKernelDependsCoreRule :=
  branchConstraintImageKernelDependsCoreRule_of_kernelShiftInvariantCore
    (branchConstraintKernelShiftInvariantCoreRule_of_baseFixedRootShiftInvariantCore
      hbase)

abbrev BranchConstraintBaseBoundaryShiftZeroCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          ∀ base : ChildExternalBaseCoordinate n a cs i,
            ∀ {b : Nat} {ds : List RTree}
              (hchild : childAt cs i = RTree.node b ds),
              ∀ N : ZMod n →
                  RawNormal.NodeNonRootFieldAssignment n b ds,
                cyclicNodeRootBoundaryLinearForm
                    (n := n) (b := b) ds N
                    (fun d =>
                      castRootFieldAssignment hchild
                        (nodeChildRootFieldShiftAtExternalBase
                          (n := n) (a := a) (cs := cs) i δ base d)) =
                  0

abbrev BranchConstraintBaseBoundaryShiftZeroChildDataCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          ∀ base : ChildExternalBaseCoordinate n a cs i,
            ∀ {b : Nat} {ds : List RTree}
              (hchild : childAt cs i = RTree.node b ds),
              ∀ H : ZMod n →
                  RawNormal.NodeChildDataFamily n b ds,
                cyclicNodeRootBoundaryLinearForm
                    (n := n) (b := b) ds
                    (fun d =>
                      RawNormal.nodeFieldFromChildDataFamily
                        (n := n) (a := b) (cs := ds) (H d))
                    (fun d =>
                      castRootFieldAssignment hchild
                        (nodeChildRootFieldShiftAtExternalBase
                          (n := n) (a := a) (cs := cs) i δ base d)) =
                  0

theorem branchConstraintBaseBoundaryShiftZeroCoreRule_of_childData
    (hchildData : BranchConstraintBaseBoundaryShiftZeroChildDataCoreRule) :
    BranchConstraintBaseBoundaryShiftZeroCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ base b ds hchild N
  rw [cyclicNodeRootBoundaryLinearForm_eq_childDataFamily]
  exact
    hchildData ha hchildren n hn i δ hδ base hchild
      (cyclicNodeFieldFamilyEquivChildDataFamily n b ds N)

theorem branchConstraintKernelShiftInvariantCoreRule_of_baseBoundaryShiftZeroCore
    (hbaseZero : BranchConstraintBaseBoundaryShiftZeroCoreRule) :
    BranchConstraintKernelShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ φ
  exact
    childOpenRootInternalKernelAt_shiftInvariant_of_baseBoundaryShift_zero
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      δ
      (by
        intro base b ds hchild N
        exact hbaseZero ha hchildren n hn i δ hδ base hchild N)
      φ

theorem internalKernelConstantCore_of_fixedRootCyclicNodeFieldSumConstantCore
    (hfixed : FixedRootCyclicNodeFieldSumConstantCoreRule) :
    InternalKernelConstantCoreRule := by
  intro a cs ha hchildren n _ hn i
  rcases hfixed ha hchildren n hn i with ⟨Kcyc, hKcyc⟩
  refine
    ⟨Kcyc ^ Fintype.card (ChildExternalBaseCoordinate n a cs i), ?_⟩
  intro φ
  rw [
    childOpenRootInternalKernelAt_eq_prod_fixedRootCyclicNodeFieldSum
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      φ]
  calc
    (∏ base : ChildExternalBaseCoordinate n a cs i,
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d =>
          (nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, d)))) =
        ∏ _base : ChildExternalBaseCoordinate n a cs i, Kcyc := by
          refine Finset.prod_congr rfl ?_
          intro base _
          exact hKcyc
            (fun d =>
              (nodeChildRootFieldFamilyAtExternalEquiv
                (n := n) (a := a) (cs := cs) i φ)
                ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, d)))
    _ = Kcyc ^ Fintype.card (ChildExternalBaseCoordinate n a cs i) := by
          simp

theorem fixedRootCyclicNodeFieldSumConstantCore_of_rootSingletonShiftInvariantCore
    (hshift :
      FixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCoreRule) :
    FixedRootCyclicNodeFieldSumConstantCoreRule := by
  classical
  intro a cs ha hchildren n _ hn i
  let D := ZMod n × RawNormal.RootFieldDomain n (childAt cs i)
  let F : (D → F2) → ℤ :=
    fun α =>
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd => α (d, rd))
  refine ⟨F 0, ?_⟩
  intro Rcyc
  let α : D → F2 := fun q => Rcyc q.1 q.2
  have hsum :
      α =
        ∑ q : D, α q •
          Pi.single (M := fun _ : D => F2) q (1 : F2) :=
    function_eq_sum_single D α
  have hfinset :
      ∀ s : Finset D,
        F (s.sum (fun q => α q •
          Pi.single (M := fun _ : D => F2) q (1 : F2))) =
        F 0 := by
    intro s
    refine Finset.induction_on s ?hbase ?hstep
    · simp [F]
    · intro q s hnot ih
      rw [Finset.sum_insert hnot]
      by_cases hq : α q = 0
      · rw [hq, zero_smul, zero_add]
        exact ih
      · have hq_one : α q = 1 := by
          generalize hx : α q = x
          fin_cases x
          · exact False.elim (hq hx)
          · rfl
        rw [hq_one, one_smul]
        calc
          F (Pi.single (M := fun _ : D => F2) q (1 : F2) +
              s.sum (fun x => α x •
                Pi.single (M := fun _ : D => F2) x (1 : F2))) =
              F (s.sum (fun x => α x •
                  Pi.single (M := fun _ : D => F2) x (1 : F2)) +
                Pi.single (M := fun _ : D => F2) q (1 : F2)) := by
                congr 1
                ac_rfl
          _ =
              F (s.sum (fun x => α x •
                Pi.single (M := fun _ : D => F2) x (1 : F2))) := by
                simpa [F, D, Pi.add_apply] using
                  hshift ha hchildren n hn i q
                    (fun d rd =>
                      s.sum (fun x => α x •
                        Pi.single (M := fun _ : D => F2) x (1 : F2))
                        (d, rd))
          _ = F 0 := ih
  change F α = F 0
  rw [hsum]
  exact hfinset Finset.univ

theorem fixedRootCyclicNodeFieldSumConstantCore_of_oneFiber
    (hcancel : CyclicNodeFixedRootOneFiberCancellationCoreRule) :
    FixedRootCyclicNodeFieldSumConstantCoreRule :=
  fixedRootCyclicNodeFieldSumConstantCore_of_rootSingletonShiftInvariantCore
    (fixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCore_of_oneFiber
      hcancel)

abbrev InternalKernelSingletonReindexAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i) : Prop :=
  ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
    ∃ e :
      ChildInternalNonRootFieldFamily n a cs i ≃
        ChildInternalNonRootFieldFamily n a cs i,
      ∀ ψ : ChildInternalNonRootFieldFamily n a cs i,
        childInternalPhaseGivenRootFieldsAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            (φ +
              Pi.single
                (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2)) (e ψ) =
          childInternalPhaseGivenRootFieldsAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i φ ψ

abbrev InternalKernelSingletonExternalReindexAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i) : Prop :=
  ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
    ∃ e :
      ChildExternalNodeFieldFamily n a cs i ≃
        ChildExternalNodeFieldFamily n a cs i,
      ∀ Ψ : ChildExternalNodeFieldFamily n a cs i,
        childInternalPhaseGivenRootDataAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            ((nodeChildDataAtStructuredEquivExternalNormalAssignments
              (n := n) (a := a) (cs := cs) i hchildRoot).symm
              (childExternalNormalAssignmentOfRootNodeField
                (n := n) (a := a) (cs := cs) i
                (φ +
                  Pi.single
                    (M := fun _ :
                      RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                    d (1 : F2)) (e Ψ))) =
          childInternalPhaseGivenRootDataAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            ((nodeChildDataAtStructuredEquivExternalNormalAssignments
              (n := n) (a := a) (cs := cs) i hchildRoot).symm
              (childExternalNormalAssignmentOfRootNodeField
                (n := n) (a := a) (cs := cs) i φ Ψ))

abbrev InternalKernelDiagonalExternalReindexAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight) : Prop :=
  ∀ (shift : ZMod n)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
    ∃ e :
      ChildExternalNodeFieldFamily n a cs i ≃
        ChildExternalNodeFieldFamily n a cs i,
      ∀ Ψ : ChildExternalNodeFieldFamily n a cs i,
        childInternalPhaseGivenRootDataAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            ((nodeChildDataAtStructuredEquivExternalNormalAssignments
              (n := n) (a := a) (cs := cs) i hchildRoot).symm
              (childExternalNormalAssignmentOfRootNodeField
                (n := n) (a := a) (cs := cs) i
                (nodeChildRootFieldFunctionDiagonalShiftLinearEquiv
                  (n := n) (b := a) cs i shift φ)
                (e Ψ))) =
          childInternalPhaseGivenRootDataAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            ((nodeChildDataAtStructuredEquivExternalNormalAssignments
              (n := n) (a := a) (cs := cs) i hchildRoot).symm
              (childExternalNormalAssignmentOfRootNodeField
                (n := n) (a := a) (cs := cs) i φ Ψ))

noncomputable abbrev childExternalRootNodeFieldPhaseAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (Ψ : ChildExternalNodeFieldFamily n a cs i) : F2 :=
  childInternalPhaseGivenRootDataAt
    (n := n) (a := a) cs
    (0 : RawNormal.NodeRootFieldAssignment n a cs) i
    ((nodeChildDataAtStructuredEquivExternalNormalAssignments
      (n := n) (a := a) (cs := cs) i hchildRoot).symm
      (childExternalNormalAssignmentOfRootNodeField
        (n := n) (a := a) (cs := cs) i φ Ψ))

abbrev InternalKernelExternalReindexAt
    {n a : Nat} [NeZero n] (cs : List RTree)
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2) : Prop :=
  ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
    ∃ e :
      ChildExternalNodeFieldFamily n a cs i ≃
        ChildExternalNodeFieldFamily n a cs i,
      ∀ Ψ : ChildExternalNodeFieldFamily n a cs i,
        childExternalRootNodeFieldPhaseAt
            (n := n) (a := a) (cs := cs) i hchildRoot
            (φ + δ) (e Ψ) =
          childExternalRootNodeFieldPhaseAt
            (n := n) (a := a) (cs := cs) i hchildRoot φ Ψ

theorem childExternalRootNodeFieldPhaseAt_eq_rootFields
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
    (Ψ : ChildExternalNodeFieldFamily n a cs i) :
    childExternalRootNodeFieldPhaseAt
        (n := n) (a := a) (cs := cs) i hchildRoot φ Ψ =
      childInternalPhaseGivenRootFieldsAt
        (n := n) (a := a) cs
        (0 : RawNormal.NodeRootFieldAssignment n a cs) i φ
        ((nodeChildNonRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i hchildRoot).symm Ψ) := by
  unfold childExternalRootNodeFieldPhaseAt
  rw [
    nodeChildDataAtStructuredEquiv_symm_childExternalNormalAssignmentOfRootNodeField
      (n := n) (a := a) (cs := cs) i hchildRoot φ Ψ]
  rfl

theorem childOpenRootInternalKernelAt_shiftInvariant_of_externalReindex
    {n a : Nat} [NeZero n] {cs : List RTree}
    {i : ChildIdx cs}
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    {δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2}
    (hreindex :
      InternalKernelExternalReindexAt
        (n := n) (a := a) cs i hchildRoot δ) :
    ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
      childOpenRootInternalKernelAt
          (n := n) (a := a) cs i (φ + δ) =
        childOpenRootInternalKernelAt
          (n := n) (a := a) cs i φ := by
  classical
  intro φ
  rw [
    childOpenRootInternalKernelAt_eq_externalNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot (φ + δ),
    childOpenRootInternalKernelAt_eq_externalNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot φ]
  rcases hreindex φ with ⟨e, hphase⟩
  unfold childOpenRootInternalExternalNodeFieldSum
  refine
    Fintype.sum_equiv e.symm
      (fun Ψ : ChildExternalNodeFieldFamily n a cs i =>
        bitSign
          (childExternalRootNodeFieldPhaseAt
            (n := n) (a := a) (cs := cs) i hchildRoot
            (φ + δ) Ψ))
      (fun Ψ : ChildExternalNodeFieldFamily n a cs i =>
        bitSign
          (childExternalRootNodeFieldPhaseAt
            (n := n) (a := a) (cs := cs) i hchildRoot φ Ψ))
      ?_
  intro Ψ
  have h :
      childExternalRootNodeFieldPhaseAt
          (n := n) (a := a) (cs := cs) i hchildRoot
          (φ + δ) Ψ =
        childExternalRootNodeFieldPhaseAt
          (n := n) (a := a) (cs := cs) i hchildRoot
          φ (e.symm Ψ) := by
    simpa using hphase (e.symm Ψ)
  exact congrArg bitSign h

theorem internalKernelSingletonExternalReindexAt_of_phase_reindex
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (e :
      (RawNormal.NodeChildRootFieldDomain n a cs i → F2) →
        ChildExternalNodeFieldFamily n a cs i ≃
          ChildExternalNodeFieldFamily n a cs i)
    (hphase :
      ∀ (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
        (Ψ : ChildExternalNodeFieldFamily n a cs i),
        childExternalRootNodeFieldPhaseAt (n := n) (a := a) (cs := cs)
            i hchildRoot
            (φ +
              Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2)) ((e φ) Ψ) =
          childExternalRootNodeFieldPhaseAt (n := n) (a := a) (cs := cs)
            i hchildRoot φ Ψ) :
    InternalKernelSingletonExternalReindexAt
      (n := n) (a := a) cs i hchildRoot d := by
  intro φ
  exact ⟨e φ, hphase φ⟩

theorem internalKernelSingletonExternalReindexAt_of_single_toggle_phase
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i)
    (ext0 : ChildExternalCoordinate n a cs i)
    (v0 : NonRootVertex (childAt cs i))
    (nd0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0)
    (hphase :
      ∀ (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
        (Ψ : ChildExternalNodeFieldFamily n a cs i),
        childExternalRootNodeFieldPhaseAt (n := n) (a := a) (cs := cs)
            i hchildRoot
            (φ +
              Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2))
            (childExternalNodeFieldSingleToggleEquiv
              (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ) =
          childExternalRootNodeFieldPhaseAt (n := n) (a := a) (cs := cs)
            i hchildRoot φ Ψ) :
    InternalKernelSingletonExternalReindexAt
      (n := n) (a := a) cs i hchildRoot d :=
  internalKernelSingletonExternalReindexAt_of_phase_reindex
    (n := n) (a := a) (cs := cs) i hchildRoot d
    (fun _ =>
      childExternalNodeFieldSingleToggleEquiv
        (n := n) (a := a) (cs := cs) i ext0 v0 nd0)
    hphase

abbrev BranchVisibleSingletonExternalReindexLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i),
      BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
        InternalKernelSingletonExternalReindexAt
          (n := n) (a := a) cs i hchildRoot d

abbrev BranchVisibleSingleTogglePhaseLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i),
      BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
        ∃ ext0 : ChildExternalCoordinate n a cs i,
          ∃ v0 : NonRootVertex (childAt cs i),
            ∃ nd0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0,
              ∀ (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
                (Ψ : ChildExternalNodeFieldFamily n a cs i),
                childExternalRootNodeFieldPhaseAt
                    (n := n) (a := a) (cs := cs) i hchildRoot
                    (φ +
                      Pi.single
                        (M := fun _ :
                          RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                        d (1 : F2))
                    (childExternalNodeFieldSingleToggleEquiv
                      (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ) =
                  childExternalRootNodeFieldPhaseAt
                    (n := n) (a := a) (cs := cs) i hchildRoot φ Ψ

theorem branchVisibleSingletonExternalReindexLocalRule_of_singleTogglePhase
    (hphaseRule : BranchVisibleSingleTogglePhaseLocalRule) :
    BranchVisibleSingletonExternalReindexLocalRule := by
  intro n a _ cs i hchildRoot d hvisible
  rcases hphaseRule
      (n := n) (a := a) (cs := cs) i hchildRoot d hvisible with
    ⟨ext0, v0, nd0, hphase⟩
  exact
    internalKernelSingletonExternalReindexAt_of_single_toggle_phase
      (n := n) (a := a) (cs := cs) i hchildRoot d ext0 v0 nd0 hphase

abbrev AllSingletonShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ i : ChildIdx cs,
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          InternalKernelSingletonShiftInvariantAt
            (n := n) (a := a) cs i d

abbrev OddFiberBranchSingleShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (_R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d

abbrev OddFiberBoundaryBranchSingleShiftInvariantCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          BoundarySingletonVisibleAt (n := n) (a := a) cs R i d →
            BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
              InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d

abbrev OddFiberBranchSingleReindexCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (_R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            InternalKernelSingletonReindexAt (n := n) (a := a) cs i d

abbrev OddFiberBoundaryBranchSingleReindexCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          BoundarySingletonVisibleAt (n := n) (a := a) cs R i d →
            BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
              InternalKernelSingletonReindexAt (n := n) (a := a) cs i d

abbrev OddFiberBranchSingleExternalReindexCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (_R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            InternalKernelSingletonExternalReindexAt
              (n := n) (a := a) cs i
              (childAt_rootWeight_pos_of_openRootCert i
                (RawExpandedOpenRootSubtreeCert.childAt_of_children
                  (cs := cs) hchildren i))
              d

abbrev OddFiberBoundaryBranchSingleExternalReindexCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (R : RawNormal.NodeRootFieldAssignment n a cs)
        (i : ChildIdx cs),
        Odd
          (n ^
            (NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) →
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          BoundarySingletonVisibleAt (n := n) (a := a) cs R i d →
            BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
              InternalKernelSingletonExternalReindexAt
                (n := n) (a := a) cs i
                (childAt_rootWeight_pos_of_openRootCert i
                  (RawExpandedOpenRootSubtreeCert.childAt_of_children
                    (cs := cs) hchildren i))
                d

abbrev AllSingletonExternalReindexCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ i : ChildIdx cs,
        ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
          InternalKernelSingletonExternalReindexAt
            (n := n) (a := a) cs i
            (childAt_rootWeight_pos_of_openRootCert i
              (RawExpandedOpenRootSubtreeCert.childAt_of_children
                (cs := cs) hchildren i))
            d

theorem oddFiberBranchSingleExternalReindexCore_of_local
    (hlocal : BranchVisibleSingletonExternalReindexLocalRule) :
    OddFiberBranchSingleExternalReindexCoreRule := by
  intro a cs _ha hchildren n _ _hn _R i _hodd d hvisible
  exact
    hlocal (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      d hvisible

theorem oddFiberBranchSingleExternalReindexCore_of_singleTogglePhase
    (hphaseRule : BranchVisibleSingleTogglePhaseLocalRule) :
    OddFiberBranchSingleExternalReindexCoreRule :=
  oddFiberBranchSingleExternalReindexCore_of_local
    (branchVisibleSingletonExternalReindexLocalRule_of_singleTogglePhase
      hphaseRule)

abbrev BranchVisibleSingletonExternalReindexNonLeafLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i),
      (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
          InternalKernelSingletonExternalReindexAt
            (n := n) (a := a) cs i hchildRoot d

abbrev BranchVisibleSingletonExternalReindexNonLeafCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (d : RawNormal.NodeChildRootFieldDomain n a cs i),
        (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            InternalKernelSingletonExternalReindexAt
              (n := n) (a := a) cs i
              (childAt_rootWeight_pos_of_openRootCert i
                  (RawExpandedOpenRootSubtreeCert.childAt_of_children
                    (cs := cs) hchildren i))
              d

abbrev BranchVisibleSingletonShiftInvariantNonLeafLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i),
      (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
          InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d

abbrev BranchVisibleSingletonShiftInvariantNonLeafCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (d : RawNormal.NodeChildRootFieldDomain n a cs i),
        (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d

abbrev BranchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (d : RawNormal.NodeChildRootFieldDomain n a cs i),
        (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            ∀ base : ChildExternalBaseCoordinate n a cs i,
              ∀ Rcyc :
                  ZMod n → RawNormal.RootFieldAssignment n (childAt cs i),
                fixedRootCyclicNodeFieldSum
                    (n := n) (a := a) (cs := cs) i
                    (Rcyc +
                      nodeChildRootFieldShiftAtExternalBase
                        (n := n) (a := a) (cs := cs) i
                        (Pi.single
                          (M := fun _ :
                            RawNormal.NodeChildRootFieldDomain n a cs i =>
                              F2)
                          d (1 : F2))
                        base) =
                  fixedRootCyclicNodeFieldSum
                    (n := n) (a := a) (cs := cs) i Rcyc

abbrev BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (d : RawNormal.NodeChildRootFieldDomain n a cs i),
        (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            ∀ (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
              (base : ChildExternalBaseCoordinate n a cs i),
              fixedRootCyclicNodeFieldSum
                  (n := n) (a := a) (cs := cs) i
                  (fun t =>
                    (nodeChildRootFieldFamilyAtExternalEquiv
                      (n := n) (a := a) (cs := cs) i
                      (φ +
                        Pi.single
                          (M := fun _ :
                            RawNormal.NodeChildRootFieldDomain n a cs i =>
                              F2)
                          d (1 : F2)))
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i).symm
                        (base, t))) =
                fixedRootCyclicNodeFieldSum
                  (n := n) (a := a) (cs := cs) i
                  (fun t =>
                    (nodeChildRootFieldFamilyAtExternalEquiv
                      (n := n) (a := a) (cs := cs) i φ)
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i).symm
                        (base, t)))

theorem branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_fixedRootFactor
    (hfactor :
      BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule) :
    BranchVisibleSingletonShiftInvariantNonLeafCoreRule := by
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible
  exact
    internalKernelSingletonShiftInvariantAt_of_fixedRootFactorSingletonShift
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      d
      (hfactor ha hchildren n hn i d hnonleaf hvisible)

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedRootSingleton
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  let selectedBase :
                    ChildExternalBaseCoordinate n a cs i :=
                    (childExternalCoordinateEquivBaseDiag
                      (n := n) (a := a) (cs := cs) i
                      ((nodeChildRootFieldDomainStructuredEquiv
                        (n := n) (a := a) (cs := cs) i d).1)).1
                  let q :
                    ZMod n ×
                      RawNormal.RootFieldDomain n (childAt cs i) :=
                    ((childExternalCoordinateEquivBaseDiag
                      (n := n) (a := a) (cs := cs) i
                      ((nodeChildRootFieldDomainStructuredEquiv
                        (n := n) (a := a) (cs := cs) i d).1)).2,
                      (nodeChildRootFieldDomainStructuredEquiv
                        (n := n) (a := a) (cs := cs) i d).2)
                  fixedRootCyclicNodeFieldSum
                      (n := n) (a := a) (cs := cs) i
                      (fun t rd =>
                        (nodeChildRootFieldFamilyAtExternalEquiv
                          (n := n) (a := a) (cs := cs) i φ)
                          ((childExternalCoordinateEquivBaseDiag
                            (n := n) (a := a) (cs := cs) i).symm
                            (selectedBase, t)) rd +
                          Pi.single
                            (M := fun _ :
                              ZMod n ×
                                RawNormal.RootFieldDomain n
                                  (childAt cs i) => F2)
                            q (1 : F2) (t, rd)) =
                    fixedRootCyclicNodeFieldSum
                      (n := n) (a := a) (cs := cs) i
                      (fun t =>
                        (nodeChildRootFieldFamilyAtExternalEquiv
                          (n := n) (a := a) (cs := cs) i φ)
                          ((childExternalCoordinateEquivBaseDiag
                            (n := n) (a := a) (cs := cs) i).symm
                            (selectedBase, t)))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ base
  exact
    fixedRootCyclicNodeFieldSum_nodeChildRootFieldFamily_singletonShift_of_selectedRootSingleton
      (n := n) (a := a) (cs := cs) i φ d base
      (hselected ha hchildren n hn i d hnonleaf hvisible φ)

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingleton
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
                        (fun t rd =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, t))) rd +
                            Pi.single
                              (M := fun _ :
                                CyclicNodeRootBoundaryDomain n b ds => F2)
                              (q.1, castRootFieldDomain hchild q.2)
                              (1 : F2) (t, rd)) =
                      cyclicNodeFixedRootFieldSum (n := n) (b := b) ds
                        (fun t =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, t))))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedRootSingleton
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ
  obtain ⟨b, ds, hchild⟩ :
      ∃ b ds, childAt cs i = RTree.node b ds := by
    cases h : childAt cs i with
    | node b ds => exact ⟨b, ds, rfl⟩
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  exact
    fixedRootCyclicNodeFieldSum_rootSingletonShiftInvariant_of_cyclicNode
      (n := n) (a := a) (b := b) (cs := cs) i hchild q
      (fun t =>
        (nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (selectedBase, t)))
      (by
        simpa [selectedBase, q] using
          hselected ha hchildren n hn i d hnonleaf hvisible φ hchild)

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonSummandReindex
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ e :
                        CyclicNodeChildRootFamily n b ds ≃
                          CyclicNodeChildRootFamily n b ds,
                      ∀ Φ : CyclicNodeChildRootFamily n b ds,
                        (∏ j : ChildIdx ds,
                          cyclicNodeChildNonRootSumAtRootFamily
                            (n := n) (b := b) ds j ((e Φ) j)) *
                            bitSign
                              (dotLinear
                                (CyclicNodeRootBoundaryDomain n b ds)
                                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                                  cyclicChildRootBoundaryMap
                                    (n := n) (b := b) ds
                                    (e Φ) p.1 p.2)
                                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                                  castRootFieldAssignment hchild
                                    ((nodeChildRootFieldFamilyAtExternalEquiv
                                      (n := n) (a := a) (cs := cs) i φ)
                                      ((childExternalCoordinateEquivBaseDiag
                                        (n := n) (a := a) (cs := cs) i).symm
                                        (selectedBase, p.1))) p.2 +
                                    Pi.single
                                      (M := fun _ :
                                        CyclicNodeRootBoundaryDomain n b ds =>
                                          F2)
                                      (q.1, castRootFieldDomain hchild q.2)
                                      (1 : F2) p)) =
                          (∏ j : ChildIdx ds,
                            cyclicNodeChildNonRootSumAtRootFamily
                              (n := n) (b := b) ds j (Φ j)) *
                            bitSign
                              (dotLinear
                                (CyclicNodeRootBoundaryDomain n b ds)
                                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                                  cyclicChildRootBoundaryMap
                                    (n := n) (b := b) ds
                                    Φ p.1 p.2)
                                (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                                  castRootFieldAssignment hchild
                                    ((nodeChildRootFieldFamilyAtExternalEquiv
                                      (n := n) (a := a) (cs := cs) i φ)
                                      ((childExternalCoordinateEquivBaseDiag
                                        (n := n) (a := a) (cs := cs) i).symm
                                        (selectedBase, p.1))) p.2))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingleton
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨e, hsummand⟩
  exact
    cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_summand_reindex
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun t =>
        castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (selectedBase, t))))
      e
      (by
        simpa [selectedBase, q] using hsummand)

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonShear
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ ℓ : CyclicNodeChildRootFamily n b ds →ₗ[F2] F2,
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ : ℓ τ = 0,
                      (∀ Φ : CyclicNodeChildRootFamily n b ds,
                        ℓ Φ =
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            Φ q.1 (castRootFieldDomain hchild q.2)) ∧
                      cyclicChildRootBoundaryMap (n := n) (b := b) ds τ
                        q.1 (castRootFieldDomain hchild q.2) = 0 ∧
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = 1 ∧
                      ∀ Φ : CyclicNodeChildRootFamily n b ds,
                        (∏ j : ChildIdx ds,
                          cyclicNodeChildNonRootSumAtRootFamily
                            (n := n) (b := b) ds j
                            ((f2ShearEquiv
                              (CyclicNodeChildRootFamily n b ds) ℓ τ hτ Φ) j)) =
                          ∏ j : ChildIdx ds,
                            cyclicNodeChildNonRootSumAtRootFamily
                              (n := n) (b := b) ds j (Φ j)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingleton
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨ℓ, τ, hτ, hℓ, heval, hdot, hprod⟩
  exact
    cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_shear
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun t =>
        castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (selectedBase, t))))
      ℓ τ hτ hℓ heval hdot hprod

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShear
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = 1 ∧
                      ∀ Φ : CyclicNodeChildRootFamily n b ds,
                        (∏ j : ChildIdx ds,
                          cyclicNodeChildNonRootSumAtRootFamily
                            (n := n) (b := b) ds j
                            ((f2ShearEquiv
                              (CyclicNodeChildRootFamily n b ds)
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2))
                              τ hτ Φ) j)) =
                          ∏ j : ChildIdx ds,
                            cyclicNodeChildNonRootSumAtRootFamily
                              (n := n) (b := b) ds j (Φ j)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingleton
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨τ, hτ, hdot, hprod⟩
  exact
    cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShear
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun t =>
        castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (selectedBase, t))))
      τ hτ hdot hprod

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSign
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                    ∃ σ : F2,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = σ ∧
                      ∀ Φ : CyclicNodeChildRootFamily n b ds,
                        (∏ j : ChildIdx ds,
                          cyclicNodeChildNonRootSumAtRootFamily
                            (n := n) (b := b) ds j
                            ((f2ShearEquiv
                              (CyclicNodeChildRootFamily n b ds)
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2))
                              τ hτ Φ) j)) =
                          (∏ j : ChildIdx ds,
                            cyclicNodeChildNonRootSumAtRootFamily
                              (n := n) (b := b) ds j (Φ j)) *
                            bitSign
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2) Φ *
                                  (σ + 1))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingleton
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨τ, hτ, σ, hdot, hprod⟩
  exact
    cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSign
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun t =>
        castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (selectedBase, t))))
      τ hτ σ hdot hprod

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSingleFactor
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                    ∃ σ : F2,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = σ ∧
                    ∃ j0 : ChildIdx ds,
                      (∀ Φ : CyclicNodeChildRootFamily n b ds,
                        ∀ j : ChildIdx ds,
                          j ≠ j0 →
                            cyclicNodeChildNonRootSumAtRootFamily
                                (n := n) (b := b) ds j
                                ((f2ShearEquiv
                                  (CyclicNodeChildRootFamily n b ds)
                                  (cyclicChildRootBoundaryEvalLinearMap
                                    (n := n) (b := b) ds
                                    (q.1, castRootFieldDomain hchild q.2))
                                  τ hτ Φ) j) =
                              cyclicNodeChildNonRootSumAtRootFamily
                                (n := n) (b := b) ds j (Φ j)) ∧
                      (∀ Φ : CyclicNodeChildRootFamily n b ds,
                        cyclicNodeChildNonRootSumAtRootFamily
                            (n := n) (b := b) ds j0
                            ((f2ShearEquiv
                              (CyclicNodeChildRootFamily n b ds)
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2))
                              τ hτ Φ) j0) =
                          cyclicNodeChildNonRootSumAtRootFamily
                              (n := n) (b := b) ds j0 (Φ j0) *
                            bitSign
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2) Φ *
                                  (σ + 1)))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingleton
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨τ, hτ, σ, hdot, j0, hother, hselectedFactor⟩
  exact
    cyclicNodeFixedRootFieldSum_rootSingletonShiftInvariant_of_childRootFamily_evalShearSignSingleFactor
      (n := n) (b := b) ds
      (q.1, castRootFieldDomain hchild q.2)
      (fun t =>
        castRootFieldAssignment hchild
          ((nodeChildRootFieldFamilyAtExternalEquiv
            (n := n) (a := a) (cs := cs) i φ)
            ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm
              (selectedBase, t))))
      τ hτ σ hdot j0 hother hselectedFactor

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSingleFactorReindexPhase
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                    ∃ σ : F2,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = σ ∧
                    ∃ j0 : ChildIdx ds,
                      (∀ Φ : CyclicNodeChildRootFamily n b ds,
                        ∀ j : ChildIdx ds,
                          j ≠ j0 →
                            cyclicNodeChildNonRootSumAtRootFamily
                                (n := n) (b := b) ds j
                                ((f2ShearEquiv
                                  (CyclicNodeChildRootFamily n b ds)
                                  (cyclicChildRootBoundaryEvalLinearMap
                                    (n := n) (b := b) ds
                                    (q.1, castRootFieldDomain hchild q.2))
                                  τ hτ Φ) j) =
                              cyclicNodeChildNonRootSumAtRootFamily
                                (n := n) (b := b) ds j (Φ j)) ∧
                      (∀ Φ : CyclicNodeChildRootFamily n b ds,
                        ∃ e :
                          (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                            RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2) ≃
                          (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                            RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2),
                          ∀ Ψ :
                            ZMod n → (v : NonRootVertex (childAt ds j0)) →
                              RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2,
                            cyclicNodeChildInternalPhaseAtData
                                (n := n) (b := b) ds j0
                                ((f2ShearEquiv
                                  (CyclicNodeChildRootFamily n b ds)
                                  (cyclicChildRootBoundaryEvalLinearMap
                                    (n := n) (b := b) ds
                                    (q.1, castRootFieldDomain hchild q.2))
                                  τ hτ Φ) j0) (e Ψ) =
                              cyclicNodeChildInternalPhaseAtData
                                  (n := n) (b := b) ds j0 (Φ j0) Ψ +
                                (cyclicChildRootBoundaryEvalLinearMap
                                  (n := n) (b := b) ds
                                  (q.1, castRootFieldDomain hchild q.2) Φ *
                                  (σ + 1)))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSingleFactor
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨τ, hτ, σ, hdot, j0, hother, hphase⟩
  refine ⟨τ, hτ, σ, hdot, j0, hother, ?_⟩
  intro Φ
  rcases hphase Φ with ⟨e, he⟩
  exact
    cyclicNodeChildNonRootSumAtRootFamily_eq_mul_bitSign_of_reindex_phase
      (n := n) (b := b) ds j0 (Φ j0)
      ((f2ShearEquiv
        (CyclicNodeChildRootFamily n b ds)
        (cyclicChildRootBoundaryEvalLinearMap
          (n := n) (b := b) ds
          (q.1, castRootFieldDomain hchild q.2))
        τ hτ Φ) j0)
      (cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds
        (q.1, castRootFieldDomain hchild q.2) Φ *
        (σ + 1))
      e he

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSupportedReindexPhase
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                    ∃ σ : F2,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = σ ∧
                    ∃ j0 : ChildIdx ds,
                      (∀ j : ChildIdx ds, j ≠ j0 → τ j = 0) ∧
                      (∀ Φ : CyclicNodeChildRootFamily n b ds,
                        ∃ e :
                          (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                            RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2) ≃
                          (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                            RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2),
                          ∀ Ψ :
                            ZMod n → (v : NonRootVertex (childAt ds j0)) →
                              RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2,
                            cyclicNodeChildInternalPhaseAtData
                                (n := n) (b := b) ds j0
                                ((f2ShearEquiv
                                  (CyclicNodeChildRootFamily n b ds)
                                  (cyclicChildRootBoundaryEvalLinearMap
                                    (n := n) (b := b) ds
                                    (q.1, castRootFieldDomain hchild q.2))
                                  τ hτ Φ) j0) (e Ψ) =
                              cyclicNodeChildInternalPhaseAtData
                                  (n := n) (b := b) ds j0 (Φ j0) Ψ +
                                (cyclicChildRootBoundaryEvalLinearMap
                                  (n := n) (b := b) ds
                                  (q.1, castRootFieldDomain hchild q.2) Φ *
                                  (σ + 1)))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSingleFactorReindexPhase
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨τ, hτ, σ, hdot, j0, hτzero, hphase⟩
  refine ⟨τ, hτ, σ, hdot, j0, ?_, hphase⟩
  intro Φ j hj
  exact
    cyclicNodeChildNonRootSumAtRootFamily_f2Shear_eq_of_component_zero
      (n := n) (b := b) ds
      (cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds
        (q.1, castRootFieldDomain hchild q.2))
      τ hτ Φ j (hτzero j hj)

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSameChildPairReindexPhase
    (hselected :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ j0 : ChildIdx ds,
                    ∃ d0 : ZMod n,
                    ∃ rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0,
                    ∃ d1 : ZMod n,
                    ∃ rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0,
                    let τ : CyclicNodeChildRootFamily n b ds :=
                      cyclicNodeChildRootFamilyPair
                        (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                    ∃ σ : F2,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = σ ∧
                      (∀ Φ : CyclicNodeChildRootFamily n b ds,
                        ∃ e :
                          (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                            RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2) ≃
                          (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                            RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2),
                          ∀ Ψ :
                            ZMod n → (v : NonRootVertex (childAt ds j0)) →
                              RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2,
                            cyclicNodeChildInternalPhaseAtData
                                (n := n) (b := b) ds j0
                                ((f2ShearEquiv
                                  (CyclicNodeChildRootFamily n b ds)
                                  (cyclicChildRootBoundaryEvalLinearMap
                                    (n := n) (b := b) ds
                                    (q.1, castRootFieldDomain hchild q.2))
                                  τ hτ Φ) j0) (e Ψ) =
                              cyclicNodeChildInternalPhaseAtData
                                  (n := n) (b := b) ds j0 (Φ j0) Ψ +
                                (cyclicChildRootBoundaryEvalLinearMap
                                  (n := n) (b := b) ds
                                  (q.1, castRootFieldDomain hchild q.2) Φ *
                                  (σ + 1)))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSupportedReindexPhase
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  rcases
    hselected ha hchildren n hn i d hnonleaf hvisible φ hchild with
    ⟨j0, d0, rd0, d1, rd1, hτ, σ, hdot, hphase⟩
  let τ : CyclicNodeChildRootFamily n b ds :=
    cyclicNodeChildRootFamilyPair
      (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1
  refine ⟨τ, hτ, σ, hdot, j0, ?_, hphase⟩
  intro j hj
  exact
    cyclicNodeChildRootFamilyPair_component_eq_zero_of_ne_child
      (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1 j hj hj

theorem exists_childIdx_of_list_ne_nil
    {ds : List RTree}
    (hds : ds ≠ []) :
    ∃ j : ChildIdx ds, True := by
  cases ds with
  | nil =>
      exact False.elim (hds rfl)
  | cons C rest =>
      exact ⟨⟨0, by simp [ChildIdx]⟩, trivial⟩

theorem exists_nonleaf_childIdx_or_all_leaf_children
    (ds : List RTree) :
    (∃ j : ChildIdx ds, ∀ c : Nat, childAt ds j ≠ RTree.node c []) ∨
      (∀ j : ChildIdx ds, ∃ c : Nat, childAt ds j = RTree.node c []) := by
  classical
  by_cases h :
      ∃ j : ChildIdx ds, ∀ c : Nat, childAt ds j ≠ RTree.node c []
  · exact Or.inl h
  · refine Or.inr ?_
    intro j
    by_contra hleaf
    apply h
    refine ⟨j, ?_⟩
    intro c hc
    exact hleaf ⟨c, hc⟩

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_sameChildPairReindexPhase
    (hphase :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds)
          (q : CyclicNodeRootBoundaryDomain n b ds)
          (R : CyclicNodeRootBoundaryDomain n b ds → F2)
          (d0 : ZMod n)
          (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
          (d1 : ZMod n)
          (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0)
          (hτ :
            cyclicChildRootBoundaryEvalLinearMap
              (n := n) (b := b) ds q
              (cyclicNodeChildRootFamilyPair
                (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1) = 0)
          (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (cyclicNodeChildRootFamilyPair
                    (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              ∃ e :
                (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                  RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2) ≃
                (ZMod n → (v : NonRootVertex (childAt ds j0)) →
                  RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2),
                ∀ Ψ :
                  ZMod n → (v : NonRootVertex (childAt ds j0)) →
                    RawNormal.NodeChildNonRootFieldDomain n b ds j0 v → F2,
                  cyclicNodeChildInternalPhaseAtData
                      (n := n) (b := b) ds j0
                      ((f2ShearEquiv
                        (CyclicNodeChildRootFamily n b ds)
                        (cyclicChildRootBoundaryEvalLinearMap
                          (n := n) (b := b) ds q)
                        (cyclicNodeChildRootFamilyPair
                          (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1)
                        hτ Φ) j0) (e Ψ) =
                    cyclicNodeChildInternalPhaseAtData
                        (n := n) (b := b) ds j0 (Φ j0) Ψ +
                      (cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds q Φ *
                        (σ + 1))) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSameChildPairReindexPhase
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  let rootCoord :
      Fin ((RTree.node b ds).rootWeight - 1) → ZMod n :=
    fun _ => 0
  let R :
      CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun p : CyclicNodeRootBoundaryDomain n b ds =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (selectedBase, p.1))) p.2
  have hds : ds ≠ [] := by
    intro hnil
    apply hnonleaf b
    rw [hchild, hnil]
  rcases exists_childIdx_of_list_ne_nil hds with ⟨j0, _⟩
  rcases
    selectedAdjacentPair_supportedEvalShearDotWitness_cast
      (n := n) (b := b) (cs := cs) (ds := ds)
      i hchild j0 rootCoord q R with
    ⟨d0, rd0, d1, rd1, hτ, σ, hdot, _hτzero⟩
  refine ⟨j0, d0, rd0, d1, rd1, hτ, σ, hdot, ?_⟩
  exact
    hphase (n := n) (b := b) ds j0
      (q.1, castRootFieldDomain hchild q.2) R
      d0 rd0 d1 rd1 hτ σ hdot

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_sameChildPairEvalOneReindexPhase
    (hphaseOne :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds)
          (q : CyclicNodeRootBoundaryDomain n b ds)
          (R : CyclicNodeRootBoundaryDomain n b ds → F2)
          (d0 : ZMod n)
          (rd0 : RawNormal.NodeChildRootFieldDomain n b ds j0)
          (d1 : ZMod n)
          (rd1 : RawNormal.NodeChildRootFieldDomain n b ds j0)
          (hτ :
            cyclicChildRootBoundaryEvalLinearMap
              (n := n) (b := b) ds q
              (cyclicNodeChildRootFamilyPair
                (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1) = 0)
          (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (cyclicNodeChildRootFamilyPair
                    (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ = 1 →
              ∃ e :
                CyclicNodeChildNonRootFieldAt n b ds j0 ≃
                  CyclicNodeChildNonRootFieldAt n b ds j0,
                ∀ Ψ : CyclicNodeChildNonRootFieldAt n b ds j0,
                  cyclicNodeChildInternalPhaseAtData
                      (n := n) (b := b) ds j0
                      ((f2ShearEquiv
                        (CyclicNodeChildRootFamily n b ds)
                        (cyclicChildRootBoundaryEvalLinearMap
                          (n := n) (b := b) ds q)
                        (cyclicNodeChildRootFamilyPair
                          (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1)
                        hτ Φ) j0) (e Ψ) =
                    cyclicNodeChildInternalPhaseAtData
                        (n := n) (b := b) ds j0 (Φ j0) Ψ +
                      (σ + 1)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_sameChildPairReindexPhase
      ?_
  intro n b _ ds j0 q R d0 rd0 d1 rd1 hτ σ hdot Φ
  exact
    cyclicNodeChildInternalReindexPhase_of_evalOne
      (n := n) (b := b) ds j0
      (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds q)
      (cyclicNodeChildRootFamilyPair
        (n := n) (b := b) ds j0 d0 rd0 j0 d1 rd1)
      hτ σ
      (fun Φ hΦ =>
        hphaseOne (n := n) (b := b) ds j0 q R
          d0 rd0 d1 rd1 hτ σ hdot Φ hΦ)
      Φ

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedAdjacentPairEvalOneReindexPhase
    (hphaseOne :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds)
          (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
          (q : CyclicNodeRootBoundaryDomain n b ds)
          (R : CyclicNodeRootBoundaryDomain n b ds → F2)
          (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (selectedAdjacentPairRootFamily
                    (n := n) (b := b) ds j0 rootCoord q)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ = 1 →
              ∃ e :
                CyclicNodeChildNonRootFieldAt n b ds j0 ≃
                  CyclicNodeChildNonRootFieldAt n b ds j0,
                ∀ Ψ : CyclicNodeChildNonRootFieldAt n b ds j0,
                  cyclicNodeChildInternalPhaseAtData
                      (n := n) (b := b) ds j0
                      ((f2ShearEquiv
                        (CyclicNodeChildRootFamily n b ds)
                        (cyclicChildRootBoundaryEvalLinearMap
                          (n := n) (b := b) ds q)
                        (selectedAdjacentPairRootFamily
                          (n := n) (b := b) ds j0 rootCoord q)
                        (selectedAdjacentPairRootFamily_eval_eq_zero
                          (n := n) (b := b) ds j0 rootCoord q)
                        Φ) j0) (e Ψ) =
                    cyclicNodeChildInternalPhaseAtData
                        (n := n) (b := b) ds j0 (Φ j0) Ψ +
                      (σ + 1)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSupportedReindexPhase
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  let qcast : CyclicNodeRootBoundaryDomain n b ds :=
    (q.1, castRootFieldDomain hchild q.2)
  let rootCoord :
      Fin ((RTree.node b ds).rootWeight - 1) → ZMod n :=
    fun _ => 0
  let R :
      CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun p : CyclicNodeRootBoundaryDomain n b ds =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (selectedBase, p.1))) p.2
  have hds : ds ≠ [] := by
    intro hnil
    apply hnonleaf b
    rw [hchild, hnil]
  rcases exists_childIdx_of_list_ne_nil hds with ⟨j0, _⟩
  let τ : CyclicNodeChildRootFamily n b ds :=
    selectedAdjacentPairRootFamily
      (n := n) (b := b) ds j0 rootCoord qcast
  let hτ :
      cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds qcast τ = 0 :=
    selectedAdjacentPairRootFamily_eval_eq_zero
      (n := n) (b := b) ds j0 rootCoord qcast
  let σ : F2 :=
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
      (fun p : CyclicNodeRootBoundaryDomain n b ds =>
        cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
      R
  have hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        R = σ := rfl
  refine ⟨τ, hτ, σ, hdot, j0, ?_, ?_⟩
  · intro j hj
    exact
      selectedAdjacentPairRootFamily_component_eq_zero_of_ne_child
        (n := n) (b := b) ds j0 rootCoord qcast j hj
  · intro Φ
    exact
      cyclicNodeChildInternalReindexPhase_of_evalOne
        (n := n) (b := b) ds j0
        (cyclicChildRootBoundaryEvalLinearMap (n := n) (b := b) ds qcast)
        τ hτ σ
        (fun Φ hΦ =>
          hphaseOne (n := n) (b := b) ds j0 rootCoord qcast R σ
            hdot Φ hΦ)
        Φ

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedAdjacentPairEvalOneProduct
    (hprodOne :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds)
          (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
          (q : CyclicNodeRootBoundaryDomain n b ds)
          (R : CyclicNodeRootBoundaryDomain n b ds → F2)
          (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (selectedAdjacentPairRootFamily
                    (n := n) (b := b) ds j0 rootCoord q)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ = 1 →
                (∏ j : ChildIdx ds,
                  cyclicNodeChildNonRootSumAtRootFamily
                    (n := n) (b := b) ds j
                    ((f2ShearEquiv
                      (CyclicNodeChildRootFamily n b ds)
                      (cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds q)
                      (selectedAdjacentPairRootFamily
                        (n := n) (b := b) ds j0 rootCoord q)
                      (selectedAdjacentPairRootFamily_eval_eq_zero
                        (n := n) (b := b) ds j0 rootCoord q)
                      Φ) j)) =
                  (∏ j : ChildIdx ds,
                    cyclicNodeChildNonRootSumAtRootFamily
                      (n := n) (b := b) ds j (Φ j)) *
                    bitSign (σ + 1)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSign
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  let qcast : CyclicNodeRootBoundaryDomain n b ds :=
    (q.1, castRootFieldDomain hchild q.2)
  let rootCoord :
      Fin ((RTree.node b ds).rootWeight - 1) → ZMod n :=
    fun _ => 0
  let R :
      CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun p : CyclicNodeRootBoundaryDomain n b ds =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (selectedBase, p.1))) p.2
  have hds : ds ≠ [] := by
    intro hnil
    apply hnonleaf b
    rw [hchild, hnil]
  rcases exists_childIdx_of_list_ne_nil hds with ⟨j0, _⟩
  let τ : CyclicNodeChildRootFamily n b ds :=
    selectedAdjacentPairRootFamily
      (n := n) (b := b) ds j0 rootCoord qcast
  let hτ :
      cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds qcast τ = 0 :=
    selectedAdjacentPairRootFamily_eval_eq_zero
      (n := n) (b := b) ds j0 rootCoord qcast
  let σ : F2 :=
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
      (fun p : CyclicNodeRootBoundaryDomain n b ds =>
        cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
      R
  have hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        R = σ := rfl
  refine ⟨τ, hτ, σ, hdot, ?_⟩
  intro Φ
  exact
    cyclicNodeChildNonRootSumProduct_f2Shear_eq_mul_bitSign_of_evalOne
      (n := n) (b := b) ds
      (cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds qcast)
      τ hτ σ
      (fun Φ hΦ =>
        hprodOne (n := n) (b := b) ds j0 rootCoord qcast R σ
          hdot Φ hΦ)
      Φ

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedAdjacentPairEvalOneProductReindexPhase
    (hphaseOne :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds)
          (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
          (q : CyclicNodeRootBoundaryDomain n b ds)
          (R : CyclicNodeRootBoundaryDomain n b ds → F2)
          (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (selectedAdjacentPairRootFamily
                    (n := n) (b := b) ds j0 rootCoord q)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ = 1 →
                ∃ e :
                  CyclicNodeChildNonRootFamily n b ds ≃
                    CyclicNodeChildNonRootFamily n b ds,
                  ∀ Ψ : CyclicNodeChildNonRootFamily n b ds,
                    (∑ j : ChildIdx ds,
                      cyclicNodeChildInternalPhaseAtData
                        (n := n) (b := b) ds j
                        ((f2ShearEquiv
                          (CyclicNodeChildRootFamily n b ds)
                          (cyclicChildRootBoundaryEvalLinearMap
                            (n := n) (b := b) ds q)
                          (selectedAdjacentPairRootFamily
                            (n := n) (b := b) ds j0 rootCoord q)
                          (selectedAdjacentPairRootFamily_eval_eq_zero
                            (n := n) (b := b) ds j0 rootCoord q)
                          Φ) j)
                        ((e Ψ) j)) =
                      (∑ j : ChildIdx ds,
                        cyclicNodeChildInternalPhaseAtData
                          (n := n) (b := b) ds j (Φ j) (Ψ j)) +
                        (σ + 1)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedAdjacentPairEvalOneProduct
      ?_
  intro n b _ ds j0 rootCoord q R σ hdot Φ hΦ
  rcases
    hphaseOne (n := n) (b := b) ds j0 rootCoord q R σ
      hdot Φ hΦ with
    ⟨e, hphase⟩
  exact
    cyclicNodeChildNonRootSumProduct_eq_mul_bitSign_of_reindex_phase
      (n := n) (b := b) ds
      Φ
      (fun j =>
        (f2ShearEquiv
          (CyclicNodeChildRootFamily n b ds)
          (cyclicChildRootBoundaryEvalLinearMap
            (n := n) (b := b) ds q)
          (selectedAdjacentPairRootFamily
            (n := n) (b := b) ds j0 rootCoord q)
          (selectedAdjacentPairRootFamily_eval_eq_zero
            (n := n) (b := b) ds j0 rootCoord q)
          Φ) j)
      (σ + 1) e hphase

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_allLeafSign_or_nonLeafChildProductReindexPhase
    (hallLeafSign :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    (∀ j : ChildIdx ds,
                      ∃ c : Nat, childAt ds j = RTree.node c []) →
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                    ∃ σ : F2,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = σ ∧
                      ∀ Φ : CyclicNodeChildRootFamily n b ds,
                        (∏ j : ChildIdx ds,
                          cyclicNodeChildNonRootSumAtRootFamily
                            (n := n) (b := b) ds j
                            ((f2ShearEquiv
                              (CyclicNodeChildRootFamily n b ds)
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2))
                              τ hτ Φ) j)) =
                          (∏ j : ChildIdx ds,
                            cyclicNodeChildNonRootSumAtRootFamily
                              (n := n) (b := b) ds j (Φ j)) *
                            bitSign
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2) Φ *
                                  (σ + 1)))
    (hphaseOneNonLeafChild :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds),
          (∀ c : Nat, childAt ds j0 ≠ RTree.node c []) →
          ∀ (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
            (q : CyclicNodeRootBoundaryDomain n b ds)
            (R : CyclicNodeRootBoundaryDomain n b ds → F2)
            (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (selectedAdjacentPairRootFamily
                    (n := n) (b := b) ds j0 rootCoord q)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ = 1 →
                ∃ e :
                  CyclicNodeChildNonRootFamily n b ds ≃
                    CyclicNodeChildNonRootFamily n b ds,
                  ∀ Ψ : CyclicNodeChildNonRootFamily n b ds,
                    (∑ j : ChildIdx ds,
                      cyclicNodeChildInternalPhaseAtData
                        (n := n) (b := b) ds j
                        ((f2ShearEquiv
                          (CyclicNodeChildRootFamily n b ds)
                          (cyclicChildRootBoundaryEvalLinearMap
                            (n := n) (b := b) ds q)
                          (selectedAdjacentPairRootFamily
                            (n := n) (b := b) ds j0 rootCoord q)
                          (selectedAdjacentPairRootFamily_eval_eq_zero
                            (n := n) (b := b) ds j0 rootCoord q)
                          Φ) j)
                        ((e Ψ) j)) =
                      (∑ j : ChildIdx ds,
                        cyclicNodeChildInternalPhaseAtData
                          (n := n) (b := b) ds j (Φ j) (Ψ j)) +
                        (σ + 1)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSign
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  rcases exists_nonleaf_childIdx_or_all_leaf_children ds with hsome | hallLeaf
  ·
      rcases hsome with ⟨j0, hj0_nonleaf⟩
      let selectedBase :
          ChildExternalBaseCoordinate n a cs i :=
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1
      let q :
          ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).2,
          (nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).2)
      let qcast : CyclicNodeRootBoundaryDomain n b ds :=
        (q.1, castRootFieldDomain hchild q.2)
      let rootCoord :
          Fin ((RTree.node b ds).rootWeight - 1) → ZMod n :=
        fun _ => 0
      let R :
          CyclicNodeRootBoundaryDomain n b ds → F2 :=
        fun p : CyclicNodeRootBoundaryDomain n b ds =>
          castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm
                (selectedBase, p.1))) p.2
      let τ : CyclicNodeChildRootFamily n b ds :=
        selectedAdjacentPairRootFamily
          (n := n) (b := b) ds j0 rootCoord qcast
      let hτ :
          cyclicChildRootBoundaryEvalLinearMap
            (n := n) (b := b) ds qcast τ = 0 :=
        selectedAdjacentPairRootFamily_eval_eq_zero
          (n := n) (b := b) ds j0 rootCoord qcast
      let σ : F2 :=
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
          (fun p : CyclicNodeRootBoundaryDomain n b ds =>
            cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
          R
      have hdot :
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap
                (n := n) (b := b) ds τ p.1 p.2)
            R = σ := rfl
      refine ⟨τ, hτ, σ, hdot, ?_⟩
      intro Φ
      exact
        cyclicNodeChildNonRootSumProduct_f2Shear_eq_mul_bitSign_of_evalOne
          (n := n) (b := b) ds
          (cyclicChildRootBoundaryEvalLinearMap
            (n := n) (b := b) ds qcast)
          τ hτ σ
          (fun Φ hΦ => by
            rcases
              hphaseOneNonLeafChild
                (n := n) (b := b) ds j0 hj0_nonleaf
                rootCoord qcast R σ hdot Φ hΦ with
              ⟨e, hphase⟩
            exact
              cyclicNodeChildNonRootSumProduct_eq_mul_bitSign_of_reindex_phase
                (n := n) (b := b) ds
                Φ
                (fun j =>
                  (f2ShearEquiv
                    (CyclicNodeChildRootFamily n b ds)
                    (cyclicChildRootBoundaryEvalLinearMap
                      (n := n) (b := b) ds qcast)
                    τ hτ Φ) j)
                (σ + 1) e hphase)
          Φ
  ·
      exact
        hallLeafSign ha hchildren n hn i d hnonleaf hvisible φ hchild
          hallLeaf

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_allLeafSign_or_nonLeafChildSingleReindexPhase
    (hallLeafSign :
      ∀ {a : Nat} {cs : List RTree},
        0 < a →
        (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
        ∀ (n : Nat) [NeZero n],
          1 < n →
          ∀ (i : ChildIdx cs)
            (d : RawNormal.NodeChildRootFieldDomain n a cs i),
            (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
              BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
                ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
                  ∀ {b : Nat} {ds : List RTree}
                    (hchild : childAt cs i = RTree.node b ds),
                    (∀ j : ChildIdx ds,
                      ∃ c : Nat, childAt ds j = RTree.node c []) →
                    let selectedBase :
                      ChildExternalBaseCoordinate n a cs i :=
                      (childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).1
                    let q :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) :=
                      ((childExternalCoordinateEquivBaseDiag
                        (n := n) (a := a) (cs := cs) i
                        ((nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).1)).2,
                        (nodeChildRootFieldDomainStructuredEquiv
                          (n := n) (a := a) (cs := cs) i d).2)
                    ∃ τ : CyclicNodeChildRootFamily n b ds,
                    ∃ hτ :
                      cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds
                        (q.1, castRootFieldDomain hchild q.2) τ = 0,
                    ∃ σ : F2,
                      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          cyclicChildRootBoundaryMap (n := n) (b := b) ds
                            τ p.1 p.2)
                        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                          castRootFieldAssignment hchild
                            ((nodeChildRootFieldFamilyAtExternalEquiv
                              (n := n) (a := a) (cs := cs) i φ)
                              ((childExternalCoordinateEquivBaseDiag
                                (n := n) (a := a) (cs := cs) i).symm
                                (selectedBase, p.1))) p.2) = σ ∧
                      ∀ Φ : CyclicNodeChildRootFamily n b ds,
                        (∏ j : ChildIdx ds,
                          cyclicNodeChildNonRootSumAtRootFamily
                            (n := n) (b := b) ds j
                            ((f2ShearEquiv
                              (CyclicNodeChildRootFamily n b ds)
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2))
                              τ hτ Φ) j)) =
                          (∏ j : ChildIdx ds,
                            cyclicNodeChildNonRootSumAtRootFamily
                              (n := n) (b := b) ds j (Φ j)) *
                            bitSign
                              (cyclicChildRootBoundaryEvalLinearMap
                                (n := n) (b := b) ds
                                (q.1, castRootFieldDomain hchild q.2) Φ *
                                  (σ + 1)))
    (hphaseOneNonLeafChild :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds),
          (∀ c : Nat, childAt ds j0 ≠ RTree.node c []) →
          ∀ (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
            (q : CyclicNodeRootBoundaryDomain n b ds)
            (R : CyclicNodeRootBoundaryDomain n b ds → F2)
            (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (selectedAdjacentPairRootFamily
                    (n := n) (b := b) ds j0 rootCoord q)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ = 1 →
                ∃ e :
                  CyclicNodeChildNonRootFieldAt n b ds j0 ≃
                    CyclicNodeChildNonRootFieldAt n b ds j0,
                  ∀ Ψ : CyclicNodeChildNonRootFieldAt n b ds j0,
                    cyclicNodeChildInternalPhaseAtData
                        (n := n) (b := b) ds j0
                        ((f2ShearEquiv
                          (CyclicNodeChildRootFamily n b ds)
                          (cyclicChildRootBoundaryEvalLinearMap
                            (n := n) (b := b) ds q)
                          (selectedAdjacentPairRootFamily
                            (n := n) (b := b) ds j0 rootCoord q)
                          (selectedAdjacentPairRootFamily_eval_eq_zero
                            (n := n) (b := b) ds j0 rootCoord q)
                          Φ) j0) (e Ψ) =
                      cyclicNodeChildInternalPhaseAtData
                          (n := n) (b := b) ds j0 (Φ j0) Ψ +
                        (σ + 1)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSign
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  rcases exists_nonleaf_childIdx_or_all_leaf_children ds with hsome | hallLeaf
  ·
      rcases hsome with ⟨j0, hj0_nonleaf⟩
      let selectedBase :
          ChildExternalBaseCoordinate n a cs i :=
        (childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).1
      let q :
          ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
        ((childExternalCoordinateEquivBaseDiag
          (n := n) (a := a) (cs := cs) i
          ((nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).1)).2,
          (nodeChildRootFieldDomainStructuredEquiv
            (n := n) (a := a) (cs := cs) i d).2)
      let qcast : CyclicNodeRootBoundaryDomain n b ds :=
        (q.1, castRootFieldDomain hchild q.2)
      let rootCoord :
          Fin ((RTree.node b ds).rootWeight - 1) → ZMod n :=
        fun _ => 0
      let R :
          CyclicNodeRootBoundaryDomain n b ds → F2 :=
        fun p : CyclicNodeRootBoundaryDomain n b ds =>
          castRootFieldAssignment hchild
            ((nodeChildRootFieldFamilyAtExternalEquiv
              (n := n) (a := a) (cs := cs) i φ)
              ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm
                (selectedBase, p.1))) p.2
      let τ : CyclicNodeChildRootFamily n b ds :=
        selectedAdjacentPairRootFamily
          (n := n) (b := b) ds j0 rootCoord qcast
      let hτ :
          cyclicChildRootBoundaryEvalLinearMap
            (n := n) (b := b) ds qcast τ = 0 :=
        selectedAdjacentPairRootFamily_eval_eq_zero
          (n := n) (b := b) ds j0 rootCoord qcast
      let σ : F2 :=
        dotLinear (CyclicNodeRootBoundaryDomain n b ds)
          (fun p : CyclicNodeRootBoundaryDomain n b ds =>
            cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
          R
      have hdot :
          dotLinear (CyclicNodeRootBoundaryDomain n b ds)
            (fun p : CyclicNodeRootBoundaryDomain n b ds =>
              cyclicChildRootBoundaryMap
                (n := n) (b := b) ds τ p.1 p.2)
            R = σ := rfl
      refine ⟨τ, hτ, σ, hdot, ?_⟩
      intro Φ
      exact
        cyclicNodeChildNonRootSumProduct_shearSign_of_single_factor
          (n := n) (b := b) ds
          (cyclicChildRootBoundaryEvalLinearMap
            (n := n) (b := b) ds qcast)
          τ hτ σ j0
          (fun Φ j hj =>
            cyclicNodeChildNonRootSumAtRootFamily_f2Shear_eq_of_component_zero
              (n := n) (b := b) ds
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds qcast)
              τ hτ Φ j
              (selectedAdjacentPairRootFamily_component_eq_zero_of_ne_child
                (n := n) (b := b) ds j0 rootCoord qcast j hj))
          (fun Φ =>
            cyclicNodeChildNonRootSumAtRootFamily_f2Shear_eq_mul_bitSign_of_evalOne
              (n := n) (b := b) ds j0
              (cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds qcast)
              τ hτ σ
              (fun Φ hΦ => by
                rcases
                  hphaseOneNonLeafChild
                    (n := n) (b := b) ds j0 hj0_nonleaf
                    rootCoord qcast R σ hdot Φ hΦ with
                  ⟨e, hphase⟩
                exact
                  cyclicNodeChildNonRootSumAtRootFamily_eq_mul_bitSign_of_reindex_phase
                    (n := n) (b := b) ds j0
                    (Φ j0)
                    ((f2ShearEquiv
                      (CyclicNodeChildRootFamily n b ds)
                      (cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds qcast)
                      τ hτ Φ) j0)
                    (σ + 1) e hphase)
              Φ)
          Φ
  ·
      exact
        hallLeafSign ha hchildren n hn i d hnonleaf hvisible φ hchild
          hallLeaf

theorem branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedAdjacentPairEvalOneSum
    (hsumOne :
      ∀ {n b : Nat} [NeZero n],
        ∀ (ds : List RTree)
          (j0 : ChildIdx ds)
          (rootCoord : Fin ((RTree.node b ds).rootWeight - 1) → ZMod n)
          (q : CyclicNodeRootBoundaryDomain n b ds)
          (R : CyclicNodeRootBoundaryDomain n b ds → F2)
          (σ : F2),
            dotLinear (CyclicNodeRootBoundaryDomain n b ds)
              (fun p : CyclicNodeRootBoundaryDomain n b ds =>
                cyclicChildRootBoundaryMap (n := n) (b := b) ds
                  (selectedAdjacentPairRootFamily
                    (n := n) (b := b) ds j0 rootCoord q)
                  p.1 p.2)
              R = σ →
            ∀ Φ : CyclicNodeChildRootFamily n b ds,
              cyclicChildRootBoundaryEvalLinearMap
                (n := n) (b := b) ds q Φ = 1 →
                cyclicNodeChildNonRootSumAtRootFamily
                    (n := n) (b := b) ds j0
                    ((f2ShearEquiv
                      (CyclicNodeChildRootFamily n b ds)
                      (cyclicChildRootBoundaryEvalLinearMap
                        (n := n) (b := b) ds q)
                      (selectedAdjacentPairRootFamily
                        (n := n) (b := b) ds j0 rootCoord q)
                      (selectedAdjacentPairRootFamily_eval_eq_zero
                        (n := n) (b := b) ds j0 rootCoord q)
                      Φ) j0) =
                  cyclicNodeChildNonRootSumAtRootFamily
                      (n := n) (b := b) ds j0 (Φ j0) *
                    bitSign (σ + 1)) :
    BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule := by
  refine
    branchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule_of_selectedCyclicRootSingletonEvalShearSignSingleFactor
      ?_
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible φ b ds hchild
  let selectedBase :
      ChildExternalBaseCoordinate n a cs i :=
    (childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).1
  let q :
      ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    ((childExternalCoordinateEquivBaseDiag
      (n := n) (a := a) (cs := cs) i
      ((nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).1)).2,
      (nodeChildRootFieldDomainStructuredEquiv
        (n := n) (a := a) (cs := cs) i d).2)
  let qcast : CyclicNodeRootBoundaryDomain n b ds :=
    (q.1, castRootFieldDomain hchild q.2)
  let rootCoord :
      Fin ((RTree.node b ds).rootWeight - 1) → ZMod n :=
    fun _ => 0
  let R :
      CyclicNodeRootBoundaryDomain n b ds → F2 :=
    fun p : CyclicNodeRootBoundaryDomain n b ds =>
      castRootFieldAssignment hchild
        ((nodeChildRootFieldFamilyAtExternalEquiv
          (n := n) (a := a) (cs := cs) i φ)
          ((childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm
            (selectedBase, p.1))) p.2
  have hds : ds ≠ [] := by
    intro hnil
    apply hnonleaf b
    rw [hchild, hnil]
  rcases exists_childIdx_of_list_ne_nil hds with ⟨j0, _⟩
  let τ : CyclicNodeChildRootFamily n b ds :=
    selectedAdjacentPairRootFamily
      (n := n) (b := b) ds j0 rootCoord qcast
  let hτ :
      cyclicChildRootBoundaryEvalLinearMap
        (n := n) (b := b) ds qcast τ = 0 :=
    selectedAdjacentPairRootFamily_eval_eq_zero
      (n := n) (b := b) ds j0 rootCoord qcast
  let σ : F2 :=
    dotLinear (CyclicNodeRootBoundaryDomain n b ds)
      (fun p : CyclicNodeRootBoundaryDomain n b ds =>
        cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
      R
  have hdot :
      dotLinear (CyclicNodeRootBoundaryDomain n b ds)
        (fun p : CyclicNodeRootBoundaryDomain n b ds =>
          cyclicChildRootBoundaryMap (n := n) (b := b) ds τ p.1 p.2)
        R = σ := rfl
  refine ⟨τ, hτ, σ, hdot, j0, ?_, ?_⟩
  · intro Φ j hj
    exact
      cyclicNodeChildNonRootSumAtRootFamily_f2Shear_eq_of_component_zero
        (n := n) (b := b) ds
        (cyclicChildRootBoundaryEvalLinearMap
          (n := n) (b := b) ds qcast)
        τ hτ Φ j
        (selectedAdjacentPairRootFamily_component_eq_zero_of_ne_child
          (n := n) (b := b) ds j0 rootCoord qcast j hj)
  · intro Φ
    exact
      cyclicNodeChildNonRootSumAtRootFamily_f2Shear_eq_mul_bitSign_of_evalOne
        (n := n) (b := b) ds j0
        (cyclicChildRootBoundaryEvalLinearMap
          (n := n) (b := b) ds qcast)
        τ hτ σ
        (fun Φ hΦ =>
          hsumOne (n := n) (b := b) ds j0 rootCoord qcast R σ
            hdot Φ hΦ)
        Φ

theorem branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_baseFixedRoot
    (hbase :
      BranchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule) :
    BranchVisibleSingletonShiftInvariantNonLeafCoreRule := by
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible
  exact
    childOpenRootInternalKernelAt_shiftInvariant_of_baseFixedRootShiftInvariant
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      (Pi.single
        (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
        d (1 : F2))
      (hbase ha hchildren n hn i d hnonleaf hvisible)

theorem branchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule_of_rootSingleton
    (hroot : FixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCoreRule) :
    BranchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule := by
  classical
  intro a cs ha hchildren n _ hn i d _hnonleaf _hvisible base Rcyc
  let e := nodeChildRootFieldDomainStructuredEquiv
    (n := n) (a := a) (cs := cs) i
  let bd := childExternalCoordinateEquivBaseDiag
    (n := n) (a := a) (cs := cs) i (e d).1
  let q : ZMod n × RawNormal.RootFieldDomain n (childAt cs i) :=
    (bd.2, (e d).2)
  by_cases hbase : base = bd.1
  · have hshift :
        Rcyc +
            nodeChildRootFieldShiftAtExternalBase
              (n := n) (a := a) (cs := cs) i
              (Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2))
              base =
          fun t rd =>
            Rcyc t rd +
              Pi.single
                (M := fun _ :
                  ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                    F2)
                q (1 : F2) (t, rd) := by
      funext t rd
      change
        Rcyc t rd +
            nodeChildRootFieldShiftAtExternalBase
              (n := n) (a := a) (cs := cs) i
              (Pi.single
                (M := fun _ :
                  RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2))
              base t rd =
          Rcyc t rd +
            Pi.single
              (M := fun _ :
                ZMod n × RawNormal.RootFieldDomain n (childAt cs i) =>
                  F2)
              q (1 : F2) (t, rd)
      congr 1
      by_cases hp : (t, rd) = q
      · have ht : t = bd.2 := by
          simpa [q] using congrArg Prod.fst hp
        have hrd : rd = (e d).2 := by
          simpa [q] using congrArg Prod.snd hp
        have hbd : (base, t) = bd := by
          exact Prod.ext hbase ht
        have hext :
            (childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t) =
              (e d).1 := by
          rw [hbd]
          exact
            (childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm_apply_apply
              (e d).1
        have hpair :
            ((childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
              e d := by
          exact Prod.ext hext hrd
        have hdomain :
            e.symm
              ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
              d := by
          rw [hpair]
          exact e.symm_apply_apply d
        unfold nodeChildRootFieldShiftAtExternalBase
        rw [hdomain, hp]
        simp
      · have hdomain_ne :
            e.symm
              ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, t), rd) ≠
              d := by
          intro hdomain
          apply hp
          have hpair :
              ((childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
                e d := by
            exact (e.symm_apply_eq).1 hdomain
          have hext :
              (childExternalCoordinateEquivBaseDiag
                (n := n) (a := a) (cs := cs) i).symm (base, t) =
                (e d).1 := by
            simpa using congrArg Prod.fst hpair
          have hrd : rd = (e d).2 := by
            simpa using congrArg Prod.snd hpair
          have hbd :
              (base, t) = bd := by
            have happ :=
              congrArg
                (childExternalCoordinateEquivBaseDiag
                  (n := n) (a := a) (cs := cs) i) hext
            simpa [bd] using happ
          exact Prod.ext
            (by simpa [q] using congrArg Prod.snd hbd)
            (by simpa [q] using hrd)
        unfold nodeChildRootFieldShiftAtExternalBase
        rw [Pi.single_eq_of_ne hdomain_ne, Pi.single_eq_of_ne hp]
    rw [hshift]
    exact hroot ha hchildren n hn i q Rcyc
  · have hzero :
        nodeChildRootFieldShiftAtExternalBase
            (n := n) (a := a) (cs := cs) i
            (Pi.single
              (M := fun _ :
                RawNormal.NodeChildRootFieldDomain n a cs i => F2)
              d (1 : F2))
            base =
          0 := by
      funext t rd
      unfold nodeChildRootFieldShiftAtExternalBase
      apply Pi.single_eq_of_ne
      intro hdomain
      have hpair :
          ((childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i).symm (base, t), rd) =
            e d := by
        exact (e.symm_apply_eq).1 hdomain
      have hext :
          (childExternalCoordinateEquivBaseDiag
            (n := n) (a := a) (cs := cs) i).symm (base, t) =
            (e d).1 := by
        simpa using congrArg Prod.fst hpair
      have hbd :
          (base, t) = bd := by
        have happ :=
          congrArg
            (childExternalCoordinateEquivBaseDiag
              (n := n) (a := a) (cs := cs) i) hext
        simpa [bd] using happ
      exact hbase (by simpa using congrArg Prod.fst hbd)
    simp [hzero]

theorem fixedRootCyclicNodeFieldSum_shiftInvariant_of_rootSingletonShiftInvariant
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hshift :
      ∀ q :
        ZMod n × RawNormal.RootFieldDomain n (childAt cs i),
        ∀ Rcyc :
          ZMod n → RawNormal.RootFieldAssignment n (childAt cs i),
          fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i
              (fun d rd =>
                Rcyc d rd +
                  Pi.single
                    (M := fun _ :
                      ZMod n ×
                        RawNormal.RootFieldDomain n (childAt cs i) =>
                      F2)
                    q (1 : F2) (d, rd)) =
            fixedRootCyclicNodeFieldSum
              (n := n) (a := a) (cs := cs) i Rcyc)
    (R S : ZMod n → RawNormal.RootFieldAssignment n (childAt cs i)) :
    fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i (R + S) =
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i R := by
  classical
  let D := ZMod n × RawNormal.RootFieldDomain n (childAt cs i)
  let F : (D → F2) → ℤ :=
    fun α =>
      fixedRootCyclicNodeFieldSum
        (n := n) (a := a) (cs := cs) i
        (fun d rd => α (d, rd))
  let α : D → F2 := fun q => R q.1 q.2
  let β : D → F2 := fun q => S q.1 q.2
  have hsum :
      β =
        ∑ q : D, β q •
          Pi.single (M := fun _ : D => F2) q (1 : F2) :=
    function_eq_sum_single D β
  have hfinset :
      ∀ s : Finset D,
        F (α + s.sum (fun q => β q •
          Pi.single (M := fun _ : D => F2) q (1 : F2))) =
        F α := by
    intro s
    refine Finset.induction_on s ?hbase ?hstep
    · simp [F]
    · intro q s hnot ih
      rw [Finset.sum_insert hnot]
      by_cases hq : β q = 0
      · rw [hq, zero_smul, zero_add]
        exact ih
      · have hq_one : β q = 1 := by
          generalize hx : β q = x
          fin_cases x
          · exact False.elim (hq hx)
          · rfl
        rw [hq_one, one_smul]
        calc
          F (α + (Pi.single (M := fun _ : D => F2) q (1 : F2) +
              s.sum (fun x => β x •
                Pi.single (M := fun _ : D => F2) x (1 : F2)))) =
              F ((α + s.sum (fun x => β x •
                  Pi.single (M := fun _ : D => F2) x (1 : F2))) +
                Pi.single (M := fun _ : D => F2) q (1 : F2)) := by
                congr 1
                ac_rfl
          _ =
              F (α + s.sum (fun x => β x •
                Pi.single (M := fun _ : D => F2) x (1 : F2))) := by
                simpa [F, D, Pi.add_apply] using
                  hshift q
                    (fun d rd =>
                      (α + s.sum (fun x => β x •
                        Pi.single (M := fun _ : D => F2) x (1 : F2)))
                        (d, rd))
          _ = F α := ih
  change F (α + β) = F α
  rw [hsum]
  exact hfinset Finset.univ

theorem branchConstraintBaseFixedRootShiftInvariantCoreRule_of_rootSingleton
    (hroot : FixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCoreRule) :
    BranchConstraintBaseFixedRootShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i δ _hδ base Rcyc
  exact
    fixedRootCyclicNodeFieldSum_shiftInvariant_of_rootSingletonShiftInvariant
      (n := n) (a := a) (cs := cs) i
      (hroot ha hchildren n hn i)
      Rcyc
      (nodeChildRootFieldShiftAtExternalBase
        (n := n) (a := a) (cs := cs) i δ base)

abbrev BranchVisibleSingleTogglePhaseNonLeafLocalRule : Prop :=
  ∀ {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (d : RawNormal.NodeChildRootFieldDomain n a cs i),
      (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
          ∃ ext0 : ChildExternalCoordinate n a cs i,
            ∃ v0 : NonRootVertex (childAt cs i),
              ∃ nd0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0,
                ∀ (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
                  (Ψ : ChildExternalNodeFieldFamily n a cs i),
                  childExternalRootNodeFieldPhaseAt
                      (n := n) (a := a) (cs := cs) i hchildRoot
                      (φ +
                        Pi.single
                          (M := fun _ :
                            RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                          d (1 : F2))
                      (childExternalNodeFieldSingleToggleEquiv
                        (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ) =
                    childExternalRootNodeFieldPhaseAt
                      (n := n) (a := a) (cs := cs) i hchildRoot φ Ψ

abbrev BranchVisibleSingleTogglePhaseNonLeafCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (d : RawNormal.NodeChildRootFieldDomain n a cs i),
        (∀ b : Nat, childAt cs i ≠ RTree.node b []) →
          BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d →
            ∃ ext0 : ChildExternalCoordinate n a cs i,
              ∃ v0 : NonRootVertex (childAt cs i),
                ∃ nd0 : RawNormal.NonRootFieldDomain n (childAt cs i) v0,
                  ∀ (φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
                    (Ψ : ChildExternalNodeFieldFamily n a cs i),
                    childExternalRootNodeFieldPhaseAt
                        (n := n) (a := a) (cs := cs) i
                        (childAt_rootWeight_pos_of_openRootCert i
                          (RawExpandedOpenRootSubtreeCert.childAt_of_children
                            (cs := cs) hchildren i))
                        (φ +
                          Pi.single
                            (M := fun _ :
                              RawNormal.NodeChildRootFieldDomain n a cs i =>
                                F2)
                            d (1 : F2))
                        (childExternalNodeFieldSingleToggleEquiv
                          (n := n) (a := a) (cs := cs) i ext0 v0 nd0 Ψ) =
                      childExternalRootNodeFieldPhaseAt
                        (n := n) (a := a) (cs := cs) i
                        (childAt_rootWeight_pos_of_openRootCert i
                          (RawExpandedOpenRootSubtreeCert.childAt_of_children
                            (cs := cs) hchildren i))
                        φ Ψ

theorem branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    BranchVisibleSingletonExternalReindexNonLeafLocalRule := by
  intro n a _ cs i hchildRoot d hnonleaf hvisible
  rcases hphaseRule
      (n := n) (a := a) (cs := cs) i hchildRoot d hnonleaf hvisible with
    ⟨ext0, v0, nd0, hphase⟩
  exact
    internalKernelSingletonExternalReindexAt_of_single_toggle_phase
      (n := n) (a := a) (cs := cs) i hchildRoot d ext0 v0 nd0 hphase

theorem branchVisibleSingletonExternalReindexNonLeafCoreRule_of_singleTogglePhaseCore
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafCoreRule) :
    BranchVisibleSingletonExternalReindexNonLeafCoreRule := by
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible
  rcases hphaseRule ha hchildren n hn i d hnonleaf hvisible with
    ⟨ext0, v0, nd0, hphase⟩
  exact
    internalKernelSingletonExternalReindexAt_of_single_toggle_phase
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      d ext0 v0 nd0 hphase

theorem branchVisibleSingleTogglePhaseNonLeafCoreRule_of_local
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    BranchVisibleSingleTogglePhaseNonLeafCoreRule := by
  intro a cs _ha hchildren n _ _hn i d hnonleaf hvisible
  exact
    hphaseRule (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      d hnonleaf hvisible

theorem branchVisibleSingletonExternalReindexNonLeafCoreRule_of_local
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    BranchVisibleSingletonExternalReindexNonLeafCoreRule := by
  intro a cs _ha hchildren n _ _hn i d hnonleaf hvisible
  exact
    hlocal (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
          (RawExpandedOpenRootSubtreeCert.childAt_of_children
            (cs := cs) hchildren i))
      d hnonleaf hvisible

theorem branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_local
    (hlocal : BranchVisibleSingletonShiftInvariantNonLeafLocalRule) :
    BranchVisibleSingletonShiftInvariantNonLeafCoreRule := by
  intro a cs _ha _hchildren n _ _hn i d hnonleaf hvisible
  exact hlocal (n := n) (a := a) (cs := cs) i d hnonleaf hvisible

theorem allSingletonShiftInvariantCore_of_branchConstraintImageKernelDependsLocal_and_nonLeafShiftInvariantLocal
    (hdepends : BranchConstraintImageKernelDependsLocalRule)
    (hlocal : BranchVisibleSingletonShiftInvariantNonLeafLocalRule) :
    AllSingletonShiftInvariantCoreRule := by
  intro a cs _ha _hchildren n _ _hn i d
  by_cases hleaf : ∃ b : Nat, childAt cs i = RTree.node b []
  · rcases hleaf with ⟨b, hchild⟩
    exact
      branchConstraintKernelShiftInvariantAt_of_leaf_child
        (n := n) (a := a) (b := b) (cs := cs) i hchild
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
  · by_cases hvisible :
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d
    · exact
        hlocal (n := n) (a := a) (cs := cs) i d
          (by
            intro b hchild
            exact hleaf ⟨b, hchild⟩)
          hvisible
    · have hinvisible :
          BranchSingletonConstraintInvisibleAt (n := n) (a := a) cs i d := by
        by_contra hne
        exact hvisible hne
      exact
        (branchConstraintKernelShiftInvariantLocalRule_of_imageKernelDepends
          hdepends) i
          (Pi.single
            (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
            d (1 : F2))
          hinvisible

theorem allSingletonShiftInvariantCore_of_baseFixedRootRules
    (hbase : BranchConstraintBaseFixedRootShiftInvariantCoreRule)
    (hvisibleBase :
      BranchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule) :
    AllSingletonShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i d
  by_cases hleaf : ∃ b : Nat, childAt cs i = RTree.node b []
  · rcases hleaf with ⟨b, hchild⟩
    exact
      branchConstraintKernelShiftInvariantAt_of_leaf_child
        (n := n) (a := a) (b := b) (cs := cs) i hchild
        (Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2))
  · by_cases hvisible :
        BranchSingletonConstraintVisibleAt (n := n) (a := a) cs i d
    · exact
        (branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_baseFixedRoot
          hvisibleBase) ha hchildren n hn i d
          (by
            intro b hchild
            exact hleaf ⟨b, hchild⟩)
          hvisible
    · have hinvisible :
          BranchSingletonConstraintInvisibleAt (n := n) (a := a) cs i d := by
        by_contra hne
        exact hvisible hne
      exact
        (branchConstraintKernelShiftInvariantCoreRule_of_baseFixedRootShiftInvariantCore
          hbase) ha hchildren n hn i
          (Pi.single
            (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
            d (1 : F2))
          hinvisible

abbrev BranchConstraintKernelExternalReindexCoreRule : Prop :=
  ∀ {a : Nat} {cs : List RTree},
    0 < a →
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C) →
    ∀ (n : Nat) [NeZero n],
      1 < n →
      ∀ (i : ChildIdx cs)
        (δ : RawNormal.NodeChildRootFieldDomain n a cs i → F2),
        nodeChildRootBoundaryBranchConstraintMap
            (n := n) (a := a) cs i δ = 0 →
          InternalKernelExternalReindexAt
            (n := n) (a := a) cs i
            (childAt_rootWeight_pos_of_openRootCert i
              (RawExpandedOpenRootSubtreeCert.childAt_of_children
                (cs := cs) hchildren i))
            δ

theorem branchConstraintKernelShiftInvariantCoreRule_of_externalReindexCore
    (hreindex : BranchConstraintKernelExternalReindexCoreRule) :
    BranchConstraintKernelShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i δ hδ φ
  exact
    childOpenRootInternalKernelAt_shiftInvariant_of_externalReindex
      (n := n) (a := a) (cs := cs) (i := i)
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      (hreindex ha hchildren n hn i δ hδ)
      φ

theorem internalKernelSingletonShiftInvariantAt_of_leaf_child
    {n a b : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchild : childAt cs i = RTree.node b [])
    (d : RawNormal.NodeChildRootFieldDomain n a cs i) :
    InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d := by
  intro φ
  rw [
    childOpenRootInternalKernelAt_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild
      (φ +
        Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2)),
    childOpenRootInternalKernelAt_leaf_child
      (n := n) (a := a) (b := b) (cs := cs) i hchild φ]

theorem nonempty_nonRootVertex_of_not_leaf
    {T : RTree}
    (hnonleaf : ∀ b : Nat, T ≠ RTree.node b []) :
    Nonempty (NonRootVertex T) := by
  cases T with
  | node a children =>
      cases children with
      | nil =>
          exact False.elim (hnonleaf a rfl)
      | cons C rest =>
          exact
            ⟨RawNormal.childRootAsNonRootInNode
              (a := a) (idx := 0) (cs := C :: rest) (C := C) (by simp)⟩

theorem nonempty_child_nonRootVertex_of_not_leaf
    {cs : List RTree}
    (i : ChildIdx cs)
    (hnonleaf : ∀ b : Nat, childAt cs i ≠ RTree.node b []) :
    Nonempty (NonRootVertex (childAt cs i)) :=
  nonempty_nonRootVertex_of_not_leaf hnonleaf

theorem exists_child_nonRootVertex_and_nonRootFieldDomain_of_not_leaf
    {n : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hnonleaf : ∀ b : Nat, childAt cs i ≠ RTree.node b []) :
    ∃ v : NonRootVertex (childAt cs i),
      Nonempty (RawNormal.NonRootFieldDomain n (childAt cs i) v) := by
  rcases nonempty_child_nonRootVertex_of_not_leaf i hnonleaf with ⟨v⟩
  exact
    ⟨v,
      ⟨{ rootCoord := fun _ => 0
         diagonal := 0
         otherCoord := fun _ _ => 0 }⟩⟩

theorem internalKernelSingletonShiftInvariantAt_of_reindex
    {n a : Nat} [NeZero n] {cs : List RTree}
    {i : ChildIdx cs}
    {d : RawNormal.NodeChildRootFieldDomain n a cs i}
    (hreindex :
      InternalKernelSingletonReindexAt (n := n) (a := a) cs i d) :
    InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d := by
  classical
  intro φ
  rcases hreindex φ with ⟨e, hphase⟩
  unfold childOpenRootInternalKernelAt childOpenRootInternalSumAt
  refine
    Fintype.sum_equiv e.symm
      (fun ψ : ChildInternalNonRootFieldFamily n a cs i =>
        bitSign
          (childInternalPhaseGivenRootFieldsAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            (φ +
              Pi.single
                (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                d (1 : F2)) ψ))
      (fun ψ : ChildInternalNonRootFieldFamily n a cs i =>
        bitSign
          (childInternalPhaseGivenRootFieldsAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i φ ψ))
      ?_
  intro ψ
  have h :
      childInternalPhaseGivenRootFieldsAt
          (n := n) (a := a) cs
          (0 : RawNormal.NodeRootFieldAssignment n a cs) i
          (φ +
            Pi.single
              (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
              d (1 : F2)) ψ =
        childInternalPhaseGivenRootFieldsAt
          (n := n) (a := a) cs
          (0 : RawNormal.NodeRootFieldAssignment n a cs) i φ (e.symm ψ) := by
    simpa using hphase (e.symm ψ)
  exact congrArg bitSign h

theorem internalKernelSingletonShiftInvariantAt_of_externalReindex
    {n a : Nat} [NeZero n] {cs : List RTree}
    {i : ChildIdx cs}
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    {d : RawNormal.NodeChildRootFieldDomain n a cs i}
    (hreindex :
      InternalKernelSingletonExternalReindexAt
        (n := n) (a := a) cs i hchildRoot d) :
    InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d := by
  classical
  intro φ
  rw [
    childOpenRootInternalKernelAt_eq_externalNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot
      (φ +
        Pi.single
          (M := fun _ : RawNormal.NodeChildRootFieldDomain n a cs i => F2)
          d (1 : F2)),
    childOpenRootInternalKernelAt_eq_externalNodeFieldSum
      (n := n) (a := a) (cs := cs) i hchildRoot φ]
  rcases hreindex φ with ⟨e, hphase⟩
  unfold childOpenRootInternalExternalNodeFieldSum
  refine
    Fintype.sum_equiv e.symm
      (fun Ψ : ChildExternalNodeFieldFamily n a cs i =>
        bitSign
          (childInternalPhaseGivenRootDataAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            ((nodeChildDataAtStructuredEquivExternalNormalAssignments
              (n := n) (a := a) (cs := cs) i hchildRoot).symm
              (childExternalNormalAssignmentOfRootNodeField
                (n := n) (a := a) (cs := cs) i
                (φ +
                  Pi.single
                    (M := fun _ :
                      RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                    d (1 : F2)) Ψ))))
      (fun Ψ : ChildExternalNodeFieldFamily n a cs i =>
        bitSign
          (childInternalPhaseGivenRootDataAt
            (n := n) (a := a) cs
            (0 : RawNormal.NodeRootFieldAssignment n a cs) i
            ((nodeChildDataAtStructuredEquivExternalNormalAssignments
              (n := n) (a := a) (cs := cs) i hchildRoot).symm
              (childExternalNormalAssignmentOfRootNodeField
                (n := n) (a := a) (cs := cs) i φ Ψ))))
      ?_
  intro Ψ
  have h :
      childInternalPhaseGivenRootDataAt
          (n := n) (a := a) cs
          (0 : RawNormal.NodeRootFieldAssignment n a cs) i
          ((nodeChildDataAtStructuredEquivExternalNormalAssignments
            (n := n) (a := a) (cs := cs) i hchildRoot).symm
            (childExternalNormalAssignmentOfRootNodeField
              (n := n) (a := a) (cs := cs) i
              (φ +
                Pi.single
                  (M := fun _ :
                    RawNormal.NodeChildRootFieldDomain n a cs i => F2)
                  d (1 : F2)) Ψ)) =
        childInternalPhaseGivenRootDataAt
          (n := n) (a := a) cs
          (0 : RawNormal.NodeRootFieldAssignment n a cs) i
          ((nodeChildDataAtStructuredEquivExternalNormalAssignments
            (n := n) (a := a) (cs := cs) i hchildRoot).symm
            (childExternalNormalAssignmentOfRootNodeField
              (n := n) (a := a) (cs := cs) i φ (e.symm Ψ))) := by
    simpa using hphase (e.symm Ψ)
  exact congrArg bitSign h

theorem branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_externalReindexCore
    (hreindex : BranchVisibleSingletonExternalReindexNonLeafCoreRule) :
    BranchVisibleSingletonShiftInvariantNonLeafCoreRule := by
  intro a cs ha hchildren n _ hn i d hnonleaf hvisible
  exact
    internalKernelSingletonShiftInvariantAt_of_externalReindex
      (n := n) (a := a) (cs := cs) (i := i) (d := d)
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      (hreindex ha hchildren n hn i d hnonleaf hvisible)

theorem oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexLocal
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    OddFiberBranchSingleShiftInvariantCoreRule := by
  intro a cs _ha hchildren n _ _hn _R i _hodd d hvisible
  by_cases hleaf : ∃ b : Nat, childAt cs i = RTree.node b []
  · rcases hleaf with ⟨b, hchild⟩
    exact
      internalKernelSingletonShiftInvariantAt_of_leaf_child
        (n := n) (a := a) (b := b) (cs := cs) i hchild d
  · exact
      internalKernelSingletonShiftInvariantAt_of_externalReindex
        (n := n) (a := a) (cs := cs) (i := i) (d := d)
        (childAt_rootWeight_pos_of_openRootCert i
          (RawExpandedOpenRootSubtreeCert.childAt_of_children
            (cs := cs) hchildren i))
        (hlocal (n := n) (a := a) (cs := cs) i
          (childAt_rootWeight_pos_of_openRootCert i
            (RawExpandedOpenRootSubtreeCert.childAt_of_children
              (cs := cs) hchildren i))
          d (by
            intro b hchild
            exact hleaf ⟨b, hchild⟩)
          hvisible)

theorem oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexCore
    (hcore : BranchVisibleSingletonExternalReindexNonLeafCoreRule) :
    OddFiberBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn _R i _hodd d hvisible
  by_cases hleaf : ∃ b : Nat, childAt cs i = RTree.node b []
  · rcases hleaf with ⟨b, hchild⟩
    exact
      internalKernelSingletonShiftInvariantAt_of_leaf_child
        (n := n) (a := a) (b := b) (cs := cs) i hchild d
  · exact
      internalKernelSingletonShiftInvariantAt_of_externalReindex
        (n := n) (a := a) (cs := cs) (i := i) (d := d)
        (childAt_rootWeight_pos_of_openRootCert i
          (RawExpandedOpenRootSubtreeCert.childAt_of_children
            (cs := cs) hchildren i))
        (hcore ha hchildren n hn i d
          (by
            intro b hchild
            exact hleaf ⟨b, hchild⟩)
          hvisible)

theorem oddFiberBranchSingleShiftCore_of_nonLeafShiftInvariantCore
    (hcore : BranchVisibleSingletonShiftInvariantNonLeafCoreRule) :
    OddFiberBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn _R i _hodd d hvisible
  by_cases hleaf : ∃ b : Nat, childAt cs i = RTree.node b []
  · rcases hleaf with ⟨b, hchild⟩
    exact
      internalKernelSingletonShiftInvariantAt_of_leaf_child
        (n := n) (a := a) (b := b) (cs := cs) i hchild d
  · exact
      hcore ha hchildren n hn i d
        (by
          intro b hchild
          exact hleaf ⟨b, hchild⟩)
        hvisible

theorem oddFiberBranchSingleShiftCore_of_nonLeafShiftInvariantLocal
    (hlocal : BranchVisibleSingletonShiftInvariantNonLeafLocalRule) :
    OddFiberBranchSingleShiftInvariantCoreRule :=
  oddFiberBranchSingleShiftCore_of_nonLeafShiftInvariantCore
    (branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_local hlocal)

theorem oddFiberBranchSingleShiftCore_of_nonLeafSingleTogglePhase
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    OddFiberBranchSingleShiftInvariantCoreRule :=
  oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexLocal
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem evenHeavyVisibleWitnessCore_of_boundaryBranchSingleton_and_nonLeafExternalReindexLocal
    (hwitness : EvenHeavyBoundaryBranchSingletonCoreRule)
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    EvenHeavyVisibleWitnessCoreRule := by
  intro a cs ha hchildren n _ hn heven R i hweight hnonzero
  rcases hwitness ha hchildren n hn heven R i hweight hnonzero with
    ⟨d, hboundary, hbranch_if_nonleaf⟩
  refine ⟨d, hboundary, ?_⟩
  by_cases hleaf : ∃ b : Nat, childAt cs i = RTree.node b []
  · rcases hleaf with ⟨b, hchild⟩
    exact
      internalKernelSingletonShiftInvariantAt_of_leaf_child
        (n := n) (a := a) (b := b) (cs := cs) i hchild d
  · exact
      internalKernelSingletonShiftInvariantAt_of_externalReindex
        (n := n) (a := a) (cs := cs) (i := i) (d := d)
        (childAt_rootWeight_pos_of_openRootCert i
          (RawExpandedOpenRootSubtreeCert.childAt_of_children
            (cs := cs) hchildren i))
        (hlocal (n := n) (a := a) (cs := cs) i
          (childAt_rootWeight_pos_of_openRootCert i
            (RawExpandedOpenRootSubtreeCert.childAt_of_children
              (cs := cs) hchildren i))
          d
          (by
            intro b hchild
            exact hleaf ⟨b, hchild⟩)
          (hbranch_if_nonleaf (by
            intro b hchild
            exact hleaf ⟨b, hchild⟩)))

theorem evenHeavyVisibleWitnessCore_of_boundaryBranchSingleton_and_nonLeafSingleTogglePhase
    (hwitness : EvenHeavyBoundaryBranchSingletonCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    EvenHeavyVisibleWitnessCoreRule :=
  evenHeavyVisibleWitnessCore_of_boundaryBranchSingleton_and_nonLeafExternalReindexLocal
    hwitness
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem childOpenRootInternalKernelInvariantSubmoduleAt_top_of_singletons
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hsingle :
      ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
        InternalKernelSingletonShiftInvariantAt (n := n) (a := a) cs i d) :
    ChildOpenRootInternalKernelInvariantSubmoduleAt a cs n i ⊤ := by
  classical
  intro φ0 _hφ0 φ
  let D := RawNormal.NodeChildRootFieldDomain n a cs i
  let K : (D → F2) → ℤ :=
    fun ψ => childOpenRootInternalKernelAt (n := n) (a := a) cs i ψ
  have hsum :
      φ0 =
        ∑ d : D, φ0 d •
          Pi.single (M := fun _ : D => F2) d (1 : F2) :=
    function_eq_sum_single D φ0
  have hfinset :
      ∀ s : Finset D,
        K (φ +
          s.sum (fun d => φ0 d •
            Pi.single (M := fun _ : D => F2) d (1 : F2))) =
        K φ := by
    intro s
    refine Finset.induction_on s ?hbase ?hstep
    · simp [K]
    · intro d s hnot ih
      rw [Finset.sum_insert hnot]
      by_cases hd : φ0 d = 0
      · rw [hd, zero_smul, zero_add]
        exact ih
      · have hd_one : φ0 d = 1 := by
          generalize hx : φ0 d = x
          fin_cases x
          · exact False.elim (hd hx)
          · rfl
        rw [hd_one, one_smul]
        calc
          K (φ +
              (Pi.single (M := fun _ : D => F2) d (1 : F2) +
                s.sum (fun x => φ0 x •
                  Pi.single (M := fun _ : D => F2) x (1 : F2)))) =
              K ((φ +
                  s.sum (fun x => φ0 x •
                    Pi.single (M := fun _ : D => F2) x (1 : F2))) +
                Pi.single (M := fun _ : D => F2) d (1 : F2)) := by
                congr 1
                ac_rfl
          _ =
              K (φ +
                s.sum (fun x => φ0 x •
                  Pi.single (M := fun _ : D => F2) x (1 : F2))) := by
                exact hsingle d
                  (φ +
                    s.sum (fun x => φ0 x •
                      Pi.single (M := fun _ : D => F2) x (1 : F2)))
          _ = K φ := ih
  change K (φ + φ0) = K φ
  rw [hsum]
  exact hfinset Finset.univ

theorem childOpenRootInternalKernelInvariantSubmoduleAt_top_of_externalReindex
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight)
    (hreindex :
      ∀ d : RawNormal.NodeChildRootFieldDomain n a cs i,
        InternalKernelSingletonExternalReindexAt
          (n := n) (a := a) cs i hchildRoot d) :
    ChildOpenRootInternalKernelInvariantSubmoduleAt a cs n i ⊤ :=
  childOpenRootInternalKernelInvariantSubmoduleAt_top_of_singletons
    (a := a) (cs := cs) (n := n) i
    (fun d =>
      internalKernelSingletonShiftInvariantAt_of_externalReindex
        (n := n) (a := a) (cs := cs) (i := i) (d := d)
        hchildRoot (hreindex d))

theorem internalKernelDiagonalExternalReindexAt_proved
    {n a : Nat} [NeZero n] {cs : List RTree}
    (i : ChildIdx cs)
    (hchildRoot : 0 < (childAt cs i).rootWeight) :
    InternalKernelDiagonalExternalReindexAt
      (n := n) (a := a) cs i hchildRoot := by
  intro shift φ
  refine
    ⟨childExternalNodeFieldCoordinateShiftEquiv
      (n := n) (b := a) (ds := cs) i shift, ?_⟩
  intro Ψ
  dsimp [childExternalNodeFieldCoordinateShiftEquiv]
  rw [childExternalNormalAssignmentOfRootNodeField_diagonalShift]
  exact
    childInternalPhaseGivenRootDataAt_zero_externalCoordinateShift
      (n := n) (b := a) (ds := cs) i hchildRoot shift
      (childExternalNormalAssignmentOfRootNodeField
        (n := n) (a := a) (cs := cs) i φ Ψ)

theorem internalKernelTopInvariantCore_of_allSingletonShiftInvariantCore
    (hsingle : AllSingletonShiftInvariantCoreRule) :
    InternalKernelTopInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i
  exact
    childOpenRootInternalKernelInvariantSubmoduleAt_top_of_singletons
      (n := n) (a := a) (cs := cs) i
      (hsingle ha hchildren n hn i)

theorem allSingletonShiftInvariantCore_of_allSingletonExternalReindexCore
    (hreindex : AllSingletonExternalReindexCoreRule) :
    AllSingletonShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i d
  exact
    internalKernelSingletonShiftInvariantAt_of_externalReindex
      (n := n) (a := a) (cs := cs) (i := i) (d := d)
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      (hreindex ha hchildren n hn i d)

theorem internalKernelTopInvariantCore_of_allSingletonExternalReindexCore
    (hreindex : AllSingletonExternalReindexCoreRule) :
    InternalKernelTopInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i
  exact
    childOpenRootInternalKernelInvariantSubmoduleAt_top_of_externalReindex
      (n := n) (a := a) (cs := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      (fun d => hreindex ha hchildren n hn i d)

theorem oddFiberBranchSingleShiftCore_of_reindexCore
    (hreindex : OddFiberBranchSingleReindexCoreRule) :
    OddFiberBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn R i hodd d hvisible
  exact
    internalKernelSingletonShiftInvariantAt_of_reindex
      (n := n) (a := a) (cs := cs) (i := i) (d := d)
      (hreindex ha hchildren n hn R i hodd d hvisible)

theorem oddFiberBoundaryBranchSingleShiftCore_of_reindexCore
    (hreindex : OddFiberBoundaryBranchSingleReindexCoreRule) :
    OddFiberBoundaryBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn R i hodd d hboundary hvisible
  exact
    internalKernelSingletonShiftInvariantAt_of_reindex
      (n := n) (a := a) (cs := cs) (i := i) (d := d)
      (hreindex ha hchildren n hn R i hodd d hboundary hvisible)

theorem oddFiberBranchSingleShiftCore_of_externalReindexCore
    (hreindex : OddFiberBranchSingleExternalReindexCoreRule) :
    OddFiberBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn R i hodd d hvisible
  exact
    internalKernelSingletonShiftInvariantAt_of_externalReindex
      (n := n) (a := a) (cs := cs) (i := i) (d := d)
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      (hreindex ha hchildren n hn R i hodd d hvisible)

theorem oddFiberBoundaryBranchSingleShiftCore_of_externalReindexCore
    (hreindex : OddFiberBoundaryBranchSingleExternalReindexCoreRule) :
    OddFiberBoundaryBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn R i hodd d hboundary hvisible
  exact
    internalKernelSingletonShiftInvariantAt_of_externalReindex
      (n := n) (a := a) (cs := cs) (i := i) (d := d)
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      (hreindex ha hchildren n hn R i hodd d hboundary hvisible)

theorem fullRule_of_core (hcore : CoreRule) :
    ChildOpenRootFourierKernelBoundaryNonzeroBranchRule :=
  childOpenRootFourierKernelBoundaryNonzeroBranchRule_of_nontrivialRule hcore

theorem core_of_fullRule
    (hcore : ChildOpenRootFourierKernelBoundaryNonzeroBranchRule) :
    CoreRule :=
  childOpenRootFourierKernelBoundaryNonzeroBranchNontrivialRule_of_rule hcore

theorem core_iff_fullRule :
    CoreRule ↔ ChildOpenRootFourierKernelBoundaryNonzeroBranchRule :=
  ⟨fullRule_of_core, core_of_fullRule⟩

theorem witnessShiftCore_of_fullRule
    (hrule : ChildOpenRootFourierKernelBoundaryNonzeroWitnessShiftRule) :
    WitnessShiftCoreRule := by
  intro a cs ha hchildren n _ _hn R i
  exact hrule ha hchildren n R i

theorem visibleSingletonShiftInvariantCore_of_fullRule
    (hrule :
      ChildOpenRootFourierKernelBoundaryVisibleSingletonShiftInvariantRule) :
    VisibleSingletonShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ _hn R i
  exact hrule ha hchildren n R i

theorem visibleSingletonWitnessCore_of_fullRule
    (hrule :
      ChildOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftRule) :
    VisibleSingletonWitnessCoreRule := by
  intro a cs ha hchildren n _ _hn R i
  exact hrule ha hchildren n R i

theorem core_of_witnessShiftFull
    (hrule : ChildOpenRootFourierKernelBoundaryNonzeroWitnessShiftRule) :
    CoreRule := by
  intro a cs ha hchildren n _ _hn R i hnonzero
  exact
    childOpenRootFourierKernelBoundaryNonzeroBranchAt_of_witnessShift
      (a := a) (cs := cs) (n := n) R i
      (hrule ha hchildren n R i) hnonzero

theorem core_of_visibleSingletonShiftInvariantFull
    (hrule :
      ChildOpenRootFourierKernelBoundaryVisibleSingletonShiftInvariantRule) :
    CoreRule :=
  core_of_fullRule
    (childOpenRootFourierKernelBoundaryNonzeroBranchRule_of_visibleSingletonShiftInvariantRule
      hrule)

theorem core_of_visibleSingletonWitnessFull
    (hrule :
      ChildOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftRule) :
    CoreRule :=
  core_of_fullRule
    (childOpenRootFourierKernelBoundaryNonzeroBranchRule_of_visibleSingletonWitnessShiftRule
      hrule)

theorem adjacentCodimFullRule_of_core (hrange : AdjacentCodimCoreRule) :
    ChildBoundaryAdjacentSliceRangeCodimRule :=
  childBoundaryAdjacentSliceRangeCodimRule_of_nontrivialRule hrange

theorem not_adjacentCodimCoreRule :
    ¬ AdjacentCodimCoreRule :=
  not_childBoundaryAdjacentSliceRangeCodimNontrivialRule

theorem not_completeFormalization_of_core
    (hcore : CoreRule) :
    ¬ CompleteFormalization := by
  intro hcomplete
  exact
    not_adjacentCodimCoreRule
      ((completeFormalization_iff_adjacentSliceRangeCodimNontrivialRule_of_boundaryNonzeroBranch
        (fullRule_of_core hcore)).1 hcomplete)

theorem not_rawExpandedEdgeCompleteFormalization_of_core
    (hcore : CoreRule) :
    ¬ RawExpandedEdgeCompleteFormalization := by
  intro hcomplete
  exact
    not_adjacentCodimCoreRule
      ((rawExpandedEdgeCompleteFormalization_iff_adjacentSliceRangeCodimNontrivialRule_of_boundaryNonzeroBranch
        (fullRule_of_core hcore)).1 hcomplete)

theorem diagonalShiftInvariantCore_proved :
    DiagonalShiftInvariantCoreRule := by
  intro a cs _ha hchildren n _ _hn i shift φ
  exact
    childOpenRootInternalKernelAt_diagonalShift
      (n := n) (b := a) (ds := cs) i
      (childAt_rootWeight_pos_of_openRootCert i
        (RawExpandedOpenRootSubtreeCert.childAt_of_children
          (cs := cs) hchildren i))
      shift φ

theorem leafChildren_positive_of_children_cert
    {cs : List RTree}
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C)
    (hleaf : ∀ i : ChildIdx cs, ∃ b : Nat, childAt cs i = RTree.node b []) :
    ∀ i : ChildIdx cs,
      ∃ b : Nat, 0 < b ∧ childAt cs i = RTree.node b [] := by
  intro i
  rcases hleaf i with ⟨b, hchild⟩
  have hchildCert : RawExpandedOpenRootSubtreeCert (childAt cs i) :=
    RawExpandedOpenRootSubtreeCert.childAt_of_children
      (cs := cs) hchildren i
  have hleafCert : RawExpandedOpenRootSubtreeCert (RTree.node b []) := by
    simpa [hchild] using hchildCert
  exact ⟨b, RawExpandedOpenRootSubtreeCert.positiveRoot hleafCert, hchild⟩

theorem leafChildrenCore_proved :
    LeafChildrenCoreRule := by
  intro a cs ha hchildren hleaf n _ _hn R i hnonzero
  exact
    childOpenRootFourierKernelBoundaryNonzeroBranchAt_of_leaf_children
      (a := a) (cs := cs) (n := n) ha
      (leafChildren_positive_of_children_cert hchildren hleaf) R i hnonzero

theorem leafChildrenInternalKernelTopInvariantCore_proved :
    LeafChildrenInternalKernelTopInvariantCoreRule := by
  intro a cs _ha hchildren hleaf n _ _hn i
  exact
    childOpenRootInternalKernelInvariantSubmoduleAt_top_of_leaf_children
      (a := a) (cs := cs) (n := n)
      (leafChildren_positive_of_children_cert hchildren hleaf) i

theorem leafChildrenVisibleWitnessCore_proved :
    LeafChildrenVisibleWitnessCoreRule := by
  intro a cs _ha hchildren hleaf n _ _hn R i
  exact
    childOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt_of_leaf_children
      (a := a) (cs := cs) (n := n)
      (leafChildren_positive_of_children_cert hchildren hleaf) R i

theorem leafChildrenBranchSingleShiftInvariantCore_proved :
    LeafChildrenBranchSingleShiftInvariantCoreRule := by
  intro a cs _ha hchildren hleaf n _ _hn R i d hvisible
  exact
    childOpenRootFourierKernelBoundaryBranchSingleShiftInvariantAt_of_leaf_children
      (a := a) (cs := cs) (n := n)
      (leafChildren_positive_of_children_cert hchildren hleaf) R i d hvisible

theorem verifiedShapeCore_proved :
    VerifiedShapeCoreRule := by
  intro a cs hshape n _ _hn R i hnonzero
  exact
    childOpenRootFourierKernelBoundaryNonzeroBranchAt_of_verifiedShape_node
      (n := n) (a := a) (cs := cs) hshape R i hnonzero

theorem verifiedShapeInternalKernelTopInvariantCore_proved :
    VerifiedShapeInternalKernelTopInvariantCoreRule := by
  intro a cs hshape n _ _hn i
  exact
    childOpenRootInternalKernelInvariantSubmoduleAt_top_of_verifiedShape_node
      (n := n) (a := a) (cs := cs) hshape i

theorem verifiedShapeBranchSingleShiftInvariantCore_proved :
    VerifiedShapeBranchSingleShiftInvariantCoreRule := by
  intro a cs hshape n _ _hn R i d hvisible
  exact
    childOpenRootFourierKernelBoundaryBranchSingleShiftInvariantAt_of_verifiedShape_node
      (n := n) (a := a) (cs := cs) hshape R i d hvisible

theorem verifiedShapeVisibleWitnessCore_proved :
    VerifiedShapeVisibleWitnessCoreRule := by
  intro a cs hshape n _ _hn R i
  exact
    childOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt_of_verifiedShape_node
      (n := n) (a := a) (cs := cs) hshape R i

theorem verifiedShapeAdjacentCodimCore_proved :
    VerifiedShapeAdjacentCodimCoreRule := by
  intro a cs hshape n _ _hn
  exact
    childBoundaryAdjacentSliceRangeCodim_of_verifiedShape_node
      (n := n) (a := a) (cs := cs) hshape

theorem internalKernelTopInvariantCore_of_constantCore
    (hconstant : InternalKernelConstantCoreRule) :
    InternalKernelTopInvariantCoreRule := by
  intro a cs ha hchildren n _ hn i
  rcases hconstant ha hchildren n hn i with ⟨K, hK⟩
  exact
    childOpenRootInternalKernelInvariantSubmoduleAt_top_of_constant
      (a := a) (cs := cs) (n := n) i K hK

theorem invariantSupKerCore_of_internalKernelTopInvariantCore
    (htop : InternalKernelTopInvariantCoreRule) :
    InvariantSupKerCoreRule := by
  intro a cs ha hchildren n _ hn R i
  exact
    childOpenRootFourierKernelBoundaryInvariantSupKerAt_of_topInvariant
      (a := a) (cs := cs) (n := n) R i
      (htop ha hchildren n hn i)

theorem witnessShiftCore_of_invariantSupKerCore
    (hinvSupKer : InvariantSupKerCoreRule) :
    WitnessShiftCoreRule := by
  intro a cs ha hchildren n _ hn R i
  rcases hinvSupKer ha hchildren n hn R i with ⟨S, hinv, hsup⟩
  exact
    childOpenRootFourierKernelBoundaryWitnessShiftAt_of_invariantSupKer
      (a := a) (cs := cs) (n := n) R i S hinv hsup

theorem shiftInvariantCore_of_internalKernelTopInvariantCore
    (htop : InternalKernelTopInvariantCoreRule) :
    ShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn R i
  exact
    childOpenRootFourierKernelBoundaryShiftInvariantAt_of_internalKernelTopInvariantAt
      (a := a) (cs := cs) (n := n) R i
      (htop ha hchildren n hn i)

theorem visibleSingletonShiftInvariantCore_of_internalKernelTopInvariantCore
    (htop : InternalKernelTopInvariantCoreRule) :
    VisibleSingletonShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ hn R i
  exact
    childOpenRootFourierKernelBoundaryVisibleSingletonShiftInvariantAt_of_internalKernelTopInvariantAt
      (a := a) (cs := cs) (n := n) R i
      (htop ha hchildren n hn i)

theorem visibleSingletonWitnessCore_of_visibleSingletonShiftInvariantCore
    (hvisible : VisibleSingletonShiftInvariantCoreRule) :
    VisibleSingletonWitnessCoreRule := by
  intro a cs ha hchildren n _ hn R i
  exact
    childOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt_of_visibleSingletonShiftInvariant
      (a := a) (cs := cs) (n := n) R i
      (hvisible ha hchildren n hn R i)

theorem witnessShiftCore_of_visibleSingletonWitnessCore
    (hvisible : VisibleSingletonWitnessCoreRule) :
    WitnessShiftCoreRule := by
  intro a cs ha hchildren n _ hn R i
  exact
    childOpenRootFourierKernelBoundaryWitnessShiftAt_of_visibleSingletonWitnessShift
      (a := a) (cs := cs) (n := n) R i
      (hvisible ha hchildren n hn R i)

theorem oddModulusCore_of_oddFiberCore
    (hoddFiber : OddFiberCoreRule) :
    OddModulusCoreRule := by
  intro a cs ha hchildren n _ hn hodd R i hnonzero
  exact hoddFiber ha hchildren n hn R i hodd.pow hnonzero

theorem core_of_evenModulusCore_and_oddModulusCore
    (heven : EvenModulusCoreRule)
    (hodd : OddModulusCoreRule) :
    CoreRule := by
  intro a cs ha hchildren n _ hn R i hnonzero
  rcases Nat.even_or_odd n with hn_even | hn_odd
  · exact heven ha hchildren n hn hn_even R i hnonzero
  · exact hodd ha hchildren n hn hn_odd R i hnonzero

theorem core_of_evenFiberCore_and_oddFiberCore
    (hevenFiber : EvenFiberCoreRule)
    (hoddFiber : OddFiberCoreRule) :
    CoreRule := by
  intro a cs ha hchildren n _ hn R i hnonzero
  rcases Nat.even_or_odd
      (n ^
        (NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1)) with
    heven | hodd
  · exact hevenFiber ha hchildren n hn R i heven hnonzero
  · exact hoddFiber ha hchildren n hn R i hodd hnonzero

theorem evenFiberCore_of_evenModulusHeavyCore
    (hevenHeavy : EvenModulusHeavyCoreRule) :
    EvenFiberCoreRule := by
  intro a cs ha hchildren n _ hn R i hevenFiber hnonzero
  have hpow :
      Even n ∧
        (NonRootVertex.weight
            (RawNormal.childRootAtAsNonRootInNode (a := a) i) - 1) ≠ 0 := by
    simpa [Nat.even_pow] using hevenFiber
  have hweight_pos :
      0 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := a) i) :=
    childRootAtAsNonRootInNode_weight_pos_of_childCert
      (b := a) (ds := cs) hchildren i
  have hweight :
      1 < NonRootVertex.weight
        (RawNormal.childRootAtAsNonRootInNode (a := a) i) := by
    omega
  exact hevenHeavy ha hchildren n hn hpow.1 R i hweight hnonzero

theorem oddFiberCore_of_visibleWitnessCore
    (hoddWitness : OddFiberVisibleWitnessCoreRule) :
    OddFiberCoreRule := by
  intro a cs ha hchildren n _ hn R i hodd hnonzero
  exact
    childOpenRootFourierKernelBoundaryNonzeroBranchAt_of_witnessShift
      (a := a) (cs := cs) (n := n) R i
      (childOpenRootFourierKernelBoundaryWitnessShiftAt_of_visibleSingletonWitnessShift
        (a := a) (cs := cs) (n := n) R i
        (hoddWitness ha hchildren n hn R i hodd))
      hnonzero

theorem evenHeavyCore_of_visibleWitnessCore
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule) :
    EvenModulusHeavyCoreRule := by
  intro a cs ha hchildren n _ hn heven R i hweight hnonzero
  exact
    childOpenRootFourierKernelBoundaryNonzeroBranchAt_of_witnessShift
      (a := a) (cs := cs) (n := n) R i
      (childOpenRootFourierKernelBoundaryWitnessShiftAt_of_visibleSingletonWitnessShift
        (a := a) (cs := cs) (n := n) R i
        (hevenWitness ha hchildren n hn heven R i hweight))
      hnonzero

theorem visibleWitnessCore_of_evenHeavy_and_oddFiber
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddWitness : OddFiberVisibleWitnessCoreRule) :
    VisibleSingletonWitnessCoreRule := by
  intro a cs ha hchildren n _ hn R i
  by_cases heven : Even n
  · have hweight_pos :
        0 < NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i) :=
      childRootAtAsNonRootInNode_weight_pos_of_childCert
        (b := a) (ds := cs) hchildren i
    by_cases hweight :
        1 < NonRootVertex.weight
          (RawNormal.childRootAtAsNonRootInNode (a := a) i)
    · exact hevenWitness ha hchildren n hn heven R i hweight
    · have hweight_one :
          NonRootVertex.weight
              (RawNormal.childRootAtAsNonRootInNode (a := a) i) =
            1 := by
        omega
      exact
        hoddWitness ha hchildren n hn R i
          (by simp [hweight_one])
  · have hodd : Odd n := by
      exact Nat.not_even_iff_odd.mp heven
    exact hoddWitness ha hchildren n hn R i hodd.pow

theorem oddFiberVisibleWitnessCore_of_branchSingleShiftCore
    (hbranch : OddFiberBranchSingleShiftInvariantCoreRule) :
    OddFiberVisibleWitnessCoreRule := by
  intro a cs ha hchildren n _ hn R i hodd
  exact
    childOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt_of_branchSingleShiftInvariant_odd_fiberCard
      (n := n) (b := a) cs R i
      (childRootAtAsNonRootInNode_weight_pos_of_childCert
        (b := a) (ds := cs) hchildren i)
      hodd
      (hbranch ha hchildren n hn R i hodd)

theorem oddFiberVisibleWitnessCore_of_fullRule
    (hrule : ChildOpenRootFourierKernelBoundaryOddFiberVisibleSingletonWitnessShiftRule) :
    OddFiberVisibleWitnessCoreRule := by
  intro a cs ha hchildren n _ _hn R i hodd
  exact hrule (a := a) (cs := cs) ha hchildren n R i hodd

theorem evenHeavyVisibleWitnessCore_of_fullRule
    (hrule :
      ChildOpenRootFourierKernelBoundaryEvenModulusHeavyVisibleSingletonWitnessShiftRule) :
    EvenHeavyVisibleWitnessCoreRule := by
  intro a cs ha hchildren n _ _hn heven R i hweight
  exact hrule (a := a) (cs := cs) ha hchildren n heven R i hweight

theorem evenModulusHeavyCore_of_fullRule
    (hrule : ChildOpenRootFourierKernelBoundaryEvenModulusHeavyNonzeroBranchRule) :
    EvenModulusHeavyCoreRule := by
  intro a cs ha hchildren n _ _hn heven R i hweight hnonzero
  exact hrule (a := a) (cs := cs) ha hchildren n heven R i hweight hnonzero

theorem oddFiberVisibleWitnessCore_of_boundaryBranchSingleShiftCore
    (hbranch : OddFiberBoundaryBranchSingleShiftInvariantCoreRule) :
    OddFiberVisibleWitnessCoreRule := by
  intro a cs ha hchildren n _ hn R i hodd
  exact
    childOpenRootFourierKernelBoundaryVisibleSingletonWitnessShiftAt_of_boundaryBranchSingleShiftInvariant_odd_fiberCard
      (n := n) (b := a) cs R i
      (childRootAtAsNonRootInNode_weight_pos_of_childCert
        (b := a) (ds := cs) hchildren i)
      hodd
      (hbranch ha hchildren n hn R i hodd)

theorem oddFiberBranchSingleShiftCore_of_fullRule
    (hbranch :
      ChildOpenRootFourierKernelBoundaryOddFiberBranchSingleShiftInvariantRule) :
    OddFiberBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ _hn R i hodd d hvisible φ
  exact hbranch (a := a) (cs := cs) ha hchildren n R i hodd d hvisible φ

theorem oddFiberBoundaryBranchSingleShiftCore_of_fullRule
    (hbranch :
      ChildOpenRootFourierKernelBoundaryOddFiberBoundaryBranchSingleShiftInvariantRule) :
    OddFiberBoundaryBranchSingleShiftInvariantCoreRule := by
  intro a cs ha hchildren n _ _hn R i hodd d hboundary hvisible φ
  exact
    hbranch (a := a) (cs := cs) ha hchildren n R i hodd
      d hboundary hvisible φ

theorem core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddBranch : OddFiberBranchSingleShiftInvariantCoreRule) :
    CoreRule :=
  core_of_evenFiberCore_and_oddFiberCore
    (evenFiberCore_of_evenModulusHeavyCore
      (evenHeavyCore_of_visibleWitnessCore hevenWitness))
    (oddFiberCore_of_visibleWitnessCore
      (oddFiberVisibleWitnessCore_of_branchSingleShiftCore hoddBranch))

theorem core_of_branchInvisibleSingletonShiftInvariantLocal_and_oddFiberBranchSingleShiftCore
    (hinv : BranchInvisibleSingletonShiftInvariantLocalRule)
    (hoddBranch : OddFiberBranchSingleShiftInvariantCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    (evenHeavyVisibleWitnessCore_of_branchInvisibleSingletonShiftInvariantLocal
      hinv)
    hoddBranch

theorem core_of_branchInvisibleSingletonShiftInvariantLocal_and_nonLeafExternalReindexLocal
    (hinv : BranchInvisibleSingletonShiftInvariantLocalRule)
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    CoreRule :=
  core_of_branchInvisibleSingletonShiftInvariantLocal_and_oddFiberBranchSingleShiftCore
    hinv
    (oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexLocal hlocal)

theorem core_of_branchInvisibleSingletonShiftInvariantLocal_and_nonLeafShiftInvariantLocal
    (hinv : BranchInvisibleSingletonShiftInvariantLocalRule)
    (hlocal : BranchVisibleSingletonShiftInvariantNonLeafLocalRule) :
    CoreRule :=
  core_of_branchInvisibleSingletonShiftInvariantLocal_and_oddFiberBranchSingleShiftCore
    hinv
    (oddFiberBranchSingleShiftCore_of_nonLeafShiftInvariantLocal hlocal)

theorem core_of_branchConstraintKernelShiftInvariantLocal_and_nonLeafExternalReindexLocal
    (hkernel : BranchConstraintKernelShiftInvariantLocalRule)
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    CoreRule :=
  core_of_branchInvisibleSingletonShiftInvariantLocal_and_nonLeafExternalReindexLocal
    (branchInvisibleSingletonShiftInvariantLocalRule_of_branchConstraintKernelShiftInvariant
      hkernel)
    hlocal

theorem core_of_branchConstraintKernelShiftInvariantLocal_and_nonLeafShiftInvariantLocal
    (hkernel : BranchConstraintKernelShiftInvariantLocalRule)
    (hlocal : BranchVisibleSingletonShiftInvariantNonLeafLocalRule) :
    CoreRule :=
  core_of_branchInvisibleSingletonShiftInvariantLocal_and_nonLeafShiftInvariantLocal
    (branchInvisibleSingletonShiftInvariantLocalRule_of_branchConstraintKernelShiftInvariant
      hkernel)
    hlocal

theorem core_of_branchConstraintKernelShiftInvariantLocal_and_nonLeafSingleTogglePhase
    (hkernel : BranchConstraintKernelShiftInvariantLocalRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantLocal_and_nonLeafExternalReindexLocal
    hkernel
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem core_of_branchConstraintImageKernelDependsLocal_and_nonLeafExternalReindexLocal
    (hdepends : BranchConstraintImageKernelDependsLocalRule)
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantLocal_and_nonLeafExternalReindexLocal
    (branchConstraintKernelShiftInvariantLocalRule_of_imageKernelDepends
      hdepends)
    hlocal

theorem core_of_branchConstraintImageKernelDependsLocal_and_nonLeafShiftInvariantLocal
    (hdepends : BranchConstraintImageKernelDependsLocalRule)
    (hlocal : BranchVisibleSingletonShiftInvariantNonLeafLocalRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantLocal_and_nonLeafShiftInvariantLocal
    (branchConstraintKernelShiftInvariantLocalRule_of_imageKernelDepends
      hdepends)
    hlocal

theorem core_of_branchConstraintImageKernelDependsCore_and_nonLeafExternalReindexCore
    (hdepends : BranchConstraintImageKernelDependsCoreRule)
    (hreindex : BranchVisibleSingletonExternalReindexNonLeafCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    (evenHeavyVisibleWitnessCore_of_branchConstraintImageKernelDependsCore
      hdepends)
    (oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexCore
      hreindex)

theorem core_of_branchConstraintImageKernelDependsCore_and_nonLeafShiftInvariantCore
    (hdepends : BranchConstraintImageKernelDependsCoreRule)
    (hshift : BranchVisibleSingletonShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    (evenHeavyVisibleWitnessCore_of_branchConstraintImageKernelDependsCore
      hdepends)
    (oddFiberBranchSingleShiftCore_of_nonLeafShiftInvariantCore hshift)

theorem core_of_boundaryMapExponentDependsCore_and_nonLeafShiftInvariantCore
    (hexp : BranchConstraintImageBoundaryMapExponentDependsCoreRule)
    (hshift : BranchVisibleSingletonShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsCore_and_nonLeafShiftInvariantCore
    (branchConstraintImageKernelDependsCoreRule_of_boundaryMapExponent hexp)
    hshift

theorem core_of_boundaryLinearFormZeroCore_and_nonLeafShiftInvariantCore
    (hlinear : BranchConstraintKernelBoundaryLinearFormZeroCoreRule)
    (hshift : BranchVisibleSingletonShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsCore_and_nonLeafShiftInvariantCore
    (branchConstraintImageKernelDependsCoreRule_of_boundaryLinearFormZero
      hlinear)
    hshift

theorem core_of_branchConstraintImageFixedRootFactorDependsCore_and_nonLeafShiftInvariantCore
    (hfactor : BranchConstraintImageFixedRootFactorDependsCoreRule)
    (hshift : BranchVisibleSingletonShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsCore_and_nonLeafShiftInvariantCore
    (branchConstraintImageKernelDependsCoreRule_of_fixedRootFactorDependsCore
      hfactor)
    hshift

theorem core_of_fixedRootFactorRules
    (hdepends : BranchConstraintImageFixedRootFactorDependsCoreRule)
    (hvisible :
      BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageFixedRootFactorDependsCore_and_nonLeafShiftInvariantCore
    hdepends
    (branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_fixedRootFactor
      hvisible)

theorem core_of_nonLeafFixedRootFactorRules
    (hdepends :
      BranchConstraintImageFixedRootFactorDependsNonLeafCoreRule)
    (hvisible :
      BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_fixedRootFactorRules
    (branchConstraintImageFixedRootFactorDependsCoreRule_of_nonLeaf
      hdepends)
    hvisible

theorem core_of_boundaryMapDotZeroNonLeaf_and_nonLeafShiftInvariantCore
    (hdot :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule)
    (hshift : BranchVisibleSingletonShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsCore_and_nonLeafShiftInvariantCore
    (branchConstraintImageKernelDependsCoreRule_of_boundaryMapDotZeroNonLeaf
      hdot)
    hshift

theorem core_of_boundaryMapDotZeroNonLeaf_and_fixedRootFactorShiftInvariant
    (hdot :
      BranchConstraintKernelBoundaryMapDotZeroNonLeafCoreRule)
    (hvisible :
      BranchVisibleSingletonFixedRootFactorShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_boundaryMapDotZeroNonLeaf_and_nonLeafShiftInvariantCore
    hdot
    (branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_fixedRootFactor
      hvisible)

theorem core_of_branchConstraintImageKernelDependsCore_and_nonLeafBaseFixedRootShiftInvariantCore
    (hdepends : BranchConstraintImageKernelDependsCoreRule)
    (hbase :
      BranchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsCore_and_nonLeafShiftInvariantCore
    hdepends
    (branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_baseFixedRoot
      hbase)

theorem core_of_branchConstraintKernelShiftInvariantCore_and_nonLeafExternalReindexCore
    (hkernel : BranchConstraintKernelShiftInvariantCoreRule)
    (hreindex : BranchVisibleSingletonExternalReindexNonLeafCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    (evenHeavyVisibleWitnessCore_of_branchConstraintKernelShiftInvariantCore
      hkernel)
    (oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexCore
      hreindex)

theorem core_of_branchConstraintKernelShiftInvariantCore_and_nonLeafSingleTogglePhaseCore
    (hkernel : BranchConstraintKernelShiftInvariantCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantCore_and_nonLeafExternalReindexCore
    hkernel
    (branchVisibleSingletonExternalReindexNonLeafCoreRule_of_singleTogglePhaseCore
      hphaseRule)

theorem core_of_branchConstraintBaseBoundaryShiftZeroCore_and_nonLeafSingleTogglePhaseCore
    (hbaseZero : BranchConstraintBaseBoundaryShiftZeroCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantCore_and_nonLeafSingleTogglePhaseCore
    (branchConstraintKernelShiftInvariantCoreRule_of_baseBoundaryShiftZeroCore
      hbaseZero)
    hphaseRule

theorem core_of_branchConstraintKernelExternalReindexCore_and_nonLeafSingleTogglePhaseCore
    (hkernelReindex : BranchConstraintKernelExternalReindexCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantCore_and_nonLeafSingleTogglePhaseCore
    (branchConstraintKernelShiftInvariantCoreRule_of_externalReindexCore
      hkernelReindex)
    hphaseRule

theorem core_of_branchConstraintKernelExternalReindexCore_and_nonLeafExternalReindexLocal
    (hkernelReindex : BranchConstraintKernelExternalReindexCoreRule)
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantCore_and_nonLeafExternalReindexCore
    (branchConstraintKernelShiftInvariantCoreRule_of_externalReindexCore
      hkernelReindex)
    (branchVisibleSingletonExternalReindexNonLeafCoreRule_of_local hlocal)

theorem core_of_branchConstraintKernelExternalReindexCore_and_nonLeafSingleTogglePhase
    (hkernelReindex : BranchConstraintKernelExternalReindexCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    CoreRule :=
  core_of_branchConstraintKernelExternalReindexCore_and_nonLeafSingleTogglePhaseCore
    hkernelReindex
    (branchVisibleSingleTogglePhaseNonLeafCoreRule_of_local hphaseRule)

theorem core_of_branchConstraintBaseFixedRootShiftInvariantCore_and_nonLeafShiftInvariantCore
    (hbase : BranchConstraintBaseFixedRootShiftInvariantCoreRule)
    (hshift : BranchVisibleSingletonShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsCore_and_nonLeafShiftInvariantCore
    (branchConstraintImageKernelDependsCoreRule_of_baseFixedRootShiftInvariantCore
      hbase)
    hshift

theorem core_of_branchConstraintBaseFixedRootShiftInvariantCore_and_nonLeafShiftInvariantLocal
    (hbase : BranchConstraintBaseFixedRootShiftInvariantCoreRule)
    (hlocal : BranchVisibleSingletonShiftInvariantNonLeafLocalRule) :
    CoreRule :=
  core_of_branchConstraintBaseFixedRootShiftInvariantCore_and_nonLeafShiftInvariantCore
    hbase
    (branchVisibleSingletonShiftInvariantNonLeafCoreRule_of_local hlocal)

theorem core_of_branchConstraintBaseFixedRootShiftInvariantCore_and_nonLeafBaseFixedRootShiftInvariantCore
    (hbase : BranchConstraintBaseFixedRootShiftInvariantCoreRule)
    (hvisible :
      BranchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsCore_and_nonLeafBaseFixedRootShiftInvariantCore
    (branchConstraintImageKernelDependsCoreRule_of_baseFixedRootShiftInvariantCore
      hbase)
    hvisible

theorem core_of_branchConstraintImageKernelDependsCore_and_nonLeafSingleTogglePhaseCore
    (hdepends : BranchConstraintImageKernelDependsCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafCoreRule) :
    CoreRule :=
  core_of_branchConstraintKernelShiftInvariantCore_and_nonLeafSingleTogglePhaseCore
    (branchConstraintKernelShiftInvariantCoreRule_of_imageKernelDependsCore
      hdepends)
    hphaseRule

theorem core_of_branchInvisibleSingletonShiftInvariantLocal_and_nonLeafSingleTogglePhase
    (hinv : BranchInvisibleSingletonShiftInvariantLocalRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    CoreRule :=
  core_of_branchInvisibleSingletonShiftInvariantLocal_and_nonLeafExternalReindexLocal
    hinv
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem core_of_branchConstraintImageKernelDependsLocal_and_nonLeafSingleTogglePhase
    (hdepends : BranchConstraintImageKernelDependsLocalRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    CoreRule :=
  core_of_branchConstraintImageKernelDependsLocal_and_nonLeafExternalReindexLocal
    hdepends
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem core_of_evenHeavyVisibleWitness_and_oddFiberBoundaryBranchSingleShiftCore
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddBranch : OddFiberBoundaryBranchSingleShiftInvariantCoreRule) :
    CoreRule :=
  core_of_evenFiberCore_and_oddFiberCore
    (evenFiberCore_of_evenModulusHeavyCore
      (evenHeavyCore_of_visibleWitnessCore hevenWitness))
    (oddFiberCore_of_visibleWitnessCore
      (oddFiberVisibleWitnessCore_of_boundaryBranchSingleShiftCore hoddBranch))

theorem core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleReindexCore
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddReindex : OddFiberBranchSingleReindexCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    hevenWitness
    (oddFiberBranchSingleShiftCore_of_reindexCore hoddReindex)

theorem core_of_evenHeavyVisibleWitness_and_oddFiberBoundaryBranchSingleReindexCore
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddReindex : OddFiberBoundaryBranchSingleReindexCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBoundaryBranchSingleShiftCore
    hevenWitness
    (oddFiberBoundaryBranchSingleShiftCore_of_reindexCore hoddReindex)

theorem core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleExternalReindexCore
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddReindex : OddFiberBranchSingleExternalReindexCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    hevenWitness
    (oddFiberBranchSingleShiftCore_of_externalReindexCore hoddReindex)

theorem oddFiberVisibleWitnessCore_of_nonLeafExternalReindexLocal
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    OddFiberVisibleWitnessCoreRule :=
  oddFiberVisibleWitnessCore_of_branchSingleShiftCore
    (oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexLocal hlocal)

theorem oddFiberVisibleWitnessCore_of_nonLeafSingleTogglePhase
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    OddFiberVisibleWitnessCoreRule :=
  oddFiberVisibleWitnessCore_of_nonLeafExternalReindexLocal
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem core_of_evenHeavyVisibleWitness_and_nonLeafExternalReindexLocal
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBranchSingleShiftCore
    hevenWitness
    (oddFiberBranchSingleShiftCore_of_nonLeafExternalReindexLocal hlocal)

theorem core_of_evenHeavyVisibleWitness_and_nonLeafSingleTogglePhase
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_nonLeafExternalReindexLocal
    hevenWitness
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem core_of_evenHeavyBoundaryBranchSingleton_and_nonLeafExternalReindexLocal
    (hwitness : EvenHeavyBoundaryBranchSingletonCoreRule)
    (hlocal : BranchVisibleSingletonExternalReindexNonLeafLocalRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_nonLeafExternalReindexLocal
    (evenHeavyVisibleWitnessCore_of_boundaryBranchSingleton_and_nonLeafExternalReindexLocal
      hwitness hlocal)
    hlocal

theorem core_of_evenHeavyBoundaryBranchSingleton_and_nonLeafSingleTogglePhase
    (hwitness : EvenHeavyBoundaryBranchSingletonCoreRule)
    (hphaseRule : BranchVisibleSingleTogglePhaseNonLeafLocalRule) :
    CoreRule :=
  core_of_evenHeavyBoundaryBranchSingleton_and_nonLeafExternalReindexLocal
    hwitness
    (branchVisibleSingletonExternalReindexNonLeafLocalRule_of_singleTogglePhase
      hphaseRule)

theorem core_of_evenHeavyVisibleWitness_and_oddFiberBoundaryBranchSingleExternalReindexCore
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddReindex : OddFiberBoundaryBranchSingleExternalReindexCoreRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberBoundaryBranchSingleShiftCore
    hevenWitness
    (oddFiberBoundaryBranchSingleShiftCore_of_externalReindexCore hoddReindex)

theorem core_of_evenModulusHeavyCore_and_oddFiberCore
    (hevenHeavy : EvenModulusHeavyCoreRule)
    (hoddFiber : OddFiberCoreRule) :
    CoreRule :=
  core_of_evenFiberCore_and_oddFiberCore
    (evenFiberCore_of_evenModulusHeavyCore hevenHeavy)
    hoddFiber

theorem core_of_evenHeavyVisibleWitness_and_oddFiberVisibleWitness
    (hevenWitness : EvenHeavyVisibleWitnessCoreRule)
    (hoddWitness : OddFiberVisibleWitnessCoreRule) :
    CoreRule :=
  core_of_evenModulusHeavyCore_and_oddFiberCore
    (evenHeavyCore_of_visibleWitnessCore hevenWitness)
    (oddFiberCore_of_visibleWitnessCore hoddWitness)

theorem core_of_evenModulusHeavyFull_and_oddFiberVisibleWitnessFull
    (hevenHeavy : ChildOpenRootFourierKernelBoundaryEvenModulusHeavyNonzeroBranchRule)
    (hoddWitness :
      ChildOpenRootFourierKernelBoundaryOddFiberVisibleSingletonWitnessShiftRule) :
    CoreRule :=
  core_of_evenModulusHeavyCore_and_oddFiberCore
    (evenModulusHeavyCore_of_fullRule hevenHeavy)
    (oddFiberCore_of_visibleWitnessCore
      (oddFiberVisibleWitnessCore_of_fullRule hoddWitness))

theorem core_of_evenHeavyVisibleWitnessFull_and_oddFiberVisibleWitnessFull
    (hevenWitness :
      ChildOpenRootFourierKernelBoundaryEvenModulusHeavyVisibleSingletonWitnessShiftRule)
    (hoddWitness :
      ChildOpenRootFourierKernelBoundaryOddFiberVisibleSingletonWitnessShiftRule) :
    CoreRule :=
  core_of_evenHeavyVisibleWitness_and_oddFiberVisibleWitness
    (evenHeavyVisibleWitnessCore_of_fullRule hevenWitness)
    (oddFiberVisibleWitnessCore_of_fullRule hoddWitness)

theorem sum_bitSign_mul_eq_zero_of_equiv_add_one
    {V : Type} [Fintype V]
    (ℓ : V → F2) (K : V → ℤ) (e : V ≃ V)
    (hK : ∀ v, K (e v) = K v)
    (hflip : ∀ v, ℓ (e v) = ℓ v + 1) :
    (∑ v : V, bitSign (ℓ v) * K v) = 0 := by
  classical
  let S : ℤ := ∑ v : V, bitSign (ℓ v) * K v
  have htranslate :
      (∑ v : V, bitSign (ℓ (e v)) * K (e v)) = S := by
    simpa [S] using
      (Equiv.sum_comp e (fun v : V => bitSign (ℓ v) * K v))
  have hneg :
      (∑ v : V, bitSign (ℓ (e v)) * K (e v)) = -S := by
    calc
      (∑ v : V, bitSign (ℓ (e v)) * K (e v)) =
          ∑ v : V, (-bitSign (ℓ v)) * K v := by
            refine Finset.sum_congr rfl ?_
            intro v _
            have hsign :
                bitSign (ℓ (e v)) = -bitSign (ℓ v) := by
              simp [hflip v, bitSign_add, mul_comm]
            rw [hsign, hK v]
      _ = -S := by
            simp [S]
  have hS : S = -S := by
    calc
      S = (∑ v : V, bitSign (ℓ (e v)) * K (e v)) :=
        htranslate.symm
      _ = -S := hneg
  omega

theorem childOpenRootFourierKernelBoundary_sum_eq_zero_of_boundaryFlipEquiv
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : RawNormal.NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs)
    (e :
      (RawNormal.NodeChildRootFieldDomain n a cs i → F2) ≃
        (RawNormal.NodeChildRootFieldDomain n a cs i → F2))
    (hK :
      ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
        childOpenRootInternalKernelAt
            (n := n) (a := a) cs i (e φ) =
          childOpenRootInternalKernelAt
            (n := n) (a := a) cs i φ)
    (hflip :
      ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
        childBoundaryLinearFormAt (n := n) (a := a) cs R i
            (e φ) =
          childBoundaryLinearFormAt (n := n) (a := a) cs R i φ + 1) :
    (∑ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
      bitSign
        (childBoundaryLinearFormAt
          (n := n) (a := a) cs R i φ) *
        childOpenRootInternalKernelAt
          (n := n) (a := a) cs i φ) = 0 := by
  exact
    sum_bitSign_mul_eq_zero_of_equiv_add_one
      (fun φ =>
        childBoundaryLinearFormAt
          (n := n) (a := a) cs R i φ)
      (fun φ =>
        childOpenRootInternalKernelAt
          (n := n) (a := a) cs i φ)
      e hK hflip

theorem not_diagonalLinearFlipAt
    {n a : Nat} [NeZero n] {cs : List RTree}
    (R : RawNormal.NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs) :
    ¬ ∃ shift : ZMod n,
      ∀ φ : RawNormal.NodeChildRootFieldDomain n a cs i → F2,
        childBoundaryLinearFormAt (n := n) (a := a) cs R i
            (nodeChildRootFieldFunctionDiagonalShiftLinearEquiv
              (n := n) (b := a) cs i shift φ) =
          childBoundaryLinearFormAt
              (n := n) (a := a) cs R i φ +
            1 := by
  rintro ⟨shift, hflip⟩
  have hzero :=
    hflip (0 : RawNormal.NodeChildRootFieldDomain n a cs i → F2)
  simpa using hzero

theorem false_of_diagonalFlipCoreAt
    (hdiag : DiagonalFlipCoreRule)
    {a : Nat} {cs : List RTree}
    (ha : 0 < a)
    (hchildren : ∀ C ∈ cs, RawExpandedOpenRootSubtreeCert C)
    (n : Nat) [NeZero n]
    (hn : 1 < n)
    (R : RawNormal.NodeRootFieldAssignment n a cs)
    (i : ChildIdx cs)
    (hnonzero :
      childBoundaryLinearFormAt (n := n) (a := a) cs R i ≠ 0) :
    False :=
  not_diagonalLinearFlipAt (n := n) (a := a) R i
    (hdiag ha hchildren n hn R i hnonzero)

theorem boundaryFlipEquivCore_of_witnessShiftCore
    (hwitness : WitnessShiftCoreRule) :
    BoundaryFlipEquivCoreRule := by
  intro a cs ha hchildren n _ hn R i hnonzero
  rcases hwitness ha hchildren n hn R i hnonzero with
    ⟨φ0, hφ0, hshift⟩
  refine ⟨Equiv.addRight φ0, hshift, ?_⟩
  intro φ
  simp [LinearMap.map_add, hφ0]

theorem core_of_boundaryFlipEquivCore
    (hflipEquiv : BoundaryFlipEquivCoreRule) :
    CoreRule := by
  intro a cs ha hchildren n _ hn R i hnonzero
  rcases hflipEquiv ha hchildren n hn R i hnonzero with
    ⟨e, hK, hflip⟩
  exact
    childOpenRootFourierKernelBoundary_sum_eq_zero_of_boundaryFlipEquiv
      R i e hK hflip

theorem boundaryFlipEquivCore_of_diagonalFlipCore
    (hdiag : DiagonalFlipCoreRule) :
    BoundaryFlipEquivCoreRule := by
  intro a cs ha hchildren n _ hn R i hnonzero
  rcases hdiag ha hchildren n hn R i hnonzero with ⟨shift, hflip⟩
  refine
    ⟨(nodeChildRootFieldFunctionDiagonalShiftLinearEquiv
        (n := n) (b := a) cs i shift).toEquiv, ?_, hflip⟩
  exact diagonalShiftInvariantCore_proved ha hchildren n hn i shift

theorem core_of_diagonalFlipCore
    (hdiag : DiagonalFlipCoreRule) :
    CoreRule :=
  core_of_boundaryFlipEquivCore
    (boundaryFlipEquivCore_of_diagonalFlipCore hdiag)

theorem core_of_witnessShiftCore
    (hwitness : WitnessShiftCoreRule) :
    CoreRule :=
  core_of_boundaryFlipEquivCore
    (boundaryFlipEquivCore_of_witnessShiftCore hwitness)

theorem core_of_shiftInvariantCore
    (hshift : ShiftInvariantCoreRule) :
    CoreRule := by
  intro a cs ha hchildren n _ hn R i hnonzero
  exact
    childOpenRootFourierKernelBoundaryNonzeroBranchAt_of_shiftInvariant
      (a := a) (cs := cs) (n := n) R i
      (hshift ha hchildren n hn R i) hnonzero

theorem core_of_visibleSingletonShiftInvariantCore
    (hvisible : VisibleSingletonShiftInvariantCoreRule) :
    CoreRule := by
  intro a cs ha hchildren n _ hn R i hnonzero
  exact
    childOpenRootFourierKernelBoundaryNonzeroBranchAt_of_visibleSingletonShiftInvariant
      (a := a) (cs := cs) (n := n) R i
      (hvisible ha hchildren n hn R i) hnonzero

theorem core_of_visibleSingletonWitnessCore
    (hvisible : VisibleSingletonWitnessCoreRule) :
    CoreRule :=
  core_of_witnessShiftCore
    (witnessShiftCore_of_visibleSingletonWitnessCore hvisible)

theorem core_of_invariantSupKerCore
    (hinvSupKer : InvariantSupKerCoreRule) :
    CoreRule :=
  core_of_witnessShiftCore
    (witnessShiftCore_of_invariantSupKerCore hinvSupKer)

theorem core_of_internalKernelTopInvariantCore
    (htop : InternalKernelTopInvariantCoreRule) :
    CoreRule :=
  core_of_invariantSupKerCore
    (invariantSupKerCore_of_internalKernelTopInvariantCore htop)

theorem core_of_allSingletonExternalReindexCore
    (hreindex : AllSingletonExternalReindexCoreRule) :
    CoreRule :=
  core_of_internalKernelTopInvariantCore
    (internalKernelTopInvariantCore_of_allSingletonExternalReindexCore
      hreindex)

theorem core_of_allSingletonShiftInvariantCore
    (hsingle : AllSingletonShiftInvariantCoreRule) :
    CoreRule :=
  core_of_internalKernelTopInvariantCore
    (internalKernelTopInvariantCore_of_allSingletonShiftInvariantCore
      hsingle)

theorem core_of_baseFixedRootRules
    (hbase : BranchConstraintBaseFixedRootShiftInvariantCoreRule)
    (hvisibleBase :
      BranchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule) :
    CoreRule :=
  core_of_allSingletonShiftInvariantCore
    (allSingletonShiftInvariantCore_of_baseFixedRootRules
      hbase hvisibleBase)

theorem allSingletonShiftInvariantCore_of_rootSingletonShiftInvariantCore
    (hroot : FixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCoreRule) :
    AllSingletonShiftInvariantCoreRule :=
  allSingletonShiftInvariantCore_of_baseFixedRootRules
    (branchConstraintBaseFixedRootShiftInvariantCoreRule_of_rootSingleton hroot)
    (branchVisibleSingletonBaseFixedRootShiftInvariantNonLeafCoreRule_of_rootSingleton
      hroot)

theorem core_of_rootSingletonShiftInvariantCore
    (hroot : FixedRootCyclicNodeFieldSumRootSingletonShiftInvariantCoreRule) :
    CoreRule :=
  core_of_allSingletonShiftInvariantCore
    (allSingletonShiftInvariantCore_of_rootSingletonShiftInvariantCore hroot)

theorem core_of_internalKernelConstantCore
    (hconstant : InternalKernelConstantCoreRule) :
    CoreRule :=
  core_of_internalKernelTopInvariantCore
    (internalKernelTopInvariantCore_of_constantCore hconstant)

theorem core_of_fixedRootCyclicNodeFieldSumConstantCore
    (hfixed : FixedRootCyclicNodeFieldSumConstantCoreRule) :
    CoreRule :=
  core_of_internalKernelConstantCore
    (internalKernelConstantCore_of_fixedRootCyclicNodeFieldSumConstantCore
      hfixed)

theorem core_of_cyclicNodeFixedRootOneFiberCancellationCore
    (hcancel : CyclicNodeFixedRootOneFiberCancellationCoreRule) :
    CoreRule :=
  core_of_fixedRootCyclicNodeFieldSumConstantCore
    (fixedRootCyclicNodeFieldSumConstantCore_of_oneFiber hcancel)

theorem completeFormalization_of_allSingletonExternalReindexCore
    (hreindex : AllSingletonExternalReindexCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    CompleteFormalization :=
  completeFormalization_of_boundaryNonzeroBranchNontrivial_and_adjacentSliceRangeCodimNontrivial
    (core_of_allSingletonExternalReindexCore hreindex)
    hrange

theorem completeFormalization_of_allSingletonShiftInvariantCore
    (hsingle : AllSingletonShiftInvariantCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    CompleteFormalization :=
  completeFormalization_of_boundaryNonzeroBranchNontrivial_and_adjacentSliceRangeCodimNontrivial
    (core_of_allSingletonShiftInvariantCore hsingle)
    hrange

theorem completeFormalization_of_fixedRootCyclicNodeFieldSumConstantCore
    (hfixed : FixedRootCyclicNodeFieldSumConstantCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    CompleteFormalization :=
  completeFormalization_of_boundaryNonzeroBranchNontrivial_and_adjacentSliceRangeCodimNontrivial
    (core_of_fixedRootCyclicNodeFieldSumConstantCore hfixed)
    hrange

theorem completeFormalization_of_cyclicNodeFixedRootOneFiberCancellationCore
    (hcancel : CyclicNodeFixedRootOneFiberCancellationCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    CompleteFormalization :=
  completeFormalization_of_boundaryNonzeroBranchNontrivial_and_adjacentSliceRangeCodimNontrivial
    (core_of_cyclicNodeFixedRootOneFiberCancellationCore hcancel)
    hrange

theorem rawExpandedEdgeCompleteFormalization_of_allSingletonExternalReindexCore
    (hreindex : AllSingletonExternalReindexCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    RawExpandedEdgeCompleteFormalization :=
  rawExpandedEdgeCompleteFormalization_of_boundaryNonzeroBranch_and_adjacentSliceRangeCodim
    (fullRule_of_core
      (core_of_allSingletonExternalReindexCore hreindex))
    (adjacentCodimFullRule_of_core hrange)

theorem rawExpandedEdgeCompleteFormalization_of_allSingletonShiftInvariantCore
    (hsingle : AllSingletonShiftInvariantCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    RawExpandedEdgeCompleteFormalization :=
  rawExpandedEdgeCompleteFormalization_of_boundaryNonzeroBranch_and_adjacentSliceRangeCodim
    (fullRule_of_core
      (core_of_allSingletonShiftInvariantCore hsingle))
    (adjacentCodimFullRule_of_core hrange)

theorem rawExpandedEdgeCompleteFormalization_of_fixedRootCyclicNodeFieldSumConstantCore
    (hfixed : FixedRootCyclicNodeFieldSumConstantCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    RawExpandedEdgeCompleteFormalization :=
  rawExpandedEdgeCompleteFormalization_of_boundaryNonzeroBranch_and_adjacentSliceRangeCodim
    (fullRule_of_core
      (core_of_fixedRootCyclicNodeFieldSumConstantCore hfixed))
    (adjacentCodimFullRule_of_core hrange)

theorem rawExpandedEdgeCompleteFormalization_of_cyclicNodeFixedRootOneFiberCancellationCore
    (hcancel : CyclicNodeFixedRootOneFiberCancellationCoreRule)
    (hrange : AdjacentCodimCoreRule) :
    RawExpandedEdgeCompleteFormalization :=
  rawExpandedEdgeCompleteFormalization_of_boundaryNonzeroBranch_and_adjacentSliceRangeCodim
    (fullRule_of_core
      (core_of_cyclicNodeFixedRootOneFiberCancellationCore hcancel))
    (adjacentCodimFullRule_of_core hrange)

theorem completeFormalization_of_core
    (hcore : CoreRule)
    (hrange : AdjacentCodimCoreRule) :
    CompleteFormalization :=
  completeFormalization_of_boundaryNonzeroBranchNontrivial_and_adjacentSliceRangeCodimNontrivial
    hcore hrange

theorem rawExpandedEdgeCompleteFormalization_of_core
    (hcore : CoreRule)
    (hrange : AdjacentCodimCoreRule) :
    RawExpandedEdgeCompleteFormalization :=
  rawExpandedEdgeCompleteFormalization_of_boundaryNonzeroBranch_and_adjacentSliceRangeCodim
    (fullRule_of_core hcore)
    (adjacentCodimFullRule_of_core hrange)

end NonzeroBranch

end RawPrimitive

end TreeGraph
