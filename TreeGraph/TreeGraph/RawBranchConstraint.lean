import TreeGraph.BranchConstraint

namespace TreeGraph

namespace RawPrimitive

open RawLinearAlgebra

noncomputable def contextFiberSumBranchProjection
    (C : Type) (a n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    (C → (Fin a → ZMod n) → M) →ₗ[F2] (ZMod n → C → M) where
  toFun f := fun t c => fiberSum a n M (f c) t
  map_add' f g := by
    ext t c
    simp [fiberSum_apply, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r f := by
    ext t c
    simp [fiberSum_apply, Pi.smul_apply, Finset.smul_sum]

theorem contextFiberSumBranchProjection_surjective
    (C : Type) {a n : Nat} [NeZero n] (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] :
    Function.Surjective (contextFiberSumBranchProjection C a n M) := by
  intro g
  refine ⟨fun c => fiberSumSection ha (fun t => g t c), ?_⟩
  ext t c
  change fiberSum a n M (fiberSumSection ha (fun t => g t c)) t = g t c
  exact fiberSum_section_apply ha (fun t => g t c) t

noncomputable def contextBranchConstraintMap
    (C : Type) (a n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] :
    (C → (Fin a → ZMod n) → M) →ₗ[F2] (ZMod n → C → M) :=
  branchConstraintMap (C → (Fin a → ZMod n) → M) (C → M)
    (contextFiberSumBranchProjection C a n M)

@[simp] theorem contextBranchConstraintMap_apply
    (C : Type) (a n : Nat) [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M]
    (f : C → (Fin a → ZMod n) → M) (t : ZMod n) (c : C) :
    contextBranchConstraintMap C a n M f t c =
      paramCyclicDiff C n M (paramFiberSum C a n M f) c t := by
  rfl

theorem branchMessageCompatible_context_iff
    (C : Type) {n : Nat} [NeZero n] (M : Type)
    [AddCommGroup M] [Module F2 M] (g : ZMod n → C → M) :
    BranchMessageCompatible (C → M) g ↔
      ∀ c : C, totalSumLinear n M (fun t => g t c) = 0 := by
  constructor
  · intro hg c
    have hc := congrArg (fun q : C → M => q c) hg
    simpa [BranchMessageCompatible, totalSumLinear_apply, Finset.sum_apply]
      using hc
  · intro hg
    ext c
    simpa [BranchMessageCompatible, totalSumLinear_apply, Finset.sum_apply]
      using hg c

theorem contextBranchConstraintFiber_nonempty_iff_pointwise_compatible
    (C : Type) {a n : Nat} [NeZero n] (ha : 0 < a) (M : Type)
    [AddCommGroup M] [Module F2 M] (g : ZMod n → C → M) :
    Nonempty
        { f : C → (Fin a → ZMod n) → M //
          contextBranchConstraintMap C a n M f = g } ↔
      ∀ c : C, totalSumLinear n M (fun t => g t c) = 0 := by
  have h :=
    branchConstraintFiber_nonempty_iff_compatible
      (π := contextFiberSumBranchProjection C a n M)
      (contextFiberSumBranchProjection_surjective C ha M) g
  have h' :
      Nonempty
          { f : C → (Fin a → ZMod n) → M //
            contextBranchConstraintMap C a n M f = g } ↔
        BranchMessageCompatible (C → M) g := by
    simpa [contextBranchConstraintMap] using h
  exact h'.trans (branchMessageCompatible_context_iff C M g)

theorem card_contextBranchConstraintFiber_eq_branchConstraintExponent
    (C : Type) [Fintype C] {a n : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → C → M) (hg : BranchMessageCompatible (C → M) g) :
    Nat.card
        { f : C → (Fin a → ZMod n) → M //
          contextBranchConstraintMap C a n M f = g } =
      2 ^ branchConstraintExponent n
        (Fintype.card C * (n ^ a * Module.finrank F2 M))
        (Fintype.card C * Module.finrank F2 M) := by
  simpa [contextBranchConstraintMap] using
    (card_branchConstraintFiber_eq_branchConstraintExponent
      (n := n)
      (N := Fintype.card C * (n ^ a * Module.finrank F2 M))
      (Y := Fintype.card C * Module.finrank F2 M)
      (P := C → (Fin a → ZMod n) → M)
      (M := C → M)
      (π := contextFiberSumBranchProjection C a n M)
      (hπ := contextFiberSumBranchProjection_surjective C ha M)
      (g := g)
      (hg := hg)
      (hP := by
        simpa using
          finrank_paramTupleFunctionSpace C (a := a) (n := n) M)
      (hM := by
        simpa using finrank_paramFunctionSpace C M))

theorem card_contextBranchConstraintFiber_of_pointwise_compatible
    (C : Type) [Fintype C] {a n : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → C → M)
    (hg : ∀ c : C, totalSumLinear n M (fun t => g t c) = 0) :
    Nat.card
        { f : C → (Fin a → ZMod n) → M //
          contextBranchConstraintMap C a n M f = g } =
      2 ^ branchConstraintExponent n
        (Fintype.card C * (n ^ a * Module.finrank F2 M))
        (Fintype.card C * Module.finrank F2 M) := by
  exact card_contextBranchConstraintFiber_eq_branchConstraintExponent
    C ha M g ((branchMessageCompatible_context_iff C M g).2 hg)

private theorem contextBranchConstraintExponent_le
    (C : Type) [Fintype C] {a n : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M] :
    (n - 1) * (Fintype.card C * Module.finrank F2 M) ≤
      Fintype.card C * (n ^ a * Module.finrank F2 M) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hpow : n ≤ n ^ a := by
    simpa using le_self_pow hn (Nat.ne_of_gt ha)
  have hroot : n - 1 ≤ n ^ a :=
    le_trans (Nat.sub_le n 1) hpow
  have hmul :=
    Nat.mul_le_mul_left (Fintype.card C * Module.finrank F2 M) hroot
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

theorem card_contextBranchConstraintFiber_eq_two_pow_int
    (C : Type) [Fintype C] {a n : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → C → M) (hg : BranchMessageCompatible (C → M) g) :
    Nat.card
        { f : C → (Fin a → ZMod n) → M //
          contextBranchConstraintMap C a n M f = g } =
      2 ^ Int.toNat
        (((Fintype.card C * (n ^ a * Module.finrank F2 M) : Nat) : ℤ) -
          (tZ n) *
            ((Fintype.card C * Module.finrank F2 M : Nat) : ℤ)) := by
  have hle :=
    contextBranchConstraintExponent_le C (a := a) (n := n) ha M
  calc
    Nat.card
        { f : C → (Fin a → ZMod n) → M //
          contextBranchConstraintMap C a n M f = g } =
      2 ^ branchConstraintExponent n
        (Fintype.card C * (n ^ a * Module.finrank F2 M))
        (Fintype.card C * Module.finrank F2 M) := by
        exact card_contextBranchConstraintFiber_eq_branchConstraintExponent
          C ha M g hg
    _ =
      2 ^ Int.toNat
        (((Fintype.card C * (n ^ a * Module.finrank F2 M) : Nat) : ℤ) -
          (tZ n) *
            ((Fintype.card C * Module.finrank F2 M : Nat) : ℤ)) := by
        rw [← branchConstraintExponent_toNat
          (n := n)
          (N := Fintype.card C * (n ^ a * Module.finrank F2 M))
          (Y := Fintype.card C * Module.finrank F2 M)
          hle]

theorem card_contextBranchConstraintFiber_eq_two_pow_int_of_pointwise_compatible
    (C : Type) [Fintype C] {a n : Nat} [NeZero n] (ha : 0 < a)
    (M : Type) [AddCommGroup M] [Module F2 M] [FiniteDimensional F2 M]
    (g : ZMod n → C → M)
    (hg : ∀ c : C, totalSumLinear n M (fun t => g t c) = 0) :
    Nat.card
        { f : C → (Fin a → ZMod n) → M //
          contextBranchConstraintMap C a n M f = g } =
      2 ^ Int.toNat
        (((Fintype.card C * (n ^ a * Module.finrank F2 M) : Nat) : ℤ) -
          (tZ n) *
            ((Fintype.card C * Module.finrank F2 M : Nat) : ℤ)) := by
  exact card_contextBranchConstraintFiber_eq_two_pow_int C ha M g
    ((branchMessageCompatible_context_iff C M g).2 hg)

noncomputable def nonRootBranchConstraintMap
    {n : Nat} [NeZero n] (T : RTree) (v : NonRootVertex T) :
    (NonRootContext n T v →
        (Fin (NonRootVertex.weight v) → ZMod n) → F2) →ₗ[F2]
      (ZMod n → NonRootContext n T v → F2) :=
  contextBranchConstraintMap (NonRootContext n T v)
    (NonRootVertex.weight v) n F2

@[simp] theorem nonRootBranchConstraintMap_apply
    {n : Nat} [NeZero n] (T : RTree) (v : NonRootVertex T)
    (f : NonRootContext n T v →
        (Fin (NonRootVertex.weight v) → ZMod n) → F2)
    (t : ZMod n) (c : NonRootContext n T v) :
    nonRootBranchConstraintMap T v f t c =
      paramCyclicDiff (NonRootContext n T v) n F2
        (paramFiberSum (NonRootContext n T v)
          (NonRootVertex.weight v) n F2 f) c t := by
  rfl

theorem nonRootBranchConstraintFiber_nonempty_iff_pointwise_compatible
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v)
    (g : ZMod n → NonRootContext n T v → F2) :
    Nonempty
        { f : NonRootContext n T v →
            (Fin (NonRootVertex.weight v) → ZMod n) → F2 //
          nonRootBranchConstraintMap T v f = g } ↔
      ∀ c : NonRootContext n T v,
        totalSumLinear n F2 (fun t => g t c) = 0 := by
  simpa [nonRootBranchConstraintMap] using
    contextBranchConstraintFiber_nonempty_iff_pointwise_compatible
      (NonRootContext n T v) hvpos F2 g

theorem card_nonRootBranchConstraintFiber_weight_closed
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v)
    (g : ZMod n → NonRootContext n T v → F2)
    (hg :
      ∀ c : NonRootContext n T v,
        totalSumLinear n F2 (fun t => g t c) = 0) :
    Nat.card
        { f : NonRootContext n T v →
            (Fin (NonRootVertex.weight v) → ZMod n) → F2 //
          nonRootBranchConstraintMap T v f = g } =
      2 ^ branchConstraintExponent n
        (n ^ (nonRootContextExponent T v + NonRootVertex.weight v))
        (n ^ nonRootContextExponent T v) := by
  have h :=
    card_contextBranchConstraintFiber_of_pointwise_compatible
      (NonRootContext n T v)
      (a := NonRootVertex.weight v) (n := n) hvpos F2 g hg
  rw [card_nonRootContext] at h
  simpa [nonRootBranchConstraintMap, F2, Nat.pow_add, Nat.mul_assoc]
    using h

theorem card_nonRootBranchConstraintFiber_weight_closed_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (v : NonRootVertex T)
    (g : ZMod n → NonRootContext n T v → F2)
    (hg :
      ∀ c : NonRootContext n T v,
        totalSumLinear n F2 (fun t => g t c) = 0) :
    Nat.card
        { f : NonRootContext n T v →
            (Fin (NonRootVertex.weight v) → ZMod n) → F2 //
          nonRootBranchConstraintMap T v f = g } =
      2 ^ branchConstraintExponent n
        (n ^ (nonRootContextExponent T v + NonRootVertex.weight v))
        (n ^ nonRootContextExponent T v) := by
  exact card_nonRootBranchConstraintFiber_weight_closed v
    (by
      simpa [NonRootVertex.weight, Vertex.weight] using
        (RTree.weightAt_positive_of_mem_addresses hT v.1.2))
    g hg

private theorem nonRootBranchConstraintExponent_le
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    (n - 1) * n ^ nonRootContextExponent T v ≤
      n ^ (nonRootContextExponent T v + NonRootVertex.weight v) := by
  have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_neZero n)
  have hpow : n ≤ n ^ NonRootVertex.weight v := by
    simpa using le_self_pow hn (Nat.ne_of_gt hvpos)
  have hroot : n - 1 ≤ n ^ NonRootVertex.weight v :=
    le_trans (Nat.sub_le n 1) hpow
  have hmul := Nat.mul_le_mul_right (n ^ nonRootContextExponent T v) hroot
  simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

private theorem nonRootBranchConstraintExponent_toNat_closed
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v) :
    Int.toNat
        ((nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v) =
      branchConstraintExponent n
        (n ^ (nonRootContextExponent T v + NonRootVertex.weight v))
        (n ^ nonRootContextExponent T v) := by
  have hle := nonRootBranchConstraintExponent_le (n := n) v hvpos
  simpa [nZ, Nat.cast_pow] using
    (branchConstraintExponent_toNat_pow
      (n := n)
      (A := nonRootContextExponent T v + NonRootVertex.weight v)
      (Y := n ^ nonRootContextExponent T v)
      hle)

theorem card_nonRootBranchConstraintFiber_eq_two_pow_contextClosed
    {n : Nat} [NeZero n] {T : RTree} (v : NonRootVertex T)
    (hvpos : 0 < NonRootVertex.weight v)
    (g : ZMod n → NonRootContext n T v → F2)
    (hg :
      ∀ c : NonRootContext n T v,
        totalSumLinear n F2 (fun t => g t c) = 0) :
    Nat.card
        { f : NonRootContext n T v →
            (Fin (NonRootVertex.weight v) → ZMod n) → F2 //
          nonRootBranchConstraintMap T v f = g } =
      2 ^ Int.toNat
        ((nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v) := by
  calc
    Nat.card
        { f : NonRootContext n T v →
            (Fin (NonRootVertex.weight v) → ZMod n) → F2 //
          nonRootBranchConstraintMap T v f = g } =
      2 ^ branchConstraintExponent n
        (n ^ (nonRootContextExponent T v + NonRootVertex.weight v))
        (n ^ nonRootContextExponent T v) := by
        exact card_nonRootBranchConstraintFiber_weight_closed v hvpos g hg
    _ =
      2 ^ Int.toNat
        ((nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v) := by
        rw [← nonRootBranchConstraintExponent_toNat_closed (n := n) v hvpos]

theorem card_nonRootBranchConstraintFiber_eq_two_pow_contextClosed_of_positiveWeights
    {n : Nat} [NeZero n] {T : RTree} (hT : RTree.PositiveWeights T)
    (v : NonRootVertex T)
    (g : ZMod n → NonRootContext n T v → F2)
    (hg :
      ∀ c : NonRootContext n T v,
        totalSumLinear n F2 (fun t => g t c) = 0) :
    Nat.card
        { f : NonRootContext n T v →
            (Fin (NonRootVertex.weight v) → ZMod n) → F2 //
          nonRootBranchConstraintMap T v f = g } =
      2 ^ Int.toNat
        ((nZ n) ^ (nonRootContextExponent T v + NonRootVertex.weight v) -
          (tZ n) * (nZ n) ^ nonRootContextExponent T v) := by
  exact card_nonRootBranchConstraintFiber_eq_two_pow_contextClosed v
    (by
      simpa [NonRootVertex.weight, Vertex.weight] using
        (RTree.weightAt_positive_of_mem_addresses hT v.1.2))
    g hg

end RawPrimitive

end TreeGraph
