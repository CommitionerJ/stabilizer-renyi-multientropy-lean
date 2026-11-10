import Core4loop.TriangleLeaf.VisibleClosed

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

local instance instDecidableEqPassiveVisibleIndexRaw
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    DecidableEq (PassiveVisibleIndex n d hd) :=
  Classical.decEq _

/-- Raw Core3 even visible sign, before the Core3 `c₂ ↦ c₂ + cH` reindexing. -/
def leafScalarEvenRawVisibleKernelSign {n b c : ℕ} [NeZero n]
    (H : LeafScalarVisibleKernel n b c)
    (c₂ : Core3loop.ScalarCCoef b n) (b₂ : Core3loop.ScalarBCoef c n) : ℤ :=
  let bc := leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c) H
  bitSign
    (Core3loop.qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef
      + Core3loop.qScalar (b := b) (c := c) (n := n) bc.bcoef c₂
      + Core3loop.qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)

/-- Raw even block sign on the same data type used by the shifted even sign. -/
def leafScalarEvenRawBlockSign {n b c : ℕ} [NeZero n]
    (X : LeafScalarEvenBlockData n b c) : ℤ :=
  leafScalarEvenRawVisibleKernelSign
    (n := n) (b := b) (c := c) X.1.1 X.1.2 X.2

/-- Core3 even-block reindexing: translate only the free `c₂` coordinate by `cH`. -/
noncomputable def leafScalarEvenBlockShiftEquiv
    {n b c : ℕ} [NeZero n] :
    LeafScalarEvenBlockData n b c ≃ LeafScalarEvenBlockData n b c where
  toFun X :=
    let bc := leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c) X.1.1
    ((X.1.1, X.1.2 + bc.ccoef), X.2)
  invFun X :=
    let bc := leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c) X.1.1
    ((X.1.1, X.1.2 + bc.ccoef), X.2)
  left_inv := by
    intro X
    rcases X with ⟨⟨H, c₂⟩, b₂⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext y r
        simp [add_assoc, F_add_self]
    · rfl
  right_inv := by
    intro X
    rcases X with ⟨⟨H, c₂⟩, b₂⟩
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext y r
        simp [add_assoc, F_add_self]
    · rfl

theorem leafScalarEvenRawBlockSign_eq_shifted
    {n b c : ℕ} [NeZero n]
    (X : LeafScalarEvenBlockData n b c) :
    leafScalarEvenRawBlockSign (n := n) (b := b) (c := c) X =
      leafScalarEvenBlockSign (n := n) (b := b) (c := c)
        (leafScalarEvenBlockShiftEquiv (n := n) (b := b) (c := c) X) := by
  rcases X with ⟨⟨H, c₂⟩, b₂⟩
  unfold leafScalarEvenRawBlockSign leafScalarEvenRawVisibleKernelSign
    leafScalarEvenBlockSign leafScalarEvenVisibleKernelSign
    leafScalarEvenBlockShiftEquiv
  dsimp
  rw [Core3loop.qScalar_add_right]
  congr 1
  ac_rfl

theorem sum_leafScalarEvenRawBlockSign_eq_sum_leafScalarEvenBlockSign
    {n b c : ℕ} [NeZero n] :
    (∑ X : LeafScalarEvenBlockData n b c,
      leafScalarEvenRawBlockSign (n := n) (b := b) (c := c) X)
      =
    ∑ X : LeafScalarEvenBlockData n b c,
      leafScalarEvenBlockSign (n := n) (b := b) (c := c) X := by
  classical
  calc
    (∑ X : LeafScalarEvenBlockData n b c,
      leafScalarEvenRawBlockSign (n := n) (b := b) (c := c) X)
        =
      ∑ X : LeafScalarEvenBlockData n b c,
        leafScalarEvenBlockSign (n := n) (b := b) (c := c)
          (leafScalarEvenBlockShiftEquiv (n := n) (b := b) (c := c) X) := by
        refine Finset.sum_congr rfl ?_
        intro X _
        exact leafScalarEvenRawBlockSign_eq_shifted
          (n := n) (b := b) (c := c) X
    _ =
      ∑ X : LeafScalarEvenBlockData n b c,
        leafScalarEvenBlockSign (n := n) (b := b) (c := c) X := by
        exact Equiv.sum_comp
          (leafScalarEvenBlockShiftEquiv (n := n) (b := b) (c := c))
          (fun X : LeafScalarEvenBlockData n b c =>
            leafScalarEvenBlockSign (n := n) (b := b) (c := c) X)

def leafEvenRawBlockProductSign {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c) : ℤ :=
  ∏ ω : PassiveVisibleIndex n d hd,
    leafScalarEvenRawBlockSign (n := n) (b := b) (c := c) (X ω)

theorem sum_leafEvenRawBlockProductSign_eq_sum_leafEvenBlockProductSign
    {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
      =
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X := by
  classical
  calc
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
        =
      (∑ X : LeafScalarEvenBlockData n b c,
        leafScalarEvenRawBlockSign (n := n) (b := b) (c := c) X)
        ^ Fintype.card (PassiveVisibleIndex n d hd) := by
        exact sum_pi_univ_prod_const
          (ι := PassiveVisibleIndex n d hd)
          (α := LeafScalarEvenBlockData n b c)
          (fun X => leafScalarEvenRawBlockSign (n := n) (b := b) (c := c) X)
    _ =
      (∑ X : LeafScalarEvenBlockData n b c,
        leafScalarEvenBlockSign (n := n) (b := b) (c := c) X)
        ^ Fintype.card (PassiveVisibleIndex n d hd) := by
        rw [sum_leafScalarEvenRawBlockSign_eq_sum_leafScalarEvenBlockSign]
    _ =
      ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
        leafEvenBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X := by
        symm
        exact sum_pi_univ_prod_const
          (ι := PassiveVisibleIndex n d hd)
          (α := LeafScalarEvenBlockData n b c)
          (fun X => leafScalarEvenBlockSign (n := n) (b := b) (c := c) X)

theorem sum_leafEvenRawBlockProductSign_eq_closed_form_all_ge_two
    {n b c d : ℕ} [NeZero n]
    (hd : 0 < d) (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X
      =
      (2 : ℤ) ^
        ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3)
          * (n ^ d - (n - 1))) := by
  rw [sum_leafEvenRawBlockProductSign_eq_sum_leafEvenBlockProductSign
    (n := n) (b := b) (c := c) (d := d) hd]
  exact sum_leafEvenBlockProductSign_eq_closed_form_all_ge_two
    (n := n) (b := b) (c := c) (d := d) hd hn hb2 hc2

theorem sum_leafEvenRawBlockProductSign_eq_closed_form_min_eq_one
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Even n)
    (hdeg : b = 1 ∨ c = 1) :
    ∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X
      =
      (2 : ℤ) ^
        ((n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1)
          * (n ^ d - (n - 1))) := by
  rw [sum_leafEvenRawBlockProductSign_eq_sum_leafEvenBlockProductSign
    (n := n) (b := b) (c := c) (d := d) hd]
  exact sum_leafEvenBlockProductSign_eq_closed_form_min_eq_one
    (n := n) (b := b) (c := c) (d := d) hb hc hd hn hdeg

theorem triangleLeaf_raw_even_block_sum_closed_all_ge_two
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
      =
      (2 : ℤ) ^
        Int.toNat
          (PassiveVisibleDimZ d n *
            (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
  rw [sum_leafEvenRawBlockProductSign_eq_sum_leafEvenBlockProductSign
    (n := n) (b := b) (c := c) (d := d) hd]
  exact triangleLeaf_even_block_sum_closed_all_ge_two
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd hn hb2 hc2

theorem triangleLeaf_raw_even_block_sum_closed_min_eq_one
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Even n)
    (hdeg : b = 1 ∨ c = 1) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
      =
      (2 : ℤ) ^
        Int.toNat
          (PassiveVisibleDimZ d n *
            (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
  rw [sum_leafEvenRawBlockProductSign_eq_sum_leafEvenBlockProductSign
    (n := n) (b := b) (c := c) (d := d) hd]
  exact triangleLeaf_even_block_sum_closed_min_eq_one
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd hn hdeg

theorem triangleLeaf_raw_even_block_sum_closed_generic
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hn : Even n)
    (hgeneric : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c)) :
    (∑ X : PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c,
      leafEvenRawBlockProductSign (n := n) (b := b) (c := c) (d := d) hd X)
      =
      (2 : ℤ) ^
        Int.toNat
          (PassiveVisibleDimZ d n *
            (LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n)) := by
  rw [sum_leafEvenRawBlockProductSign_eq_sum_leafEvenBlockProductSign
    (n := n) (b := b) (c := c) (d := d) hd]
  exact triangleLeaf_even_block_sum_closed_generic
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd hn hgeneric

end

end TriangleLeaf
end Core4loop
