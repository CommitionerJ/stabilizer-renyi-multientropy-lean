import Core4loop.TriangleLeaf.PassiveProfile

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

abbrev LeafVisibleCompat (n b c d : ℕ) [NeZero n] :=
  YVec n b → ZVec n c → PassiveQuot n d

noncomputable def leafBProfile {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (sy : I n) (z : ZVec n c) :
    LeafProfile n a d :=
  fun p w => B p sy z w

noncomputable def leafCProfile {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (y : YVec n b) (sz : I n) :
    LeafProfile n a d :=
  fun p w => C p y sz w

noncomputable def leafBVisQuot {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (sy : I n) (z : ZVec n c) :
    PassiveQuot n d :=
  leafSigmaQuot (n := n) (a := a) (d := d) (leafBProfile B sy z)

noncomputable def leafCVisQuot {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (y : YVec n b) (sz : I n) :
    PassiveQuot n d :=
  leafSigmaQuot (n := n) (a := a) (d := d) (leafCProfile C y sz)

noncomputable def leafRootRaw {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d)
    (y : YVec n b) (z : ZVec n c) :
    PassiveRaw n d :=
  fun w =>
    (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
      + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) y z w

noncomputable def leafRootQuot {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d)
    (y : YVec n b) (z : ZVec n c) :
    PassiveQuot n d :=
  leafBVisQuot B (vecSum y) z
    + leafBVisQuot B (vecSum y + 1) z
    + leafCVisQuot C y (vecSum z)
    + leafCVisQuot C y (vecSum z + 1)

theorem leafRootQuot_eq_mkQ_leafRootRaw {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d)
    (y : YVec n b) (z : ZVec n c) :
    leafRootQuot (n := n) (a := a) (b := b) (c := c) (d := d) B C y z
      =
      (PassiveDiffSpace n d).mkQ
        (leafRootRaw (n := n) (a := a) (b := b) (c := c) (d := d) B C y z) := by
  let fB0 : PassiveRaw n d := fun w => ∑ p : PVec n a, B p (vecSum y) z w
  let fC0 : PassiveRaw n d := fun w => ∑ p : PVec n a, C p y (vecSum z) w
  let fB1 : PassiveRaw n d := fun w => ∑ p : PVec n a, B p (vecSum y + 1) z w
  let fC1 : PassiveRaw n d := fun w => ∑ p : PVec n a, C p y (vecSum z + 1) w
  have hroot :
      leafRootRaw (n := n) (a := a) (b := b) (c := c) (d := d) B C y z
        = fB0 + (fC0 + (fB1 + fC1)) := by
    funext w
    simp [leafRootRaw, fB0, fC0, fB1, fC1, KBMap, KCMap, dyB, dzC,
      betaB, gammaB, deltaC, etaC, Finset.sum_add_distrib,
      add_assoc, add_left_comm]
  have hquot :
      leafRootQuot (n := n) (a := a) (b := b) (c := c) (d := d) B C y z
        =
        (PassiveDiffSpace n d).mkQ fB0
          + ((PassiveDiffSpace n d).mkQ fC0
            + ((PassiveDiffSpace n d).mkQ fB1 + (PassiveDiffSpace n d).mkQ fC1)) := by
    unfold leafRootQuot leafBVisQuot leafCVisQuot leafSigmaQuot
      leafBProfile leafCProfile leafSigmaRaw
    change
      ((PassiveDiffSpace n d).mkQ fB0 + (PassiveDiffSpace n d).mkQ fB1)
          + (PassiveDiffSpace n d).mkQ fC0
          + (PassiveDiffSpace n d).mkQ fC1
        =
        (PassiveDiffSpace n d).mkQ fB0
          + ((PassiveDiffSpace n d).mkQ fC0
            + ((PassiveDiffSpace n d).mkQ fB1 + (PassiveDiffSpace n d).mkQ fC1))
    abel
  rw [hquot, hroot]
  change
    (Submodule.Quotient.mk (p := PassiveDiffSpace n d) fB0)
        + ((Submodule.Quotient.mk (p := PassiveDiffSpace n d) fC0)
          + ((Submodule.Quotient.mk (p := PassiveDiffSpace n d) fB1)
            + (Submodule.Quotient.mk (p := PassiveDiffSpace n d) fC1)))
      =
      Submodule.Quotient.mk (p := PassiveDiffSpace n d)
        (fB0 + (fC0 + (fB1 + fC1)))
  symm
  rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_add]

theorem leafRootQuot_eq_zero_iff_mem_PassiveDiffSpace
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d)
    (y : YVec n b) (z : ZVec n c) :
    leafRootQuot (n := n) (a := a) (b := b) (c := c) (d := d) B C y z = 0
      ↔
      leafRootRaw (n := n) (a := a) (b := b) (c := c) (d := d) B C y z
        ∈ PassiveDiffSpace n d := by
  rw [leafRootQuot_eq_mkQ_leafRootRaw
    (n := n) (a := a) (b := b) (c := c) (d := d) B C y z]
  exact
    (Submodule.Quotient.mk_eq_zero
      (p := PassiveDiffSpace n d)
      (x := leafRootRaw (n := n) (a := a) (b := b) (c := c) (d := d) B C y z))

theorem mem_WDiffSpace_iff_forall_passive
    {n b c d : ℕ} [NeZero n] (R : RootTarget n b c d) :
    R ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
      ↔
      ∀ y : YVec n b, ∀ z : ZVec n c,
        (fun w : WVec n d => R y z w) ∈ PassiveDiffSpace n d := by
  constructor
  · intro h y z
    rcases h with ⟨U, hU⟩
    refine ⟨U y z, ?_⟩
    funext w
    have hw := congrFun (congrFun (congrFun hU y) z) w
    simpa [WDiffEmbed, PassiveDiffEmbed] using hw
  · intro h
    classical
    choose U hU using h
    refine ⟨U, ?_⟩
    funext y z w
    have hw := congrFun (hU y z) w
    simpa [WDiffEmbed, PassiveDiffEmbed] using hw

theorem triangleLeaf_compatible_iff_leaf_visible_root_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
      + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
      ↔
      ∀ y : YVec n b, ∀ z : ZVec n c,
        leafBVisQuot B (vecSum y) z
          + leafBVisQuot B (vecSum y + 1) z
          + leafCVisQuot C y (vecSum z)
          + leafCVisQuot C y (vecSum z + 1)
          = 0 := by
  rw [mem_WDiffSpace_iff_forall_passive
    (R :=
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C)]
  constructor
  · intro h y z
    exact
      (leafRootQuot_eq_zero_iff_mem_PassiveDiffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d) B C y z).2 (h y z)
  · intro h y z
    exact
      (leafRootQuot_eq_zero_iff_mem_PassiveDiffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d) B C y z).1 (h y z)

end TriangleLeaf
end Core4loop
