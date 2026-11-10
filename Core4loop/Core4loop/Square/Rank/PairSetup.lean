import Core4loop.Square.Rank.DiagonalRange
import Core4loop.Square.Rank.BPairCurlCore

open scoped BigOperators

namespace Core4loop

abbrev WPairAmbient (n a b c d : ℕ) [NeZero n] :=
  WDiffSpace (n := n) (b := b) (c := c) (d := d) ×
    WDiagSpace (n := n) (a := a) (b := b) (d := d)

theorem finrank_WPairAmbient {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    Module.finrank F (WPairAmbient n a b c d) =
      (n - 1) * n ^ (b + c) + (n - 1) * n ^ (a + b) := by
  rw [Module.finrank_prod,
    finrank_WDiffSpace (n := n) (b := b) (c := c) (d := d) hd,
    finrank_WDiagSpace (n := n) (a := a) (b := b) (d := d) ha hd]

noncomputable def BPairInclude {n a b c d : ℕ} [NeZero n] :
    BPairAmbient n a b c d →ₗ[F] (RootTarget n b c d × CFun4 n a b d) where
  toFun x := (x.1.1, x.2.1)
  map_add' x y := by
    ext <;> rfl
  map_smul' r x := by
    ext <;> rfl

noncomputable def WPairInclude {n a b c d : ℕ} [NeZero n] :
    WPairAmbient n a b c d →ₗ[F] (RootTarget n b c d × CFun4 n a b d) where
  toFun x := (x.1.1, x.2.1)
  map_add' x y := by
    ext <;> rfl
  map_smul' r x := by
    ext <;> rfl

theorem BPairInclude_injective {n a b c d : ℕ} [NeZero n] :
    Function.Injective (BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst h
  · apply Subtype.ext
    exact congrArg Prod.snd h

theorem WPairInclude_injective {n a b c d : ℕ} [NeZero n] :
    Function.Injective (WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst h
  · apply Subtype.ext
    exact congrArg Prod.snd h

noncomputable def SquareBMapAmbient {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F] BPairAmbient n a b c d where
  toFun B :=
    (⟨KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B, by
        rw [← range_KBMap_eq_YDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
        exact ⟨B, rfl⟩⟩,
      ⟨((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) B, by
        exact range_squareCompat_B_le_BDiagSpace
          (n := n) (a := a) (b := b) (c := c) (d := d) ⟨B, rfl⟩⟩)
  map_add' B B' := by
    apply Prod.ext
    · apply Subtype.ext
      exact (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_add B B'
    · apply Subtype.ext
      exact (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))).map_add B B')
  map_smul' r B := by
    apply Prod.ext
    · apply Subtype.ext
      exact (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r B
    · apply Subtype.ext
      exact (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareBInclusion (n := n) (a := a) (b := b) (c := c) (d := d))).map_smul r B)

noncomputable def SquareWMapAmbient {n a b c d : ℕ} [NeZero n] :
    WFun4 n a b c →ₗ[F] WPairAmbient n a b c d where
  toFun W :=
    (⟨KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W, by
        rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
        exact ⟨W, rfl⟩⟩,
      ⟨((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))) W, by
        exact range_squareCompat_W_le_WDiagSpace
          (n := n) (a := a) (b := b) (c := c) (d := d) ⟨W, rfl⟩⟩)
  map_add' W W' := by
    apply Prod.ext
    · apply Subtype.ext
      exact (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_add W W'
    · apply Subtype.ext
      exact (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))).map_add W W')
  map_smul' r W := by
    apply Prod.ext
    · apply Subtype.ext
      exact (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r W
    · apply Subtype.ext
      exact (((squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (SquareWInclusion (n := n) (a := a) (b := b) (c := c) (d := d))).map_smul r W)

theorem BPairInclude_SquareBMapAmbient
    {n a b c d : ℕ} [NeZero n] (B : BFun4 n a c d) :
    BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B) =
      SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d) B := rfl

theorem WPairInclude_SquareWMapAmbient
    {n a b c d : ℕ} [NeZero n] (W : WFun4 n a b c) :
    WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W) =
      SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d) W := rfl

end Core4loop
