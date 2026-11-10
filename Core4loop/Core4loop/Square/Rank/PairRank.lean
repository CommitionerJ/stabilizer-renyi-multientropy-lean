import Core4loop.Square.Rank.PairExactW
import Core4loop.Square.Rank.PairSurj

namespace Core4loop

theorem finrank_range_SquareBMapAmbient_add_vertex_d
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F
        (LinearMap.range
          (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ d =
    Module.finrank F (BPairAmbient n a b c d) := by
  let L := BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  have hsurj : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr
      (BPairCurlMap_surjective (n := n) (a := a) (b := b) (c := c) (d := d) hb hc)
  rw [hsurj,
    ker_BPairCurlMap_eq_range_SquareBMapAmbient
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc] at hnull
  rw [finrank_top, finrank_WVec_to_PairCurlSpace] at hnull
  calc
    Module.finrank F
          (LinearMap.range
            (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
        + (n - 1) ^ 2 * n ^ d
        =
      n ^ d * (n - 1) ^ 2 +
        Module.finrank F
          (LinearMap.range
            (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d))) := by
          ring
    _ = Module.finrank F (BPairAmbient n a b c d) := hnull

theorem finrank_range_SquareWMapAmbient_add_vertex_b
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ b =
    Module.finrank F (WPairAmbient n a b c d) := by
  let L := WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  have hsurj : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr
      (WPairCurlMap_surjective (n := n) (a := a) (b := b) (c := c) (d := d) hc hd)
  rw [hsurj,
    ker_WPairCurlMap_eq_range_SquareWMapAmbient
      (n := n) (a := a) (b := b) (c := c) (d := d) hc hd] at hnull
  rw [finrank_top, finrank_YVec_to_PairCurlSpace] at hnull
  calc
    Module.finrank F
          (LinearMap.range
            (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
        + (n - 1) ^ 2 * n ^ b
        =
      n ^ b * (n - 1) ^ 2 +
        Module.finrank F
          (LinearMap.range
            (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d))) := by
          ring
    _ = Module.finrank F (WPairAmbient n a b c d) := hnull

noncomputable def range_SquareBMapAmbient_equiv_range_SquareBMap
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.range
        (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun y :=
    ⟨BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.1, by
      rcases y.2 with ⟨B, hB⟩
      refine ⟨B, ?_⟩
      rw [← hB]
      exact BPairInclude_SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) B⟩
  invFun z :=
    ⟨SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)
        (Classical.choose z.2),
      ⟨Classical.choose z.2, rfl⟩⟩
  left_inv y := by
    apply Subtype.ext
    have hmem :
        BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.1 ∈
          LinearMap.range
            (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rcases y.2 with ⟨B, hB⟩
      refine ⟨B, ?_⟩
      rw [← hB]
      exact BPairInclude_SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) B
    have hchoose := Classical.choose_spec hmem
    apply BPairInclude_injective
      (n := n) (a := a) (b := b) (c := c) (d := d)
    change
      BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)
          (Classical.choose hmem)) =
        BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.1
    rw [BPairInclude_SquareBMapAmbient, hchoose]
  right_inv z := by
    apply Subtype.ext
    have hchoose := Classical.choose_spec z.2
    change
      BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)
          (Classical.choose z.2)) = z.1
    rw [BPairInclude_SquareBMapAmbient, hchoose]
  map_add' y z := by
    apply Subtype.ext
    rfl
  map_smul' r y := by
    apply Subtype.ext
    rfl

theorem finrank_range_SquareBMap_eq_ambient
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  (LinearEquiv.finrank_eq
    (range_SquareBMapAmbient_equiv_range_SquareBMap
      (n := n) (a := a) (b := b) (c := c) (d := d))).symm

noncomputable def range_SquareWMapAmbient_equiv_range_SquareWMap
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.range
        (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun y :=
    ⟨WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.1, by
      rcases y.2 with ⟨W, hW⟩
      refine ⟨W, ?_⟩
      rw [← hW]
      exact WPairInclude_SquareWMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) W⟩
  invFun z :=
    ⟨SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)
        (Classical.choose z.2),
      ⟨Classical.choose z.2, rfl⟩⟩
  left_inv y := by
    apply Subtype.ext
    have hmem :
        WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.1 ∈
          LinearMap.range
            (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rcases y.2 with ⟨W, hW⟩
      refine ⟨W, ?_⟩
      rw [← hW]
      exact WPairInclude_SquareWMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) W
    have hchoose := Classical.choose_spec hmem
    apply WPairInclude_injective
      (n := n) (a := a) (b := b) (c := c) (d := d)
    change
      WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)
          (Classical.choose hmem)) =
        WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.1
    rw [WPairInclude_SquareWMapAmbient, hchoose]
  right_inv z := by
    apply Subtype.ext
    have hchoose := Classical.choose_spec z.2
    change
      WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)
          (Classical.choose z.2)) = z.1
    rw [WPairInclude_SquareWMapAmbient, hchoose]
  map_add' y z := by
    apply Subtype.ext
    rfl
  map_smul' r y := by
    apply Subtype.ext
    rfl

theorem finrank_range_SquareWMap_eq_ambient
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  (LinearEquiv.finrank_eq
    (range_SquareWMapAmbient_equiv_range_SquareWMap
      (n := n) (a := a) (b := b) (c := c) (d := d))).symm

theorem finrank_range_SquareBMap_add_vertex_d
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F
        (LinearMap.range
          (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ d =
      (n - 1) * n ^ (c + d) + (n - 1) * n ^ (a + d) := by
  rw [finrank_range_SquareBMap_eq_ambient
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  calc
    Module.finrank F
        (LinearMap.range
          (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ d
        = Module.finrank F (BPairAmbient n a b c d) :=
          finrank_range_SquareBMapAmbient_add_vertex_d
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc
    _ = (n - 1) * n ^ (c + d) + (n - 1) * n ^ (a + d) :=
          finrank_BPairAmbient (n := n) (a := a) (b := b) (c := c) (d := d) ha hb

theorem finrank_range_SquareWMap_add_vertex_b
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ b =
      (n - 1) * n ^ (b + c) + (n - 1) * n ^ (a + b) := by
  rw [finrank_range_SquareWMap_eq_ambient
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  calc
    Module.finrank F
        (LinearMap.range
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ b
        = Module.finrank F (WPairAmbient n a b c d) :=
          finrank_range_SquareWMapAmbient_add_vertex_b
            (n := n) (a := a) (b := b) (c := c) (d := d) hc hd
    _ = (n - 1) * n ^ (b + c) + (n - 1) * n ^ (a + b) :=
          finrank_WPairAmbient (n := n) (a := a) (b := b) (c := c) (d := d) ha hd

end Core4loop
