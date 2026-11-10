import Core4loop.TriangleLeaf.ProfileKernelBaseSpec

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem passiveVisiblePart_PassiveDiffEmbed
    {n d : ℕ} [NeZero n] (hd : 0 < d) (R : ZeroSumProfile n) :
    passiveVisiblePart (n := n) (d := d) hd
        (PassiveDiffEmbed (n := n) (d := d) R) =
      0 := by
  exact
    (passiveVisiblePart_eq_zero_iff_mem_PassiveDiffSpace
      (n := n) (d := d) hd
      (PassiveDiffEmbed (n := n) (d := d) R)).2
      ⟨R, rfl⟩

theorem passiveVisiblePart_add_visible_diff
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (v : PassiveVisibleSpace n d hd) (R : ZeroSumProfile n) :
    passiveVisiblePart (n := n) (d := d) hd
        (v.1 + PassiveDiffEmbed (n := n) (d := d) R)
      =
      v.1 := by
  rw [map_add]
  rw [passiveVisiblePart_fixed_of_mem_visibleSpace (n := n) (d := d) hd v]
  rw [passiveVisiblePart_PassiveDiffEmbed (n := n) (d := d) hd R]
  simp

theorem passiveRepProfileMap_add_visible_diff
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (v : PassiveVisibleSpace n d hd) (R : ZeroSumProfile n) :
    passiveRepProfileMap (n := n) (d := d) hd
        (v.1 + PassiveDiffEmbed (n := n) (d := d) R)
      =
      R := by
  rw [map_add]
  rw [passiveRepProfileMap_eq_zero_of_mem_visibleSpace
    (n := n) (d := d) hd v]
  rw [passiveRepProfileMap_PassiveDiffEmbed (n := n) (d := d) hd R]
  simp

theorem passiveVisible_diff_recompose
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : PassiveRaw n d) :
    (passiveVisiblePartToSpace (n := n) (d := d) hd f).1
      + PassiveDiffEmbed (n := n) (d := d)
          (passiveRepProfileMap (n := n) (d := d) hd f)
      =
      f := by
  funext w
  simp [passiveVisiblePartToSpace_apply, passiveVisiblePart, passiveDiffPart,
    F_add_self, add_assoc]

noncomputable def passiveRawEquivVisibleDiff
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    PassiveRaw n d ≃ₗ[F] PassiveVisibleSpace n d hd × ZeroSumProfile n where
  toFun f :=
    (passiveVisiblePartToSpace (n := n) (d := d) hd f,
      passiveRepProfileMap (n := n) (d := d) hd f)
  invFun X :=
    X.1.1 + PassiveDiffEmbed (n := n) (d := d) X.2
  left_inv f := by
    exact passiveVisible_diff_recompose (n := n) (d := d) hd f
  right_inv X := by
    apply Prod.ext
    · apply Subtype.ext
      exact passiveVisiblePart_add_visible_diff (n := n) (d := d) hd X.1 X.2
    · exact passiveRepProfileMap_add_visible_diff (n := n) (d := d) hd X.1 X.2
  map_add' f g := by
    ext <;> simp
  map_smul' r f := by
    ext <;> simp

theorem passiveRawEquivVisibleDiff_apply_fst
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : PassiveRaw n d) :
    (passiveRawEquivVisibleDiff (n := n) (d := d) hd f).1 =
      passiveVisiblePartToSpace (n := n) (d := d) hd f := rfl

theorem passiveRawEquivVisibleDiff_apply_snd
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : PassiveRaw n d) :
    (passiveRawEquivVisibleDiff (n := n) (d := d) hd f).2 =
      passiveRepProfileMap (n := n) (d := d) hd f := rfl

theorem passiveRawEquivVisibleDiff_symm_apply
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (X : PassiveVisibleSpace n d hd × ZeroSumProfile n) :
    (passiveRawEquivVisibleDiff (n := n) (d := d) hd).symm X =
      X.1.1 + PassiveDiffEmbed (n := n) (d := d) X.2 := rfl

end

end TriangleLeaf
end Core4loop
