import Core4loop.Square.Rank.Maps
import Core4loop.SquareDiagonal.BWSupport

namespace Core4loop
namespace SquareDiagonal

noncomputable def sqdiagBWZCompatRestrictedMap
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) →ₗ[F]
      sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) where
  toFun x :=
    ⟨SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x.1, x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

theorem sqdiagBWZCompatRestrictedMap_apply
    {n a b c d : ℕ} [NeZero n]
    (x : sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) :
    (sqdiagBWZCompatRestrictedMap
      (n := n) (a := a) (b := b) (c := c) (d := d) x).1 =
      SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x.1 := rfl

noncomputable def sqdiagBWZCompatRestrictedRangeToInf
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWZCompatRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) →ₗ[F]
      (↑(LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
        sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))) where
  toFun y :=
    ⟨(y.1 : RootTarget n b c d × CFun4 n a b d), by
      constructor
      · rcases y.2 with ⟨x, hx⟩
        refine ⟨x.1, ?_⟩
        exact congrArg Subtype.val hx
      · exact y.1.2⟩
  map_add' y z := by
    apply Subtype.ext
    rfl
  map_smul' r y := by
    apply Subtype.ext
    rfl

theorem sqdiagBWZCompatRestrictedRangeToInf_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagBWZCompatRestrictedRangeToInf
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro y z hyz
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun t :
      (↑(LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
        sqdiagZCompatTargetSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d))) =>
        (t : RootTarget n b c d × CFun4 n a b d))
    hyz

theorem sqdiagBWZCompatRestrictedRangeToInf_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWZCompatRestrictedRangeToInf
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro z
  rcases z.2.1 with ⟨x0, hx0⟩
  have hxSupport :
      x0 ∈ sqdiagBWZCompatSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
    change
      SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x0 ∈
        sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)
    rw [hx0]
    exact z.2.2
  let xs : sqdiagBWZCompatSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d) :=
    ⟨x0, hxSupport⟩
  let yTarget : sqdiagZCompatTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d) :=
    ⟨z.1, z.2.2⟩
  have hyRange :
      yTarget ∈ LinearMap.range
        (sqdiagBWZCompatRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    refine ⟨xs, ?_⟩
    apply Subtype.ext
    exact hx0
  refine ⟨⟨yTarget, hyRange⟩, ?_⟩
  apply Subtype.ext
  rfl

noncomputable def sqdiagBWZCompatRestrictedRangeEquivInf
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWZCompatRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      (↑(LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
        sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))) :=
  LinearEquiv.ofBijective
    (sqdiagBWZCompatRestrictedRangeToInf
      (n := n) (a := a) (b := b) (c := c) (d := d))
    ⟨sqdiagBWZCompatRestrictedRangeToInf_injective
      (n := n) (a := a) (b := b) (c := c) (d := d),
     sqdiagBWZCompatRestrictedRangeToInf_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d)⟩

theorem finrank_range_sqdiagBWZCompatRestrictedMap_eq_inf
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWZCompatRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  exact (sqdiagBWZCompatRestrictedRangeEquivInf
    (n := n) (a := a) (b := b) (c := c) (d := d)).finrank_eq

theorem sqdiagBWZCompat_image_inf_root_mem
    {n a b c d : ℕ} [NeZero n]
    (x :
      ↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d))) :
    x.1.1 ∈
      (YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  constructor
  · rw [← range_K_yw_eq_sup_YW (n := n) (a := a) (b := b) (c := c) (d := d)]
    rcases x.2.1 with ⟨BW, hBW⟩
    exact ⟨BW, congrArg Prod.fst hBW⟩
  · exact
      ((sqdiagZCompatTargetSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2.2).1

noncomputable def sqdiagBWZCompatImageRootMap
    {n a b c d : ℕ} [NeZero n] :
    ↑(LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
        sqdiagZCompatTargetSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)) →ₗ[F]
      ↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun x := ⟨x.1.1, sqdiagBWZCompat_image_inf_root_mem
    (n := n) (a := a) (b := b) (c := c) (d := d) x⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

theorem sqdiagBWZCompatImageRootMap_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagBWZCompatImageRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg
      (fun t :
        ↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
            WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)) =>
          (t : RootTarget n b c d))
      hxy
  · have hx0 :
        x.1.2 = 0 :=
        ((sqdiagZCompatTargetSubmodule_mem_iff
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2.2).2
    have hy0 :
        y.1.2 = 0 :=
        ((sqdiagZCompatTargetSubmodule_mem_iff
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).mp y.2.2).2
    rw [hx0, hy0]

theorem sqdiagBWZCompatImageRootMap_ker_eq_bot
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) = ⊥ := by
  exact LinearMap.ker_eq_bot_of_injective
    (sqdiagBWZCompatImageRootMap_injective
      (n := n) (a := a) (b := b) (c := c) (d := d))

theorem finrank_sqdiagBWZCompat_image_inf_eq_root_projection_range
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (sqdiagBWZCompatImageRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  exact (LinearMap.finrank_range_of_inj
    (sqdiagBWZCompatImageRootMap_injective
      (n := n) (a := a) (b := b) (c := c) (d := d))).symm

theorem finrank_sqdiagBWZCompat_image_inf_le_root_sup_inf
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d))) ≤
      Module.finrank F
        (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
            WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
          ZDiffSpace (n := n) (b := b) (c := c) (d := d))) := by
  rw [finrank_sqdiagBWZCompat_image_inf_eq_root_projection_range
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact Submodule.finrank_le
    (LinearMap.range
      (sqdiagBWZCompatImageRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)))

noncomputable def sqdiagBWZCompatRestrictedKerEquivSquareCombinedKernel
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWZCompatRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      SquareCombinedKernel n a b c d where
  toFun x :=
    ⟨x.1.1, by
      apply LinearMap.mem_ker.mpr
      have hx0 :
          sqdiagBWZCompatRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 = 0 :=
        LinearMap.mem_ker.mp x.2
      exact congrArg Subtype.val hx0⟩
  invFun x :=
    ⟨⟨x.1,
        SquareCombinedKernel_le_sqdiagBWZCompatSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) x.2⟩,
      by
        apply LinearMap.mem_ker.mpr
        apply Subtype.ext
        exact LinearMap.mem_ker.mp x.2⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem finrank_ker_sqdiagBWZCompatRestrictedMap
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.ker
          (sqdiagBWZCompatRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F (SquareCombinedKernel n a b c d) := by
  exact (sqdiagBWZCompatRestrictedKerEquivSquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)).finrank_eq

theorem finrank_sqdiagBWZCompatRestricted_range_add_SquareCombinedKernel
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWZCompatRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (SquareCombinedKernel n a b c d)
      =
    Module.finrank F
      (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (sqdiagBWZCompatRestrictedMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rwa [finrank_ker_sqdiagBWZCompatRestrictedMap
    (n := n) (a := a) (b := b) (c := c) (d := d)] at h

theorem finrank_sqdiagBWZCompat_image_inf_add_SquareCombinedKernel
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑(LinearMap.range
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (SquareCombinedKernel n a b c d)
      =
    Module.finrank F
      (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [← finrank_range_sqdiagBWZCompatRestrictedMap_eq_inf
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact finrank_sqdiagBWZCompatRestricted_range_add_SquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagBWZCompat_image_inf_eq_BW_sup_inf
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
        sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) =
      (LinearMap.range
            (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) ⊔
          LinearMap.range
            (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) ⊓
        sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [range_SquareCombined_eq_sup_range_B_W
    (n := n) (a := a) (b := b) (c := c) (d := d)]

theorem finrank_sqdiagBWZCompat_BW_sup_inf_add_SquareCombinedKernel
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (↑((LinearMap.range
              (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) ⊔
            LinearMap.range
              (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) ⊓
          sqdiagZCompatTargetSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)))
      + Module.finrank F (SquareCombinedKernel n a b c d)
      =
    Module.finrank F
      (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rw [← sqdiagBWZCompat_image_inf_eq_BW_sup_inf
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact finrank_sqdiagBWZCompat_image_inf_add_SquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)

theorem finrank_sqdiagBWZCompatSubmodule_le_root_sup_inf_add_SquareCombinedKernel
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      Module.finrank F
          (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
              WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
            ZDiffSpace (n := n) (b := b) (c := c) (d := d))) +
        Module.finrank F (SquareCombinedKernel n a b c d) := by
  rw [← finrank_sqdiagBWZCompat_image_inf_add_SquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact Nat.add_le_add_right
    (finrank_sqdiagBWZCompat_image_inf_le_root_sup_inf
      (n := n) (a := a) (b := b) (c := c) (d := d))
    (Module.finrank F (SquareCombinedKernel n a b c d))

theorem finrank_sqdiagBWZCompatSubmodule_add_inf_YZW_le_pair_infs_add_SquareCombinedKernel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))
      + (n - 1) ^ 3 ≤
      (n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ b +
        Module.finrank F (SquareCombinedKernel n a b c d) := by
  have hSupport :=
    finrank_sqdiagBWZCompatSubmodule_le_root_sup_inf_add_SquareCombinedKernel
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hRoot :=
    finrank_inf_sup_YW_Z_add_finrank_inf_YZW
      (n := n) (b := b) (c := c) (d := d) hb hc hd
  nlinarith

end SquareDiagonal
end Core4loop
