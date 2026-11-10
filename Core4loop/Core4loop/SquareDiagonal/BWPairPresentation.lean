import Core4loop.SquareDiagonal.BWReducedRelation
import Core4loop.Square.Rank.PairRank

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

abbrev SqdiagAdjointAmbientPairProduct
    (n a b c d : ℕ) [NeZero n] :=
  ↑(LinearMap.range
      (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d))) ×
    ↑(LinearMap.range
      (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))

noncomputable def sqdiagAdjointAmbientPairProductEquiv
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointAmbientPairProduct n a b c d ≃ₗ[F]
      (↑(LinearMap.range
          (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) ×
        ↑(LinearMap.range
          (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)))) :=
  (range_SquareBMapAmbient_equiv_range_SquareBMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).prodCongr
      (range_SquareWMapAmbient_equiv_range_SquareWMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 200000 in
-- The ambient add map is over a product of nested range subtypes.
noncomputable def sqdiagAdjointAmbientPairAdd
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointAmbientPairProduct n a b c d →ₗ[F]
      RootTarget n b c d × CFun4 n a b d where
  toFun x :=
    BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 +
      WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1
  map_add' x y := by
    change
      BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
          (x.1.1 + y.1.1) +
        WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
          (x.2.1 + y.2.1) =
      (BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 +
          WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1) +
        (BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1 +
          WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) y.2.1)
    rw [(BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
      (WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)).map_add]
    abel
  map_smul' r x := by
    change
      BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) (r • x.1.1) +
        WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) (r • x.2.1) =
      r •
        (BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 +
          WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1)
    rw [(BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul,
      (WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul,
      smul_add]

@[simp]
theorem sqdiagAdjointAmbientPairProductEquiv_pairAdd
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairProduct n a b c d) :
    sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagAdjointAmbientPairProductEquiv
          (n := n) (a := a) (b := b) (c := c) (d := d) x) =
      sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  rfl

noncomputable def sqdiagAdjointAmbientPairPresentationSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Submodule F (SqdiagAdjointAmbientPairProduct n a b c d) :=
  (sqdiagAdjointPairPresentationSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)).comap
    (sqdiagAdjointAmbientPairProductEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)).toLinearMap

abbrev SqdiagAdjointAmbientPairPresentation
    (n a b c d : ℕ) [NeZero n] :=
  ↑(sqdiagAdjointAmbientPairPresentationSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))

theorem sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairProduct n a b c d) :
    x ∈ sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) ↔
      sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagZAdjointTargetSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rfl

theorem sqdiagAdjointAmbientPairPresentation_target_mem
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 ∈
      sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) :=
  (sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2

theorem sqdiagAdjointAmbientPairPresentation_root_mem_ZDiff
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∈
      ZDiffSpace (n := n) (b := b) (c := c) (d := d) :=
  ((sqdiagZAdjointTargetSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1)).mp
      (sqdiagAdjointAmbientPairPresentation_target_mem
        (n := n) (a := a) (b := b) (c := c) (d := d) x)).1

theorem sqdiagAdjointAmbientPairPresentation_exists_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    ∃ A : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 :=
  ((sqdiagZAdjointTargetSubmodule_mem_iff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1)).mp
      (sqdiagAdjointAmbientPairPresentation_target_mem
        (n := n) (a := a) (b := b) (c := c) (d := d) x)).2

set_option synthInstance.maxHeartbeats 200000 in
-- Projection out of the nested ambient presentation subtype needs extra instance budget.
noncomputable def sqdiagAdjointAmbientPairPresentationBPair
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointAmbientPairPresentation n a b c d →ₗ[F]
      BPairAmbient n a b c d where
  toFun x := x.1.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Projection out of the nested ambient presentation subtype needs extra instance budget.
noncomputable def sqdiagAdjointAmbientPairPresentationWPair
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointAmbientPairPresentation n a b c d →ₗ[F]
      WPairAmbient n a b c d where
  toFun x := x.1.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sqdiagAdjointAmbientPairPresentationBPair_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    sqdiagAdjointAmbientPairPresentationBPair
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      x.1.1.1 := by
  simp [sqdiagAdjointAmbientPairPresentationBPair]

@[simp]
theorem sqdiagAdjointAmbientPairPresentationWPair_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    sqdiagAdjointAmbientPairPresentationWPair
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      x.1.2.1 := by
  simp [sqdiagAdjointAmbientPairPresentationWPair]

theorem sqdiagAdjointAmbientPairPresentation_B_mem_ker_pairCurl
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    x.1.1.1 ∈
      LinearMap.ker
        (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) :=
  range_SquareBMapAmbient_le_ker_BPairCurlMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hb
    x.1.1.2

theorem sqdiagAdjointAmbientPairPresentation_W_mem_ker_pairCurl
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    x.1.2.1 ∈
      LinearMap.ker
        (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) :=
  range_SquareWMapAmbient_le_ker_WPairCurlMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd
    x.1.2.2

theorem sqdiagAdjointAmbientPairPresentation_BPairCurl_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x.1.1.1 =
      0 := by
  exact LinearMap.mem_ker.mp
    (sqdiagAdjointAmbientPairPresentation_B_mem_ker_pairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hb x)

theorem sqdiagAdjointAmbientPairPresentation_WPairCurl_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x.1.2.1 =
      0 := by
  exact LinearMap.mem_ker.mp
    (sqdiagAdjointAmbientPairPresentation_W_mem_ker_pairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hd x)

theorem sqdiagAdjointAmbientPairPresentation_BPairCurl_comp_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) :
    (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb).comp
        (sqdiagAdjointAmbientPairPresentationBPair
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      0 := by
  apply LinearMap.ext
  intro x
  simpa [sqdiagAdjointAmbientPairPresentationBPair] using
    sqdiagAdjointAmbientPairPresentation_BPairCurl_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hb x

theorem sqdiagAdjointAmbientPairPresentation_WPairCurl_comp_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) :
    (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd).comp
        (sqdiagAdjointAmbientPairPresentationWPair
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      0 := by
  apply LinearMap.ext
  intro x
  simpa [sqdiagAdjointAmbientPairPresentationWPair] using
    sqdiagAdjointAmbientPairPresentation_WPairCurl_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hd x

@[simp]
theorem sqdiagAdjointAmbientPairAdd_root_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairProduct n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1 =
      x.1.1.1.1 + x.2.1.1.1 := rfl

@[simp]
theorem sqdiagAdjointAmbientPairAdd_coeff_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairProduct n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x).2 =
      x.1.1.2.1 + x.2.1.2.1 := rfl

@[simp]
theorem sqdiagAdjointAmbientPairPresentation_root_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
      x.1.1.1.1.1 + x.1.2.1.1.1 := rfl

@[simp]
theorem sqdiagAdjointAmbientPairPresentation_coeff_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 =
      x.1.1.1.2.1 + x.1.2.1.2.1 := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- Restricting the product equivalence to the presentation submodule stresses instance search.
noncomputable def sqdiagAdjointAmbientPairEquivPairPresentation
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointAmbientPairPresentation n a b c d ≃ₗ[F]
      SqdiagAdjointPairPresentation n a b c d :=
  (sqdiagAdjointAmbientPairProductEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d)).ofSubmodule'
    (sqdiagAdjointPairPresentationSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))

@[simp]
theorem sqdiagAdjointAmbientPairEquivPairPresentation_apply_val
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1 =
      sqdiagAdjointAmbientPairProductEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 := rfl

noncomputable def sqdiagAdjointAmbientPairPresentationSum
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointAmbientPairPresentation n a b c d →ₗ[F]
      SqdiagReducedRelation n a b c d :=
  (sqdiagAdjointPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d)).toLinearMap

theorem sqdiagAdjointAmbientPairPresentationSum_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro z
  rcases sqdiagAdjointPairPresentationSum_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) z with
    ⟨x, hx⟩
  refine
    ⟨(sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d)).symm x, ?_⟩
  simp [sqdiagAdjointAmbientPairPresentationSum, hx]

set_option synthInstance.maxHeartbeats 200000 in
-- The finrank statement unfolds the same nested ambient-presentation subtype.
theorem finrank_sqdiagAdjointAmbientPairPresentation_eq_pairPresentation
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagAdjointAmbientPairPresentation n a b c d) =
      Module.finrank F (SqdiagAdjointPairPresentation n a b c d) :=
  LinearEquiv.finrank_eq
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d))

set_option synthInstance.maxHeartbeats 200000 in
-- This dimension transport unfolds the nested ambient-presentation subtype.
theorem finrank_sqdiagAdjointAmbientPairPresentation_add_core_eq_relation_add_square_terms
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (SqdiagAdjointAmbientPairPresentation n a b c d) +
        2 * (n - 1) ^ 3 =
      Module.finrank F (SqdiagReducedRelation n a b c d) +
        ((n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1)) := by
  rw [finrank_sqdiagAdjointAmbientPairPresentation_eq_pairPresentation
    (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact
    finrank_sqdiagAdjointPairPresentation_add_core_eq_relation_add_square_terms
      (n := n) (a := a) (b := b) (c := c) (d := d) ha hb hc hd

noncomputable def sqdiagAdjointAmbientPairPresentationRootMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagAdjointAmbientPairPresentation n a b c d →ₗ[F]
      ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :=
  (sqdiagAdjointPairPresentationRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d)).toLinearMap

abbrev sqdiagAdjointAmbientPairPresentationVertical
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagAdjointAmbientPairPresentation n a b c d) :=
  (sqdiagAdjointPairPresentationVertical n a b c d).comap
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d)).toLinearMap

theorem sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d) :
    (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
  have hxpair :
      sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagAdjointPairPresentationVertical n a b c d := hx
  have hroot := LinearMap.mem_ker.mp hxpair
  have hval :
      (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagAdjointAmbientPairEquivPairPresentation
            (n := n) (a := a) (b := b) (c := c) (d := d) x)).1.1.1 =
        0 := by
    exact congrArg Subtype.val hroot
  rw [sqdiagAdjointPairPresentationSum_root_apply] at hval
  simpa [sqdiagAdjointAmbientPairAdd] using hval

theorem sqdiagAdjointAmbientPairPresentationVertical_B_root_eq_W_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d) :
    x.1.1.1.1.1 = x.1.2.1.1.1 := by
  have hroot :=
    sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx
  change x.1.1.1.1.1 + x.1.2.1.1.1 = 0 at hroot
  exact (add_eq_zero_iff_eq_of_F_module _ _).mp hroot

theorem sqdiagAdjointAmbientPairPresentation_mem_vertical_of_B_root_eq_W_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hxroot : x.1.1.1.1.1 = x.1.2.1.1.1) :
    x ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d := by
  change
    sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagAdjointPairPresentationVertical n a b c d
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change
    (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x).1).1 = 0
  change x.1.1.1.1.1 + x.1.2.1.1.1 = 0
  exact (add_eq_zero_iff_eq_of_F_module _ _).mpr hxroot

theorem sqdiagAdjointAmbientPairPresentation_mem_vertical_iff_B_root_eq_W_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    x ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ↔
      x.1.1.1.1.1 = x.1.2.1.1.1 :=
  ⟨sqdiagAdjointAmbientPairPresentationVertical_B_root_eq_W_root
      (n := n) (a := a) (b := b) (c := c) (d := d) x,
    sqdiagAdjointAmbientPairPresentation_mem_vertical_of_B_root_eq_W_root
      (n := n) (a := a) (b := b) (c := c) (d := d) x⟩

theorem sqdiagAdjointAmbientPairPresentation_mem_vertical_of_root_add_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hxroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0) :
    x ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d := by
  change
    sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagAdjointPairPresentationVertical n a b c d
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change
    (sqdiagAdjointPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x).1).1 = 0
  simpa [sqdiagAdjointAmbientPairAdd] using hxroot

noncomputable def sqdiagAdjointAmbientPairPresentationQ
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) : F :=
  sqdiagAdjointPairPresentationQ
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d) x)

noncomputable def sqdiagAdjointAmbientPairPresentationPolar
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagAdjointAmbientPairPresentation n a b c d) : F :=
  sqdiagAdjointPairPresentationPolar
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d) x)
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d) y)

theorem sqdiagAdjointAmbientPairPresentationPolar_eq_rootCoeffApply_of_coeff_eq
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A B : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (hB :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2) :
    sqdiagAdjointAmbientPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y =
      sqdiagRootCoeffApply A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 +
        sqdiagRootCoeffApply B
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  exact
    sqdiagAdjointPairPresentationPolar_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
      (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) y)
      A B hA hB

abbrev sqdiagAdjointAmbientPairPresentationVerticalOrthogonal
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagAdjointAmbientPairPresentation n a b c d) :=
  (sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d).comap
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d)).toLinearMap

theorem sqdiagAdjointAmbientPairPresentationVertical_le_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointAmbientPairPresentationVertical n a b c d ≤
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  intro x hx
  change
    sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d
  exact
    sqdiagAdjointPairPresentationVertical_le_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) hx

theorem sqdiagAdjointAmbientPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hy : y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d) :
    sqdiagAdjointAmbientPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 := by
  have hxpair :
      sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := hx
  have hypair :
      sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) y ∈
        sqdiagAdjointPairPresentationVertical n a b c d := hy
  have hxDual := LinearMap.mem_ker.mp hxpair
  have happ :=
    congrArg
      (fun T : Module.Dual F (sqdiagAdjointPairPresentationVertical n a b c d) =>
        T
          ⟨sqdiagAdjointAmbientPairEquivPairPresentation
              (n := n) (a := a) (b := b) (c := c) (d := d) y,
            hypair⟩)
      hxDual
  simpa [sqdiagAdjointAmbientPairPresentationPolar,
    sqdiagAdjointPairPresentationPolarToVertical] using happ

theorem sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_iff_polar_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d ↔
      ∀ y : SqdiagAdjointAmbientPairPresentation n a b c d,
        y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d →
          sqdiagAdjointAmbientPairPresentationPolar
              (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 := by
  constructor
  · intro hx y hy
    exact
      sqdiagAdjointAmbientPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x hx y hy
  · intro h
    change
      sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    let yamb : SqdiagAdjointAmbientPairPresentation n a b c d :=
      (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d)).symm y.1
    have hyamb :
        yamb ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d := by
      change
        sqdiagAdjointAmbientPairEquivPairPresentation
            (n := n) (a := a) (b := b) (c := c) (d := d) yamb ∈
          sqdiagAdjointPairPresentationVertical n a b c d
      simpa [yamb] using y.2
    have hzero := h yamb hyamb
    simpa [sqdiagAdjointAmbientPairPresentationPolar,
      sqdiagAdjointPairPresentationPolarToVertical, yamb] using hzero

theorem sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_of_sum_mem_reducedVerticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx :
      sqdiagAdjointAmbientPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  change
    sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d
  refine
    sqdiagAdjointPairPresentation_mem_verticalOrthogonal_of_sum_mem_reducedVerticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x) ?_
  simpa [sqdiagAdjointAmbientPairPresentationSum] using hx

theorem sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_of_rootZeroACoeffSpace_annihilates_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hann :
      ∀ A : RootTarget n b c d,
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0) :
    x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
  refine
    sqdiagAdjointAmbientPairPresentation_mem_verticalOrthogonal_of_sum_mem_reducedVerticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) x ?_
  rw [sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace]
  intro A hA
  have hroot :
      (sqdiagAdjointAmbientPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1.1 =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
    change
      (sqdiagAdjointPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagAdjointAmbientPairEquivPairPresentation
            (n := n) (a := a) (b := b) (c := c) (d := d) x)).1.1.1 =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1
    rw [sqdiagAdjointPairPresentationSum_root_apply]
    exact congrArg Prod.fst
      (sqdiagAdjointAmbientPairProductEquiv_pairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1)
  rw [hroot]
  exact hann A hA

theorem sqdiagAdjointAmbientPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal_of_root_add_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hyroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0) :
    sqdiagAdjointAmbientPairPresentationPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y = 0 :=
  sqdiagAdjointAmbientPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d) x hx y
    (sqdiagAdjointAmbientPairPresentation_mem_vertical_of_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y hyroot)

theorem sqdiagAdjointAmbientPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hyroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0)
    (A B : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (hB :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2) :
    sqdiagRootCoeffApply A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 +
        sqdiagRootCoeffApply B
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
      0 := by
  have hpolar :=
    sqdiagAdjointAmbientPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal_of_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx y hyroot
  rw [sqdiagAdjointAmbientPairPresentationPolar_eq_rootCoeffApply_of_coeff_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) x y A B hA hB] at hpolar
  exact hpolar

theorem sqdiagAdjointAmbientPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal_of_B_root_eq_W_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hyroot : y.1.1.1.1.1 = y.1.2.1.1.1)
    (A B : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (hB :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2) :
    sqdiagRootCoeffApply A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 +
        sqdiagRootCoeffApply B
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
      0 := by
  refine
    sqdiagAdjointAmbientPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx y ?_ A B hA hB
  change y.1.1.1.1.1 + y.1.2.1.1.1 = 0
  exact (add_eq_zero_iff_eq_of_F_module _ _).mpr hyroot

theorem sqdiagAdjointAmbientPairPresentation_exists_rootCoeff_equation_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hyroot :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0) :
    ∃ A B : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 ∧
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
      sqdiagRootCoeffApply A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 +
          sqdiagRootCoeffApply B
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
        0 := by
  rcases sqdiagAdjointAmbientPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA⟩
  rcases sqdiagAdjointAmbientPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) y with
    ⟨B, hB⟩
  refine ⟨A, B, hA, hB, ?_⟩
  exact
    sqdiagAdjointAmbientPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx y hyroot A B hA hB

theorem sqdiagAdjointPairPresentationQ_eq_zero_of_ambientPairPresentationQ_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hamb :
      ∀ x : SqdiagAdjointAmbientPairPresentation n a b c d,
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointAmbientPairPresentationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0)
    (x : SqdiagAdjointPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  let y : SqdiagAdjointAmbientPairPresentation n a b c d :=
    (sqdiagAdjointAmbientPairEquivPairPresentation
      (n := n) (a := a) (b := b) (c := c) (d := d)).symm x
  have hy :
      y ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d := by
    change
      sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) y ∈
        sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d
    simpa [y] using hx
  have hq := hamb y hy
  simpa [sqdiagAdjointAmbientPairPresentationQ, y] using hq

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentationQ_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (hamb :
      ∀ x : SqdiagAdjointAmbientPairPresentation n a b c d,
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          sqdiagAdjointAmbientPairPresentationQ
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointPairPresentationQ_eq_zero_of_ambientPairPresentationQ_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hamb y hy

theorem sqdiagAdjointAmbientPairPresentationQ_eq_rootCoeffApply_of_coeff_eq
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x =
      sqdiagRootCoeffApply A
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  exact
    sqdiagAdjointPairPresentationQ_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x) A hA

theorem sqdiagAdjointAmbientPairPresentation_exists_Q_rootCoeffApply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    ∃ A : RootTarget n b c d,
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 ∧
      sqdiagAdjointAmbientPairPresentationQ
          (n := n) (a := a) (b := b) (c := c) (d := d) x =
        sqdiagRootCoeffApply A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  rcases sqdiagAdjointAmbientPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA⟩
  refine ⟨A, hA, ?_⟩
  exact
    sqdiagAdjointAmbientPairPresentationQ_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) x A hA

theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hzero :
      ∀ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
        sqdiagRootCoeffApply A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  rcases sqdiagAdjointAmbientPairPresentation_exists_Q_rootCoeffApply
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA, hq⟩
  rw [hq]
  exact hzero A hA

theorem sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
      sqdiagReducedRelationVerticalOrthogonal n a b c d := by
  have hxpair :
      sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := hx
  simpa [sqdiagAdjointAmbientPairPresentationSum] using
    sqdiagAdjointPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
      hxpair

theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  have hxpair :
      sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagAdjointPairPresentationVerticalOrthogonal n a b c d := hx
  have hq :=
    sqdiagAdjointPairPresentationQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) hred
      (sqdiagAdjointAmbientPairEquivPairPresentation
        (n := n) (a := a) (b := b) (c := c) (d := d) x)
      hxpair
  simpa [sqdiagAdjointAmbientPairPresentationQ] using hq

theorem sqdiagAdjointAmbientPairPresentation_coeff_rootCoeff_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    sqdiagRootCoeffApply A
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
  have hq0 :=
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) hred x hx
  have hq :=
    sqdiagAdjointAmbientPairPresentationQ_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) x A hA
  rw [hq] at hq0
  exact hq0

theorem sqdiagAdjointAmbientPairPresentation_verticalOrthogonal_coeff_rootCoeff_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0) :
    ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
      x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
        ∀ A : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
          sqdiagRootCoeffApply A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
  intro x hx A hA
  exact
    sqdiagAdjointAmbientPairPresentation_coeff_rootCoeff_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) hred x hx A hA

set_option synthInstance.maxHeartbeats 500000 in
-- Production bridge from reduced root separation to the ambient pair root-coeff phase condition.
theorem sqdiagAdjointAmbientPairPresentation_verticalOrthogonal_coeff_rootCoeff_zero_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0) :
    ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
      x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
        ∀ A : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
          sqdiagRootCoeffApply A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 :=
  sqdiagAdjointAmbientPairPresentation_verticalOrthogonal_coeff_rootCoeff_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep)

theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_mem_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  rcases sqdiagAdjointAmbientPairPresentation_exists_Q_rootCoeffApply
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA, hq⟩
  rw [hq]
  have hroot :=
    sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx
  simp [hroot, sqdiagRootCoeffApply]

theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_verticalOrthogonal_le_vertical
    {n a b c d : ℕ} [NeZero n]
    (hle :
      sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d ≤
        sqdiagAdjointAmbientPairPresentationVertical n a b c d)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_mem_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d) x (hle hx)

/--
Conditional diagnostic route only.
The premise asks every `sqdiagKCAdjointCoeff` value to have a root-zero
ambient pair representative. Exact finite-field checks show this is too strong
for the positive SquareDiagonal family, e.g. at `n = 3`, `a = b = c = d = 1`.
The production proof should instead establish the pointwise root-coefficient
vanishing criterion above on the vertical orthogonal.
-/
theorem sqdiagAdjointAmbientPairPresentation_verticalOrthogonal_le_vertical_of_verticalCoeff_surjective
    {n a b c d : ℕ} [NeZero n]
    (hcoeff :
      ∀ A : RootTarget n b c d,
        ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
          y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2) :
    sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d ≤
      sqdiagAdjointAmbientPairPresentationVertical n a b c d := by
  intro x hx
  rcases sqdiagAdjointAmbientPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨X, hX⟩
  apply sqdiagAdjointAmbientPairPresentation_mem_vertical_of_root_add_eq_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) x
  apply (sqdiagRootCoeffApply_forall_eq_zero_iff
    (n := n) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1).mp
  intro A
  rcases hcoeff A with ⟨y, hyvert, hA⟩
  have hpolar :=
    sqdiagAdjointAmbientPairPresentationPolar_eq_zero_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx y hyvert
  rw [sqdiagAdjointAmbientPairPresentationPolar_eq_rootCoeffApply_of_coeff_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) x y X A hX hA] at hpolar
  have hyroot :=
    sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y hyvert
  simpa [hyroot, sqdiagRootCoeffApply] using hpolar

theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_verticalCoeff_surjective
    {n a b c d : ℕ} [NeZero n]
    (hcoeff :
      ∀ A : RootTarget n b c d,
        ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
          y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_verticalOrthogonal_le_vertical
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairPresentation_verticalOrthogonal_le_vertical_of_verticalCoeff_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) hcoeff)
    x hx

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentation_verticalCoeff_surjective
    {n a b c d : ℕ} [NeZero n]
    (hcoeff :
      ∀ A : RootTarget n b c d,
        ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
          y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentationQ_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_verticalCoeff_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d) hcoeff y hy

theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_verticalOrthogonal_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
  sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) x (hzero x hx)

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentation_coeff_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentationQ_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_verticalOrthogonal_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hzero y hy

abbrev sqdiagAdjointAmbientPairingMatchVertical
    (n a b c d : ℕ) [NeZero n] : Prop :=
  ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
    x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
      ∀ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
        ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
          y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
            ∃ B : RootTarget n b c d,
              sqdiagKCAdjointCoeff
                  (n := n) (a := a) (b := b) (c := c) (d := d) B =
                (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
                sqdiagRootCoeffApply B
                    (sqdiagAdjointAmbientPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
                  sqdiagRootCoeffApply A
                    (sqdiagAdjointAmbientPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1

theorem sqdiagAdjointAmbientPairPresentation_rootCoeff_zero_of_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hy : y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d)
    (B : RootTarget n b c d)
    (hB :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2)
    (hmatch :
      sqdiagRootCoeffApply B
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
        sqdiagRootCoeffApply A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1) :
    sqdiagRootCoeffApply A
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
  have hyroot :=
    sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y hy
  have heq :=
    sqdiagAdjointAmbientPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx y hyroot A B hA hB
  have hBzero :
      sqdiagRootCoeffApply B
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
    simpa [hyroot, sqdiagRootCoeffApply] using heq
  exact hmatch.symm.trans hBzero

theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  refine
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_coeff_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) x ?_
  intro A hA
  rcases hmatch x hx A hA with ⟨y, hy, B, hB, hpair⟩
  exact
    sqdiagAdjointAmbientPairPresentation_rootCoeff_zero_of_pairing_match_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx A hA y hy B hB hpair

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentation_pairing_match_vertical
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentationQ_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_pairing_match_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch y hy

/--
Conditional diagnostic route only.
This root-zero coefficient representative test is a sufficient condition for
the production goal, but small exact models show the literal representative
condition is still stronger than the actual `Q = 0` statement. The next proof
step should prove the root-coefficient vanishing criterion directly from the
pair/core exactness API.
-/
theorem sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_rootZeroCoeffTest
    {n a b c d : ℕ} [NeZero n]
    (htest :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
              (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 ∧
                sqdiagKCAdjointCoeff
                    (n := n) (a := a) (b := b) (c := c) (d := d) A =
                  (sqdiagAdjointAmbientPairAdd
                    (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d) :
    sqdiagAdjointAmbientPairPresentationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 := by
  rcases sqdiagAdjointAmbientPairPresentation_exists_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x with
    ⟨A, hA⟩
  rcases htest x hx A hA with ⟨y, hyroot, hycoeff⟩
  have heq :=
    sqdiagAdjointAmbientPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx y hyroot A A hA hycoeff
  have hq :=
    sqdiagAdjointAmbientPairPresentationQ_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) x A hA
  rw [hq]
  simpa [hyroot, sqdiagRootCoeffApply] using heq

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentation_rootZeroCoeffTest
    {n a b c d : ℕ} [NeZero n]
    (htest :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
              (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 ∧
                sqdiagKCAdjointCoeff
                    (n := n) (a := a) (b := b) (c := c) (d := d) A =
                  (sqdiagAdjointAmbientPairAdd
                    (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentationQ_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_rootZeroCoeffTest
      (n := n) (a := a) (b := b) (c := c) (d := d) htest y hy

end

end SquareDiagonal
end Core4loop
