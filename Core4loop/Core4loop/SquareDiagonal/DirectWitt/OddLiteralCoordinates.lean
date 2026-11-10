import Core4loop.SquareDiagonal.PreC.Reduction
import Core4loop.SquareDiagonal.DirectWitt.OddJTail

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

noncomputable section

local instance (S : Type*) : DecidableEq S := Classical.decEq S

/-!
# Odd pointed coordinates for literal Diamond fields

This file lifts the scalar odd pointed-coordinate normal form to values in
an arbitrary `F`-module.  It also records the literal head/passive-tail
reindexings of the `A`, `B`, and `W` fields.  No source constraint or phase
is transported here.
-/

/-- Scalar and pointed-tail coordinates for an arbitrary module-valued
function. -/
abbrev PointedOddValueCoords
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V] :=
  V × (PointedTail S s0 → V)

private theorem value_add_self
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 := by
  rw [← two_smul F x, show (2 : F) = 0 by decide, zero_smul]

private theorem sum_eq_at_point_add_tail_value
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] (f : S → V) :
    (∑ s, f s) = f s0 + ∑ t : PointedTail S s0, f t.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset S)) (p := fun s : S => s = s0) f).symm
  calc
    (∑ s, f s) =
        (∑ s ∈ (Finset.univ : Finset S) with s = s0, f s) +
          ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
            simpa using hpart
    _ = f s0 + ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
          congr 1
          rw [Finset.sum_eq_single s0]
          · intro s hs hne
            exact (hne (Finset.mem_filter.mp hs).2).elim
          · simp
    _ = f s0 + ∑ t : PointedTail S s0, f t.1 := by
          congr 1
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset S)) (p := fun s : S => s ≠ s0)
              (f := f)).symm

private theorem oddTail_sum_const_zero_value
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (x : V) :
    (∑ _ : PointedTail S s0, x) = 0 := by
  have hcast : ((Fintype.card (PointedTail S s0) : Nat) : F) = 0 := by
    rcases oddTail_card_even s0 hodd with ⟨k, hk⟩
    rw [hk]
    push_cast
    exact F_add_self _
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, hcast, zero_smul]

private noncomputable def pointedSrcOddValueRead
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V] :
    (S → V) →ₗ[F] PointedOddValueCoords S V s0 where
  toFun f := (∑ s, f s, fun t => f t.1 + ∑ s, f s)
  map_add' f g := by
    apply Prod.ext
    · change (Finset.univ.sum fun s : S => f s + g s) =
        Finset.univ.sum f + Finset.univ.sum g
      rw [Finset.sum_add_distrib]
    · funext t
      change (f t.1 + g t.1) +
          (Finset.univ.sum fun s : S => f s + g s) =
        (f t.1 + Finset.univ.sum f) + (g t.1 + Finset.univ.sum g)
      rw [Finset.sum_add_distrib]
      abel
  map_smul' r f := by
    apply Prod.ext
    · change (∑ s : S, r • f s) = r • ∑ s : S, f s
      exact Finset.smul_sum.symm
    · funext t
      change r • f t.1 + (∑ s : S, r • f s) =
        r • (f t.1 + ∑ s : S, f s)
      rw [← Finset.smul_sum, smul_add]

private noncomputable def pointedSrcOddValueBuild
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V] :
    PointedOddValueCoords S V s0 →ₗ[F] (S → V) where
  toFun x := fun s =>
    if hs : s = s0 then x.1 + ∑ t, x.2 t else x.2 ⟨s, hs⟩ + x.1
  map_add' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs, Finset.sum_add_distrib]
      abel
    · simp [hs]
      abel
  map_smul' r x := by
    funext s
    by_cases hs : s = s0
    · simp [hs, Finset.smul_sum, smul_add]
    · simp [hs, smul_add]

private theorem pointedSrcOddValueBuild_at_point
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (x : PointedOddValueCoords S V s0) :
    pointedSrcOddValueBuild S V s0 x s0 = x.1 + ∑ t, x.2 t := by
  simp [pointedSrcOddValueBuild]

private theorem pointedSrcOddValueBuild_at_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (x : PointedOddValueCoords S V s0) (t : PointedTail S s0) :
    pointedSrcOddValueBuild S V s0 x t.1 = x.2 t + x.1 := by
  change
    (if hs : t.1 = s0 then x.1 + ∑ u, x.2 u else x.2 ⟨t.1, hs⟩ + x.1) =
      x.2 t + x.1
  rw [dif_neg t.2]

private theorem pointedSrcOddValueBuild_sum
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S))
    (x : PointedOddValueCoords S V s0) :
    (∑ s, pointedSrcOddValueBuild S V s0 x s) = x.1 := by
  rw [sum_eq_at_point_add_tail_value]
  rw [pointedSrcOddValueBuild_at_point]
  simp_rw [pointedSrcOddValueBuild_at_tail]
  rw [Finset.sum_add_distrib, oddTail_sum_const_zero_value s0 hodd]
  simp only [add_zero]
  calc
    x.1 + ∑ t, x.2 t + ∑ t, x.2 t =
        x.1 + ((∑ t, x.2 t) + ∑ t, x.2 t) := by abel
    _ = x.1 := by rw [value_add_self, add_zero]

private theorem pointedSrcOddValueRead_build
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S))
    (x : PointedOddValueCoords S V s0) :
    pointedSrcOddValueRead S V s0
        (pointedSrcOddValueBuild S V s0 x) = x := by
  apply Prod.ext
  · exact pointedSrcOddValueBuild_sum s0 hodd x
  · funext t
    change pointedSrcOddValueBuild S V s0 x t.1 +
      (∑ s : S, pointedSrcOddValueBuild S V s0 x s) = x.2 t
    rw [pointedSrcOddValueBuild_at_tail,
      pointedSrcOddValueBuild_sum s0 hodd, add_assoc, value_add_self]
    simp

private theorem pointedSrcOddValueBuild_read
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (f : S → V) :
    pointedSrcOddValueBuild S V s0
        (pointedSrcOddValueRead S V s0 f) = f := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedSrcOddValueBuild_at_point]
    simp only [pointedSrcOddValueRead, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_add_distrib,
      oddTail_sum_const_zero_value s0 hodd,
      sum_eq_at_point_add_tail_value s0 f]
    simp only [add_zero]
    rw [add_assoc, value_add_self, add_zero]
  · change
      (if h : s = s0 then
          (∑ u : S, f u) +
            ∑ t : PointedTail S s0, (f t.1 + ∑ u : S, f u)
        else (f s + ∑ u : S, f u) + ∑ u : S, f u) = f s
    rw [dif_neg hs, add_assoc, value_add_self, add_zero]

/-- The explicit odd source-coordinate equivalence for `V`-valued
functions. -/
noncomputable def pointedSrcOddValueEquiv
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) :
    (S → V) ≃ₗ[F] PointedOddValueCoords S V s0 where
  toLinearMap := pointedSrcOddValueRead S V s0
  invFun := pointedSrcOddValueBuild S V s0
  left_inv := pointedSrcOddValueBuild_read s0 hodd
  right_inv := pointedSrcOddValueRead_build s0 hodd

@[simp] theorem pointedSrcOddValueEquiv_apply_fst
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (f : S → V) :
    (pointedSrcOddValueEquiv S V s0 hodd f).1 = ∑ s, f s := rfl

@[simp] theorem pointedSrcOddValueEquiv_apply_snd
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (f : S → V)
    (t : PointedTail S s0) :
    (pointedSrcOddValueEquiv S V s0 hodd f).2 t =
      f t.1 + ∑ s, f s := rfl

private noncomputable def pointedDualOddValueRead
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V] :
    (S → V) →ₗ[F] PointedOddValueCoords S V s0 where
  toFun g := (∑ s, g s, fun t => g t.1 + g s0)
  map_add' f g := by
    apply Prod.ext
    · change (Finset.univ.sum fun s : S => f s + g s) =
        Finset.univ.sum f + Finset.univ.sum g
      rw [Finset.sum_add_distrib]
    · funext t
      change (f t.1 + g t.1) + (f s0 + g s0) =
        (f t.1 + f s0) + (g t.1 + g s0)
      abel
  map_smul' r g := by
    apply Prod.ext
    · change (∑ s : S, r • g s) = r • ∑ s : S, g s
      exact Finset.smul_sum.symm
    · funext t
      change r • g t.1 + r • g s0 = r • (g t.1 + g s0)
      rw [smul_add]

private noncomputable def pointedDualOddValueBuild
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V] :
    PointedOddValueCoords S V s0 →ₗ[F] (S → V) where
  toFun x :=
    let g0 := x.1 + ∑ t, x.2 t
    fun s => if hs : s = s0 then g0 else x.2 ⟨s, hs⟩ + g0
  map_add' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs, Finset.sum_add_distrib]
      abel
    · simp [hs, Finset.sum_add_distrib]
      abel
  map_smul' r x := by
    funext s
    by_cases hs : s = s0
    · simp [hs, Finset.smul_sum, smul_add]
    · simp [hs, Finset.smul_sum, smul_add]

private theorem pointedDualOddValueBuild_at_point
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (x : PointedOddValueCoords S V s0) :
    pointedDualOddValueBuild S V s0 x s0 = x.1 + ∑ t, x.2 t := by
  simp [pointedDualOddValueBuild]

private theorem pointedDualOddValueBuild_at_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (x : PointedOddValueCoords S V s0) (t : PointedTail S s0) :
    pointedDualOddValueBuild S V s0 x t.1 =
      x.2 t + (x.1 + ∑ u, x.2 u) := by
  change
    (if hs : t.1 = s0 then x.1 + ∑ u, x.2 u
      else x.2 ⟨t.1, hs⟩ + (x.1 + ∑ u, x.2 u)) =
        x.2 t + (x.1 + ∑ u, x.2 u)
  rw [dif_neg t.2]

private theorem pointedDualOddValueBuild_sum
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S))
    (x : PointedOddValueCoords S V s0) :
    (∑ s, pointedDualOddValueBuild S V s0 x s) = x.1 := by
  rw [sum_eq_at_point_add_tail_value]
  rw [pointedDualOddValueBuild_at_point]
  simp_rw [pointedDualOddValueBuild_at_tail]
  rw [Finset.sum_add_distrib, oddTail_sum_const_zero_value s0 hodd]
  simp only [add_zero]
  calc
    x.1 + ∑ t, x.2 t + ∑ t, x.2 t =
        x.1 + ((∑ t, x.2 t) + ∑ t, x.2 t) := by abel
    _ = x.1 := by rw [value_add_self, add_zero]

private theorem pointedDualOddValueRead_build
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S))
    (x : PointedOddValueCoords S V s0) :
    pointedDualOddValueRead S V s0
        (pointedDualOddValueBuild S V s0 x) = x := by
  apply Prod.ext
  · exact pointedDualOddValueBuild_sum s0 hodd x
  · funext t
    change pointedDualOddValueBuild S V s0 x t.1 +
      pointedDualOddValueBuild S V s0 x s0 = x.2 t
    rw [pointedDualOddValueBuild_at_tail,
      pointedDualOddValueBuild_at_point, add_assoc, value_add_self]
    simp

private theorem pointedDualOddValueRead_point_reconstruct
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (g : S → V) :
    (pointedDualOddValueRead S V s0 g).1 +
        ∑ t, (pointedDualOddValueRead S V s0 g).2 t = g s0 := by
  simp only [pointedDualOddValueRead, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_add_distrib,
    oddTail_sum_const_zero_value s0 hodd,
    sum_eq_at_point_add_tail_value s0 g]
  simp only [add_zero]
  rw [add_assoc, value_add_self, add_zero]

private theorem pointedDualOddValueBuild_read
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (g : S → V) :
    pointedDualOddValueBuild S V s0
        (pointedDualOddValueRead S V s0 g) = g := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedDualOddValueBuild_at_point]
    exact pointedDualOddValueRead_point_reconstruct s0 hodd g
  · let t : PointedTail S s0 := ⟨s, hs⟩
    change pointedDualOddValueBuild S V s0
        (pointedDualOddValueRead S V s0 g) t.1 = g s
    rw [pointedDualOddValueBuild_at_tail]
    change (g s + g s0) +
      ((pointedDualOddValueRead S V s0 g).1 +
        ∑ u, (pointedDualOddValueRead S V s0 g).2 u) = g s
    rw [pointedDualOddValueRead_point_reconstruct s0 hodd g,
      add_assoc, value_add_self, add_zero]

/-- The explicit odd dual-coordinate equivalence for `V`-valued
functions. -/
noncomputable def pointedDualOddValueEquiv
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) :
    (S → V) ≃ₗ[F] PointedOddValueCoords S V s0 where
  toLinearMap := pointedDualOddValueRead S V s0
  invFun := pointedDualOddValueBuild S V s0
  left_inv := pointedDualOddValueBuild_read s0 hodd
  right_inv := pointedDualOddValueRead_build s0 hodd

@[simp] theorem pointedDualOddValueEquiv_apply_fst
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (g : S → V) :
    (pointedDualOddValueEquiv S V s0 hodd g).1 = ∑ s, g s := rfl

@[simp] theorem pointedDualOddValueEquiv_apply_snd
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (g : S → V)
    (t : PointedTail S s0) :
    (pointedDualOddValueEquiv S V s0 hodd g).2 t =
      g t.1 + g s0 := rfl

/-- The genuine source-to-dual twist on a vector-valued pointed tail. -/
noncomputable def oddValueTailJ
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V] :
    (PointedTail S s0 → V) →ₗ[F] (PointedTail S s0 → V) where
  toFun u := fun t => u t + ∑ v, u v
  map_add' u v := by
    funext t
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    abel
  map_smul' r u := by
    funext t
    simp only [Pi.smul_apply]
    rw [← Finset.smul_sum, smul_add]
    rfl

@[simp] theorem oddValueTailJ_apply
    (S V : Type*) [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (u : PointedTail S s0 → V) (t : PointedTail S s0) :
    oddValueTailJ S V s0 u t = u t + ∑ v, u v := rfl

private theorem oddValueTailJ_sum
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S))
    (u : PointedTail S s0 → V) :
    (∑ t, oddValueTailJ S V s0 u t) = ∑ t, u t := by
  simp only [oddValueTailJ_apply]
  rw [Finset.sum_add_distrib,
    oddTail_sum_const_zero_value s0 hodd, add_zero]

@[simp] theorem oddValueTailJ_sq_apply
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S))
    (u : PointedTail S s0 → V) :
    oddValueTailJ S V s0 (oddValueTailJ S V s0 u) = u := by
  funext t
  rw [oddValueTailJ_apply, oddValueTailJ_apply,
    oddValueTailJ_sum s0 hodd, add_assoc, value_add_self, add_zero]

/-- Source tail, followed by `J`, is the dual tail. -/
theorem pointedDualOddValue_tail_eq_oddValueTailJ_source
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S)) (g : S → V) :
    (pointedDualOddValueEquiv S V s0 hodd g).2 =
      oddValueTailJ S V s0
        (pointedSrcOddValueEquiv S V s0 hodd g).2 := by
  funext t
  simp only [pointedDualOddValueEquiv_apply_snd,
    oddValueTailJ_apply, pointedSrcOddValueEquiv_apply_snd]
  rw [Finset.sum_add_distrib,
    oddTail_sum_const_zero_value s0 hodd]
  simp only [add_zero]
  rw [sum_eq_at_point_add_tail_value s0 g]
  symm
  change
    g t.1 + (g s0 + ∑ v : PointedTail S s0, g v.1) +
        ∑ v : PointedTail S s0, g v.1 =
      g t.1 + g s0
  rw [add_assoc, add_assoc, value_add_self, add_zero]

/-- Pointwise bilinear pairing in odd source coordinates.  The second tail
coordinate is genuinely `J`-twisted. -/
theorem pointedOddValue_pairing_source_J
    {S V : Type*} [Fintype S] (s0 : S)
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card S))
    (beta : V →ₗ[F] V →ₗ[F] F) (f g : S → V) :
    (∑ s, beta (f s) (g s)) =
      beta
          (pointedSrcOddValueEquiv S V s0 hodd f).1
          (pointedSrcOddValueEquiv S V s0 hodd g).1
        +
      ∑ t,
        beta
          ((pointedSrcOddValueEquiv S V s0 hodd f).2 t)
          (oddValueTailJ S V s0
            (pointedSrcOddValueEquiv S V s0 hodd g).2 t) := by
  rw [← pointedDualOddValue_tail_eq_oddValueTailJ_source s0 hodd g]
  simp only [pointedSrcOddValueEquiv_apply_fst,
    pointedSrcOddValueEquiv_apply_snd,
    pointedDualOddValueEquiv_apply_snd]
  rw [sum_eq_at_point_add_tail_value s0
    (fun s => beta (f s) (g s))]
  simp_rw [map_add, LinearMap.add_apply]
  repeat' rw [Finset.sum_add_distrib]
  have hft :
      (∑ t : PointedTail S s0, beta (f t.1) (g s0)) =
        beta (∑ t : PointedTail S s0, f t.1) (g s0) := by
    exact
      (map_sum ((LinearMap.flip beta) (g s0))
        (fun t : PointedTail S s0 => f t.1) Finset.univ).symm
  rw [hft, oddTail_sum_const_zero_value s0 hodd]
  simp only [add_zero]
  have hSg :
      (∑ t : PointedTail S s0, beta (∑ s : S, f s) (g t.1)) =
        beta (∑ s : S, f s)
          (∑ t : PointedTail S s0, g t.1) :=
    (map_sum (beta (∑ s : S, f s))
      (fun t : PointedTail S s0 => g t.1) Finset.univ).symm
  rw [hSg]
  rw [sum_eq_at_point_add_tail_value s0 f,
    sum_eq_at_point_add_tail_value s0 g]
  simp_rw [map_add, LinearMap.add_apply]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

/-- The passive axis of every odd block has odd cardinality, including the
empty internal tail. -/
theorem odd_card_PVec
    {n k : Nat} [NeZero n] (hn : Odd n) :
    Odd (Fintype.card (PVec n k)) := by
  rw [card_vec]
  exact hn.pow

/-- Odd source coordinates specialized to a passive vector axis. -/
noncomputable def diamondOddAxisSrcCoordEquiv
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) :
    (PVec n k → V) ≃ₗ[F]
      PointedOddValueCoords (PVec n k) V (zeroVec : PVec n k) :=
  pointedSrcOddValueEquiv
    (PVec n k) V (zeroVec : PVec n k) (odd_card_PVec hn)

/-- Odd dual coordinates specialized to a passive vector axis. -/
noncomputable def diamondOddAxisDualCoordEquiv
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) :
    (PVec n k → V) ≃ₗ[F]
      PointedOddValueCoords (PVec n k) V (zeroVec : PVec n k) :=
  pointedDualOddValueEquiv
    (PVec n k) V (zeroVec : PVec n k) (odd_card_PVec hn)

/-- Split the first coordinate of a positive-length vector. -/
noncomputable def diamondOddVecHeadTailEquiv
    {n k : Nat} [NeZero n] (hk : 0 < k) :
    Vec n k ≃ I n × PVec n k := by
  simpa [PVec, Nat.sub_add_cancel hk] using vecSuccEquiv n (k - 1)

@[simp] theorem diamondOddVecHeadTailEquiv_apply
    {n k : Nat} [NeZero n] (hk : 0 < k) (v : Vec n k) :
    diamondOddVecHeadTailEquiv hk v =
      (v ⟨0, hk⟩, fun q : Fin (k - 1) =>
        v ⟨q.1 + 1, by omega⟩) := by
  cases k with
  | zero => omega
  | succ k => rfl

@[simp] theorem diamondOddVecHeadTailEquiv_symm_apply_head
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (head : I n) (tail : PVec n k) :
    ((diamondOddVecHeadTailEquiv hk).symm (head, tail)) ⟨0, hk⟩ =
      head := by
  have h := congrArg Prod.fst
    ((diamondOddVecHeadTailEquiv hk).apply_symm_apply (head, tail))
  simpa only [diamondOddVecHeadTailEquiv_apply] using h

@[simp] theorem diamondOddVecHeadTailEquiv_symm_apply_tail
    {n k : Nat} [NeZero n] (hk : 0 < k)
    (head : I n) (tail : PVec n k) (q : Fin (k - 1)) :
    ((diamondOddVecHeadTailEquiv hk).symm (head, tail))
        ⟨q.1 + 1, by omega⟩ =
      tail q := by
  have h := congrArg Prod.snd
    ((diamondOddVecHeadTailEquiv hk).apply_symm_apply (head, tail))
  have hq := congrFun h q
  simpa only [diamondOddVecHeadTailEquiv_apply] using hq

/-- Literal `B` reindexed as passive `P/Z/W` tails and one cyclic cube. -/
noncomputable def diamondOddBPassiveCubeEquiv
    {n a c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    BFun4 n a c d ≃ₗ[F]
      (PVec n a → PVec n c → PVec n d → CyclicCube n) where
  toFun B p zt wt i j k :=
    B p i
      ((diamondOddVecHeadTailEquiv hc).symm (j, zt))
      ((diamondOddVecHeadTailEquiv hd).symm (k, wt))
  invFun G p i z w :=
    G p
      (diamondOddVecHeadTailEquiv hc z).2
      (diamondOddVecHeadTailEquiv hd w).2
      i
      (diamondOddVecHeadTailEquiv hc z).1
      (diamondOddVecHeadTailEquiv hd w).1
  left_inv B := by
    funext p i z w
    change
      B p i
          ((diamondOddVecHeadTailEquiv hc).symm
            (diamondOddVecHeadTailEquiv hc z))
          ((diamondOddVecHeadTailEquiv hd).symm
            (diamondOddVecHeadTailEquiv hd w)) =
        B p i z w
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv G := by
    funext p zt wt i j k
    simp
  map_add' B B' := rfl
  map_smul' r B := rfl

@[simp] theorem diamondOddBPassiveCubeEquiv_apply
    {n a c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n a c d)
    (p : PVec n a) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    diamondOddBPassiveCubeEquiv hc hd B p zt wt i j k =
      B p i
        ((diamondOddVecHeadTailEquiv hc).symm (j, zt))
        ((diamondOddVecHeadTailEquiv hd).symm (k, wt)) := rfl

@[simp] theorem diamondOddBPassiveCubeEquiv_symm_apply
    {n a c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (G : PVec n a → PVec n c → PVec n d → CyclicCube n)
    (p : PVec n a) (i : I n) (z : ZVec n c) (w : WVec n d) :
    (diamondOddBPassiveCubeEquiv hc hd).symm G p i z w =
      G p
        (diamondOddVecHeadTailEquiv hc z).2
        (diamondOddVecHeadTailEquiv hd w).2
        i
        (diamondOddVecHeadTailEquiv hc z).1
        (diamondOddVecHeadTailEquiv hd w).1 := rfl

/-- Literal `W` reindexed as passive `P/Y/Z` tails and one cyclic cube. -/
noncomputable def diamondOddWPassiveCubeEquiv
    {n a b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    WFun4 n a b c ≃ₗ[F]
      (PVec n a → PVec n b → PVec n c → CyclicCube n) where
  toFun W p yt zt i j k :=
    W p
      ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
      ((diamondOddVecHeadTailEquiv hc).symm (j, zt))
      k
  invFun G p y z k :=
    G p
      (diamondOddVecHeadTailEquiv hb y).2
      (diamondOddVecHeadTailEquiv hc z).2
      (diamondOddVecHeadTailEquiv hb y).1
      (diamondOddVecHeadTailEquiv hc z).1
      k
  left_inv W := by
    funext p y z k
    change
      W p
          ((diamondOddVecHeadTailEquiv hb).symm
            (diamondOddVecHeadTailEquiv hb y))
          ((diamondOddVecHeadTailEquiv hc).symm
            (diamondOddVecHeadTailEquiv hc z))
          k =
        W p y z k
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv G := by
    funext p yt zt i j k
    simp
  map_add' W W' := rfl
  map_smul' r W := rfl

@[simp] theorem diamondOddWPassiveCubeEquiv_apply
    {n a b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (W : WFun4 n a b c)
    (p : PVec n a) (yt : PVec n b) (zt : PVec n c)
    (i j k : I n) :
    diamondOddWPassiveCubeEquiv hb hc W p yt zt i j k =
      W p
        ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
        ((diamondOddVecHeadTailEquiv hc).symm (j, zt))
        k := rfl

@[simp] theorem diamondOddWPassiveCubeEquiv_symm_apply
    {n a b c : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (G : PVec n a → PVec n b → PVec n c → CyclicCube n)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (k : I n) :
    (diamondOddWPassiveCubeEquiv hb hc).symm G p y z k =
      G p
        (diamondOddVecHeadTailEquiv hb y).2
        (diamondOddVecHeadTailEquiv hc z).2
        (diamondOddVecHeadTailEquiv hb y).1
        (diamondOddVecHeadTailEquiv hc z).1
        k := rfl

/-- Literal `A` reindexed as passive `Y/Z/W` tails and one cyclic cube. -/
noncomputable def diamondOddAPassiveCubeEquiv
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    AFun4 n b c d ≃ₗ[F]
      (PVec n b → PVec n c → PVec n d → CyclicCube n) where
  toFun A yt zt wt i j k :=
    A
      ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
      ((diamondOddVecHeadTailEquiv hc).symm (j, zt))
      ((diamondOddVecHeadTailEquiv hd).symm (k, wt))
  invFun G y z w :=
    G
      (diamondOddVecHeadTailEquiv hb y).2
      (diamondOddVecHeadTailEquiv hc z).2
      (diamondOddVecHeadTailEquiv hd w).2
      (diamondOddVecHeadTailEquiv hb y).1
      (diamondOddVecHeadTailEquiv hc z).1
      (diamondOddVecHeadTailEquiv hd w).1
  left_inv A := by
    funext y z w
    change
      A
          ((diamondOddVecHeadTailEquiv hb).symm
            (diamondOddVecHeadTailEquiv hb y))
          ((diamondOddVecHeadTailEquiv hc).symm
            (diamondOddVecHeadTailEquiv hc z))
          ((diamondOddVecHeadTailEquiv hd).symm
            (diamondOddVecHeadTailEquiv hd w)) =
        A y z w
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply]
  right_inv G := by
    funext yt zt wt i j k
    simp
  map_add' A A' := rfl
  map_smul' r A := rfl

@[simp] theorem diamondOddAPassiveCubeEquiv_apply
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n b c d)
    (yt : PVec n b) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    diamondOddAPassiveCubeEquiv hb hc hd A yt zt wt i j k =
      A
        ((diamondOddVecHeadTailEquiv hb).symm (i, yt))
        ((diamondOddVecHeadTailEquiv hc).symm (j, zt))
        ((diamondOddVecHeadTailEquiv hd).symm (k, wt)) := rfl

@[simp] theorem diamondOddAPassiveCubeEquiv_symm_apply
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (G : PVec n b → PVec n c → PVec n d → CyclicCube n)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    (diamondOddAPassiveCubeEquiv hb hc hd).symm G y z w =
      G
        (diamondOddVecHeadTailEquiv hb y).2
        (diamondOddVecHeadTailEquiv hc z).2
        (diamondOddVecHeadTailEquiv hd w).2
        (diamondOddVecHeadTailEquiv hb y).1
        (diamondOddVecHeadTailEquiv hc z).1
        (diamondOddVecHeadTailEquiv hd w).1 := rfl

end

end Core4loop.SquareDiagonal.DirectWitt
