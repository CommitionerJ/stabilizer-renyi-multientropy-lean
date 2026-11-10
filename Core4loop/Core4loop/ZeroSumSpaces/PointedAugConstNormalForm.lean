import Core4loop.Basic

open scoped BigOperators

namespace Core4loop

noncomputable section

local instance (S : Type*) : DecidableEq S := Classical.decEq S

/-- The explicit complement of a chosen point. -/
abbrev PointedTail (S : Type*) (s0 : S) := {s : S // s ≠ s0}

/-- Summation on the pointed tail. -/
noncomputable def pointedTailSum (S : Type*) [Fintype S] (s0 : S) :
    (PointedTail S s0 → F) →ₗ[F] F where
  toFun k := ∑ t, k t
  map_add' k l := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' x k := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

/-- Zero-sum functions on the explicit complement of the chosen point. -/
noncomputable abbrev PointedTailZero (S : Type*) [Fintype S] (s0 : S) :=
  LinearMap.ker (pointedTailSum S s0)

private lemma sum_eq_at_point_add_tail
    {S : Type*} [Fintype S] (s0 : S) (f : S → F) :
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

lemma card_pointedTail
    {S : Type*} [Fintype S] (s0 : S) :
    Fintype.card (PointedTail S s0) = Fintype.card S - 1 := by
  classical
  calc
    Fintype.card (PointedTail S s0) =
        Fintype.card S - Fintype.card {s : S // s = s0} := by
          simpa [PointedTail] using
            (Fintype.card_subtype_compl (fun s : S => s = s0))
    _ = Fintype.card S - 1 := by
          rw [Fintype.card_subtype_eq s0]

private lemma cast_card_eq_zero_of_even
    {m : ℕ} (hm : Even m) : (m : F) = 0 := by
  rcases hm with ⟨k, hk⟩
  rw [hk]
  push_cast
  exact F_add_self _

private lemma cast_card_eq_one_of_odd
    {m : ℕ} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨k, hk⟩
  rw [hk]
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private lemma sum_const_eq_card_mul
    {S : Type*} [Fintype S] (x : F) :
    (∑ _ : S, x) = (Fintype.card S : F) * x := by
  simp [nsmul_eq_mul]

private lemma pointedTail_even_of_card_odd
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) :
    Even (Fintype.card (PointedTail S s0)) := by
  rcases hodd with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [card_pointedTail, hk]
  omega

private lemma pointedTail_odd_of_card_even
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) :
    Odd (Fintype.card (PointedTail S s0)) := by
  letI : Nonempty S := ⟨s0⟩
  rcases heven with ⟨k, hk⟩
  have hpos : 0 < Fintype.card S := Fintype.card_pos
  refine ⟨k - 1, ?_⟩
  rw [card_pointedTail, hk]
  omega

private lemma sum_tail_const_of_card_odd
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (x : F) :
    (∑ _ : PointedTail S s0, x) = 0 := by
  rw [sum_const_eq_card_mul,
    cast_card_eq_zero_of_even (pointedTail_even_of_card_odd s0 hodd)]
  simp

private lemma sum_tail_const_of_card_even
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (x : F) :
    (∑ _ : PointedTail S s0, x) = x := by
  rw [sum_const_eq_card_mul,
    cast_card_eq_one_of_odd (pointedTail_odd_of_card_even s0 heven)]
  simp

private lemma sum_all_const_of_card_odd
    {S : Type*} [Fintype S]
    (hodd : Odd (Fintype.card S)) (x : F) :
    (∑ _ : S, x) = x := by
  rw [sum_const_eq_card_mul, cast_card_eq_one_of_odd hodd]
  simp

private lemma sum_all_const_of_card_even
    {S : Type*} [Fintype S]
    (heven : Even (Fintype.card S)) (x : F) :
    (∑ _ : S, x) = 0 := by
  rw [sum_const_eq_card_mul, cast_card_eq_zero_of_even heven]
  simp

/-- Odd-cardinality source coordinates: augmentation and its shifted tail. -/
noncomputable def pointedSrcOddRead
    (S : Type*) [Fintype S] (s0 : S) :
    (S → F) →ₗ[F] F × (PointedTail S s0 → F) where
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
  map_smul' x f := by
    apply Prod.ext
    · change (∑ s : S, x * f s) = x * ∑ s : S, f s
      rw [← Finset.mul_sum]
    · funext t
      change x * f t.1 + (∑ s : S, x * f s) =
        x * (f t.1 + ∑ s : S, f s)
      rw [← Finset.mul_sum]
      ring

/-- Explicit build map inverse to `pointedSrcOddRead` at odd cardinality. -/
noncomputable def pointedSrcOddBuild
    (S : Type*) [Fintype S] (s0 : S) :
    (F × (PointedTail S s0 → F)) →ₗ[F] (S → F) where
  toFun x := fun s =>
    if hs : s = s0 then x.1 + ∑ t, x.2 t else x.2 ⟨s, hs⟩ + x.1
  map_add' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs, Finset.sum_add_distrib]
      abel
    · simp [hs]
      abel
  map_smul' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs]
      rw [← Finset.mul_sum]
      ring
    · simp [hs]
      ring

@[simp] lemma pointedSrcOddBuild_at_point
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (PointedTail S s0 → F)) :
    pointedSrcOddBuild S s0 x s0 = x.1 + ∑ t, x.2 t := by
  simp [pointedSrcOddBuild]

@[simp] lemma pointedSrcOddBuild_at_tail
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (PointedTail S s0 → F)) (t : PointedTail S s0) :
    pointedSrcOddBuild S s0 x t.1 = x.2 t + x.1 := by
  change
    (if hs : t.1 = s0 then x.1 + ∑ u, x.2 u else x.2 ⟨t.1, hs⟩ + x.1) =
      x.2 t + x.1
  rw [dif_neg t.2]

lemma pointedSrcOddBuild_sum
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S))
    (x : F × (PointedTail S s0 → F)) :
    (∑ s, pointedSrcOddBuild S s0 x s) = x.1 := by
  rw [sum_eq_at_point_add_tail]
  rw [pointedSrcOddBuild_at_point]
  simp_rw [pointedSrcOddBuild_at_tail]
  rw [Finset.sum_add_distrib, sum_tail_const_of_card_odd s0 hodd]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

lemma pointedSrcOddRead_build
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S))
    (x : F × (PointedTail S s0 → F)) :
    pointedSrcOddRead S s0 (pointedSrcOddBuild S s0 x) = x := by
  apply Prod.ext
  · exact pointedSrcOddBuild_sum s0 hodd x
  · funext t
    change pointedSrcOddBuild S s0 x t.1 +
      (∑ s : S, pointedSrcOddBuild S s0 x s) = x.2 t
    rw [pointedSrcOddBuild_at_tail, pointedSrcOddBuild_sum s0 hodd,
      add_assoc, F_add_self]
    simp

lemma pointedSrcOddBuild_read
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (f : S → F) :
    pointedSrcOddBuild S s0 (pointedSrcOddRead S s0 f) = f := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedSrcOddBuild_at_point]
    simp only [pointedSrcOddRead, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_add_distrib, sum_tail_const_of_card_odd s0 hodd,
      sum_eq_at_point_add_tail s0 f]
    ring_nf
    rw [show (2 : F) = 0 by decide]
    simp
  · change
      (if h : s = s0 then
          (∑ u : S, f u) +
            ∑ t : PointedTail S s0, (f t.1 + ∑ u : S, f u)
        else (f s + ∑ u : S, f u) + ∑ u : S, f u) = f s
    rw [dif_neg hs, add_assoc, F_add_self]
    simp

/-- The explicit odd-cardinality source linear equivalence. -/
noncomputable def pointedSrcOddEquiv
    (S : Type*) [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) :
    (S → F) ≃ₗ[F] F × (PointedTail S s0 → F) where
  toFun := pointedSrcOddRead S s0
  invFun := pointedSrcOddBuild S s0
  left_inv := pointedSrcOddBuild_read s0 hodd
  right_inv := pointedSrcOddRead_build s0 hodd
  map_add' := (pointedSrcOddRead S s0).map_add
  map_smul' := (pointedSrcOddRead S s0).map_smul

/-- Odd-cardinality dual coordinates: augmentation and difference from the point. -/
noncomputable def pointedDualOddRead
    (S : Type*) [Fintype S] (s0 : S) :
    (S → F) →ₗ[F] F × (PointedTail S s0 → F) where
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
  map_smul' x f := by
    apply Prod.ext
    · change (∑ s : S, x * f s) = x * ∑ s : S, f s
      rw [← Finset.mul_sum]
    · funext t
      change x * f t.1 + x * f s0 = x * (f t.1 + f s0)
      ring

/-- Explicit build map inverse to `pointedDualOddRead` at odd cardinality. -/
noncomputable def pointedDualOddBuild
    (S : Type*) [Fintype S] (s0 : S) :
    (F × (PointedTail S s0 → F)) →ₗ[F] (S → F) where
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
  map_smul' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs]
      rw [← Finset.mul_sum]
      ring
    · simp [hs]
      rw [← Finset.mul_sum]
      ring

@[simp] lemma pointedDualOddBuild_at_point
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (PointedTail S s0 → F)) :
    pointedDualOddBuild S s0 x s0 = x.1 + ∑ t, x.2 t := by
  simp [pointedDualOddBuild]

@[simp] lemma pointedDualOddBuild_at_tail
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (PointedTail S s0 → F)) (t : PointedTail S s0) :
    pointedDualOddBuild S s0 x t.1 =
      x.2 t + (x.1 + ∑ u, x.2 u) := by
  change
    (if hs : t.1 = s0 then x.1 + ∑ u, x.2 u
      else x.2 ⟨t.1, hs⟩ + (x.1 + ∑ u, x.2 u)) =
        x.2 t + (x.1 + ∑ u, x.2 u)
  rw [dif_neg t.2]

lemma pointedDualOddBuild_sum
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S))
    (x : F × (PointedTail S s0 → F)) :
    (∑ s, pointedDualOddBuild S s0 x s) = x.1 := by
  rw [sum_eq_at_point_add_tail]
  rw [pointedDualOddBuild_at_point]
  simp_rw [pointedDualOddBuild_at_tail]
  rw [Finset.sum_add_distrib, sum_tail_const_of_card_odd s0 hodd]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

lemma pointedDualOddRead_build
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S))
    (x : F × (PointedTail S s0 → F)) :
    pointedDualOddRead S s0 (pointedDualOddBuild S s0 x) = x := by
  apply Prod.ext
  · exact pointedDualOddBuild_sum s0 hodd x
  · funext t
    change pointedDualOddBuild S s0 x t.1 +
      pointedDualOddBuild S s0 x s0 = x.2 t
    rw [pointedDualOddBuild_at_tail, pointedDualOddBuild_at_point,
      add_assoc, F_add_self]
    simp

lemma pointedDualOddRead_point_reconstruct
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (g : S → F) :
    (pointedDualOddRead S s0 g).1 +
        ∑ t, (pointedDualOddRead S s0 g).2 t = g s0 := by
  simp only [pointedDualOddRead, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ s : S, g s) +
    ∑ t : PointedTail S s0, (g t.1 + g s0) = g s0
  rw [Finset.sum_add_distrib, sum_tail_const_of_card_odd s0 hodd,
    sum_eq_at_point_add_tail s0 g]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

lemma pointedDualOddBuild_read
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (g : S → F) :
    pointedDualOddBuild S s0 (pointedDualOddRead S s0 g) = g := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedDualOddBuild_at_point]
    exact pointedDualOddRead_point_reconstruct s0 hodd g
  · let t : PointedTail S s0 := ⟨s, hs⟩
    change pointedDualOddBuild S s0 (pointedDualOddRead S s0 g) t.1 = g s
    rw [pointedDualOddBuild_at_tail]
    change (g s + g s0) +
      ((pointedDualOddRead S s0 g).1 +
        ∑ u, (pointedDualOddRead S s0 g).2 u) = g s
    rw [pointedDualOddRead_point_reconstruct s0 hodd g, add_assoc, F_add_self]
    simp

/-- The explicit odd-cardinality dual linear equivalence. -/
noncomputable def pointedDualOddEquiv
    (S : Type*) [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) :
    (S → F) ≃ₗ[F] F × (PointedTail S s0 → F) where
  toFun := pointedDualOddRead S s0
  invFun := pointedDualOddBuild S s0
  left_inv := pointedDualOddBuild_read s0 hodd
  right_inv := pointedDualOddRead_build s0 hodd
  map_add' := (pointedDualOddRead S s0).map_add
  map_smul' := (pointedDualOddRead S s0).map_smul

@[simp] lemma pointedSrcOddEquiv_apply_fst
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (f : S → F) :
    (pointedSrcOddEquiv S s0 hodd f).1 = ∑ s, f s := rfl

@[simp] lemma pointedDualOddEquiv_apply_fst
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (g : S → F) :
    (pointedDualOddEquiv S s0 hodd g).1 = ∑ s, g s := rfl

@[simp] lemma pointedSrcOddEquiv_const
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (x : F) :
    pointedSrcOddEquiv S s0 hodd (fun _ => x) = (x, 0) := by
  apply Prod.ext
  · exact sum_all_const_of_card_odd hodd x
  · funext t
    simp [pointedSrcOddEquiv, pointedSrcOddRead,
      sum_all_const_of_card_odd hodd]
    exact F_add_self x

@[simp] lemma pointedDualOddEquiv_const
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (x : F) :
    pointedDualOddEquiv S s0 hodd (fun _ => x) = (x, 0) := by
  apply Prod.ext
  · exact sum_all_const_of_card_odd hodd x
  · funext t
    simp [pointedDualOddEquiv, pointedDualOddRead]
    exact F_add_self x

theorem pointedOdd_pairing
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (f g : S → F) :
    (∑ s, f s * g s) =
      (pointedSrcOddEquiv S s0 hodd f).1 *
          (pointedDualOddEquiv S s0 hodd g).1 +
        ∑ t,
          (pointedSrcOddEquiv S s0 hodd f).2 t *
            (pointedDualOddEquiv S s0 hodd g).2 t := by
  rw [sum_eq_at_point_add_tail s0 (fun s => f s * g s)]
  simp only [pointedSrcOddEquiv, pointedDualOddEquiv,
    pointedSrcOddRead, pointedDualOddRead, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [add_mul, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_tail_const_of_card_odd s0 hodd]
  rw [sum_eq_at_point_add_tail (s0 := s0) f,
    sum_eq_at_point_add_tail (s0 := s0) g]
  ring_nf
  simp [show (2 : F) = 0 by decide]

@[simp] lemma pointedTailZero_sum
    {S : Type*} [Fintype S] {s0 : S}
    (k : PointedTailZero S s0) :
    (∑ t, k.1 t) = 0 := by
  exact LinearMap.mem_ker.mp k.2

/-- Even-cardinality source coordinates `(sum, constant, zero-sum tail)`. -/
noncomputable def pointedSrcEvenRead
    (S : Type*) [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) :
    (S → F) →ₗ[F] F × (F × PointedTailZero S s0) where
  toFun f :=
    let b := ∑ t : PointedTail S s0, f t.1
    (∑ s, f s,
      (b, ⟨fun t => f t.1 + b, by
        apply LinearMap.mem_ker.mpr
        simp only [pointedTailSum, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_add_distrib, sum_tail_const_of_card_even s0 heven]
        exact F_add_self b⟩))
  map_add' f g := by
    apply Prod.ext
    · change (Finset.univ.sum fun s : S => f s + g s) =
        Finset.univ.sum f + Finset.univ.sum g
      rw [Finset.sum_add_distrib]
    · apply Prod.ext
      · change
          (Finset.univ.sum fun t : PointedTail S s0 => f t.1 + g t.1) =
            (∑ t : PointedTail S s0, f t.1) +
              ∑ t : PointedTail S s0, g t.1
        rw [Finset.sum_add_distrib]
      · apply Subtype.ext
        funext t
        change (f t.1 + g t.1) +
            (Finset.univ.sum fun u : PointedTail S s0 => f u.1 + g u.1) =
          (f t.1 + Finset.univ.sum fun u : PointedTail S s0 => f u.1) +
            (g t.1 + Finset.univ.sum fun u : PointedTail S s0 => g u.1)
        rw [Finset.sum_add_distrib]
        abel
  map_smul' x f := by
    apply Prod.ext
    · change (Finset.univ.sum fun s : S => x * f s) =
        x * Finset.univ.sum f
      rw [← Finset.mul_sum]
    · apply Prod.ext
      · change
          (Finset.univ.sum fun t : PointedTail S s0 => x * f t.1) =
            x * ∑ t : PointedTail S s0, f t.1
        rw [← Finset.mul_sum]
      · apply Subtype.ext
        funext t
        change x * f t.1 +
            (∑ u : PointedTail S s0, x * f u.1) =
          x * (f t.1 + ∑ u : PointedTail S s0, f u.1)
        rw [← Finset.mul_sum]
        ring

/-- Explicit build map for even-cardinality source coordinates. -/
noncomputable def pointedSrcEvenBuild
    (S : Type*) [Fintype S] (s0 : S) :
    (F × (F × PointedTailZero S s0)) →ₗ[F] (S → F) where
  toFun x := fun s =>
    if hs : s = s0 then x.1 + x.2.1 else x.2.2.1 ⟨s, hs⟩ + x.2.1
  map_add' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs]
      abel
    · simp [hs]
      abel
  map_smul' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs]
      ring
    · simp [hs]
      ring

@[simp] lemma pointedSrcEvenBuild_at_point
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (F × PointedTailZero S s0)) :
    pointedSrcEvenBuild S s0 x s0 = x.1 + x.2.1 := by
  simp [pointedSrcEvenBuild]

@[simp] lemma pointedSrcEvenBuild_at_tail
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (F × PointedTailZero S s0))
    (t : PointedTail S s0) :
    pointedSrcEvenBuild S s0 x t.1 = x.2.2.1 t + x.2.1 := by
  change
    (if hs : t.1 = s0 then x.1 + x.2.1
      else x.2.2.1 ⟨t.1, hs⟩ + x.2.1) =
        x.2.2.1 t + x.2.1
  rw [dif_neg t.2]

lemma pointedSrcEvenBuild_sum
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S))
    (x : F × (F × PointedTailZero S s0)) :
    (∑ s, pointedSrcEvenBuild S s0 x s) = x.1 := by
  rw [sum_eq_at_point_add_tail s0 (pointedSrcEvenBuild S s0 x)]
  rw [pointedSrcEvenBuild_at_point]
  simp_rw [pointedSrcEvenBuild_at_tail]
  rw [Finset.sum_add_distrib, pointedTailZero_sum,
    sum_tail_const_of_card_even s0 heven]
  simp only [zero_add]
  rw [add_assoc, F_add_self]
  simp

lemma pointedSrcEvenBuild_tail_sum
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S))
    (x : F × (F × PointedTailZero S s0)) :
    (∑ t : PointedTail S s0, pointedSrcEvenBuild S s0 x t.1) = x.2.1 := by
  simp_rw [pointedSrcEvenBuild_at_tail]
  rw [Finset.sum_add_distrib, pointedTailZero_sum,
    sum_tail_const_of_card_even s0 heven]
  simp

lemma pointedSrcEvenRead_build
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S))
    (x : F × (F × PointedTailZero S s0)) :
    pointedSrcEvenRead S s0 heven (pointedSrcEvenBuild S s0 x) = x := by
  apply Prod.ext
  · exact pointedSrcEvenBuild_sum s0 heven x
  · apply Prod.ext
    · exact pointedSrcEvenBuild_tail_sum s0 heven x
    · apply Subtype.ext
      funext t
      change pointedSrcEvenBuild S s0 x t.1 +
        (∑ u : PointedTail S s0, pointedSrcEvenBuild S s0 x u.1) =
          x.2.2.1 t
      rw [pointedSrcEvenBuild_at_tail,
        pointedSrcEvenBuild_tail_sum s0 heven, add_assoc, F_add_self]
      simp

lemma pointedSrcEvenBuild_read
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (f : S → F) :
    pointedSrcEvenBuild S s0 (pointedSrcEvenRead S s0 heven f) = f := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedSrcEvenBuild_at_point]
    simp only [pointedSrcEvenRead, LinearMap.coe_mk, AddHom.coe_mk]
    rw [sum_eq_at_point_add_tail s0 f, add_assoc, F_add_self]
    simp
  · let t : PointedTail S s0 := ⟨s, hs⟩
    change pointedSrcEvenBuild S s0
      (pointedSrcEvenRead S s0 heven f) t.1 = f s
    rw [pointedSrcEvenBuild_at_tail]
    change (f s + ∑ u : PointedTail S s0, f u.1) +
      ∑ u : PointedTail S s0, f u.1 = f s
    rw [add_assoc, F_add_self]
    simp

/-- The explicit even-cardinality source linear equivalence. -/
noncomputable def pointedSrcEvenEquiv
    (S : Type*) [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) :
    (S → F) ≃ₗ[F] F × (F × PointedTailZero S s0) where
  toFun := pointedSrcEvenRead S s0 heven
  invFun := pointedSrcEvenBuild S s0
  left_inv := pointedSrcEvenBuild_read s0 heven
  right_inv := pointedSrcEvenRead_build s0 heven
  map_add' := (pointedSrcEvenRead S s0 heven).map_add
  map_smul' := (pointedSrcEvenRead S s0 heven).map_smul

/-- The dual sum channel before the zero-sum tail correction. -/
noncomputable def pointedDualEvenD
    (S : Type*) [Fintype S] (s0 : S) :
    (S → F) →ₗ[F] F where
  toFun g := ∑ t : PointedTail S s0, (g t.1 + g s0)
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    change (f t.1 + g t.1) + (f s0 + g s0) =
      (f t.1 + f s0) + (g t.1 + g s0)
    abel
  map_smul' x f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_add]
    rw [← Finset.mul_sum]

/-- The corrected dual tail, explicitly valued in the zero-sum subspace. -/
noncomputable def pointedDualEvenTail
    (S : Type*) [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) :
    (S → F) →ₗ[F] PointedTailZero S s0 where
  toFun g :=
    ⟨fun t => g t.1 + g s0 + pointedDualEvenD S s0 g, by
      apply LinearMap.mem_ker.mpr
      simp only [pointedTailSum, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_tail_const_of_card_even s0 heven,
        sum_tail_const_of_card_even s0 heven]
      simp only [pointedDualEvenD, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_add_distrib,
        sum_tail_const_of_card_even s0 heven]
      exact F_add_self _⟩
  map_add' f g := by
    apply Subtype.ext
    funext t
    change (f t.1 + g t.1) + (f s0 + g s0) +
        pointedDualEvenD S s0 (f + g) =
      (f t.1 + f s0 + pointedDualEvenD S s0 f) +
        (g t.1 + g s0 + pointedDualEvenD S s0 g)
    rw [(pointedDualEvenD S s0).map_add]
    abel
  map_smul' x f := by
    apply Subtype.ext
    funext t
    change x * f t.1 + x * f s0 +
        pointedDualEvenD S s0 (x • f) =
      x * (f t.1 + f s0 + pointedDualEvenD S s0 f)
    rw [(pointedDualEvenD S s0).map_smul]
    simp only [smul_eq_mul]
    ring

/-- Even-cardinality dual coordinates `(constant, sum, zero-sum tail)`. -/
noncomputable def pointedDualEvenRead
    (S : Type*) [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) :
    (S → F) →ₗ[F] F × (F × PointedTailZero S s0) where
  toFun g :=
    (g s0, (pointedDualEvenD S s0 g, pointedDualEvenTail S s0 heven g))
  map_add' f g := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact (pointedDualEvenD S s0).map_add f g
      · exact (pointedDualEvenTail S s0 heven).map_add f g
  map_smul' x f := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact (pointedDualEvenD S s0).map_smul x f
      · exact (pointedDualEvenTail S s0 heven).map_smul x f

/-- Explicit build map for even-cardinality dual coordinates. -/
noncomputable def pointedDualEvenBuild
    (S : Type*) [Fintype S] (s0 : S) :
    (F × (F × PointedTailZero S s0)) →ₗ[F] (S → F) where
  toFun x := fun s =>
    if hs : s = s0 then x.1 else x.2.2.1 ⟨s, hs⟩ + x.2.1 + x.1
  map_add' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs]
    · simp [hs]
      abel
  map_smul' x y := by
    funext s
    by_cases hs : s = s0
    · simp [hs]
    · simp [hs]
      ring

@[simp] lemma pointedDualEvenBuild_at_point
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (F × PointedTailZero S s0)) :
    pointedDualEvenBuild S s0 x s0 = x.1 := by
  simp [pointedDualEvenBuild]

@[simp] lemma pointedDualEvenBuild_at_tail
    {S : Type*} [Fintype S] (s0 : S)
    (x : F × (F × PointedTailZero S s0))
    (t : PointedTail S s0) :
    pointedDualEvenBuild S s0 x t.1 =
      x.2.2.1 t + x.2.1 + x.1 := by
  change
    (if hs : t.1 = s0 then x.1
      else x.2.2.1 ⟨t.1, hs⟩ + x.2.1 + x.1) =
        x.2.2.1 t + x.2.1 + x.1
  rw [dif_neg t.2]

lemma pointedDualEvenBuild_sum
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S))
    (x : F × (F × PointedTailZero S s0)) :
    (∑ s, pointedDualEvenBuild S s0 x s) = x.2.1 := by
  rw [sum_eq_at_point_add_tail s0 (pointedDualEvenBuild S s0 x)]
  rw [pointedDualEvenBuild_at_point]
  simp_rw [pointedDualEvenBuild_at_tail]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    pointedTailZero_sum, sum_tail_const_of_card_even s0 heven,
    sum_tail_const_of_card_even s0 heven]
  rw [zero_add, add_comm x.2.1 x.1, ← add_assoc, F_add_self]
  simp

lemma pointedDualEvenBuild_difference_sum
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S))
    (x : F × (F × PointedTailZero S s0)) :
    (∑ t : PointedTail S s0,
      (pointedDualEvenBuild S s0 x t.1 +
        pointedDualEvenBuild S s0 x s0)) = x.2.1 := by
  simp_rw [pointedDualEvenBuild_at_tail, pointedDualEvenBuild_at_point]
  simp_rw [add_assoc, F_add_self, add_zero]
  rw [Finset.sum_add_distrib, pointedTailZero_sum,
    sum_tail_const_of_card_even s0 heven]
  simp

lemma pointedDualEvenRead_build
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S))
    (x : F × (F × PointedTailZero S s0)) :
    pointedDualEvenRead S s0 heven (pointedDualEvenBuild S s0 x) = x := by
  apply Prod.ext
  · exact pointedDualEvenBuild_at_point s0 x
  · apply Prod.ext
    · exact pointedDualEvenBuild_difference_sum s0 heven x
    · apply Subtype.ext
      funext t
      change pointedDualEvenBuild S s0 x t.1 +
          pointedDualEvenBuild S s0 x s0 +
          (∑ u : PointedTail S s0,
            (pointedDualEvenBuild S s0 x u.1 +
              pointedDualEvenBuild S s0 x s0)) =
        x.2.2.1 t
      rw [pointedDualEvenBuild_at_tail, pointedDualEvenBuild_at_point]
      have hds :
          (∑ u : PointedTail S s0,
            (pointedDualEvenBuild S s0 x u.1 + x.1)) = x.2.1 := by
        simpa only [pointedDualEvenBuild_at_point] using
          pointedDualEvenBuild_difference_sum s0 heven x
      rw [hds]
      ring_nf
      rw [show (2 : F) = 0 by decide]
      simp

lemma pointedDualEvenBuild_read
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (g : S → F) :
    pointedDualEvenBuild S s0 (pointedDualEvenRead S s0 heven g) = g := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedDualEvenBuild_at_point]
    rfl
  · let t : PointedTail S s0 := ⟨s, hs⟩
    change pointedDualEvenBuild S s0
      (pointedDualEvenRead S s0 heven g) t.1 = g s
    rw [pointedDualEvenBuild_at_tail]
    change (g s + g s0 +
        ∑ u : PointedTail S s0, (g u.1 + g s0)) +
      (∑ u : PointedTail S s0, (g u.1 + g s0)) + g s0 = g s
    ring_nf
    rw [show (2 : F) = 0 by decide]
    simp

/-- The explicit even-cardinality dual linear equivalence. -/
noncomputable def pointedDualEvenEquiv
    (S : Type*) [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) :
    (S → F) ≃ₗ[F] F × (F × PointedTailZero S s0) where
  toFun := pointedDualEvenRead S s0 heven
  invFun := pointedDualEvenBuild S s0
  left_inv := pointedDualEvenBuild_read s0 heven
  right_inv := pointedDualEvenRead_build s0 heven
  map_add' := (pointedDualEvenRead S s0 heven).map_add
  map_smul' := (pointedDualEvenRead S s0 heven).map_smul

@[simp] lemma pointedSrcOddEquiv_apply_snd
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (f : S → F)
    (t : PointedTail S s0) :
    (pointedSrcOddEquiv S s0 hodd f).2 t =
      f t.1 + ∑ s, f s := rfl

@[simp] lemma pointedDualOddEquiv_apply_snd
    {S : Type*} [Fintype S] (s0 : S)
    (hodd : Odd (Fintype.card S)) (g : S → F)
    (t : PointedTail S s0) :
    (pointedDualOddEquiv S s0 hodd g).2 t =
      g t.1 + g s0 := rfl

@[simp] lemma pointedSrcEvenEquiv_apply_fst
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (f : S → F) :
    (pointedSrcEvenEquiv S s0 heven f).1 = ∑ s, f s := rfl

@[simp] lemma pointedSrcEvenEquiv_apply_constant
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (f : S → F) :
    (pointedSrcEvenEquiv S s0 heven f).2.1 =
      ∑ t : PointedTail S s0, f t.1 := rfl

@[simp] lemma pointedSrcEvenEquiv_apply_tail
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (f : S → F)
    (t : PointedTail S s0) :
    (pointedSrcEvenEquiv S s0 heven f).2.2.1 t =
      f t.1 + ∑ u : PointedTail S s0, f u.1 := rfl

@[simp] lemma pointedDualEvenEquiv_apply_fst
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (g : S → F) :
    (pointedDualEvenEquiv S s0 heven g).1 = g s0 := rfl

@[simp] lemma pointedDualEvenEquiv_apply_sum
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (g : S → F) :
    (pointedDualEvenEquiv S s0 heven g).2.1 =
      ∑ t : PointedTail S s0, (g t.1 + g s0) := rfl

@[simp] lemma pointedDualEvenEquiv_apply_tail
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (g : S → F)
    (t : PointedTail S s0) :
    (pointedDualEvenEquiv S s0 heven g).2.2.1 t =
      g t.1 + g s0 +
        ∑ u : PointedTail S s0, (g u.1 + g s0) := rfl

lemma pointedDualEven_sum_projection
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (g : S → F) :
    (pointedDualEvenEquiv S s0 heven g).2.1 = ∑ s, g s := by
  rw [pointedDualEvenEquiv_apply_sum, Finset.sum_add_distrib,
    sum_tail_const_of_card_even s0 heven,
    sum_eq_at_point_add_tail s0 g]
  abel

@[simp] lemma pointedSrcEvenEquiv_const
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (x : F) :
    pointedSrcEvenEquiv S s0 heven (fun _ => x) =
      (0, (x, 0)) := by
  apply Prod.ext
  · exact sum_all_const_of_card_even heven x
  · apply Prod.ext
    · exact sum_tail_const_of_card_even s0 heven x
    · apply Subtype.ext
      funext t
      rw [pointedSrcEvenEquiv_apply_tail,
        sum_tail_const_of_card_even s0 heven]
      exact F_add_self x

@[simp] lemma pointedDualEvenEquiv_const
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (x : F) :
    pointedDualEvenEquiv S s0 heven (fun _ => x) =
      (x, (0, 0)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [pointedDualEvenEquiv_apply_sum]
      have hzero :
          (fun _ : PointedTail S s0 => x + x) = (0 : PointedTail S s0 → F) := by
        funext t
        exact F_add_self x
      rw [hzero]
      simp
    · apply Subtype.ext
      funext t
      rw [pointedDualEvenEquiv_apply_tail]
      have hzero :
          (∑ u : PointedTail S s0, (x + x)) = 0 := by
        have hfun :
            (fun _ : PointedTail S s0 => x + x) =
              (0 : PointedTail S s0 → F) := by
          funext u
          exact F_add_self x
        rw [hfun]
        simp
      rw [hzero, add_zero, F_add_self]
      rfl

private theorem pointedEven_build_pairing
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S))
    (x y : F × (F × PointedTailZero S s0)) :
    (∑ s, pointedSrcEvenBuild S s0 x s *
      pointedDualEvenBuild S s0 y s) =
        x.1 * y.1 + x.2.1 * y.2.1 +
          ∑ t, x.2.2.1 t * y.2.2.1 t := by
  rw [sum_eq_at_point_add_tail s0
    (fun s => pointedSrcEvenBuild S s0 x s *
      pointedDualEvenBuild S s0 y s)]
  rw [pointedSrcEvenBuild_at_point, pointedDualEvenBuild_at_point]
  simp_rw [pointedSrcEvenBuild_at_tail, pointedDualEvenBuild_at_tail]
  simp_rw [mul_add, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  rw [← Finset.mul_sum, pointedTailZero_sum, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, pointedTailZero_sum, zero_mul,
    sum_tail_const_of_card_even s0 heven]
  rw [← Finset.sum_mul, pointedTailZero_sum, zero_mul,
    sum_tail_const_of_card_even s0 heven]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

theorem pointedEven_pairing
    {S : Type*} [Fintype S] (s0 : S)
    (heven : Even (Fintype.card S)) (f g : S → F) :
    (∑ s, f s * g s) =
      (pointedSrcEvenEquiv S s0 heven f).1 *
          (pointedDualEvenEquiv S s0 heven g).1 +
        (pointedSrcEvenEquiv S s0 heven f).2.1 *
          (pointedDualEvenEquiv S s0 heven g).2.1 +
        ∑ t,
          (pointedSrcEvenEquiv S s0 heven f).2.2.1 t *
            (pointedDualEvenEquiv S s0 heven g).2.2.1 t := by
  let x := pointedSrcEvenEquiv S s0 heven f
  let y := pointedDualEvenEquiv S s0 heven g
  have hx : pointedSrcEvenBuild S s0 x = f :=
    pointedSrcEvenBuild_read s0 heven f
  have hy : pointedDualEvenBuild S s0 y = g :=
    pointedDualEvenBuild_read s0 heven g
  calc
    (∑ s, f s * g s) =
        ∑ s, pointedSrcEvenBuild S s0 x s *
          pointedDualEvenBuild S s0 y s := by rw [hx, hy]
    _ = x.1 * y.1 + x.2.1 * y.2.1 +
          ∑ t, x.2.2.1 t * y.2.2.1 t :=
      pointedEven_build_pairing s0 heven x y
    _ = _ := rfl

end

end Core4loop
