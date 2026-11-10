import Core4loop.SquareDiagonal.EvenP.SourceSplit

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

private theorem pointedValue_module_add_self
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 :=
  (add_eq_zero_iff_eq_of_F_module x x).2 rfl

private theorem pointedValue_cast_card_eq_zero_of_even
    {m : Nat} (hm : Even m) : (m : F) = 0 := by
  rcases hm with ⟨k, hk⟩
  rw [hk]
  push_cast
  exact F_add_self _

private theorem pointedValue_cast_card_eq_one_of_odd
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨k, hk⟩
  rw [hk]
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem pointedValue_sum_eq_at_point_add_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommMonoid V] (f : S → V) :
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

private theorem pointedValue_pointedTail_odd_of_card_even
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S)) :
    Odd (Fintype.card (PointedTail S s0)) := by
  classical
  letI : Nonempty S := ⟨s0⟩
  rcases heven with ⟨k, hk⟩
  have hpos : 0 < Fintype.card S := Fintype.card_pos
  have hfinal :
      Fintype.card (PointedTail S s0) =
        Fintype.card S - 1 := by
    calc
      Fintype.card (PointedTail S s0) =
          @Fintype.card (PointedTail S s0)
            (Subtype.fintype (fun s : S => s ≠ s0)) :=
        @Fintype.card_congr
          (PointedTail S s0) (PointedTail S s0)
          (inferInstanceAs (Fintype (PointedTail S s0)))
          (Subtype.fintype (fun s : S => s ≠ s0))
          (Equiv.refl _)
      _ = Fintype.card S - 1 :=
        card_pointedTail (S := S) s0
  refine ⟨k - 1, ?_⟩
  exact hfinal.trans (by
    rw [hk]
    omega)

private theorem pointedValue_sum_tail_const_of_card_even
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (x : V) :
    (∑ _ : PointedTail S s0, x) = x := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    pointedValue_cast_card_eq_one_of_odd
      (pointedValue_pointedTail_odd_of_card_even s0 heven),
    one_smul]

private theorem pointedValue_sum_all_const_of_card_even
    {S V : Type*} [Fintype S]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (x : V) :
    (∑ _ : S, x) = 0 := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    pointedValue_cast_card_eq_zero_of_even heven, zero_smul]

noncomputable abbrev PointedValueTailZero
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V] :=
  LinearMap.ker
    (fintypeSumLinearMap
      (S := PointedTail S s0) (V := V))

abbrev PointedEvenValueCoords
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V] :=
  (V × V) × PointedValueTailZero S V s0

@[simp] theorem pointedValueTailZero_sum
    {S V : Type*} [Fintype S] {s0 : S}
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (x : PointedValueTailZero S V s0) :
    (∑ t, x.1 t) = 0 :=
  LinearMap.mem_ker.mp x.2

noncomputable def pointedSrcEvenValueRead
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) :
    (S → V) →ₗ[F] PointedEvenValueCoords S V s0 where
  toFun f :=
    let K := ∑ t : PointedTail S s0, f t.1
    ((∑ s, f s, K),
      ⟨fun t => f t.1 + K, by
        apply LinearMap.mem_ker.mpr
        change (∑ t : PointedTail S s0, (f t.1 + K)) = 0
        rw [Finset.sum_add_distrib,
          pointedValue_sum_tail_const_of_card_even s0 heven]
        exact pointedValue_module_add_self K⟩)
  map_add' f g := by
    apply Prod.ext
    · apply Prod.ext
      · change (∑ s : S, (f s + g s)) = (∑ s, f s) + ∑ s, g s
        rw [Finset.sum_add_distrib]
      · change
          (∑ t : PointedTail S s0, (f t.1 + g t.1)) =
            (∑ t : PointedTail S s0, f t.1) +
              ∑ t : PointedTail S s0, g t.1
        rw [Finset.sum_add_distrib]
    · apply Subtype.ext
      funext t
      change
        (f t.1 + g t.1) +
            (∑ u : PointedTail S s0, (f u.1 + g u.1)) =
          (f t.1 + ∑ u : PointedTail S s0, f u.1) +
            (g t.1 + ∑ u : PointedTail S s0, g u.1)
      rw [Finset.sum_add_distrib]
      abel
  map_smul' r f := by
    apply Prod.ext
    · apply Prod.ext
      · change (∑ s : S, r • f s) = r • ∑ s, f s
        rw [Finset.smul_sum]
      · change
          (∑ t : PointedTail S s0, r • f t.1) =
            r • ∑ t : PointedTail S s0, f t.1
        rw [Finset.smul_sum]
    · apply Subtype.ext
      funext t
      change
        r • f t.1 + (∑ u : PointedTail S s0, r • f u.1) =
          r • (f t.1 + ∑ u : PointedTail S s0, f u.1)
      rw [← Finset.smul_sum, smul_add]

noncomputable def pointedSrcEvenValueBuild
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V] :
    PointedEvenValueCoords S V s0 →ₗ[F] (S → V) := by
  classical
  exact
    { toFun := fun x s =>
        if hs : s = s0 then x.1.1 + x.1.2
        else x.2.1 ⟨s, hs⟩ + x.1.2
      map_add' := fun x y => by
        funext s
        by_cases hs : s = s0
        · simp [hs]
          abel
        · simp [hs]
          abel
      map_smul' := fun r x => by
        funext s
        by_cases hs : s = s0 <;> simp [hs, smul_add] }

@[simp] theorem pointedSrcEvenValueBuild_at_point
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (x : PointedEvenValueCoords S V s0) :
    pointedSrcEvenValueBuild S V s0 x s0 = x.1.1 + x.1.2 := by
  simp [pointedSrcEvenValueBuild]

@[simp] theorem pointedSrcEvenValueBuild_at_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (x : PointedEvenValueCoords S V s0)
    (t : PointedTail S s0) :
    pointedSrcEvenValueBuild S V s0 x t.1 =
      x.2.1 t + x.1.2 := by
  simp [pointedSrcEvenValueBuild, t.2]

theorem pointedSrcEvenValueRead_build
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S))
    (x : PointedEvenValueCoords S V s0) :
    pointedSrcEvenValueRead S V s0 heven
        (pointedSrcEvenValueBuild S V s0 x) = x := by
  have htail :
      (∑ t : PointedTail S s0,
          pointedSrcEvenValueBuild S V s0 x t.1) = x.1.2 := by
    simp_rw [pointedSrcEvenValueBuild_at_tail]
    rw [Finset.sum_add_distrib, pointedValueTailZero_sum,
      pointedValue_sum_tail_const_of_card_even s0 heven, zero_add]
  apply Prod.ext
  · apply Prod.ext
    · change
        (∑ s : S, pointedSrcEvenValueBuild S V s0 x s) = x.1.1
      rw [pointedValue_sum_eq_at_point_add_tail s0, htail,
        pointedSrcEvenValueBuild_at_point,
        add_assoc, pointedValue_module_add_self, add_zero]
    · exact htail
  · apply Subtype.ext
    funext t
    change
      pointedSrcEvenValueBuild S V s0 x t.1 +
          (∑ u : PointedTail S s0,
            pointedSrcEvenValueBuild S V s0 x u.1) =
        x.2.1 t
    rw [pointedSrcEvenValueBuild_at_tail, htail,
      add_assoc, pointedValue_module_add_self, add_zero]

theorem pointedSrcEvenValueBuild_read
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (f : S → V) :
    pointedSrcEvenValueBuild S V s0
        (pointedSrcEvenValueRead S V s0 heven f) = f := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedSrcEvenValueBuild_at_point]
    change (∑ u : S, f u) +
        (∑ t : PointedTail S s0, f t.1) = f s0
    rw [pointedValue_sum_eq_at_point_add_tail s0, add_assoc,
      pointedValue_module_add_self, add_zero]
  · let t : PointedTail S s0 := ⟨s, hs⟩
    change
      pointedSrcEvenValueBuild S V s0
        (pointedSrcEvenValueRead S V s0 heven f) t.1 = f s
    rw [pointedSrcEvenValueBuild_at_tail]
    change
      (f s + ∑ u : PointedTail S s0, f u.1) +
        ∑ u : PointedTail S s0, f u.1 = f s
    rw [add_assoc, pointedValue_module_add_self, add_zero]

noncomputable def pointedSrcEvenValueEquiv
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) :
    (S → V) ≃ₗ[F] PointedEvenValueCoords S V s0 where
  toFun := pointedSrcEvenValueRead S V s0 heven
  invFun := pointedSrcEvenValueBuild S V s0
  left_inv := pointedSrcEvenValueBuild_read s0 heven
  right_inv := pointedSrcEvenValueRead_build s0 heven
  map_add' := (pointedSrcEvenValueRead S V s0 heven).map_add
  map_smul' := (pointedSrcEvenValueRead S V s0 heven).map_smul

noncomputable def pointedDualEvenValueRead
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) :
    (S → V) →ₗ[F] PointedEvenValueCoords S V s0 where
  toFun g :=
    let A := ∑ t : PointedTail S s0, (g t.1 + g s0)
    ((g s0, A),
      ⟨fun t => g t.1 + g s0 + A, by
        apply LinearMap.mem_ker.mpr
        change
          (∑ t : PointedTail S s0, (g t.1 + g s0 + A)) = 0
        rw [Finset.sum_add_distrib,
          pointedValue_sum_tail_const_of_card_even s0 heven]
        exact pointedValue_module_add_self A⟩)
  map_add' f g := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change
          (∑ t : PointedTail S s0,
              ((f t.1 + g t.1) + (f s0 + g s0))) =
            (∑ t : PointedTail S s0, (f t.1 + f s0)) +
              ∑ t : PointedTail S s0, (g t.1 + g s0)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _
        abel
    · apply Subtype.ext
      funext t
      have hsum :
          (∑ u : PointedTail S s0,
              ((f u.1 + g u.1) + (f s0 + g s0))) =
            (∑ u : PointedTail S s0, (f u.1 + f s0)) +
              ∑ u : PointedTail S s0, (g u.1 + g s0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u _
        abel
      change
        (f t.1 + g t.1) + (f s0 + g s0) +
            (∑ u : PointedTail S s0,
              ((f u.1 + g u.1) + (f s0 + g s0))) =
          (f t.1 + f s0 +
              ∑ u : PointedTail S s0, (f u.1 + f s0)) +
            (g t.1 + g s0 +
              ∑ u : PointedTail S s0, (g u.1 + g s0))
      rw [hsum]
      abel
  map_smul' r f := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change
          (∑ t : PointedTail S s0, (r • f t.1 + r • f s0)) =
            r • ∑ t : PointedTail S s0, (f t.1 + f s0)
        simp_rw [← smul_add]
        rw [Finset.smul_sum]
    · apply Subtype.ext
      funext t
      change
        r • f t.1 + r • f s0 +
            (∑ u : PointedTail S s0, (r • f u.1 + r • f s0)) =
          r • (f t.1 + f s0 +
            ∑ u : PointedTail S s0, (f u.1 + f s0))
      simp_rw [← smul_add]
      rw [← Finset.smul_sum, smul_add, smul_add, smul_add]

noncomputable def pointedDualEvenValueBuild
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V] :
    PointedEvenValueCoords S V s0 →ₗ[F] (S → V) := by
  classical
  exact
    { toFun := fun x s =>
        if hs : s = s0 then x.1.1
        else x.2.1 ⟨s, hs⟩ + x.1.1 + x.1.2
      map_add' := fun x y => by
        funext s
        by_cases hs : s = s0
        · simp [hs]
        · simp [hs]
          abel
      map_smul' := fun r x => by
        funext s
        by_cases hs : s = s0 <;> simp [hs, smul_add] }

@[simp] theorem pointedDualEvenValueBuild_at_point
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (x : PointedEvenValueCoords S V s0) :
    pointedDualEvenValueBuild S V s0 x s0 = x.1.1 := by
  simp [pointedDualEvenValueBuild]

@[simp] theorem pointedDualEvenValueBuild_at_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (x : PointedEvenValueCoords S V s0)
    (t : PointedTail S s0) :
    pointedDualEvenValueBuild S V s0 x t.1 =
      x.2.1 t + x.1.1 + x.1.2 := by
  simp [pointedDualEvenValueBuild, t.2]

theorem pointedDualEvenValueRead_build
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S))
    (x : PointedEvenValueCoords S V s0) :
    pointedDualEvenValueRead S V s0 heven
        (pointedDualEvenValueBuild S V s0 x) = x := by
  have hdiff :
      (∑ t : PointedTail S s0,
        (pointedDualEvenValueBuild S V s0 x t.1 +
          pointedDualEvenValueBuild S V s0 x s0)) = x.1.2 := by
    simp_rw [pointedDualEvenValueBuild_at_tail,
      pointedDualEvenValueBuild_at_point]
    have hpoint :
        (fun t : PointedTail S s0 =>
            (x.2.1 t + x.1.1 + x.1.2) + x.1.1) =
          fun t => x.2.1 t + x.1.2 := by
      funext t
      calc
        (x.2.1 t + x.1.1 + x.1.2) + x.1.1 =
            x.2.1 t + x.1.2 + (x.1.1 + x.1.1) := by abel
        _ = x.2.1 t + x.1.2 := by
          rw [pointedValue_module_add_self, add_zero]
    rw [hpoint, Finset.sum_add_distrib,
      pointedValueTailZero_sum,
      pointedValue_sum_tail_const_of_card_even s0 heven, zero_add]
  apply Prod.ext
  · apply Prod.ext
    · exact pointedDualEvenValueBuild_at_point s0 x
    · exact hdiff
  · apply Subtype.ext
    funext t
    have hdiff' :
        (∑ u : PointedTail S s0,
          (pointedDualEvenValueBuild S V s0 x u.1 + x.1.1)) =
            x.1.2 := by
      simpa only [pointedDualEvenValueBuild_at_point] using hdiff
    change
      pointedDualEvenValueBuild S V s0 x t.1 +
          pointedDualEvenValueBuild S V s0 x s0 +
          (∑ u : PointedTail S s0,
            (pointedDualEvenValueBuild S V s0 x u.1 +
              pointedDualEvenValueBuild S V s0 x s0)) =
        x.2.1 t
    rw [pointedDualEvenValueBuild_at_tail,
      pointedDualEvenValueBuild_at_point, hdiff']
    calc
      x.2.1 t + x.1.1 + x.1.2 + x.1.1 + x.1.2 =
          x.2.1 t + (x.1.1 + x.1.1) + (x.1.2 + x.1.2) := by abel
      _ = x.2.1 t := by
        rw [pointedValue_module_add_self, pointedValue_module_add_self,
          add_zero, add_zero]

theorem pointedDualEvenValueBuild_read
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (g : S → V) :
    pointedDualEvenValueBuild S V s0
        (pointedDualEvenValueRead S V s0 heven g) = g := by
  funext s
  by_cases hs : s = s0
  · subst s
    rw [pointedDualEvenValueBuild_at_point]
    rfl
  · let t : PointedTail S s0 := ⟨s, hs⟩
    change
      pointedDualEvenValueBuild S V s0
        (pointedDualEvenValueRead S V s0 heven g) t.1 = g s
    rw [pointedDualEvenValueBuild_at_tail]
    change
      (g s + g s0 + ∑ u : PointedTail S s0, (g u.1 + g s0)) +
          g s0 + ∑ u : PointedTail S s0, (g u.1 + g s0) = g s
    calc
      (g s + g s0 + ∑ u : PointedTail S s0, (g u.1 + g s0)) +
            g s0 + ∑ u : PointedTail S s0, (g u.1 + g s0) =
          g s + (g s0 + g s0) +
            ((∑ u : PointedTail S s0, (g u.1 + g s0)) +
              ∑ u : PointedTail S s0, (g u.1 + g s0)) := by abel
      _ = g s := by
        rw [pointedValue_module_add_self, pointedValue_module_add_self,
          add_zero, add_zero]

noncomputable def pointedDualEvenValueEquiv
    (S V : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) :
    (S → V) ≃ₗ[F] PointedEvenValueCoords S V s0 where
  toFun := pointedDualEvenValueRead S V s0 heven
  invFun := pointedDualEvenValueBuild S V s0
  left_inv := pointedDualEvenValueBuild_read s0 heven
  right_inv := pointedDualEvenValueRead_build s0 heven
  map_add' := (pointedDualEvenValueRead S V s0 heven).map_add
  map_smul' := (pointedDualEvenValueRead S V s0 heven).map_smul

@[simp] theorem pointedSrcEvenValueEquiv_apply_sigma
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (f : S → V) :
    (pointedSrcEvenValueEquiv S V s0 heven f).1.1 =
      ∑ s, f s := rfl

@[simp] theorem pointedSrcEvenValueEquiv_apply_K
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (f : S → V) :
    (pointedSrcEvenValueEquiv S V s0 heven f).1.2 =
      ∑ t : PointedTail S s0, f t.1 := rfl

@[simp] theorem pointedSrcEvenValueEquiv_apply_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (f : S → V)
    (t : PointedTail S s0) :
    (pointedSrcEvenValueEquiv S V s0 heven f).2.1 t =
      f t.1 + ∑ u : PointedTail S s0, f u.1 := rfl

@[simp] theorem pointedDualEvenValueEquiv_apply_point
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (g : S → V) :
    (pointedDualEvenValueEquiv S V s0 heven g).1.1 = g s0 := rfl

@[simp] theorem pointedDualEvenValueEquiv_apply_sum
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (g : S → V) :
    (pointedDualEvenValueEquiv S V s0 heven g).1.2 =
      ∑ t : PointedTail S s0, (g t.1 + g s0) := rfl

@[simp] theorem pointedDualEvenValueEquiv_apply_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (g : S → V)
    (t : PointedTail S s0) :
    (pointedDualEvenValueEquiv S V s0 heven g).2.1 t =
      g t.1 + g s0 +
        ∑ u : PointedTail S s0, (g u.1 + g s0) := rfl

private theorem pointedValue_sum_beta_left
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (beta : U →ₗ[F] Module.Dual F V)
    (u : T → U) (v : V) :
    (∑ t, beta (u t) v) = beta (∑ t, u t) v := by
  rw [← LinearMap.sum_apply, ← map_sum]

private theorem pointedValue_sum_beta_right
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (beta : U →ₗ[F] Module.Dual F V)
    (u : U) (v : T → V) :
    (∑ t, beta u (v t)) = beta u (∑ t, v t) := by
  exact (map_sum (beta u) v (Finset.univ : Finset T)).symm

private theorem pointedValue_sum_beta_const
    {T U V : Type*} [Fintype T]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T))
    (beta : U →ₗ[F] Module.Dual F V)
    (u : U) (v : V) :
    (∑ _t : T, beta u v) = beta u v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    pointedValue_cast_card_eq_one_of_odd hodd, one_smul]

private theorem pointedEvenValue_build_pairing
    {S U V : Type*} [Fintype S]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S))
    (beta : U →ₗ[F] Module.Dual F V)
    (x : PointedEvenValueCoords S U s0)
    (y : PointedEvenValueCoords S V s0) :
    (∑ s,
      beta
        (pointedSrcEvenValueBuild S U s0 x s)
        (pointedDualEvenValueBuild S V s0 y s)) =
      beta x.1.1 y.1.1 + beta x.1.2 y.1.2 +
        ∑ t, beta (x.2.1 t) (y.2.1 t) := by
  rw [pointedValue_sum_eq_at_point_add_tail s0]
  rw [pointedSrcEvenValueBuild_at_point,
    pointedDualEvenValueBuild_at_point]
  simp_rw [pointedSrcEvenValueBuild_at_tail,
    pointedDualEvenValueBuild_at_tail]
  simp_rw [map_add, LinearMap.add_apply]
  repeat' rw [Finset.sum_add_distrib]
  rw [pointedValue_sum_beta_left beta x.2.1 y.1.1,
    pointedValue_sum_beta_left beta x.2.1 y.1.2,
    pointedValue_sum_beta_right beta x.1.2 y.2.1,
    pointedValueTailZero_sum,
    pointedValueTailZero_sum]
  simp only [map_zero, LinearMap.zero_apply, zero_add]
  rw [pointedValue_sum_beta_const
      (pointedValue_pointedTail_odd_of_card_even s0 heven)
      beta x.1.2 y.1.1,
    pointedValue_sum_beta_const
      (pointedValue_pointedTail_odd_of_card_even s0 heven)
      beta x.1.2 y.1.2]
  abel_nf
  simp only [two_smul, F_add_self, zero_add]

theorem pointedEvenValue_pairing
    {S U V : Type*} [Fintype S]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S))
    (beta : U →ₗ[F] Module.Dual F V)
    (f : S → U) (g : S → V) :
    (∑ s, beta (f s) (g s)) =
      beta
          (pointedSrcEvenValueEquiv S U s0 heven f).1.1
          (pointedDualEvenValueEquiv S V s0 heven g).1.1
      +
      beta
          (pointedSrcEvenValueEquiv S U s0 heven f).1.2
          (pointedDualEvenValueEquiv S V s0 heven g).1.2
      +
      ∑ t,
        beta
          ((pointedSrcEvenValueEquiv S U s0 heven f).2.1 t)
          ((pointedDualEvenValueEquiv S V s0 heven g).2.1 t) := by
  let x := pointedSrcEvenValueEquiv S U s0 heven f
  let y := pointedDualEvenValueEquiv S V s0 heven g
  have hx : pointedSrcEvenValueBuild S U s0 x = f :=
    pointedSrcEvenValueBuild_read s0 heven f
  have hy : pointedDualEvenValueBuild S V s0 y = g :=
    pointedDualEvenValueBuild_read s0 heven g
  calc
    (∑ s, beta (f s) (g s)) =
        ∑ s,
          beta (pointedSrcEvenValueBuild S U s0 x s)
            (pointedDualEvenValueBuild S V s0 y s) := by
          rw [hx, hy]
    _ = beta x.1.1 y.1.1 + beta x.1.2 y.1.2 +
          ∑ t, beta (x.2.1 t) (y.2.1 t) :=
      pointedEvenValue_build_pairing s0 heven beta x y
    _ = _ := rfl

theorem pointedTailSum_eq_fintypeSumLinearMap
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)] :
    pointedTailSum S s0 =
      fintypeSumLinearMap
        (S := PointedTail S s0) (V := F) := by
  ext f
  simp only [pointedTailSum, fintypeSumLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr
  · ext t
    simp
  · intro t ht
    rfl

theorem pointedTailZero_eq_pointedValueTailZero
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)] :
    PointedTailZero S s0 =
      PointedValueTailZero S F s0 := by
  exact congrArg LinearMap.ker
    (pointedTailSum_eq_fintypeSumLinearMap s0)

noncomputable def pointedValueTailZeroScalarEquiv
    (S : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)] :
    PointedValueTailZero S F s0 ≃ₗ[F] PointedTailZero S s0 :=
  LinearEquiv.ofEq _ _
    (pointedTailZero_eq_pointedValueTailZero s0).symm

noncomputable def pointedValueScalarCoordsEquiv
    (S : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)] :
    PointedEvenValueCoords S F s0 ≃ₗ[F]
      F × (F × PointedTailZero S s0) where
  toFun x := (x.1.1, (x.1.2, pointedValueTailZeroScalarEquiv S s0 x.2))
  invFun x := ((x.1, x.2.1),
    (pointedValueTailZeroScalarEquiv S s0).symm x.2.2)
  left_inv x := by
    apply Prod.ext
    · rfl
    · exact (pointedValueTailZeroScalarEquiv S s0).left_inv x.2
  right_inv x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact (pointedValueTailZeroScalarEquiv S s0).right_inv x.2.2
  map_add' x y := rfl
  map_smul' r x := rfl

theorem pointedSrcEvenValueEquiv_scalar_compat
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S)) :
    (pointedSrcEvenValueEquiv S F s0 heven).trans
        (pointedValueScalarCoordsEquiv S s0) =
      pointedSrcEvenEquiv S s0 heven := by
  apply LinearEquiv.ext
  intro f
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change
        (∑ t : PointedTail S s0, f t.1) =
          pointedTailSum S s0 (fun t => f t.1)
      have h := congrArg
        (fun L : (PointedTail S s0 → F) →ₗ[F] F =>
          L (fun t => f t.1))
        (pointedTailSum_eq_fintypeSumLinearMap s0)
      exact h.symm
    · apply Subtype.ext
      funext t
      change
        f t.1 + (∑ u : PointedTail S s0, f u.1) =
          f t.1 + pointedTailSum S s0 (fun u => f u.1)
      congr 1
      have h := congrArg
        (fun L : (PointedTail S s0 → F) →ₗ[F] F =>
          L (fun u => f u.1))
        (pointedTailSum_eq_fintypeSumLinearMap s0)
      exact h.symm

theorem pointedDualEvenValueEquiv_scalar_compat
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S)) :
    (pointedDualEvenValueEquiv S F s0 heven).trans
        (pointedValueScalarCoordsEquiv S s0) =
      pointedDualEvenEquiv S s0 heven := by
  apply LinearEquiv.ext
  intro g
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change
        (∑ t : PointedTail S s0, (g t.1 + g s0)) =
          pointedTailSum S s0 (fun t => g t.1 + g s0)
      have h := congrArg
        (fun L : (PointedTail S s0 → F) →ₗ[F] F =>
          L (fun t => g t.1 + g s0))
        (pointedTailSum_eq_fintypeSumLinearMap s0)
      exact h.symm
    · apply Subtype.ext
      funext t
      change
        g t.1 + g s0 +
            (∑ u : PointedTail S s0, (g u.1 + g s0)) =
          g t.1 + g s0 +
            pointedTailSum S s0 (fun u => g u.1 + g s0)
      congr 1
      have h := congrArg
        (fun L : (PointedTail S s0 → F) →ₗ[F] F =>
          L (fun u => g u.1 + g s0))
        (pointedTailSum_eq_fintypeSumLinearMap s0)
      exact h.symm

noncomputable def pointedValueScalarDot :
    F →ₗ[F] Module.Dual F F :=
  LinearMap.mk₂ F (fun x y => x * y)
    add_mul mul_assoc mul_add (fun r x y => by
      change x * (r * y) = r * (x * y)
      ring)

theorem pointedEvenValue_pairing_scalar_compat
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S)) (f g : S → F) :
    (∑ s, pointedValueScalarDot (f s) (g s)) =
      (pointedSrcEvenEquiv S s0 heven f).1 *
          (pointedDualEvenEquiv S s0 heven g).1 +
        (pointedSrcEvenEquiv S s0 heven f).2.1 *
          (pointedDualEvenEquiv S s0 heven g).2.1 +
        ∑ t,
          (pointedSrcEvenEquiv S s0 heven f).2.2.1 t *
            (pointedDualEvenEquiv S s0 heven g).2.2.1 t := by
  let h : PointedTail S s0 → F := fun t =>
    (pointedSrcEvenEquiv S s0 heven f).2.2.1 t *
      (pointedDualEvenEquiv S s0 heven g).2.2.1 t
  have hsum :
      (∑ t : PointedTail S s0, h t) =
        pointedTailSum S s0 h := by
    have hs := congrArg
      (fun L : (PointedTail S s0 → F) →ₗ[F] F => L h)
      (pointedTailSum_eq_fintypeSumLinearMap s0)
    exact hs.symm
  change
    (∑ s, f s * g s) =
      (pointedSrcEvenEquiv S s0 heven f).1 *
          (pointedDualEvenEquiv S s0 heven g).1 +
        (pointedSrcEvenEquiv S s0 heven f).2.1 *
          (pointedDualEvenEquiv S s0 heven g).2.1 +
        ∑ t : PointedTail S s0, h t
  rw [hsum]
  simpa only [pointedTailSum, LinearMap.coe_mk, AddHom.coe_mk] using
    pointedEven_pairing s0 heven f g

private theorem pointedValue_sum_prod_fst
    {T U V : Type*} [Fintype T]
    [AddCommMonoid U] [AddCommMonoid V]
  (f : T → U × V) :
    (∑ t, f t).1 = ∑ t, (f t).1 := by
  exact map_sum (AddMonoidHom.fst U V) f (Finset.univ : Finset T)

private theorem pointedValue_sum_prod_snd
    {T U V : Type*} [Fintype T]
    [AddCommMonoid U] [AddCommMonoid V]
  (f : T → U × V) :
    (∑ t, f t).2 = ∑ t, (f t).2 := by
  exact map_sum (AddMonoidHom.snd U V) f (Finset.univ : Finset T)

theorem diamondEvenPBWPointedEquiv_eq_valueNormalForm
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2
      =
    (diamondEvenPBWCurryEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d)).trans
      (pointedSrcEvenValueEquiv
        (PVec n a)
        (DiamondEvenPBWSlice n b c d)
        (zeroVec : PVec n a)
        (even_card_PVec hn ha2)) := by
  apply LinearEquiv.ext
  rintro ⟨B, W⟩
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · change
          (diamondEvenPBWPointedEquiv hn ha2 (B, W)).1.1.1 =
            (pointedSrcEvenValueEquiv
              (PVec n a) (DiamondEvenPBWSlice n b c d)
              (zeroVec : PVec n a) (even_card_PVec hn ha2)
              (diamondEvenPBWCurryEquiv (B, W))).1.1.1
        rw [diamondEvenPBWPointedEquiv_apply_sigma,
          pointedSrcEvenValueEquiv_apply_sigma,
          pointedValue_sum_prod_fst]
        funext q sy z w
        rw [pVec_one_eq_zeroVec q]
        simp [diamondEvenPBSigma, diamondEvenPBWCurryEquiv]
      · change
          (diamondEvenPBWPointedEquiv hn ha2 (B, W)).1.1.2 =
            (pointedSrcEvenValueEquiv
              (PVec n a) (DiamondEvenPBWSlice n b c d)
              (zeroVec : PVec n a) (even_card_PVec hn ha2)
              (diamondEvenPBWCurryEquiv (B, W))).1.1.2
        rw [diamondEvenPBWPointedEquiv_apply_sigma,
          pointedSrcEvenValueEquiv_apply_sigma,
          pointedValue_sum_prod_snd]
        funext q y z sw
        rw [pVec_one_eq_zeroVec q]
        simp [diamondEvenPWSigma, diamondEvenPBWCurryEquiv]
    · apply Prod.ext
      · change
          (diamondEvenPBWPointedEquiv hn ha2 (B, W)).1.2.1 =
            (pointedSrcEvenValueEquiv
              (PVec n a) (DiamondEvenPBWSlice n b c d)
              (zeroVec : PVec n a) (even_card_PVec hn ha2)
              (diamondEvenPBWCurryEquiv (B, W))).1.2.1
        rw [diamondEvenPBWPointedEquiv_apply_K,
          pointedSrcEvenValueEquiv_apply_K,
          pointedValue_sum_prod_fst]
        funext q sy z w
        rw [pVec_one_eq_zeroVec q]
        simp [diamondEvenPBK, diamondEvenPBWCurryEquiv]
      · change
          (diamondEvenPBWPointedEquiv hn ha2 (B, W)).1.2.2 =
            (pointedSrcEvenValueEquiv
              (PVec n a) (DiamondEvenPBWSlice n b c d)
              (zeroVec : PVec n a) (even_card_PVec hn ha2)
              (diamondEvenPBWCurryEquiv (B, W))).1.2.2
        rw [diamondEvenPBWPointedEquiv_apply_K,
          pointedSrcEvenValueEquiv_apply_K,
          pointedValue_sum_prod_snd]
        funext q y z sw
        rw [pVec_one_eq_zeroVec q]
        simp [diamondEvenPWK, diamondEvenPBWCurryEquiv]
  · apply Subtype.ext
    funext t
    change
      (diamondEvenPBWPointedEquiv hn ha2 (B, W)).2.1 t =
        (pointedSrcEvenValueEquiv
          (PVec n a) (DiamondEvenPBWSlice n b c d)
          (zeroVec : PVec n a) (even_card_PVec hn ha2)
          (diamondEvenPBWCurryEquiv (B, W))).2.1 t
    rw [diamondEvenPBWPointedEquiv_apply_tail,
      pointedSrcEvenValueEquiv_apply_tail]
    apply Prod.ext
    · funext q sy z w
      rw [pVec_one_eq_zeroVec q]
      simp only [Nat.add_one_sub_one, ne_eq, Prod.fst_add, Pi.add_apply]
      rw [pointedValue_sum_prod_fst]
      simp only [Finset.sum_apply]
      simp only [diamondEvenPBTail, diamondEvenPBK,
        diamondEvenPBWCurryEquiv, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk]
    · funext q y z sw
      rw [pVec_one_eq_zeroVec q]
      simp only [Nat.add_one_sub_one, ne_eq, Prod.snd_add, Pi.add_apply]
      rw [pointedValue_sum_prod_snd]
      simp only [Finset.sum_apply]
      simp only [diamondEvenPWTail, diamondEvenPWK,
        diamondEvenPBWCurryEquiv, LinearEquiv.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk]

end

end Core4loop.SquareDiagonal.EvenP
