import Core4loop.Sign

open scoped BigOperators

namespace Core4loop

noncomputable section

private theorem add_self_eq_zero_of_F_module
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 := by
  have htwo : (1 : F) + 1 = 0 := by decide
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + 1) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

theorem add_eq_zero_iff_eq_of_F_module
    {V : Type*} [AddCommGroup V] [Module F V] (x y : V) :
    x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc
      x = x + 0 := by rw [add_zero]
      _ = x + (x + y) := by rw [h]
      _ = y := by
        rw [← add_assoc, add_self_eq_zero_of_F_module, zero_add]
  · intro h
    subst h
    exact add_self_eq_zero_of_F_module x

private noncomputable def addRightF2Equiv
    {V : Type*} [AddCommGroup V] [Module F V] (x0 : V) : V ≃ V where
  toFun x := x + x0
  invFun x := x + x0
  left_inv x := by
    change (x + x0) + x0 = x
    rw [add_assoc, add_self_eq_zero_of_F_module x0, add_zero]
  right_inv x := by
    change (x + x0) + x0 = x
    rw [add_assoc, add_self_eq_zero_of_F_module x0, add_zero]

theorem sum_bitSign_linearMap_add_const
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (L : V →ₗ[F] F) (q : F) :
    (∑ x : V, bitSign (L x + q)) =
      if L = 0 then (Fintype.card V : ℤ) * bitSign q else 0 := by
  classical
  by_cases hL : L = 0
  · simp [hL]
  · have hnonzero : ∃ x0 : V, L x0 ≠ 0 := by
      by_contra hforall
      apply hL
      ext x
      by_contra hx
      exact hforall ⟨x, hx⟩
    rcases hnonzero with ⟨x0, hx0⟩
    have hLx0 : L x0 = 1 := F_ne_zero_eq_one _ hx0
    have hsum :
        (∑ x : V, bitSign (L x + q)) =
          -(∑ x : V, bitSign (L x + q)) := by
      calc
        (∑ x : V, bitSign (L x + q))
            =
            ∑ x : V, bitSign (L (addRightF2Equiv x0 x) + q) := by
              simpa using
                (((addRightF2Equiv x0).sum_comp
                  (fun x : V => bitSign (L x + q))).symm)
        _ =
            ∑ x : V, -bitSign (L x + q) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              change bitSign (L (x + x0) + q) = -bitSign (L x + q)
              rw [map_add, hLx0]
              have hcomm : L x + 1 + q = L x + q + 1 := by ac_rfl
              rw [hcomm, bitSign_add_one]
        _ =
          -(∑ x : V, bitSign (L x + q)) := by
            simp
    have hz : (∑ x : V, bitSign (L x + q)) = 0 := by
      linarith
    simp [hL, hz]

theorem sum_bitSign_linearMap
    {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (L : V →ₗ[F] F) :
    (∑ x : V, bitSign (L x)) =
      if L = 0 then (Fintype.card V : ℤ) else 0 := by
  simpa [bitSign_zero] using
    sum_bitSign_linearMap_add_const (V := V) L 0

theorem sum_if_linearMap_eq_zero_bitSign_linearMap_add_const
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) [Fintype (LinearMap.ker L)]
    (M : V →ₗ[F] F) (q : F) :
    (∑ x : V, if L x = 0 then bitSign (M x + q) else 0) =
      if (M.comp (LinearMap.ker L).subtype) = 0 then
        (Fintype.card (LinearMap.ker L) : ℤ) * bitSign q
      else 0 := by
  classical
  have hsum :
      (∑ x : V, if L x = 0 then bitSign (M x + q) else 0) =
        ∑ x : LinearMap.ker L, bitSign (M x.1 + q) := by
    calc
      (∑ x : V, if L x = 0 then bitSign (M x + q) else 0)
          = ∑ x ∈ (Finset.univ.filter (fun x : V => L x = 0)),
              bitSign (M x + q) := by
            exact (Finset.sum_filter (fun x : V => L x = 0)
              (fun x : V => bitSign (M x + q))).symm
      _ = ∑ x ∈ (Finset.univ.subtype (fun x : V => L x = 0)),
              bitSign (M x.1 + q) := by
            exact (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset V))
              (f := fun x : V => bitSign (M x + q))
              (p := fun x : V => L x = 0)).symm
      _ = ∑ x : LinearMap.ker L, bitSign (M x.1 + q) := by
            apply Finset.sum_congr
            · ext x
              constructor
              · intro _
                exact @Finset.mem_univ (LinearMap.ker L) _ x
              · intro _
                exact (Finset.mem_subtype).2 (Finset.mem_univ x.1)
            · intro _ _
              rfl
  rw [hsum]
  simpa using sum_bitSign_linearMap_add_const
    (V := LinearMap.ker L)
    (M.comp (LinearMap.ker L).subtype) q

theorem sum_if_linearMap_eq_const_bitSign_linearMap_add_const_of_preimage
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) [Fintype (LinearMap.ker L)]
    (M : V →ₗ[F] F) (q : F) (target : W)
    (x0 : V) (hx0 : L x0 = target) :
    (∑ x : V, if L x = target then bitSign (M x + q) else 0) =
      if (M.comp (LinearMap.ker L).subtype) = 0 then
        (Fintype.card (LinearMap.ker L) : ℤ) * bitSign (M x0 + q)
      else 0 := by
  classical
  have htranslate :
      (∑ x : V, if L x = target then bitSign (M x + q) else 0) =
        ∑ x : V,
          if L (addRightF2Equiv x0 x) = target then
            bitSign (M (addRightF2Equiv x0 x) + q)
          else 0 := by
    simpa using
      (((addRightF2Equiv x0).sum_comp
        (fun x : V => if L x = target then bitSign (M x + q) else 0)).symm)
  rw [htranslate]
  have hreduce :
      (∑ x : V,
          if L (addRightF2Equiv x0 x) = target then
            bitSign (M (addRightF2Equiv x0 x) + q)
          else 0)
        =
      (∑ x : V, if L x = 0 then bitSign (M x + (M x0 + q)) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    change
      (if L (x + x0) = target then bitSign (M (x + x0) + q) else 0)
        =
      (if L x = 0 then bitSign (M x + (M x0 + q)) else 0)
    have hcond : L (x + x0) = target ↔ L x = 0 := by
      rw [map_add, hx0]
      constructor
      · intro h
        simpa using h
      · intro h
        simp [h]
    have hvalue : M (x + x0) + q = M x + (M x0 + q) := by
      rw [map_add]
      ac_rfl
    by_cases hleft : L (x + x0) = target
    · have hx : L x = 0 := hcond.mp hleft
      simp only [hleft, hx, ↓reduceIte]
      exact congrArg bitSign hvalue
    · have hx : L x ≠ 0 := by
        intro hx
        exact hleft (hcond.mpr hx)
      simp only [hleft, hx, ↓reduceIte]
  rw [hreduce]
  simpa using
    sum_if_linearMap_eq_zero_bitSign_linearMap_add_const
      (V := V) (W := W) L M (M x0 + q)

theorem sum_if_linearMap_eq_const_bitSign_linearMap_add_const_of_not_exists
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) (M : V →ₗ[F] F) (q : F) (target : W)
    (hno : ¬ ∃ x0 : V, L x0 = target) :
    (∑ x : V, if L x = target then bitSign (M x + q) else 0) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro x _
  have hx : L x ≠ target := by
    intro h
    exact hno ⟨x, h⟩
  simp [hx]

theorem sum_if_linearMap_eq_const_bitSign_linearMap_add_const
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) [Fintype (LinearMap.ker L)]
    (M : V →ₗ[F] F) (q : F) (target : W) :
    (∑ x : V, if L x = target then bitSign (M x + q) else 0) =
      if htarget : ∃ x0 : V, L x0 = target then
        if (M.comp (LinearMap.ker L).subtype) = 0 then
          (Fintype.card (LinearMap.ker L) : ℤ) *
            bitSign (M (Classical.choose htarget) + q)
        else 0
      else 0 := by
  classical
  by_cases htarget : ∃ x0 : V, L x0 = target
  · rw [dif_pos htarget]
    exact
      sum_if_linearMap_eq_const_bitSign_linearMap_add_const_of_preimage
        (V := V) (W := W) L M q target
        (Classical.choose htarget) (Classical.choose_spec htarget)
  · rw [dif_neg htarget]
    exact
      sum_if_linearMap_eq_const_bitSign_linearMap_add_const_of_not_exists
        (V := V) (W := W) L M q target htarget

noncomputable def linearMapFiberSignValue
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) [Fintype (LinearMap.ker L)]
    (M : V →ₗ[F] F) (q : F) (target : W) : ℤ := by
  classical
  exact
    if htarget : ∃ x0 : V, L x0 = target then
      if (M.comp (LinearMap.ker L).subtype) = 0 then
        (Fintype.card (LinearMap.ker L) : ℤ) *
          bitSign (M (Classical.choose htarget) + q)
      else 0
    else 0

theorem sum_if_linearMap_eq_const_bitSign_linearMap_add_const_eq_fiberSignValue
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) [Fintype (LinearMap.ker L)]
    (M : V →ₗ[F] F) (q : F) (target : W) :
    (∑ x : V, if L x = target then bitSign (M x + q) else 0) =
      linearMapFiberSignValue L M q target := by
  unfold linearMapFiberSignValue
  exact sum_if_linearMap_eq_const_bitSign_linearMap_add_const L M q target

theorem linearMapFiberSignValue_eq_of_preimage
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) [Fintype (LinearMap.ker L)]
    (M : V →ₗ[F] F) (q : F) (target : W)
    (x0 : V) (hx0 : L x0 = target) :
    linearMapFiberSignValue L M q target =
      if (M.comp (LinearMap.ker L).subtype) = 0 then
        (Fintype.card (LinearMap.ker L) : ℤ) * bitSign (M x0 + q)
      else 0 := by
  classical
  unfold linearMapFiberSignValue
  rw [dif_pos ⟨x0, hx0⟩]
  by_cases hM : (M.comp (LinearMap.ker L).subtype) = 0
  · rw [if_pos hM, if_pos hM]
    have hker :
        Classical.choose (⟨x0, hx0⟩ : ∃ x : V, L x = target) - x0
          ∈ LinearMap.ker L := by
      rw [LinearMap.mem_ker, map_sub,
        Classical.choose_spec (⟨x0, hx0⟩ : ∃ x : V, L x = target), hx0,
        sub_self]
    have hzero :
        M (Classical.choose (⟨x0, hx0⟩ : ∃ x : V, L x = target) - x0) = 0 := by
      have happly :=
        congrArg
          (fun L' : LinearMap.ker L →ₗ[F] F =>
            L' ⟨Classical.choose (⟨x0, hx0⟩ : ∃ x : V, L x = target) - x0, hker⟩)
          hM
      simpa using happly
    have hMx :
        M (Classical.choose (⟨x0, hx0⟩ : ∃ x : V, L x = target)) = M x0 := by
      rw [map_sub] at hzero
      exact sub_eq_zero.mp hzero
    rw [hMx]
  · rw [if_neg hM, if_neg hM]

theorem linearMapFiberSignValue_eq_zero_of_not_exists
    {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [DecidableEq W]
    (L : V →ₗ[F] W) [Fintype (LinearMap.ker L)]
    (M : V →ₗ[F] F) (q : F) (target : W)
    (htarget : ¬ ∃ x0 : V, L x0 = target) :
    linearMapFiberSignValue L M q target = 0 := by
  classical
  unfold linearMapFiberSignValue
  rw [dif_neg htarget]

end

end Core4loop
