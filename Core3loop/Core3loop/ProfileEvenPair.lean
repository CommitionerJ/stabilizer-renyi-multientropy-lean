import Core3loop.OperatorT
import Core3loop.ProfileEvenTail

open scoped BigOperators

namespace Core3loop

noncomputable def evenPlaneCoordInv {a n : ℕ} [NeZero n] (z : F × F) :
    ↥(EvenPlane (a := a) (n := n)) := by
  rcases z with ⟨u, v⟩
  refine ⟨u • (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)) +
      v • eProfile (a := a) (n := n), ?_⟩
  refine Submodule.mem_sup.2 ?_
  refine ⟨u • (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)), ?_,
    v • eProfile (a := a) (n := n), ?_, rfl⟩
  · exact Submodule.mem_span_singleton.2 ⟨u, rfl⟩
  · exact Submodule.mem_span_singleton.2 ⟨v, rfl⟩

noncomputable def evenPlaneCoordMap {a n : ℕ} [NeZero n] :
    ↥(EvenPlane (a := a) (n := n)) →ₗ[F] F × F where
  toFun x := evenPairMap (a := a) (n := n) x.1
  map_add' := by
    intro x y
    simp
  map_smul' := by
    intro u x
    simp

lemma evenPlaneCoordMap_inv_apply {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (z : F × F) :
    evenPlaneCoordMap (a := a) (n := n) (evenPlaneCoordInv (a := a) (n := n) z) = z := by
  rcases z with ⟨u, v⟩
  have heven : Even (Fintype.card (XCoord a n)) := even_card_XCoord_of_even (a := a) hn ha2
  change evenPairMap (a := a) (n := n)
      (u • (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)) +
        v • eProfile (a := a) (n := n)) = (u, v)
  rw [LinearMap.map_add, LinearMap.map_smul, LinearMap.map_smul,
    evenPairMap_e_add_f (a := a) (n := n) heven, evenPairMap_eProfile (a := a) (n := n) heven]
  ext <;> simp

lemma evenPlaneCoordInv_map_apply {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (x : ↥(EvenPlane (a := a) (n := n))) :
    evenPlaneCoordInv (a := a) (n := n) (evenPlaneCoordMap (a := a) (n := n) x) = x := by
  apply Subtype.ext
  have hxP : (x : ProfileABC a n) ∈ EvenPlane (a := a) (n := n) := x.2
  have hzU :
      (x : ProfileABC a n) +
          (evenPlaneCoordInv (a := a) (n := n)
            (evenPlaneCoordMap (a := a) (n := n) x)).1 ∈
        Ueven (a := a) (n := n) := by
    change evenPairMap (a := a) (n := n)
        ((x : ProfileABC a n) +
          (evenPlaneCoordInv (a := a) (n := n)
            (evenPlaneCoordMap (a := a) (n := n) x)).1) = 0
    rw [LinearMap.map_add]
    change evenPlaneCoordMap (a := a) (n := n) x +
        evenPlaneCoordMap (a := a) (n := n)
          (evenPlaneCoordInv (a := a) (n := n)
            (evenPlaneCoordMap (a := a) (n := n) x)) = 0
    rw [evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2]
    ext <;> simp [evenPlaneCoordMap, F_add_self]
  have hzP :
      (x : ProfileABC a n) +
          (evenPlaneCoordInv (a := a) (n := n)
            (evenPlaneCoordMap (a := a) (n := n) x)).1 ∈
        EvenPlane (a := a) (n := n) := by
    exact Submodule.add_mem _ hxP
      (evenPlaneCoordInv (a := a) (n := n)
        (evenPlaneCoordMap (a := a) (n := n) x)).2
  have hdisj := evenPlane_disjoint_Ueven (a := a) (n := n)
    (even_card_XCoord_of_even (a := a) hn ha2)
  rw [Submodule.disjoint_def] at hdisj
  have hz0 :
      (x : ProfileABC a n) +
          (evenPlaneCoordInv (a := a) (n := n)
            (evenPlaneCoordMap (a := a) (n := n) x)).1 = 0 :=
    hdisj _ hzP hzU
  calc
    (evenPlaneCoordInv (a := a) (n := n)
        (evenPlaneCoordMap (a := a) (n := n) x)).1
      =
        (evenPlaneCoordInv (a := a) (n := n)
          (evenPlaneCoordMap (a := a) (n := n) x)).1 +
          ((x : ProfileABC a n) +
            (evenPlaneCoordInv (a := a) (n := n)
              (evenPlaneCoordMap (a := a) (n := n) x)).1) := by
            rw [hz0]
            simp
    _ = x := by
          funext p
          simp [add_assoc, add_left_comm, add_comm, F_add_self]

lemma dot_evenPlaneCoordInv_right {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (z : F × F) (y : ProfileABC a n) :
    dotProfile (a := a) (n := n) (evenPlaneCoordInv (a := a) (n := n) z).1 y =
      z.1 * (evenPairMap (a := a) (n := n) y).1 +
        z.1 * (evenPairMap (a := a) (n := n) y).2 +
          z.2 * (evenPairMap (a := a) (n := n) y).1 := by
  rcases z with ⟨u, v⟩
  have heven : Even (Fintype.card (XCoord a n)) := even_card_XCoord_of_even (a := a) hn ha2
  change
    dotProfile (a := a) (n := n)
      (u • (eProfile (a := a) (n := n) + fProfile (a := a) (n := n)) +
        v • eProfile (a := a) (n := n)) y =
      u * (evenPairMap (a := a) (n := n) y).1 +
        u * (evenPairMap (a := a) (n := n) y).2 +
          v * (evenPairMap (a := a) (n := n) y).1
  rw [dot_add_left, dot_smul_left, dot_smul_left, dot_add_left]
  simp [evenPairMap, dot_eProfile_eProfile_even (a := a) (n := n) heven,
    dot_eProfile_fProfile, dot_fProfile_fProfile, dot_comm,
    add_assoc, add_left_comm, add_comm]
  rw [mul_add]
  ac_rfl

lemma dot_evenPlaneCoordInv_left {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (x : ProfileABC a n) (z : F × F) :
    dotProfile (a := a) (n := n) x (evenPlaneCoordInv (a := a) (n := n) z).1 =
      (evenPairMap (a := a) (n := n) x).1 * z.1 +
        (evenPairMap (a := a) (n := n) x).2 * z.1 +
          (evenPairMap (a := a) (n := n) x).1 * z.2 := by
  rw [dot_comm, dot_evenPlaneCoordInv_right (a := a) (n := n) hn ha2 z x]
  simp [mul_comm, add_assoc, add_left_comm, add_comm]

lemma dot_evenPlaneCoordInv_uEven_eq_zero {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (z : F × F) {y : ProfileABC a n}
    (hy : y ∈ Ueven (a := a) (n := n)) :
    dotProfile (a := a) (n := n) (evenPlaneCoordInv (a := a) (n := n) z).1 y = 0 := by
  change evenPairMap (a := a) (n := n) y = 0 at hy
  rw [dot_evenPlaneCoordInv_right (a := a) (n := n) hn ha2 z y, hy]
  simp

lemma dot_uEven_evenPlaneCoordInv_eq_zero {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) {x : ProfileABC a n}
    (hx : x ∈ Ueven (a := a) (n := n)) (z : F × F) :
    dotProfile (a := a) (n := n) x (evenPlaneCoordInv (a := a) (n := n) z).1 = 0 := by
  rw [dot_comm]
  exact dot_evenPlaneCoordInv_uEven_eq_zero (a := a) (n := n) hn ha2 z hx

lemma dot_nondegenerate_on_Ueven {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) {x : ProfileABC a n}
    (hxU : x ∈ Ueven (a := a) (n := n))
    (hx : ∀ y : ProfileABC a n, y ∈ Ueven (a := a) (n := n) →
      dotProfile (a := a) (n := n) x y = 0) :
    x = 0 := by
  apply dot_nondegenerate
  intro y
  have hyTop : y ∈ (⊤ : Submodule F (ProfileABC a n)) := by simp
  rw [← evenPlane_sup_Ueven_eq_top (a := a) (n := n)
    (even_card_XCoord_of_even (a := a) hn ha2)] at hyTop
  rcases Submodule.mem_sup.1 hyTop with ⟨e, heP, u, huU, rfl⟩
  rw [dot_add_right, hx u huU]
  let e' : ↥(EvenPlane (a := a) (n := n)) := ⟨e, heP⟩
  have heq :
      (evenPlaneCoordInv (a := a) (n := n)
        (evenPlaneCoordMap (a := a) (n := n) e')).1 = e := by
    exact congrArg Subtype.val
      (evenPlaneCoordInv_map_apply (a := a) (n := n) hn ha2 e')
  rw [← heq]
  simpa using
    dot_uEven_evenPlaneCoordInv_eq_zero (a := a) (n := n) hn ha2 hxU
      (evenPlaneCoordMap (a := a) (n := n) e')

lemma exists_dot_one_on_Ueven {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) {x : Ueven (a := a) (n := n)}
    (hx : x ≠ 0) :
    ∃ y : Ueven (a := a) (n := n), dotProfile (a := a) (n := n) y.1 x.1 = 1 := by
  by_contra h
  have hx0 : x.1 = 0 := by
    apply dot_nondegenerate_on_Ueven (a := a) (n := n) hn ha2 x.2
    intro y hy
    have hneq1 : dotProfile (a := a) (n := n) x.1 y ≠ 1 := by
      intro h1
      exact h ⟨⟨y, hy⟩, by simpa [dot_comm] using h1⟩
    let z : F := dotProfile (a := a) (n := n) x.1 y
    have hcases : z = 0 ∨ z = 1 := by
      by_cases hz : z = 0
      · exact Or.inl hz
      · exact Or.inr (F_ne_zero_eq_one z hz)
    rcases hcases with h0 | h1
    · simpa [z] using h0
    · exact False.elim (hneq1 (by simpa [z] using h1))
  exact hx (Subtype.ext hx0)

noncomputable def evenTailPairModelABC {a c n : ℕ} [NeZero n]
    (XB ZB : EvenTailBModelABC a c n) : F :=
  ∑ t : I n, ∑ z : ZCoord c n,
    dotProfile (a := a) (n := n) (XB t z).1 (ZB t z).1

noncomputable def toggleAtEvenTailBModelABC {a c n : ℕ} [NeZero n]
    (u0 : I n × ZCoord c n) (y0 : Ueven (a := a) (n := n))
    (XB : EvenTailBModelABC a c n) : EvenTailBModelABC a c n :=
  fun t z => XB t z + if (t, z) = u0 then y0 else 0

noncomputable def toggleEquivEvenTailBModelABC {a c n : ℕ} [NeZero n]
    (u0 : I n × ZCoord c n) (y0 : Ueven (a := a) (n := n)) :
    EvenTailBModelABC a c n ≃ EvenTailBModelABC a c n where
  toFun := toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0
  invFun := toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0
  left_inv := by
    intro XB
    funext t z
    by_cases h : (t, z) = u0
    · have hyy : y0 + y0 = 0 := by
        apply Subtype.ext
        funext p
        simp [F_add_self]
      simpa [toggleAtEvenTailBModelABC, h, add_assoc] using hyy
    · simp [toggleAtEvenTailBModelABC, h]
  right_inv := by
    intro XB
    funext t z
    by_cases h : (t, z) = u0
    · have hyy : y0 + y0 = 0 := by
        apply Subtype.ext
        funext p
        simp [F_add_self]
      simpa [toggleAtEvenTailBModelABC, h, add_assoc] using hyy
    · simp [toggleAtEvenTailBModelABC, h]

lemma toggleAtEvenTailBModelABC_apply {a c n : ℕ} [NeZero n]
    (u0 : I n × ZCoord c n) (y0 : Ueven (a := a) (n := n))
    (XB : EvenTailBModelABC a c n) (t : I n) (z : ZCoord c n) :
    toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0 XB t z =
      XB t z + if (t, z) = u0 then y0 else 0 := by
  rfl

lemma evenTailPairModelABC_zero_right {a c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) :
    evenTailPairModelABC (a := a) (c := c) (n := n) XB 0 = 0 := by
  unfold evenTailPairModelABC
  simp [dotProfile]

lemma evenTailPairModelABC_toggleAt {a c n : ℕ} [NeZero n]
    (u0 : I n × ZCoord c n) (y0 : Ueven (a := a) (n := n))
    (XB MB : EvenTailBModelABC a c n)
    (hm : dotProfile (a := a) (n := n) y0.1 (MB u0.1 u0.2).1 = 1) :
    evenTailPairModelABC (a := a) (c := c) (n := n)
      (toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0 XB) MB =
        evenTailPairModelABC (a := a) (c := c) (n := n) XB MB + 1 := by
  rcases u0 with ⟨t0, z0⟩
  unfold evenTailPairModelABC
  have hsplit :
      ∀ t : I n, ∀ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          ((toggleAtEvenTailBModelABC (a := a) (c := c) (n := n)
            (t0, z0) y0 XB t z).1)
          (MB t z).1 =
            dotProfile (a := a) (n := n) (XB t z).1 (MB t z).1 +
              dotProfile (a := a) (n := n)
                ((if (t, z) = (t0, z0) then y0 else 0).1)
                (MB t z).1 := by
    intro t z
    rw [toggleAtEvenTailBModelABC_apply]
    change
      dotProfile (a := a) (n := n)
        ((XB t z).1 + (if (t, z) = (t0, z0) then y0 else 0).1)
        (MB t z).1 = _
    rw [dot_add_left]
  simp_rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  have hs :
      ∑ t : I n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          ((if (t, z) = (t0, z0) then y0 else 0).1)
          (MB t z).1 = 1 := by
    rw [Finset.sum_eq_single t0]
    · rw [Finset.sum_eq_single z0]
      · simpa using hm
      · intro z hz hne
        simp [hne, dotProfile]
      · simp
    · intro t ht hne
      simp [hne, dotProfile]
    · simp
  rw [hs]

lemma sum_bitSign_evenTailPairModelABC {a c n : ℕ} [NeZero n]
    [DecidableEq (EvenTailBModelABC a c n)]
    (hn : Even n) (ha2 : 2 ≤ a) (MB : EvenTailBModelABC a c n) :
    ∑ XB : EvenTailBModelABC a c n,
      bitSign (evenTailPairModelABC (a := a) (c := c) (n := n) XB MB) =
        if h : MB = 0 then Fintype.card (EvenTailBModelABC a c n) else 0 := by
  classical
  by_cases hm : MB = 0
  · subst MB
    have hsum :
        ∑ XB : EvenTailBModelABC a c n,
            bitSign (evenTailPairModelABC (a := a) (c := c) (n := n) XB 0) =
          Fintype.card (EvenTailBModelABC a c n) := by
      calc
      ∑ XB : EvenTailBModelABC a c n,
          bitSign (evenTailPairModelABC (a := a) (c := c) (n := n) XB 0)
        =
          ∑ XB : EvenTailBModelABC a c n, (1 : ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro XB hXB
            rw [evenTailPairModelABC_zero_right]
            simpa using No13Migration.bitSign_zero
      _ = Fintype.card (EvenTailBModelABC a c n) := by simp
    simpa using hsum
  · have hex : ∃ u0 : I n × ZCoord c n, MB u0.1 u0.2 ≠ 0 := by
      by_contra h
      apply hm
      funext t z
      by_cases hz : MB t z = 0
      · exact hz
      · exact False.elim (h ⟨(t, z), hz⟩)
    rcases hex with ⟨u0, hu0⟩
    rcases exists_dot_one_on_Ueven (a := a) (n := n) hn ha2 hu0 with ⟨y0, hy0⟩
    let S : ℤ := ∑ XB : EvenTailBModelABC a c n,
      bitSign (evenTailPairModelABC (a := a) (c := c) (n := n) XB MB)
    have htoggle :
        S =
          ∑ XB : EvenTailBModelABC a c n,
            bitSign (evenTailPairModelABC (a := a) (c := c) (n := n)
              (toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0 XB) MB) := by
      simpa [S] using
        (((toggleEquivEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0).symm.sum_comp
          (fun XB : EvenTailBModelABC a c n =>
            bitSign (evenTailPairModelABC (a := a) (c := c) (n := n) XB MB))).symm)
    have hneg :
        ∑ XB : EvenTailBModelABC a c n,
            bitSign (evenTailPairModelABC (a := a) (c := c) (n := n)
              (toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0 XB) MB)
          = -S := by
      calc
        ∑ XB : EvenTailBModelABC a c n,
            bitSign (evenTailPairModelABC (a := a) (c := c) (n := n)
              (toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0 XB) MB)
          = ∑ XB : EvenTailBModelABC a c n,
              -bitSign (evenTailPairModelABC (a := a) (c := c) (n := n) XB MB) := by
                refine Finset.sum_congr rfl ?_
                intro XB hXB
                rw [evenTailPairModelABC_toggleAt (a := a) (c := c) (n := n) u0 y0 XB MB hy0]
                simpa using
                  (No13Migration.bitSign_add_one
                    (evenTailPairModelABC (a := a) (c := c) (n := n) XB MB))
        _ = -S := by simp [S]
    have hs : S = -S := by
      calc
        S =
            ∑ XB : EvenTailBModelABC a c n,
              bitSign (evenTailPairModelABC (a := a) (c := c) (n := n)
                (toggleAtEvenTailBModelABC (a := a) (c := c) (n := n) u0 y0 XB) MB) := htoggle
        _ = -S := hneg
    have hzero : S = 0 := by linarith
    simpa [S, hm] using hzero

end Core3loop
