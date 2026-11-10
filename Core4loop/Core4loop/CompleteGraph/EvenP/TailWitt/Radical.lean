import Core4loop.CompleteGraph.EvenP.TailWitt.Gram

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.TailWitt

open Core4loop
open Core4loop.CompleteGraph.EvenP

noncomputable section

/-! ## Generic coordinate radical -/

noncomputable abbrev K4TailCoordinateRadical
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L) :=
  LinearMap.ker (k4TailCoordinateGram (R := R) B)

theorem k4TailCoordinateGram_mem_ker_iff
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R)) (v : R → L) :
    v ∈ LinearMap.ker (k4TailCoordinateGram B) ↔
      ∀ s, v s ∈ LinearMap.ker B := by
  classical
  constructor
  · intro hv s
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    let probe : R → L := Pi.single s y
    have hzero := LinearMap.congr_fun (LinearMap.mem_ker.mp hv)
      (k4TailGramJ R L probe)
    rw [k4TailCoordinateGram_apply,
      k4TailGramJ_sq_apply heven] at hzero
    rw [Finset.sum_eq_single s] at hzero
    · simpa [probe] using hzero
    · intro r hr hrs
      rw [show probe r = 0 by
        simp [probe, Pi.single_eq_of_ne hrs]]
      simp
    · simp [probe]
  · intro hv
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro w
    rw [k4TailCoordinateGram_apply]
    apply Finset.sum_eq_zero
    intro s hs
    have hBs := LinearMap.mem_ker.mp (hv s)
    exact LinearMap.congr_fun hBs (k4TailGramJ R L w s)

noncomputable def k4TailCoordinateRadicalRead
    (R L : Type*) [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R)) :
    K4TailCoordinateRadical (R := R) B →ₗ[F]
      (R → LinearMap.ker B) where
  toFun v := fun s =>
    ⟨v.1 s,
      (k4TailCoordinateGram_mem_ker_iff B heven v.1).mp v.2 s⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def k4TailCoordinateRadicalBuild
    (R L : Type*) [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R)) :
    (R → LinearMap.ker B) →ₗ[F]
      K4TailCoordinateRadical (R := R) B where
  toFun f :=
    ⟨fun s => (f s).1,
      (k4TailCoordinateGram_mem_ker_iff B heven
        (fun s => (f s).1)).mpr (fun s => (f s).2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem k4TailCoordinateRadicalRead_build
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R))
    (f : R → LinearMap.ker B) :
    k4TailCoordinateRadicalRead R L B heven
        (k4TailCoordinateRadicalBuild R L B heven f) = f := by
  funext s
  apply Subtype.ext
  rfl

@[simp] theorem k4TailCoordinateRadicalBuild_read
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R))
    (v : K4TailCoordinateRadical (R := R) B) :
    k4TailCoordinateRadicalBuild R L B heven
        (k4TailCoordinateRadicalRead R L B heven v) = v := by
  apply Subtype.ext
  funext s
  rfl

noncomputable def k4TailCoordinateRadicalEquiv
    (R L : Type*) [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R)) :
    K4TailCoordinateRadical (R := R) B ≃ₗ[F]
      (R → LinearMap.ker B) where
  toLinearMap := k4TailCoordinateRadicalRead R L B heven
  invFun := k4TailCoordinateRadicalBuild R L B heven
  left_inv := k4TailCoordinateRadicalBuild_read B heven
  right_inv := k4TailCoordinateRadicalRead_build B heven

theorem k4TailCoordinateRadical_annihilates_right
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v : K4TailCoordinateRadical (R := R) B)
    (w : R → L) :
    k4TailCoordinateGram B w v.1 = 0 := by
  rw [k4TailCoordinateGram_comm B hsym]
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp v.2) w

/-! ## Quadratic vanishing on the coordinate radical -/

private theorem k4TailPairSumList_map_eq_zero_of_mem_ker
    {R L : Type*}
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (v : R → L) (hv : ∀ s, v s ∈ LinearMap.ker B)
    (rs : List R) :
    k4TailPairSumList B (rs.map v) = 0 := by
  induction rs with
  | nil => simp [k4TailPairSumList]
  | cons r rs ih =>
      simp only [List.map_cons, k4TailPairSumList]
      have hr := LinearMap.mem_ker.mp (hv r)
      have hhead :
          (List.map (fun y => B (v r) y) (List.map v rs)).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz
        rw [List.mem_map] at hz
        rcases hz with ⟨y, hy, rfl⟩
        exact LinearMap.congr_fun hr y
      rw [hhead, ih, add_zero]

theorem k4TailCoordinatePairSum_eq_zero_of_pointwise_mem_ker
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (v : R → L) (hv : ∀ s, v s ∈ LinearMap.ker B) :
    k4TailCoordinatePairSum B v = 0 := by
  unfold k4TailCoordinatePairSum
  exact k4TailPairSumList_map_eq_zero_of_mem_ker
    B v hv Finset.univ.toList

theorem k4TailCoordinatePairSum_eq_zero_on_radical
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R))
    (v : K4TailCoordinateRadical (R := R) B) :
    k4TailCoordinatePairSum B v.1 = 0 := by
  apply k4TailCoordinatePairSum_eq_zero_of_pointwise_mem_ker
  exact (k4TailCoordinateGram_mem_ker_iff B heven v.1).mp v.2

/-! ## Finrank consequences of the explicit radical equivalence -/

theorem finrank_k4TailCoordinateRadical
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L] [FiniteDimensional F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R)) :
    Module.finrank F (K4TailCoordinateRadical (R := R) B) =
      Fintype.card R * Module.finrank F (LinearMap.ker B) := by
  rw [LinearEquiv.finrank_eq
    (k4TailCoordinateRadicalEquiv R L B heven)]
  simp [Module.finrank_pi_fintype]

theorem finrank_range_k4TailCoordinateGram
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L] [FiniteDimensional F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R)) :
    Module.finrank F (LinearMap.range (k4TailCoordinateGram (R := R) B)) =
      Fintype.card R * Module.finrank F (LinearMap.range B) := by
  have hgram := LinearMap.finrank_range_add_finrank_ker
    (k4TailCoordinateGram (R := R) B)
  have hbase := LinearMap.finrank_range_add_finrank_ker B
  have hscaled := congrArg
    (fun q : Nat => Fintype.card R * q) hbase
  have hdom :
      Module.finrank F (R → L) =
        Fintype.card R * Module.finrank F L := by
    simp [Module.finrank_pi_fintype]
  rw [finrank_k4TailCoordinateRadical B heven, hdom] at hgram
  change
    Fintype.card R *
        (Module.finrank F (LinearMap.range B) +
          Module.finrank F (LinearMap.ker B)) =
      Fintype.card R * Module.finrank F L at hscaled
  rw [Nat.mul_add] at hscaled
  omega

/-! ## Exact K4 specialization -/

noncomputable abbrev K4EvenPTailCoordinateRadical
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a) :=
  LinearMap.ker (k4EvenPTailCoordinateGram
    (n := n) (a := a) (b := b) (c := c) (d := d) t0)

noncomputable def k4EvenPTailCoordinateRadicalEquiv
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a) :
    K4EvenPTailCoordinateRadical
        (n := n) (a := a) (b := b) (c := c) (d := d) t0 ≃ₗ[F]
      (PointedTail (K4EvenPTailIndex n a) t0 →
        LinearMap.ker (k4EvenPGPolar
          (n := n) (b := b) (c := c) (d := d))) :=
  k4TailCoordinateRadicalEquiv
    (PointedTail (K4EvenPTailIndex n a) t0)
    (K4EvenPLeft n b c d)
    k4EvenPGPolar
    (k4EvenPTailCoordinateIndex_card_even hn ha2 t0)

theorem k4EvenPTailCoordinateRadical_annihilates_right
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a)
    (v : K4EvenPTailCoordinateRadical
      (n := n) (a := a) (b := b) (c := c) (d := d) t0)
    (w : PointedTail (K4EvenPTailIndex n a) t0 →
      K4EvenPLeft n b c d) :
    k4EvenPTailCoordinateGram t0 w v.1 = 0 := by
  exact k4TailCoordinateRadical_annihilates_right
    k4EvenPGPolar k4EvenPGPolar_comm v w

theorem k4EvenPTailCoordinatePairSum_eq_zero_on_radical
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a)
    (v : K4EvenPTailCoordinateRadical
      (n := n) (a := a) (b := b) (c := c) (d := d) t0) :
    k4TailCoordinatePairSum k4EvenPGPolar v.1 = 0 := by
  exact k4TailCoordinatePairSum_eq_zero_on_radical
    k4EvenPGPolar
    (k4EvenPTailCoordinateIndex_card_even hn ha2 t0) v

theorem k4EvenPTailQ_build_eq_zero_on_coordinateRadical
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a)
    (v : K4EvenPTailCoordinateRadical
      (n := n) (a := a) (b := b) (c := c) (d := d) t0) :
    k4EvenPTailQ
        (k4TailZeroSumBuild
          (K4EvenPTailIndex n a) (K4EvenPLeft n b c d) t0 v.1) = 0 := by
  rw [k4EvenPTailQ_build_eq_pairSum]
  exact k4EvenPTailCoordinatePairSum_eq_zero_on_radical hn ha2 t0 v

theorem finrank_k4EvenPTailCoordinateRadical
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a) :
    Module.finrank F
        (K4EvenPTailCoordinateRadical
          (n := n) (a := a) (b := b) (c := c) (d := d) t0) =
      Fintype.card
          (PointedTail (K4EvenPTailIndex n a) t0) *
        Module.finrank F (LinearMap.ker (k4EvenPGPolar
          (n := n) (b := b) (c := c) (d := d))) := by
  exact finrank_k4TailCoordinateRadical
    k4EvenPGPolar
    (k4EvenPTailCoordinateIndex_card_even hn ha2 t0)

theorem finrank_range_k4EvenPTailCoordinateGram
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a) :
    Module.finrank F
        (LinearMap.range (k4EvenPTailCoordinateGram
          (n := n) (a := a) (b := b) (c := c) (d := d) t0)) =
      Fintype.card
          (PointedTail (K4EvenPTailIndex n a) t0) *
        Module.finrank F (LinearMap.range (k4EvenPGPolar
          (n := n) (b := b) (c := c) (d := d))) := by
  exact finrank_range_k4TailCoordinateGram
    k4EvenPGPolar
    (k4EvenPTailCoordinateIndex_card_even hn ha2 t0)

end

end Core4loop.CompleteGraph.EvenP.TailWitt
