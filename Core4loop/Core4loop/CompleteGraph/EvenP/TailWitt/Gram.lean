import Core4loop.CompleteGraph.EvenP.TailWitt.Coordinates

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.TailWitt

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

private theorem k4Tail_value_add_self
    {L : Type*} [AddCommGroup L] [Module F L] (x : L) :
    x + x = 0 := by
  rw [← two_smul F x, show (2 : F) = 0 by decide, zero_smul]

/-! ## Even coordinate-tail cardinality -/

theorem k4TailPointed_card_even
    {T : Type*} [Fintype T] [DecidableEq T]
    (t0 : T) (hodd : Odd (Fintype.card T)) :
    Even (Fintype.card (PointedTail T t0)) := by
  have htail :
      Fintype.card (PointedTail T t0) = Fintype.card T - 1 := by
    calc
      Fintype.card (PointedTail T t0) =
          Fintype.card T - Fintype.card {t : T // t = t0} := by
            exact Fintype.card_subtype_compl (fun t : T => t = t0)
      _ = Fintype.card T - 1 := by
            rw [Fintype.card_subtype_eq t0]
  rcases hodd with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [htail, hk]
  omega

theorem k4EvenPTailCoordinateIndex_card_even
    {n a : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a) :
    Even
      (Fintype.card
        (PointedTail (K4EvenPTailIndex n a) t0)) :=
  k4TailPointed_card_even t0 (k4EvenPTailIndex_card_odd hn ha2)

/-! ## The off-diagonal Gram involution -/

noncomputable def k4TailGramJ
    (R L : Type*) [Fintype R]
    [AddCommGroup L] [Module F L] :
    (R → L) →ₗ[F] (R → L) where
  toFun v := fun s => v s + ∑ r, v r
  map_add' v w := by
    funext s
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    abel
  map_smul' c v := by
    funext s
    simp only [Pi.smul_apply]
    rw [← Finset.smul_sum, smul_add]
    rfl

@[simp] theorem k4TailGramJ_apply
    (R L : Type*) [Fintype R]
    [AddCommGroup L] [Module F L]
    (v : R → L) (s : R) :
    k4TailGramJ R L v s = v s + ∑ r, v r := rfl

theorem k4TailGramJ_apply_eq_sum_ne
    (R L : Type*) [Fintype R] [DecidableEq R]
    [AddCommGroup L] [Module F L]
    (v : R → L) (s : R) :
    k4TailGramJ R L v s =
      ∑ r ∈ (Finset.univ : Finset R) with r ≠ s, v r := by
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset R)) (p := fun r : R => r ≠ s) v).symm
  have hdiag :
      (∑ r ∈ (Finset.univ : Finset R) with ¬r ≠ s, v r) = v s := by
    rw [Finset.sum_eq_single s]
    · intro r hr hrs
      exact (hrs (not_not.mp (Finset.mem_filter.mp hr).2)).elim
    · simp
  rw [hdiag] at hpart
  rw [k4TailGramJ_apply]
  calc
    v s + ∑ r, v r =
        v s +
          ((∑ r ∈ (Finset.univ : Finset R) with r ≠ s, v r) + v s) := by
            rw [hpart]
    _ = (v s + v s) +
          ∑ r ∈ (Finset.univ : Finset R) with r ≠ s, v r := by
          abel
    _ = ∑ r ∈ (Finset.univ : Finset R) with r ≠ s, v r := by
          rw [k4Tail_value_add_self, zero_add]

private theorem k4Tail_sum_const_zero_of_even
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (heven : Even (Fintype.card R)) (x : L) :
    (∑ _ : R, x) = 0 := by
  rcases heven with ⟨k, hk⟩
  rw [Finset.sum_const, Finset.card_univ, hk, add_nsmul]
  exact add_eq_zero_iff_eq_of_F_module _ _ |>.mpr rfl

private theorem k4TailGramJ_sum
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (heven : Even (Fintype.card R)) (v : R → L) :
    (∑ s, k4TailGramJ R L v s) = ∑ s, v s := by
  simp only [k4TailGramJ_apply]
  rw [Finset.sum_add_distrib,
    k4Tail_sum_const_zero_of_even heven, add_zero]

@[simp] theorem k4TailGramJ_sq_apply
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (heven : Even (Fintype.card R)) (v : R → L) :
    k4TailGramJ R L (k4TailGramJ R L v) = v := by
  funext s
  rw [k4TailGramJ_apply, k4TailGramJ_apply,
    k4TailGramJ_sum heven, add_assoc, k4Tail_value_add_self, add_zero]

noncomputable def k4TailGramJEquiv
    (R L : Type*) [Fintype R]
    [AddCommGroup L] [Module F L]
    (heven : Even (Fintype.card R)) :
    (R → L) ≃ₗ[F] (R → L) where
  toLinearMap := k4TailGramJ R L
  invFun := k4TailGramJ R L
  left_inv := k4TailGramJ_sq_apply heven
  right_inv := k4TailGramJ_sq_apply heven

/-! ## Coordinate Gram map -/

def k4TailCoordinateGramScalar
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (v w : R → L) : F :=
  ∑ s, B (v s) (k4TailGramJ R L w s)

noncomputable def k4TailCoordinateGram
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L) :
    (R → L) →ₗ[F] Module.Dual F (R → L) :=
  LinearMap.mk₂ F (k4TailCoordinateGramScalar B)
    (by
      intro v w z
      unfold k4TailCoordinateGramScalar
      simp only [Pi.add_apply, map_add, LinearMap.add_apply,
        Finset.sum_add_distrib])
    (by
      intro c v w
      unfold k4TailCoordinateGramScalar
      simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply,
        ]
      exact Finset.smul_sum.symm)
    (by
      intro v w z
      unfold k4TailCoordinateGramScalar
      rw [(k4TailGramJ R L).map_add]
      simp only [Pi.add_apply, map_add, Finset.sum_add_distrib])
    (by
      intro c v w
      unfold k4TailCoordinateGramScalar
      rw [(k4TailGramJ R L).map_smul]
      simp only [Pi.smul_apply, map_smul]
      exact Finset.smul_sum.symm)

@[simp] theorem k4TailCoordinateGram_apply
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (v w : R → L) :
    k4TailCoordinateGram B v w =
      ∑ s, B (v s) (k4TailGramJ R L w s) := rfl

theorem k4TailCoordinateGram_apply_eq_ordered_ne
    {R L : Type*} [Fintype R] [DecidableEq R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (v w : R → L) :
    k4TailCoordinateGram B v w =
      ∑ s, ∑ r ∈ (Finset.univ : Finset R) with r ≠ s,
        B (v s) (w r) := by
  rw [k4TailCoordinateGram_apply]
  apply Finset.sum_congr rfl
  intro s hs
  rw [k4TailGramJ_apply_eq_sum_ne]
  simpa only using
    (map_sum (B (v s)) w
      ((Finset.univ : Finset R).filter fun r => r ≠ s))

/-! ## Pair quadratic and its exact polar -/

private def k4TailPairCrossList
    {L : Type*} [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L) : List (L × L) → F
  | [] => 0
  | z :: zs =>
      (zs.map (fun u => B z.1 u.2 + B z.2 u.1)).sum +
        k4TailPairCrossList B zs

private theorem k4TailPairSumList_add
    {L : Type*} [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (zs : List (L × L)) :
    k4TailPairSumList B (zs.map (fun z => z.1 + z.2)) =
      k4TailPairSumList B (zs.map Prod.fst) +
        k4TailPairSumList B (zs.map Prod.snd) +
          k4TailPairCrossList B zs := by
  induction zs with
  | nil => simp [k4TailPairSumList, k4TailPairCrossList]
  | cons z zs ih =>
      simp only [List.map_cons, k4TailPairSumList, k4TailPairCrossList,
        List.map_map]
      rw [ih]
      have hhead :
          (List.map
            ((fun y => B (z.1 + z.2) y) ∘
              fun u : L × L => u.1 + u.2) zs).sum =
            (List.map ((fun y => B z.1 y) ∘ Prod.fst) zs).sum +
              (List.map ((fun y => B z.2 y) ∘ Prod.snd) zs).sum +
                (List.map
                  (fun u => B z.1 u.2 + B z.2 u.1) zs).sum := by
        simp only [Function.comp_def, map_add, LinearMap.add_apply]
        repeat' rw [List.sum_map_add]
        abel
      rw [hhead]
      abel

private theorem k4Tail_toList_map_sum_gram
    {R L : Type*} [Fintype R]
    [AddCommMonoid L] (v : R → L) :
    ((Finset.univ.toList).map v).sum = ∑ r, v r := by
  classical
  induction (Finset.univ : Finset R) using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih => simp [hr]

private def k4TailGramList
    {R L : Type*} [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (v w : R → L) (rs : List R) : F :=
  (rs.map (fun s => B (v s) (w s + (rs.map w).sum))).sum

private theorem k4TailGramList_cons
    {R L : Type*} [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v w : R → L) (r : R) (rs : List R) :
    k4TailGramList B v w (r :: rs) =
      (rs.map (fun s => B (v r) (w s) + B (w r) (v s))).sum +
        k4TailGramList B v w rs := by
  unfold k4TailGramList
  simp only [List.map_cons, List.sum_cons]
  have hhead :
      B (v r) (w r + (w r + (rs.map w).sum)) =
        (rs.map (fun s => B (v r) (w s))).sum := by
    calc
      B (v r) (w r + (w r + (rs.map w).sum)) =
          B (v r) ((rs.map w).sum) := by
            congr 1
            calc
              w r + (w r + (rs.map w).sum) =
                  (w r + w r) + (rs.map w).sum := by abel
              _ = (rs.map w).sum := by
                    rw [k4Tail_value_add_self, zero_add]
      _ = (rs.map (fun s => B (v r) (w s))).sum := by
            simpa only [List.map_map, Function.comp_apply] using
              (map_list_sum (B (v r)) (rs.map w))
  have htailMap :
      rs.map
          (fun s => B (v s)
            (w s + (w r + (rs.map w).sum))) =
        rs.map
          (fun s => B (w r) (v s) +
            B (v s) (w s + (rs.map w).sum)) := by
    apply List.map_congr_left
    intro s hs
    rw [← hsym (v s) (w r)]
    simp only [map_add]
    abel
  rw [hhead, htailMap, List.sum_map_add, List.sum_map_add]
  abel

private theorem k4TailPairCrossList_eq_gramList
    {R L : Type*} [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v w : R → L) (rs : List R) :
    k4TailPairCrossList B (rs.map (fun r => (v r, w r))) =
      k4TailGramList B v w rs := by
  induction rs with
  | nil => simp [k4TailPairCrossList, k4TailGramList]
  | cons r rs ih =>
      simp only [List.map_cons, k4TailPairCrossList]
      rw [ih, k4TailGramList_cons B hsym]
      congr 1
      simp only [List.map_map, Function.comp_def]

private theorem k4TailGramList_univ
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (v w : R → L) :
    k4TailGramList B v w Finset.univ.toList =
      k4TailCoordinateGramScalar B v w := by
  unfold k4TailGramList k4TailCoordinateGramScalar
  have hwsum := k4Tail_toList_map_sum_gram w
  rw [hwsum]
  simp only [k4TailGramJ_apply]
  exact k4Tail_toList_map_sum_gram
    (fun s => B (v s) (w s + ∑ r, w r))

theorem k4TailCoordinatePairSum_add
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v w : R → L) :
    k4TailCoordinatePairSum B (v + w) =
      k4TailCoordinatePairSum B v +
        k4TailCoordinatePairSum B w +
          k4TailCoordinateGram B v w := by
  unfold k4TailCoordinatePairSum
  let rs : List R := Finset.univ.toList
  let zs : List (L × L) := rs.map (fun r => (v r, w r))
  have hadd := k4TailPairSumList_add B zs
  have hcross := k4TailPairCrossList_eq_gramList B hsym v w rs
  change
    k4TailPairSumList B (rs.map (fun r => (v + w) r)) =
      k4TailPairSumList B (rs.map v) +
        k4TailPairSumList B (rs.map w) +
          k4TailCoordinateGram B v w
  rw [show rs.map (fun r => (v + w) r) =
      zs.map (fun z => z.1 + z.2) by
        simp [zs],
    show rs.map v = zs.map Prod.fst by simp [zs],
    show rs.map w = zs.map Prod.snd by simp [zs],
    hadd, hcross, k4TailGramList_univ]
  rfl

theorem k4TailCoordinateGram_comm
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v w : R → L) :
    k4TailCoordinateGram B v w =
      k4TailCoordinateGram B w v := by
  have hvw := k4TailCoordinatePairSum_add B hsym v w
  have hwv := k4TailCoordinatePairSum_add B hsym w v
  have hcancel :
      k4TailCoordinatePairSum B v +
          k4TailCoordinatePairSum B w +
            k4TailCoordinateGram B v w =
        k4TailCoordinatePairSum B v +
          k4TailCoordinatePairSum B w +
            k4TailCoordinateGram B w v := by
    calc
      k4TailCoordinatePairSum B v +
            k4TailCoordinatePairSum B w +
              k4TailCoordinateGram B v w =
          k4TailCoordinatePairSum B (v + w) := hvw.symm
      _ = k4TailCoordinatePairSum B (w + v) := by rw [add_comm v w]
      _ = k4TailCoordinatePairSum B w +
            k4TailCoordinatePairSum B v +
              k4TailCoordinateGram B w v := hwv
      _ = k4TailCoordinatePairSum B v +
            k4TailCoordinatePairSum B w +
              k4TailCoordinateGram B w v := by abel
  exact add_left_cancel hcancel

theorem k4TailCoordinatePairSum_polar_eq_gram
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v w : R → L) :
    k4TailCoordinatePairSum B (v + w) +
        k4TailCoordinatePairSum B v +
          k4TailCoordinatePairSum B w =
      k4TailCoordinateGram B v w := by
  rw [k4TailCoordinatePairSum_add B hsym]
  calc
    (k4TailCoordinatePairSum B v +
          k4TailCoordinatePairSum B w +
            k4TailCoordinateGram B v w) +
        k4TailCoordinatePairSum B v +
          k4TailCoordinatePairSum B w =
      (k4TailCoordinatePairSum B v +
          k4TailCoordinatePairSum B v) +
        (k4TailCoordinatePairSum B w +
          k4TailCoordinatePairSum B w) +
        k4TailCoordinateGram B v w := by abel
    _ = k4TailCoordinateGram B v w := by
      rw [F_add_self, F_add_self, zero_add, zero_add]

theorem k4TailCoordinatePairSum_polar_eq_ordered_ne
    {R L : Type*} [Fintype R] [DecidableEq R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v w : R → L) :
    k4TailCoordinatePairSum B (v + w) +
        k4TailCoordinatePairSum B v +
          k4TailCoordinatePairSum B w =
      ∑ s, ∑ r ∈ (Finset.univ : Finset R) with r ≠ s,
        B (v s) (w r) := by
  rw [k4TailCoordinatePairSum_polar_eq_gram B hsym,
    k4TailCoordinateGram_apply_eq_ordered_ne]

theorem k4TailCoordinateGram_apply_eq_ordered_ne_swap
    {R L : Type*} [Fintype R] [DecidableEq R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (v w : R → L) :
    k4TailCoordinateGram B v w =
      ∑ s, ∑ r ∈ (Finset.univ : Finset R) with r ≠ s,
        B (w s) (v r) := by
  rw [k4TailCoordinateGram_comm B hsym]
  exact k4TailCoordinateGram_apply_eq_ordered_ne B w v

/-! ## Exact K4 specialization -/

theorem k4EvenPGPolar_comm
    {n b c d : Nat} [NeZero n]
    (sigma tau : K4EvenPLeft n b c d) :
    k4EvenPGPolar sigma tau = k4EvenPGPolar tau sigma := by
  change k4EvenPSlicePolar sigma.1 tau.1 =
    k4EvenPSlicePolar tau.1 sigma.1
  unfold k4EvenPSlicePolar
  rw [add_comm]

noncomputable def k4EvenPTailCoordinateGram
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a) :
    (PointedTail (K4EvenPTailIndex n a) t0 →
        K4EvenPLeft n b c d) →ₗ[F]
      Module.Dual F
        (PointedTail (K4EvenPTailIndex n a) t0 →
          K4EvenPLeft n b c d) :=
  k4TailCoordinateGram k4EvenPGPolar

theorem k4EvenPTailCoordinatePairSum_add
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a)
    (v w : PointedTail (K4EvenPTailIndex n a) t0 →
      K4EvenPLeft n b c d) :
    k4TailCoordinatePairSum k4EvenPGPolar (v + w) =
      k4TailCoordinatePairSum k4EvenPGPolar v +
        k4TailCoordinatePairSum k4EvenPGPolar w +
          k4EvenPTailCoordinateGram t0 v w := by
  exact k4TailCoordinatePairSum_add
    k4EvenPGPolar k4EvenPGPolar_comm v w

theorem k4EvenPTailCoordinateGram_comm
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a)
    (v w : PointedTail (K4EvenPTailIndex n a) t0 →
      K4EvenPLeft n b c d) :
    k4EvenPTailCoordinateGram t0 v w =
      k4EvenPTailCoordinateGram t0 w v := by
  exact k4TailCoordinateGram_comm
    k4EvenPGPolar k4EvenPGPolar_comm v w

theorem k4EvenPTailCoordinatePairSum_polar_eq_gram
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a)
    (v w : PointedTail (K4EvenPTailIndex n a) t0 →
      K4EvenPLeft n b c d) :
    k4TailCoordinatePairSum k4EvenPGPolar (v + w) +
        k4TailCoordinatePairSum k4EvenPGPolar v +
          k4TailCoordinatePairSum k4EvenPGPolar w =
      k4EvenPTailCoordinateGram t0 v w := by
  exact k4TailCoordinatePairSum_polar_eq_gram
    k4EvenPGPolar k4EvenPGPolar_comm v w

theorem k4EvenPTailQ_build_add
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a)
    (v w : PointedTail (K4EvenPTailIndex n a) t0 →
      K4EvenPLeft n b c d) :
    k4EvenPTailQ
        (k4TailZeroSumBuild
          (K4EvenPTailIndex n a) (K4EvenPLeft n b c d) t0 (v + w)) =
      k4EvenPTailQ
          (k4TailZeroSumBuild
            (K4EvenPTailIndex n a) (K4EvenPLeft n b c d) t0 v) +
        k4EvenPTailQ
          (k4TailZeroSumBuild
            (K4EvenPTailIndex n a) (K4EvenPLeft n b c d) t0 w) +
          k4EvenPTailCoordinateGram t0 v w := by
  repeat' rw [k4EvenPTailQ_build_eq_pairSum]
  exact k4EvenPTailCoordinatePairSum_add t0 v w

end

end Core4loop.CompleteGraph.EvenP.TailWitt
