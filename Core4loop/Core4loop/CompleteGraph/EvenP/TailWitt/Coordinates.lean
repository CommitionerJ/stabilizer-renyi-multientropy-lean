import Core4loop.CompleteGraph.EvenP.Model

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.TailWitt

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

/-! ## Mandatory project-cardinality gate -/

theorem k4EvenPTailIndex_card_odd
    {n a : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a) :
    Odd (Fintype.card (K4EvenPTailIndex n a)) := by
  letI : Nonempty (PVec n a) := ⟨zeroVec⟩
  rcases even_card_PVec hn ha2 with ⟨k, hk⟩
  have hpos : 0 < Fintype.card (PVec n a) := Fintype.card_pos
  have htail :
      Fintype.card (K4EvenPTailIndex n a) =
        Fintype.card (PVec n a) - 1 := by
    calc
      Fintype.card (K4EvenPTailIndex n a) =
          Fintype.card (PVec n a) -
            Fintype.card {p : PVec n a // p = zeroVec} := by
              exact Fintype.card_subtype_compl
                (fun p : PVec n a => p = zeroVec)
      _ = Fintype.card (PVec n a) - 1 := by
            rw [Fintype.card_subtype_eq (zeroVec : PVec n a)]
  refine ⟨k - 1, ?_⟩
  rw [htail]
  rw [hk]
  omega

/-! ## Generic zero-sum coordinates -/

noncomputable abbrev K4TailZeroSum
    (T L : Type*) [Fintype T]
    [AddCommGroup L] [Module F L] :=
  LinearMap.ker
    (fintypeSumLinearMap (S := T) (V := L))

private theorem k4Tail_sum_eq_point_add_tail
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommMonoid L]
    (t0 : T) (f : T → L) :
    (∑ t, f t) = f t0 + ∑ s : PointedTail T t0, f s.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset T)) (p := fun t : T => t = t0) f).symm
  calc
    (∑ t, f t) =
        (∑ t ∈ (Finset.univ : Finset T) with t = t0, f t) +
          ∑ t ∈ (Finset.univ : Finset T) with t ≠ t0, f t := by
            simpa using hpart
    _ = f t0 +
          ∑ t ∈ (Finset.univ : Finset T) with t ≠ t0, f t := by
          congr 1
          rw [Finset.sum_eq_single t0]
          · intro t ht hne
            exact (hne (Finset.mem_filter.mp ht).2).elim
          · simp
    _ = f t0 + ∑ s : PointedTail T t0, f s.1 := by
          congr 1
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset T))
              (p := fun t : T => t ≠ t0) (f := f)).symm

noncomputable def k4TailZeroSumRead
    (T L : Type*) [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) :
    K4TailZeroSum T L →ₗ[F] (PointedTail T t0 → L) where
  toFun U := fun s => U.1 s.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def k4TailZeroSumRawBuild
    (T L : Type*) [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) :
    (PointedTail T t0 → L) →ₗ[F] (T → L) where
  toFun v := fun t => if ht : t = t0 then ∑ s, v s else v ⟨t, ht⟩
  map_add' v w := by
    funext t
    by_cases ht : t = t0
    · subst t
      simp only [dif_pos, Pi.add_apply, Finset.sum_add_distrib]
    · simp only [dif_neg ht, Pi.add_apply]
  map_smul' r v := by
    funext t
    by_cases ht : t = t0
    · subst t
      simp only [dif_pos, Pi.smul_apply, RingHom.id_apply]
      rw [Finset.smul_sum]
    · simp only [dif_neg ht, Pi.smul_apply, RingHom.id_apply]

@[simp] private theorem k4TailZeroSumRawBuild_at_point
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (v : PointedTail T t0 → L) :
    k4TailZeroSumRawBuild T L t0 v t0 = ∑ s, v s := by
  simp [k4TailZeroSumRawBuild]

@[simp] private theorem k4TailZeroSumRawBuild_at_tail
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (v : PointedTail T t0 → L)
    (s : PointedTail T t0) :
    k4TailZeroSumRawBuild T L t0 v s.1 = v s := by
  change (if hs : s.1 = t0 then ∑ u, v u else v ⟨s.1, hs⟩) = v s
  rw [dif_neg s.2]

private theorem k4TailZeroSumRawBuild_sum_zero
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (v : PointedTail T t0 → L) :
    (∑ t, k4TailZeroSumRawBuild T L t0 v t) = 0 := by
  rw [k4Tail_sum_eq_point_add_tail t0]
  rw [k4TailZeroSumRawBuild_at_point]
  simp_rw [k4TailZeroSumRawBuild_at_tail]
  exact F_module_add_self _

noncomputable def k4TailZeroSumBuild
    (T L : Type*) [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) :
    (PointedTail T t0 → L) →ₗ[F] K4TailZeroSum T L where
  toFun v := ⟨k4TailZeroSumRawBuild T L t0 v, by
    apply LinearMap.mem_ker.mpr
    exact k4TailZeroSumRawBuild_sum_zero t0 v⟩
  map_add' v w := by
    apply Subtype.ext
    exact (k4TailZeroSumRawBuild T L t0).map_add v w
  map_smul' r v := by
    apply Subtype.ext
    exact (k4TailZeroSumRawBuild T L t0).map_smul r v

@[simp] theorem k4TailZeroSumBuild_at_point
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (v : PointedTail T t0 → L) :
    (k4TailZeroSumBuild T L t0 v).1 t0 = ∑ s, v s :=
  k4TailZeroSumRawBuild_at_point t0 v

@[simp] theorem k4TailZeroSumBuild_at_tail
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (v : PointedTail T t0 → L)
    (s : PointedTail T t0) :
    (k4TailZeroSumBuild T L t0 v).1 s.1 = v s :=
  k4TailZeroSumRawBuild_at_tail t0 v s

@[simp] theorem k4TailZeroSumRead_build
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (v : PointedTail T t0 → L) :
    k4TailZeroSumRead T L t0 (k4TailZeroSumBuild T L t0 v) = v := by
  funext s
  exact k4TailZeroSumRawBuild_at_tail t0 v s

@[simp] theorem k4TailZeroSumBuild_read
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (U : K4TailZeroSum T L) :
    k4TailZeroSumBuild T L t0 (k4TailZeroSumRead T L t0 U) = U := by
  apply Subtype.ext
  funext t
  by_cases ht : t = t0
  · subst t
    rw [show
      (k4TailZeroSumBuild T L t0 (k4TailZeroSumRead T L t0 U)).1 t0 =
          ∑ s : PointedTail T t0, U.1 s.1 by
        exact k4TailZeroSumRawBuild_at_point t0 _]
    have hsum := LinearMap.mem_ker.mp U.2
    change (∑ t, U.1 t) = 0 at hsum
    rw [k4Tail_sum_eq_point_add_tail t0] at hsum
    exact ((add_eq_zero_iff_eq_of_F_module _ _).mp hsum).symm
  · let s : PointedTail T t0 := ⟨t, ht⟩
    change k4TailZeroSumRawBuild T L t0
        (k4TailZeroSumRead T L t0 U) s.1 = U.1 s.1
    rw [k4TailZeroSumRawBuild_at_tail]
    rfl

noncomputable def k4TailZeroSumEquiv
    (T L : Type*) [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) :
    K4TailZeroSum T L ≃ₗ[F] (PointedTail T t0 → L) where
  toLinearMap := k4TailZeroSumRead T L t0
  invFun := k4TailZeroSumBuild T L t0
  left_inv := k4TailZeroSumBuild_read t0
  right_inv := k4TailZeroSumRead_build t0

/-! ## Quadratic elimination in the frozen coordinates -/

def k4TailQuadratic
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (q : L → F) (U : K4TailZeroSum T L) : F :=
  ∑ t, q (U.1 t)

def k4TailPairSumList
    {L : Type*} [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L) : List L → F
  | [] => 0
  | x :: xs => (List.map (fun y => B x y) xs).sum +
      k4TailPairSumList B xs

def k4TailCoordinatePairSum
    {R L : Type*} [Fintype R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L) (v : R → L) : F :=
  k4TailPairSumList B ((Finset.univ.toList).map v)

private theorem k4Tail_toList_map_sum
    {R L : Type*} [Fintype R]
    [AddCommMonoid L] (v : R → L) :
    ((Finset.univ.toList).map v).sum = ∑ r, v r := by
  classical
  induction (Finset.univ : Finset R) using Finset.induction_on with
  | empty => simp
  | @insert r s hr ih =>
      simp [hr]

private theorem k4Tail_quadratic_list_sum
    {L : Type*} [AddCommGroup L] [Module F L]
    (q : L → F) (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q 0 = 0)
    (hqadd : ∀ x y, q (x + y) = q x + q y + B x y)
    (xs : List L) :
    q xs.sum = (List.map q xs).sum + k4TailPairSumList B xs := by
  induction xs with
  | nil => simpa [k4TailPairSumList] using hq0
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons, k4TailPairSumList]
      rw [hqadd, ih, map_list_sum]
      abel

theorem k4TailQuadratic_build_eq_coordinate
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (q : L → F)
    (v : PointedTail T t0 → L) :
    k4TailQuadratic q (k4TailZeroSumBuild T L t0 v) =
      q (∑ s, v s) + ∑ s, q (v s) := by
  unfold k4TailQuadratic
  rw [k4Tail_sum_eq_point_add_tail t0]
  rw [k4TailZeroSumBuild_at_point]
  simp_rw [k4TailZeroSumBuild_at_tail]

theorem k4TailQuadratic_build_eq_pairSum
    {T L : Type*} [Fintype T] [DecidableEq T]
    [AddCommGroup L] [Module F L]
    (t0 : T) (q : L → F)
    (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q 0 = 0)
    (hqadd : ∀ x y, q (x + y) = q x + q y + B x y)
    (v : PointedTail T t0 → L) :
    k4TailQuadratic q (k4TailZeroSumBuild T L t0 v) =
      k4TailCoordinatePairSum B v := by
  rw [k4TailQuadratic_build_eq_coordinate]
  have hq := k4Tail_quadratic_list_sum q B hq0 hqadd
    ((Finset.univ.toList).map v)
  rw [k4Tail_toList_map_sum] at hq
  change q (∑ s, v s) + ∑ s, q (v s) =
    k4TailPairSumList B ((Finset.univ.toList).map v)
  rw [hq]
  have hqsum : (List.map q ((Finset.univ.toList).map v)).sum =
      ∑ s, q (v s) := by
    simpa only [List.map_map, Function.comp_apply] using
      (k4Tail_toList_map_sum (fun s => q (v s)))
  rw [hqsum]
  calc
    (∑ s, q (v s)) + k4TailPairSumList B ((Finset.univ.toList).map v) +
          ∑ s, q (v s) =
        ((∑ s, q (v s)) + ∑ s, q (v s)) +
          k4TailPairSumList B ((Finset.univ.toList).map v) := by
      abel
    _ = k4TailPairSumList B ((Finset.univ.toList).map v) := by
      rw [F_add_self, zero_add]

/-! ## Exact specialization to the frozen K4 Even-P Model -/

noncomputable def k4EvenPTailCoordinates
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a) :
    K4EvenPTail n a b c d ≃ₗ[F]
      (PointedTail (K4EvenPTailIndex n a) t0 →
        K4EvenPLeft n b c d) :=
  k4TailZeroSumEquiv
    (K4EvenPTailIndex n a) (K4EvenPLeft n b c d) t0

theorem k4EvenPTailQ_eq_generic
    {n a b c d : Nat} [NeZero n]
    (U : K4EvenPTail n a b c d) :
    k4EvenPTailQ U =
      k4TailQuadratic (fun sigma : K4EvenPLeft n b c d =>
        k4EvenPSliceQ sigma.1) U := by
  rfl

private theorem k4EvenPGPolar_apply
    {n b c d : Nat} [NeZero n]
    (sigma tau : K4EvenPLeft n b c d) :
    k4EvenPGPolar sigma tau =
      k4EvenPSlicePolar sigma.1 tau.1 := by
  rfl

theorem k4EvenPTailQ_build_eq_pairSum
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a)
    (v : PointedTail (K4EvenPTailIndex n a) t0 →
      K4EvenPLeft n b c d) :
    k4EvenPTailQ
        (k4TailZeroSumBuild
          (K4EvenPTailIndex n a) (K4EvenPLeft n b c d) t0 v) =
      k4TailCoordinatePairSum k4EvenPGPolar v := by
  rw [k4EvenPTailQ_eq_generic]
  apply k4TailQuadratic_build_eq_pairSum
  · simp [k4EvenPSliceQ, k4BWSlice_zero_left]
  · intro sigma tau
    change k4EvenPSliceQ (sigma.1 + tau.1) =
      k4EvenPSliceQ sigma.1 + k4EvenPSliceQ tau.1 +
        k4EvenPGPolar sigma tau
    rw [k4EvenPSliceQ_add]
    rw [k4EvenPGPolar_apply]

end

end Core4loop.CompleteGraph.EvenP.TailWitt
