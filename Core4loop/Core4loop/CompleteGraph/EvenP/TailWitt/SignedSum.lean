import Core4loop.CompleteGraph.EvenP.TailWitt.Radical
import Core4loop.QuadraticSignSum

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.TailWitt

open Core4loop
open Core4loop.CompleteGraph.EvenP

noncomputable section

/-! ## A proof-explicit pairing of every finite even coordinate type -/

noncomputable def k4TailEvenPairEquiv
    (R : Type*) [Fintype R]
    (heven : Even (Fintype.card R)) :
    Fin (Fintype.card R / 2) × Bool ≃ R :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans
    (finProdFinEquiv.trans
      ((finCongr (by
        have h := Nat.two_mul_div_two_of_even heven
        omega)).trans (Fintype.equivFin R).symm))

/-! ## Pair-defect Lagrangian -/

noncomputable def k4TailPairDefect
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) :
    (R → L) →ₗ[F] (S → Module.Dual F L) where
  toFun v := fun s => B (v (e (s, false)) + v (e (s, true)))
  map_add' v w := by
    funext s
    simp only [Pi.add_apply, map_add]
    abel
  map_smul' c v := by
    funext s
    simp only [Pi.smul_apply]
    rw [← smul_add, map_smul]
    simp only [RingHom.id_apply]

noncomputable abbrev K4TailPairLagrangian
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) :=
  LinearMap.ker (k4TailPairDefect B e)

theorem k4TailPairLagrangian_mem_iff
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) (v : R → L) :
    v ∈ K4TailPairLagrangian B e ↔
      ∀ s : S,
        v (e (s, false)) + v (e (s, true)) ∈ LinearMap.ker B := by
  constructor
  · intro hv s
    have hzero := congrFun (LinearMap.mem_ker.mp hv) s
    exact LinearMap.mem_ker.mpr hzero
  · intro hv
    apply LinearMap.mem_ker.mpr
    funext s
    exact LinearMap.mem_ker.mp (hv s)

private theorem k4TailPair_total_mem_ker
    {R S L : Type*} [Fintype R] [Finite S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R)
    (v : R → L)
    (hv : ∀ s : S,
      v (e (s, false)) + v (e (s, true)) ∈ LinearMap.ker B) :
    (∑ r, v r) ∈ LinearMap.ker B := by
  letI : Fintype S := Fintype.ofFinite _
  apply LinearMap.mem_ker.mpr
  rw [map_sum]
  rw [← e.sum_comp]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  apply Finset.sum_eq_zero
  intro s hs
  simpa only [map_add, add_comm] using LinearMap.mem_ker.mp (hv s)

private theorem k4TailPair_diagonal_eq_zero
    {R S L : Type*}
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (e : S × Bool ≃ R) (v w : R → L)
    (hv : ∀ s : S,
      v (e (s, false)) + v (e (s, true)) ∈ LinearMap.ker B)
    (hw : ∀ s : S,
      w (e (s, false)) + w (e (s, true)) ∈ LinearMap.ker B)
    (s : S) :
    B (v (e (s, false))) (w (e (s, false))) +
        B (v (e (s, true))) (w (e (s, true))) = 0 := by
  have hv0 := LinearMap.congr_fun
    (LinearMap.mem_ker.mp (hv s)) (w (e (s, false)))
  have hw0 := LinearMap.congr_fun
    (LinearMap.mem_ker.mp (hw s)) (v (e (s, true)))
  have hw0' :
      B (v (e (s, true)))
          (w (e (s, false)) + w (e (s, true))) = 0 := by
    rw [hsym]
    simpa only [LinearMap.zero_apply] using hw0
  simp only [map_add, LinearMap.add_apply, LinearMap.zero_apply] at hv0 hw0'
  have hleft := (add_eq_zero_iff_eq_of_F_module _ _).mp hv0
  have hright := (add_eq_zero_iff_eq_of_F_module _ _).mp hw0'
  rw [hleft, hright]
  exact F_add_self _

theorem k4TailPairLagrangian_annihilates
    {R S L : Type*} [Fintype R] [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (e : S × Bool ≃ R)
    (v w : K4TailPairLagrangian B e) :
    k4TailCoordinateGram B v.1 w.1 = 0 := by
  have hv := (k4TailPairLagrangian_mem_iff B e v.1).mp v.2
  have hw := (k4TailPairLagrangian_mem_iff B e w.1).mp w.2
  have htotal := k4TailPair_total_mem_ker B e w.1 hw
  rw [k4TailCoordinateGram_apply]
  calc
    (∑ r, B (v.1 r) (k4TailGramJ R L w.1 r)) =
        ∑ r, B (v.1 r) (w.1 r) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [k4TailGramJ_apply, map_add]
          have hright : B (v.1 r) (∑ u, w.1 u) = 0 := by
            rw [hsym]
            exact LinearMap.congr_fun (LinearMap.mem_ker.mp htotal) (v.1 r)
          rw [hright, add_zero]
    _ = ∑ z : S × Bool, B (v.1 (e z)) (w.1 (e z)) := by
          exact (e.sum_comp (fun r => B (v.1 r) (w.1 r))).symm
    _ = ∑ s : S,
          (B (v.1 (e (s, true))) (w.1 (e (s, true))) +
            B (v.1 (e (s, false))) (w.1 (e (s, false)))) := by
          rw [Fintype.sum_prod_type]
          simp_rw [Fintype.sum_bool]
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro s hs
          rw [add_comm]
          exact k4TailPair_diagonal_eq_zero B hsym e v.1 w.1 hv hw s

private theorem k4TailPair_probe_mem
    {R S L : Type*} [Fintype S] [DecidableEq R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) (s : S) (y : L) :
    (Pi.single (e (s, false)) y + Pi.single (e (s, true)) y) ∈
      K4TailPairLagrangian B e := by
  apply (k4TailPairLagrangian_mem_iff B e _).mpr
  intro u
  by_cases hus : u = s
  · subst u
    have hne : e (s, false) ≠ e (s, true) := by
      intro h
      have hpair := e.injective h
      simp at hpair
    apply LinearMap.mem_ker.mpr
    simp [Pi.single, hne, hne.symm, F_module_add_self]
  · have hff : e (u, false) ≠ e (s, false) := by
      intro h
      have hpair := e.injective h
      exact hus (congrArg Prod.fst hpair)
    have hft : e (u, false) ≠ e (s, true) := by
      intro h
      have hpair := e.injective h
      have : false = true := congrArg Prod.snd hpair
      simp at this
    have htf : e (u, true) ≠ e (s, false) := by
      intro h
      have hpair := e.injective h
      have : true = false := congrArg Prod.snd hpair
      simp at this
    have htt : e (u, true) ≠ e (s, true) := by
      intro h
      have hpair := e.injective h
      exact hus (congrArg Prod.fst hpair)
    apply LinearMap.mem_ker.mpr
    simp [Pi.single, hff, hft, htf, htt]

private theorem k4TailPair_probe_sum
    {R S L : Type*} [Fintype R] [DecidableEq R]
    [AddCommGroup L] [Module F L]
    (e : S × Bool ≃ R) (s : S) (y : L) :
    (∑ r : R,
        ((Pi.single (e (s, false)) y : R → L) +
        (Pi.single (e (s, true)) y : R → L)) r) = 0 := by
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib]
  simp [F_module_add_self]

private theorem k4TailCoordinateGram_pair_probe
    {R S L : Type*} [Fintype R] [DecidableEq R]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) (v : R → L) (s : S) (y : L) :
    k4TailCoordinateGram B v
        ((Pi.single (e (s, false)) y : R → L) +
          (Pi.single (e (s, true)) y : R → L)) =
      B (v (e (s, false)) + v (e (s, true))) y := by
  rw [k4TailCoordinateGram_apply]
  have hsum :
      (∑ r : R,
        ((Pi.single (e (s, false)) y : R → L) +
          (Pi.single (e (s, true)) y : R → L)) r) = 0 :=
    k4TailPair_probe_sum e s y
  simp only [k4TailGramJ_apply, hsum, add_zero]
  simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  have hsingle (r0 : R) :
      (∑ x : R, B (v x) ((Pi.single r0 y : R → L) x)) =
        B (v r0) y := by
    rw [Finset.sum_eq_single r0]
    · simp [Pi.single]
    · intro r hr hne'
      rw [Pi.single_eq_of_ne hne']
      simp
    · simp
  rw [hsingle, hsingle]
  simp only [LinearMap.add_apply]

theorem k4TailPairLagrangian_selfDual
    {R S L : Type*} [Fintype R] [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (e : S × Bool ≃ R) (v : R → L) :
    ((k4TailCoordinateGram B v).comp
          (K4TailPairLagrangian B e).subtype = 0 ↔
      v ∈ K4TailPairLagrangian B e) := by
  classical
  constructor
  · intro hv
    apply (k4TailPairLagrangian_mem_iff B e v).mpr
    intro s
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    let probe : R → L :=
      Pi.single (e (s, false)) y + Pi.single (e (s, true)) y
    have hprobe : probe ∈ K4TailPairLagrangian B e := by
      exact k4TailPair_probe_mem B e s y
    have hzero := LinearMap.congr_fun hv ⟨probe, hprobe⟩
    change k4TailCoordinateGram B v probe = 0 at hzero
    rw [show k4TailCoordinateGram B v probe =
        B (v (e (s, false)) + v (e (s, true))) y by
      exact k4TailCoordinateGram_pair_probe B e v s y] at hzero
    simpa only [LinearMap.zero_apply] using hzero
  · intro hv
    apply LinearMap.ext
    intro w
    change k4TailCoordinateGram B v w.1 = 0
    exact k4TailPairLagrangian_annihilates B hsym e ⟨v, hv⟩ w

/-! ## The literal pair quadratic vanishes on the paired Lagrangian -/

private theorem k4TailSign_quadratic_list_sum
    {L : Type*} [AddCommGroup L] [Module F L]
    (q0 : L → F) (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q0 0 = 0)
    (hqadd : ∀ x y, q0 (x + y) = q0 x + q0 y + B x y)
    (xs : List L) :
    q0 xs.sum = (xs.map q0).sum + k4TailPairSumList B xs := by
  induction xs with
  | nil => simpa [k4TailPairSumList] using hq0
  | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons, k4TailPairSumList]
      rw [hqadd, ih, map_list_sum]
      abel

private theorem k4TailPairSumList_solve
    {L : Type*} [AddCommGroup L] [Module F L]
    (q0 : L → F) (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q0 0 = 0)
    (hqadd : ∀ x y, q0 (x + y) = q0 x + q0 y + B x y)
    (xs : List L) :
    k4TailPairSumList B xs = q0 xs.sum + (xs.map q0).sum := by
  have h := k4TailSign_quadratic_list_sum q0 B hq0 hqadd xs
  calc
    k4TailPairSumList B xs =
        k4TailPairSumList B xs + 0 := by rw [add_zero]
    _ = k4TailPairSumList B xs +
          ((xs.map q0).sum + (xs.map q0).sum) := by
            rw [F_add_self]
    _ = ((xs.map q0).sum + k4TailPairSumList B xs) +
          (xs.map q0).sum := by abel
    _ = q0 xs.sum + (xs.map q0).sum := by rw [← h]

private theorem k4TailPairSumList_eq_of_perm
    {L : Type*} [AddCommGroup L] [Module F L]
    (q0 : L → F) (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q0 0 = 0)
    (hqadd : ∀ x y, q0 (x + y) = q0 x + q0 y + B x y)
    {xs ys : List L} (hperm : xs.Perm ys) :
    k4TailPairSumList B xs = k4TailPairSumList B ys := by
  rw [k4TailPairSumList_solve q0 B hq0 hqadd,
    k4TailPairSumList_solve q0 B hq0 hqadd]
  rw [hperm.sum_eq]
  rw [(hperm.map q0).sum_eq]

private def k4TailPairedIndexList
    {R S : Type*} [Fintype S]
    (e : S × Bool ≃ R) : List R :=
  (Finset.univ.toList : List S).flatMap
    (fun s => [e (s, false), e (s, true)])

private theorem k4TailPairedIndexList_nodup
    {R S : Type*} [Fintype S]
    (e : S × Bool ≃ R) :
    (k4TailPairedIndexList e).Nodup := by
  classical
  unfold k4TailPairedIndexList
  rw [List.nodup_flatMap]
  constructor
  · intro s hs
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil,
      List.nodup_nil, and_true]
    constructor
    · intro heq
      have hpair := e.injective heq
      simp at hpair
    · simp
  · rw [List.pairwise_iff_get]
    intro i j hij
    change List.Disjoint
      [e (Finset.univ.toList[i], false), e (Finset.univ.toList[i], true)]
      [e (Finset.univ.toList[j], false), e (Finset.univ.toList[j], true)]
    rw [List.disjoint_left]
    intro r hri hrj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hri hrj
    have hget : Finset.univ.toList[i] ≠ Finset.univ.toList[j] := by
      intro h
      have hij' : i.val = j.val :=
        ((Finset.nodup_toList Finset.univ).getElem_inj_iff).mp h
      exact (ne_of_lt hij) (Fin.ext hij')
    rcases hri with hri | hri <;> rcases hrj with hrj | hrj
    · have hpair := e.injective (hri.symm.trans hrj)
      have hs := congrArg Prod.fst hpair
      exact hget hs
    · have hpair := e.injective (hri.symm.trans hrj)
      have : false = true := congrArg Prod.snd hpair
      simp at this
    · have hpair := e.injective (hri.symm.trans hrj)
      have : true = false := congrArg Prod.snd hpair
      simp at this
    · have hpair := e.injective (hri.symm.trans hrj)
      have hs := congrArg Prod.fst hpair
      exact hget hs

private theorem k4TailPairedIndexList_toFinset
    {R S : Type*} [Fintype S] [Fintype R] [DecidableEq R]
    (e : S × Bool ≃ R) :
    (k4TailPairedIndexList e).toFinset = Finset.univ := by
  ext r
  simp only [k4TailPairedIndexList, List.mem_toFinset,
    List.mem_flatMap, Finset.mem_univ, iff_true]
  let z := e.symm r
  refine ⟨z.1, by simp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases hz : z.2 with _ | _
  · left
    have hz' : (e.symm r).2 = false := by simpa [z] using hz
    rw [← hz']
    exact (e.apply_symm_apply r).symm
  · right
    have hz' : (e.symm r).2 = true := by simpa [z] using hz
    rw [← hz']
    exact (e.apply_symm_apply r).symm

private theorem k4TailPairedIndexList_perm_univ
    {R S : Type*} [Fintype S] [Fintype R]
    (e : S × Bool ≃ R) :
    (k4TailPairedIndexList e).Perm (Finset.univ.toList : List R) := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact k4TailPairedIndexList_nodup e
  · exact Finset.univ.nodup_toList
  · rw [k4TailPairedIndexList_toFinset]
    simp

private theorem k4TailPairSumList_paired_eq_zero
    {R S L : Type*}
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x, B x x = 0)
    (e : S × Bool ≃ R) (v : R → L)
    (ss : List S)
    (hv : ∀ s ∈ ss,
      v (e (s, false)) + v (e (s, true)) ∈ LinearMap.ker B) :
    k4TailPairSumList B
        ((ss.flatMap (fun s => [e (s, false), e (s, true)])).map v) = 0 := by
  induction ss with
  | nil => simp [k4TailPairSumList]
  | cons s ss ih =>
      let x := v (e (s, false))
      let y := v (e (s, true))
      let ys :=
        (ss.flatMap (fun u => [e (u, false), e (u, true)])).map v
      have hsrad : x + y ∈ LinearMap.ker B := by
        exact hv s (by simp)
      have hxy : B x y = 0 := by
        have hzero := LinearMap.congr_fun
          (LinearMap.mem_ker.mp hsrad) x
        simp only [map_add, LinearMap.add_apply, LinearMap.zero_apply] at hzero
        rw [hdiag] at hzero
        simp only [zero_add] at hzero
        rw [hsym]
        exact hzero
      have hcross :
          (ys.map (fun z => B x z)).sum +
              (ys.map (fun z => B y z)).sum = 0 := by
        rw [← List.sum_map_add]
        apply List.sum_eq_zero
        intro z hz
        rw [List.mem_map] at hz
        rcases hz with ⟨u, hu, rfl⟩
        simpa only [map_add, LinearMap.add_apply, LinearMap.zero_apply] using
          LinearMap.congr_fun (LinearMap.mem_ker.mp hsrad) u
      have htail : k4TailPairSumList B ys = 0 := by
        apply ih
        intro u hu
        exact hv u (by simp [hu])
      change k4TailPairSumList B (x :: y :: ys) = 0
      simp only [k4TailPairSumList, List.map_cons, List.sum_cons]
      rw [hxy, zero_add, htail, add_zero]
      exact hcross

theorem k4TailCoordinatePairSum_eq_zero_on_pairLagrangian
    {R S L : Type*} [Fintype R] [Fintype S]
    [AddCommGroup L] [Module F L]
    (q0 : L → F) (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q0 0 = 0)
    (hqadd : ∀ x y, q0 (x + y) = q0 x + q0 y + B x y)
    (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x, B x x = 0)
    (e : S × Bool ≃ R)
    (v : K4TailPairLagrangian B e) :
    k4TailCoordinatePairSum B v.1 = 0 := by
  classical
  unfold k4TailCoordinatePairSum
  have hperm := (k4TailPairedIndexList_perm_univ e).map v.1
  rw [← k4TailPairSumList_eq_of_perm q0 B hq0 hqadd hperm]
  unfold k4TailPairedIndexList
  apply k4TailPairSumList_paired_eq_zero B hsym hdiag e v.1
  intro s hs
  exact (k4TailPairLagrangian_mem_iff B e v.1).mp v.2 s

/-! ## Explicit dimension coordinates for the paired Lagrangian -/

noncomputable def k4TailPairLagrangianRead
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) :
    K4TailPairLagrangian B e →ₗ[F]
      (S → L) × (S → LinearMap.ker B) where
  toFun v :=
    (fun s => v.1 (e (s, false)),
      fun s =>
        ⟨v.1 (e (s, false)) + v.1 (e (s, true)),
          (k4TailPairLagrangian_mem_iff B e v.1).mp v.2 s⟩)
  map_add' v w := by
    apply Prod.ext
    · funext s
      rfl
    · funext s
      apply Subtype.ext
      change
        (v.1 (e (s, false)) + w.1 (e (s, false))) +
            (v.1 (e (s, true)) + w.1 (e (s, true))) =
          (v.1 (e (s, false)) + v.1 (e (s, true))) +
            (w.1 (e (s, false)) + w.1 (e (s, true)))
      abel
  map_smul' c v := by
    apply Prod.ext
    · funext s
      rfl
    · funext s
      apply Subtype.ext
      change c • v.1 (e (s, false)) + c • v.1 (e (s, true)) =
        c • (v.1 (e (s, false)) + v.1 (e (s, true)))
      rw [smul_add]

private noncomputable def k4TailPairLagrangianRawBuild
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) :
    ((S → L) × (S → LinearMap.ker B)) →ₗ[F] (R → L) where
  toFun z := fun r =>
    match (e.symm r).2 with
    | false => z.1 (e.symm r).1
    | true => z.1 (e.symm r).1 + (z.2 (e.symm r).1).1
  map_add' z w := by
    funext r
    rcases h : (e.symm r).2 with _ | _
    · simp only [h, Prod.fst_add, Pi.add_apply]
    · simp only [h, Prod.fst_add, Prod.snd_add, Pi.add_apply,
        Submodule.coe_add]
      abel
  map_smul' c z := by
    funext r
    rcases h : (e.symm r).2 with _ | _
    · simp only [h, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
    · simp only [h, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
        Submodule.coe_smul, RingHom.id_apply]
      rw [smul_add]

private theorem k4TailPairLagrangianRawBuild_at_false
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R)
    (z : (S → L) × (S → LinearMap.ker B)) (s : S) :
    k4TailPairLagrangianRawBuild B e z (e (s, false)) = z.1 s := by
  change
    (match (e.symm (e (s, false))).2 with
      | false => z.1 (e.symm (e (s, false))).1
      | true => z.1 (e.symm (e (s, false))).1 +
          (z.2 (e.symm (e (s, false))).1).1) = z.1 s
  rw [e.symm_apply_apply]

private theorem k4TailPairLagrangianRawBuild_at_true
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R)
    (z : (S → L) × (S → LinearMap.ker B)) (s : S) :
    k4TailPairLagrangianRawBuild B e z (e (s, true)) =
      z.1 s + (z.2 s).1 := by
  change
    (match (e.symm (e (s, true))).2 with
      | false => z.1 (e.symm (e (s, true))).1
      | true => z.1 (e.symm (e (s, true))).1 +
          (z.2 (e.symm (e (s, true))).1).1) = z.1 s + (z.2 s).1
  rw [e.symm_apply_apply]

noncomputable def k4TailPairLagrangianBuild
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) :
    ((S → L) × (S → LinearMap.ker B)) →ₗ[F]
      K4TailPairLagrangian B e where
  toFun z :=
    ⟨k4TailPairLagrangianRawBuild B e z, by
      apply (k4TailPairLagrangian_mem_iff B e _).mpr
      intro s
      rw [k4TailPairLagrangianRawBuild_at_false,
        k4TailPairLagrangianRawBuild_at_true]
      have hcancel : z.1 s + (z.1 s + (z.2 s).1) = (z.2 s).1 := by
        rw [← add_assoc, F_module_add_self, zero_add]
      rw [hcancel]
      exact (z.2 s).2⟩
  map_add' z w := by
    apply Subtype.ext
    exact (k4TailPairLagrangianRawBuild B e).map_add z w
  map_smul' c z := by
    apply Subtype.ext
    exact (k4TailPairLagrangianRawBuild B e).map_smul c z

@[simp] theorem k4TailPairLagrangianRead_build
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R)
    (z : (S → L) × (S → LinearMap.ker B)) :
    k4TailPairLagrangianRead B e
        (k4TailPairLagrangianBuild B e z) = z := by
  apply Prod.ext
  · funext s
    exact k4TailPairLagrangianRawBuild_at_false B e z s
  · funext s
    apply Subtype.ext
    change
      k4TailPairLagrangianRawBuild B e z (e (s, false)) +
          k4TailPairLagrangianRawBuild B e z (e (s, true)) =
        (z.2 s).1
    rw [k4TailPairLagrangianRawBuild_at_false,
      k4TailPairLagrangianRawBuild_at_true]
    rw [← add_assoc, F_module_add_self, zero_add]

@[simp] theorem k4TailPairLagrangianBuild_read
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R)
    (v : K4TailPairLagrangian B e) :
    k4TailPairLagrangianBuild B e
        (k4TailPairLagrangianRead B e v) = v := by
  apply Subtype.ext
  funext r
  let z := e.symm r
  have hr : e z = r := e.apply_symm_apply r
  rcases hz : z.2 with _ | _
  · have hzpair : z = (z.1, false) := Prod.ext rfl hz
    have hr' : e (z.1, false) = r := by rw [← hzpair]; exact hr
    rw [← hr']
    change k4TailPairLagrangianRawBuild B e
        (k4TailPairLagrangianRead B e v) (e (z.1, false)) =
      v.1 (e (z.1, false))
    rw [k4TailPairLagrangianRawBuild_at_false]
    rfl
  · have hzpair : z = (z.1, true) := Prod.ext rfl hz
    have hr' : e (z.1, true) = r := by rw [← hzpair]; exact hr
    rw [← hr']
    change k4TailPairLagrangianRawBuild B e
        (k4TailPairLagrangianRead B e v) (e (z.1, true)) =
      v.1 (e (z.1, true))
    rw [k4TailPairLagrangianRawBuild_at_true]
    change v.1 (e (z.1, false)) +
        (v.1 (e (z.1, false)) + v.1 (e (z.1, true))) =
      v.1 (e (z.1, true))
    rw [← add_assoc, F_module_add_self, zero_add]

noncomputable def k4TailPairLagrangianEquiv
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) :
    K4TailPairLagrangian B e ≃ₗ[F]
      (S → L) × (S → LinearMap.ker B) where
  toLinearMap := k4TailPairLagrangianRead B e
  invFun := k4TailPairLagrangianBuild B e
  left_inv := k4TailPairLagrangianBuild_read B e
  right_inv := k4TailPairLagrangianRead_build B e

theorem finrank_k4TailPairLagrangian
    {R S L : Type*} [Fintype S]
    [AddCommGroup L] [Module F L] [FiniteDimensional F L]
    (B : L →ₗ[F] Module.Dual F L)
    (e : S × Bool ≃ R) :
    Module.finrank F (K4TailPairLagrangian B e) =
      Fintype.card S *
        (Module.finrank F L + Module.finrank F (LinearMap.ker B)) := by
  rw [LinearEquiv.finrank_eq (k4TailPairLagrangianEquiv B e)]
  simp [Module.finrank_pi_fintype, Nat.mul_add]

theorem sum_bitSign_k4TailCoordinatePairSum_eq_pairLagrangian
    {R S L : Type*} [Fintype R] [DecidableEq R] [Fintype S] [Fintype L]
    [AddCommGroup L] [Module F L]
    (q0 : L → F) (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q0 0 = 0)
    (hqadd : ∀ x y, q0 (x + y) = q0 x + q0 y + B x y)
    (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x, B x x = 0)
    (e : S × Bool ≃ R) :
    (∑ v : R → L, bitSign (k4TailCoordinatePairSum B v)) =
      (2 : Int) ^ Module.finrank F (K4TailPairLagrangian B e) := by
  classical
  letI : Fintype (K4TailPairLagrangian B e) := Fintype.ofFinite _
  exact sum_bitSign_eq_pow_finrank_of_selfDual_isotropic
    (q := k4TailCoordinatePairSum B)
    (polar := k4TailCoordinateGram B)
    (hq_add := k4TailCoordinatePairSum_add B hsym)
    (L := K4TailPairLagrangian B e)
    (hq_zero := k4TailCoordinatePairSum_eq_zero_on_pairLagrangian
      q0 B hq0 hqadd hsym hdiag e)
    (hself := k4TailPairLagrangian_selfDual B hsym e)

private theorem k4TailEvenPairEquiv_card
    {R S : Type*} [Fintype R] [Fintype S]
    (e : S × Bool ≃ R) :
    Fintype.card R = 2 * Fintype.card S := by
  have h := Fintype.card_congr e
  simp only [Fintype.card_prod, Fintype.card_bool] at h
  omega

theorem finrank_k4TailPairLagrangian_eq_radical_add_half_range
    {R S L : Type*} [Fintype R] [Fintype S]
    [AddCommGroup L] [Module F L] [FiniteDimensional F L]
    (B : L →ₗ[F] Module.Dual F L)
    (heven : Even (Fintype.card R))
    (e : S × Bool ≃ R) :
    Module.finrank F (K4TailPairLagrangian B e) =
      Module.finrank F (K4TailCoordinateRadical (R := R) B) +
        Module.finrank F (LinearMap.range
          (k4TailCoordinateGram (R := R) B)) / 2 := by
  rw [finrank_k4TailPairLagrangian B e,
    finrank_k4TailCoordinateRadical B heven,
    finrank_range_k4TailCoordinateGram B heven]
  have hcard := k4TailEvenPairEquiv_card e
  have hbase := LinearMap.finrank_range_add_finrank_ker B
  rw [hcard, ← hbase]
  have hhalf :
      (2 * Fintype.card S * Module.finrank F (LinearMap.range B)) / 2 =
        Fintype.card S * Module.finrank F (LinearMap.range B) := by
    rw [show
      2 * Fintype.card S * Module.finrank F (LinearMap.range B) =
        2 * (Fintype.card S * Module.finrank F (LinearMap.range B)) by ring]
    exact Nat.mul_div_cancel_left _ (by omega)
  rw [hhalf]
  ring

theorem sum_bitSign_k4TailCoordinatePairSum_eq_radical_add_half_range
    {R S L : Type*} [Fintype R] [DecidableEq R] [Finite S] [Fintype L]
    [AddCommGroup L] [Module F L]
    (q0 : L → F) (B : L →ₗ[F] Module.Dual F L)
    (hq0 : q0 0 = 0)
    (hqadd : ∀ x y, q0 (x + y) = q0 x + q0 y + B x y)
    (hsym : ∀ x y, B x y = B y x)
    (hdiag : ∀ x, B x x = 0)
    (heven : Even (Fintype.card R))
    (e : S × Bool ≃ R) :
    (∑ v : R → L, bitSign (k4TailCoordinatePairSum B v)) =
      (2 : Int) ^
        (Module.finrank F (K4TailCoordinateRadical (R := R) B) +
          Module.finrank F (LinearMap.range
            (k4TailCoordinateGram (R := R) B)) / 2) := by
  letI : Fintype S := Fintype.ofFinite _
  rw [sum_bitSign_k4TailCoordinatePairSum_eq_pairLagrangian
    q0 B hq0 hqadd hsym hdiag e]
  rw [finrank_k4TailPairLagrangian_eq_radical_add_half_range B heven e]

/-! ## Exact K4 Tail specialization -/

theorem k4EvenPGPolar_self_eq_zero
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) :
    k4EvenPGPolar sigma sigma = 0 := by
  change k4EvenPSlicePolar sigma.1 sigma.1 = 0
  unfold k4EvenPSlicePolar
  exact F_add_self _

noncomputable local instance k4TailSign_K4EvenPLeft_fintype
    {n b c d : Nat} [NeZero n] :
    Fintype (K4EvenPLeft n b c d) := Fintype.ofFinite _

noncomputable local instance k4TailSign_coordinate_fintype
    {n a b c d : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a) :
    Fintype
      (PointedTail (K4EvenPTailIndex n a) t0 →
        K4EvenPLeft n b c d) := inferInstance

noncomputable local instance k4TailSign_K4EvenPTail_fintype
    {n a b c d : Nat} [NeZero n] :
    Fintype (K4EvenPTail n a b c d) := by
  letI : Fintype (K4EvenPTailIndex n a) := Fintype.ofFinite _
  letI : Fintype
      (K4EvenPTailIndex n a → K4EvenPLeft n b c d) := inferInstance
  exact Fintype.ofFinite _

theorem sum_bitSign_k4EvenPTailCoordinatePairSum_eq_radical_add_half_range
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a) :
    (∑ v : PointedTail (K4EvenPTailIndex n a) t0 →
          K4EvenPLeft n b c d,
        bitSign (k4TailCoordinatePairSum k4EvenPGPolar v)) =
      (2 : Int) ^
        (Module.finrank F
            (K4EvenPTailCoordinateRadical
              (n := n) (a := a) (b := b) (c := c) (d := d) t0) +
          Module.finrank F
            (LinearMap.range
              (k4EvenPTailCoordinateGram
                (n := n) (a := a) (b := b) (c := c) (d := d) t0)) / 2) := by
  classical
  have heven : Even
      (Fintype.card (PointedTail (K4EvenPTailIndex n a) t0)) :=
    k4EvenPTailCoordinateIndex_card_even hn ha2 t0
  let e :
      Fin (Fintype.card
          (PointedTail (K4EvenPTailIndex n a) t0) / 2) × Bool ≃
        PointedTail (K4EvenPTailIndex n a) t0 :=
    k4TailEvenPairEquiv
      (PointedTail (K4EvenPTailIndex n a) t0) heven
  exact sum_bitSign_k4TailCoordinatePairSum_eq_radical_add_half_range
    (q0 := fun sigma : K4EvenPLeft n b c d =>
      k4EvenPSliceQ sigma.1)
    (B := k4EvenPGPolar)
    (hq0 := by simp [k4EvenPSliceQ, k4BWSlice_zero_left])
    (hqadd := by
      intro sigma tau
      change k4EvenPSliceQ (sigma.1 + tau.1) =
        k4EvenPSliceQ sigma.1 + k4EvenPSliceQ tau.1 +
          k4EvenPSlicePolar sigma.1 tau.1
      exact k4EvenPSliceQ_add sigma.1 tau.1)
    (hsym := k4EvenPGPolar_comm)
    (hdiag := k4EvenPGPolar_self_eq_zero)
    (heven := heven)
    (e := e)

theorem sum_bitSign_k4EvenPTailQ_eq_radical_add_half_range
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (t0 : K4EvenPTailIndex n a) :
    (∑ U : K4EvenPTail n a b c d, bitSign (k4EvenPTailQ U)) =
      (2 : Int) ^
        (Module.finrank F
            (K4EvenPTailCoordinateRadical
              (n := n) (a := a) (b := b) (c := c) (d := d) t0) +
          Module.finrank F
            (LinearMap.range
              (k4EvenPTailCoordinateGram
                (n := n) (a := a) (b := b) (c := c) (d := d) t0)) / 2) := by
  classical
  let E := k4EvenPTailCoordinates
    (n := n) (a := a) (b := b) (c := c) (d := d) t0
  calc
    (∑ U : K4EvenPTail n a b c d, bitSign (k4EvenPTailQ U)) =
        ∑ v : PointedTail (K4EvenPTailIndex n a) t0 →
            K4EvenPLeft n b c d,
          bitSign (k4EvenPTailQ (E.symm v)) := by
            exact (E.symm.sum_comp
              (fun U : K4EvenPTail n a b c d =>
                bitSign (k4EvenPTailQ U))).symm
    _ = ∑ v : PointedTail (K4EvenPTailIndex n a) t0 →
            K4EvenPLeft n b c d,
          bitSign (k4TailCoordinatePairSum k4EvenPGPolar v) := by
            apply Finset.sum_congr rfl
            intro v hv
            congr 1
            change k4EvenPTailQ
                (k4TailZeroSumBuild
                  (K4EvenPTailIndex n a) (K4EvenPLeft n b c d) t0 v) =
              k4TailCoordinatePairSum k4EvenPGPolar v
            exact k4EvenPTailQ_build_eq_pairSum t0 v
    _ = _ :=
      sum_bitSign_k4EvenPTailCoordinatePairSum_eq_radical_add_half_range
        hn ha2 t0

end

end Core4loop.CompleteGraph.EvenP.TailWitt
