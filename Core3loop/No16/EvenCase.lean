import No16.OddCase

open scoped BigOperators

namespace No16

/-!
The even-case special sector, factorization, and final even formula for
`Delta16` will live here.
-/

abbrev RowColBalanced (n : ℕ) [NeZero n] :=
  { rc : Profile n × Profile n // sigma rc.1 = sigma rc.2 }

noncomputable instance rowColBalancedFintype {n : ℕ} [NeZero n] : Fintype (RowColBalanced n) := by
  classical
  infer_instance

noncomputable def rowColBalancedToData {n : ℕ} [NeZero n] :
    RowColBalanced n → Profile n × Wodd (n := n)
  | ⟨rc, hrc⟩ =>
      (rc.1, ⟨rc.2 + rc.1, by
        change sigma (rc.2 + rc.1) = 0
        calc
          sigma (rc.2 + rc.1) = sigma rc.2 + sigma rc.1 := by
            unfold sigma
            simp [Finset.sum_add_distrib]
          _ = 0 := by
            rw [hrc]
            simp [F_add_self]⟩)

noncomputable def dataToRowColBalanced {n : ℕ} [NeZero n] :
    Profile n × Wodd (n := n) → RowColBalanced n
  | (r, w) =>
      ⟨(r, w.1 + r), by
        have hw : sigma w.1 = 0 := sigma_eq_zero_of_mem_Wodd w.2
        have hcalc : sigma (w.1 + r) = sigma r := by
          calc
            sigma (w.1 + r) = sigma w.1 + sigma r := by
              unfold sigma
              simp [Finset.sum_add_distrib]
            _ = sigma r := by simp [hw]
        exact hcalc.symm⟩

lemma dataToRowColBalanced_left_inv {n : ℕ} [NeZero n] (x : RowColBalanced n) :
    dataToRowColBalanced (n := n) (rowColBalancedToData (n := n) x) = x := by
  rcases x with ⟨x, hx⟩
  have hcancel : ∀ a b : F, b + a + a = b := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext t
    simpa [dataToRowColBalanced, rowColBalancedToData] using hcancel (x.1 t) (x.2 t)

lemma rowColBalancedToData_right_inv {n : ℕ} [NeZero n] (x : Profile n × Wodd (n := n)) :
    rowColBalancedToData (n := n) (dataToRowColBalanced (n := n) x) = x := by
  rcases x with ⟨r, w⟩
  have hcancel : ∀ a b : F, b + a + a = b := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext t
    simpa [dataToRowColBalanced, rowColBalancedToData] using hcancel (r t) (w.1 t)

noncomputable def rowColBalancedEquivData {n : ℕ} [NeZero n] :
    RowColBalanced n ≃ Profile n × Wodd (n := n) where
  toFun := rowColBalancedToData (n := n)
  invFun := dataToRowColBalanced (n := n)
  left_inv := dataToRowColBalanced_left_inv (n := n)
  right_inv := rowColBalancedToData_right_inv (n := n)

lemma natCard_rowColBalanced {n : ℕ} [NeZero n] :
    Nat.card (RowColBalanced n) = 2 ^ (2 * n - 1) := by
  rw [Nat.card_congr (rowColBalancedEquivData (n := n))]
  rw [Nat.card_prod]
  have hProf : Nat.card (Profile n) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_profile]
    simp [F]
  have hW : Nat.card (Wodd (n := n)) = 2 ^ (n - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_Wodd_eq]
    simp [F]
  rw [hProf, hW]
  calc
    2 ^ n * 2 ^ (n - 1) = 2 ^ (n + (n - 1)) := by
      symm
      exact pow_add 2 n (n - 1)
    _ = 2 ^ (2 * n - 1) := by
      congr
      omega

lemma sigma_rowSum_eq_sigma_colSum_even {n : ℕ} [NeZero n] (h : HFun n) :
    sigma (rowSum h) = sigma (colSum h) := by
  unfold sigma rowSum colSum
  rw [Finset.sum_comm]

lemma rowSum_add_even {n : ℕ} [NeZero n] (h k : HFun n) :
    rowSum (h + k) = rowSum h + rowSum k := by
  funext t
  simp [rowSum, Finset.sum_add_distrib]

lemma colSum_add_even {n : ℕ} [NeZero n] (h k : HFun n) :
    colSum (h + k) = colSum h + colSum k := by
  funext s
  simp [colSum, Finset.sum_add_distrib]

noncomputable def rowSeed_even {n : ℕ} [NeZero n] (r : Profile n) : Profile n :=
  fun t => r t + if t = 0 then sigma r else 0

lemma sigma_rowSeed_eq_zero_even {n : ℕ} [NeZero n] (r : Profile n) :
    sigma (rowSeed_even r) = 0 := by
  unfold sigma rowSeed_even
  rw [Finset.sum_add_distrib]
  have hsingle : (∑ x : I n, if x = 0 then sigma r else 0) = sigma r := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t _ ht
      simp [ht]
    · simp
  rw [hsingle]
  exact F_add_self (sigma r)

noncomputable def rowColBalancedMap {n : ℕ} [NeZero n] : HFun n → RowColBalanced n
  | h => ⟨(rowSum h, colSum h), sigma_rowSum_eq_sigma_colSum_even (h := h)⟩

noncomputable def rowColBalancedLift {n : ℕ} [NeZero n] (rc : RowColBalanced n) : HFun n :=
  fun t s =>
    (if s = 0 then rowSeed_even rc.1.1 t else 0) + (if t = 0 then rc.1.2 s else 0)

lemma rowSum_rowColBalancedLift {n : ℕ} [NeZero n] (rc : RowColBalanced n) :
    rowSum (rowColBalancedLift (n := n) rc) = rc.1.1 := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  have hrc' : sigma r = sigma c := hrc
  funext t
  by_cases ht : t = 0
  · subst ht
    unfold rowSum rowColBalancedLift
    rw [Finset.sum_add_distrib, Finset.sum_eq_single 0]
    · have hseed : (if (0 : I n) = 0 then rowSeed_even r 0 else 0) = r 0 + sigma r := by
        simp [rowSeed_even]
      have hsigma : (∑ x : I n, if (0 : I n) = 0 then c x else 0) = sigma c := by
        simp [sigma]
      rw [hseed, hsigma, hrc']
      have hs : sigma c + sigma c = 0 := by
        exact F_add_self (sigma c)
      have hs' : sigma c + (sigma c + r 0) = r 0 := by
        simpa [add_assoc] using congrArg (fun z : F => z + r 0) hs
      simpa [add_assoc, add_left_comm, add_comm] using hs'
    · intro s _ hs
      simp [hs]
    · simp
  · unfold rowSum rowColBalancedLift
    rw [Finset.sum_add_distrib, Finset.sum_eq_single 0]
    · simp [rowSeed_even, ht]
    · intro s _ hs
      simp [hs]
    · simp

lemma colSum_rowColBalancedLift {n : ℕ} [NeZero n] (rc : RowColBalanced n) :
    colSum (rowColBalancedLift (n := n) rc) = rc.1.2 := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  funext s
  by_cases hs : s = 0
  · subst hs
    unfold colSum rowColBalancedLift
    rw [Finset.sum_add_distrib]
    have hleft : (∑ x : I n, (if (0 : I n) = 0 then rowSeed_even r x else 0)) = sigma (rowSeed_even r) := by
      simp [sigma]
    have hright : (∑ x : I n, (if x = 0 then c 0 else 0)) = c 0 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro t _ ht
        simp [ht]
      · simp
    rw [hleft, hright, sigma_rowSeed_eq_zero_even]
    simp
  · unfold colSum rowColBalancedLift
    rw [Finset.sum_add_distrib, Finset.sum_eq_zero]
    · rw [Finset.sum_eq_single 0]
      · simp [hs]
      · intro t _ ht
        simp [ht]
      · simp
    · intro t _
      simp [hs]

lemma rowColBalancedMap_rowColBalancedLift {n : ℕ} [NeZero n] (rc : RowColBalanced n) :
    rowColBalancedMap (n := n) (rowColBalancedLift (n := n) rc) = rc := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  apply Subtype.ext
  apply Prod.ext
  · exact rowSum_rowColBalancedLift (n := n) ⟨(r, c), hrc⟩
  · exact colSum_rowColBalancedLift (n := n) ⟨(r, c), hrc⟩

noncomputable def hResidual {n : ℕ} [NeZero n] (h : HFun n) : HFun n :=
  h + rowColBalancedLift (n := n) (rowColBalancedMap (n := n) h)

lemma hResidual_mem_HSpace {n : ℕ} [NeZero n] (h : HFun n) :
    hResidual (n := n) h ∈ HSpace (n := n) := by
  change hResidual (n := n) h ∈ LinearMap.ker (rowSumMap (n := n)) ∧
      hResidual (n := n) h ∈ LinearMap.ker (colSumMap (n := n))
  constructor
  · change rowSum (hResidual (n := n) h) = 0
    rw [show hResidual (n := n) h = h + rowColBalancedLift (n := n) (rowColBalancedMap (n := n) h) by rfl]
    rw [rowSum_add_even, rowSum_rowColBalancedLift]
    funext t
    simp [rowColBalancedMap, F_add_self]
  · change colSum (hResidual (n := n) h) = 0
    rw [show hResidual (n := n) h = h + rowColBalancedLift (n := n) (rowColBalancedMap (n := n) h) by rfl]
    rw [colSum_add_even, colSum_rowColBalancedLift]
    funext s
    simp [rowColBalancedMap, F_add_self]

noncomputable def hFunToRowColHSpace {n : ℕ} [NeZero n] :
    HFun n → RowColBalanced n × HSpace (n := n)
  | h => (rowColBalancedMap (n := n) h, ⟨hResidual (n := n) h, hResidual_mem_HSpace (n := n) h⟩)

noncomputable def rowColHSpaceToHFun {n : ℕ} [NeZero n] :
    RowColBalanced n × HSpace (n := n) → HFun n
  | (rc, kh) => rowColBalancedLift (n := n) rc + kh.1

lemma rowColHSpaceToHFun_hFunToRowColHSpace {n : ℕ} [NeZero n] (h : HFun n) :
    rowColHSpaceToHFun (n := n) (hFunToRowColHSpace (n := n) h) = h := by
  funext t s
  simp [rowColHSpaceToHFun, hFunToRowColHSpace, hResidual,
    add_assoc, add_left_comm, add_comm, F_add_self]

lemma rowColBalancedMap_add_hspace {n : ℕ} [NeZero n] (rc : RowColBalanced n)
    {k : HFun n} (hk : k ∈ HSpace (n := n)) :
    rowColBalancedMap (n := n) (rowColBalancedLift (n := n) rc + k) = rc := by
  rcases rc with ⟨⟨r, c⟩, hrc⟩
  apply Subtype.ext
  apply Prod.ext
  · funext t
    simp [rowColBalancedMap, rowSum_add_even, rowSum_rowColBalancedLift,
      rowSum_eq_zero_of_mem_HSpace (n := n) hk t]
  · funext s
    simp [rowColBalancedMap, colSum_add_even, colSum_rowColBalancedLift,
      colSum_eq_zero_of_mem_HSpace (n := n) hk s]

lemma hFunToRowColHSpace_rowColHSpaceToHFun {n : ℕ} [NeZero n]
    (x : RowColBalanced n × HSpace (n := n)) :
    hFunToRowColHSpace (n := n) (rowColHSpaceToHFun (n := n) x) = x := by
  rcases x with ⟨rc, kh⟩
  rcases kh with ⟨k, hk⟩
  have hmap :
      rowColBalancedMap (n := n) (rowColHSpaceToHFun (n := n) (rc, ⟨k, hk⟩)) = rc := by
    exact rowColBalancedMap_add_hspace (n := n) rc hk
  have hmap' :
      rowColBalancedMap (n := n) (k + rowColBalancedLift (n := n) rc) = rc := by
    simpa [add_comm] using rowColBalancedMap_add_hspace (n := n) rc hk
  apply Prod.ext
  · exact hmap
  · apply Subtype.ext
    funext t s
    simp [hFunToRowColHSpace, rowColHSpaceToHFun, hResidual, hmap',
      add_assoc, add_left_comm, add_comm, F_add_self]

noncomputable def hFunEquivRowColHSpace {n : ℕ} [NeZero n] :
    HFun n ≃ (RowColBalanced n × HSpace (n := n)) where
  toFun := hFunToRowColHSpace (n := n)
  invFun := rowColHSpaceToHFun (n := n)
  left_inv := rowColHSpaceToHFun_hFunToRowColHSpace (n := n)
  right_inv := hFunToRowColHSpace_rowColHSpaceToHFun (n := n)

lemma natCard_HFun {n : ℕ} [NeZero n] :
    Nat.card (HFun n) = 2 ^ (n ^ 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_uvFun]

lemma finrank_HSpace_even {n : ℕ} [NeZero n] :
    Module.finrank F (HSpace (n := n)) = (n - 1) ^ 2 := by
  have hcard :
      Nat.card (HFun n) = Nat.card (RowColBalanced n) * Nat.card (HSpace (n := n)) := by
    calc
      Nat.card (HFun n) = Nat.card (RowColBalanced n × HSpace (n := n)) := by
        rw [Nat.card_congr (hFunEquivRowColHSpace (n := n))]
      _ = Nat.card (RowColBalanced n) * Nat.card (HSpace (n := n)) := by
        rw [Nat.card_prod]
  rw [natCard_HFun, natCard_rowColBalanced, Module.natCard_eq_pow_finrank (K := F)] at hcard
  simp [F] at hcard
  rw [← pow_add] at hcard
  have hexp : n ^ 2 = (2 * n - 1) + Module.finrank F (HSpace (n := n)) := by
    exact Nat.pow_right_injective (by omega : 1 < 2) hcard
  have hdim : Module.finrank F (HSpace (n := n)) = n ^ 2 - (2 * n - 1) := by
    omega
  have hsq : n ^ 2 - (2 * n - 1) = (n - 1) ^ 2 := by
    rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
    simp [pow_two]
    have hc : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      ring_nf
    have hk : 2 * (k + 1) - 1 ≤ (k + 1) * (k + 1) := by
      omega
    have h2 : 2 * (k + 1) = 2 * k + 2 := by
      omega
    rw [hc, h2]
    omega
  rw [hdim, hsq]

lemma natCard_HSpace_even {n : ℕ} [NeZero n] :
    Nat.card (HSpace (n := n)) = 2 ^ ((n - 1) ^ 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_HSpace_even]

abbrev RectNZIndex (n : ℕ) [NeZero n] := INonzero n × INonzero n

noncomputable def rectNZVec {n : ℕ} [NeZero n] (i : RectNZIndex n) : HSpace (n := n) :=
  ⟨rect i.1.1 i.2.1, rect_mem_HSpace i.1.1 i.2.1⟩

lemma rect_apply_rectNZIndex {n : ℕ} [NeZero n] (i j : RectNZIndex n) :
    rect i.1.1 i.2.1 j.1.1 j.2.1 = if j = i then 1 else 0 := by
  rw [rect_apply_nonzero_nonzero i.1.2 i.2.2 j.1.2 j.2.2]
  by_cases h : j = i
  · simp [h]
  · have hneq : ¬ (j.1.1 = i.1.1 ∧ j.2.1 = i.2.1) := by
      intro hji
      apply h
      rcases i with ⟨⟨i1, hi1⟩, ⟨i2, hi2⟩⟩
      rcases j with ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩
      cases hji with
      | intro h1 h2 =>
          simp only at h1 h2
          subst h1
          subst h2
          rfl
    simp [h, hneq]

lemma linearIndependent_rectNZVec {n : ℕ} [NeZero n] :
    LinearIndependent F (rectNZVec (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro l hl i
  have hEval :=
    congrFun (congrFun (congrArg Subtype.val hl) i.1.1) i.2.1
  simpa [rectNZVec, rect_apply_rectNZIndex] using hEval

lemma card_rectNZIndex {n : ℕ} [NeZero n] :
    Fintype.card (RectNZIndex n) = (n - 1) ^ 2 := by
  simp [RectNZIndex, card_INonzero, pow_two]

lemma span_rectNZVec_eq_top {n : ℕ} [NeZero n] (hn : Even n) :
    Submodule.span F (Set.range (rectNZVec (n := n))) = ⊤ := by
  have hspanfin :
      Fintype.card (RectNZIndex n) =
        Module.finrank F (Submodule.span F (Set.range (rectNZVec (n := n)))) :=
    linearIndependent_iff_card_eq_finrank_span.mp (linearIndependent_rectNZVec (n := n))
  have hcard :
      Fintype.card (RectNZIndex n) = Module.finrank F (HSpace (n := n)) := by
    rw [card_rectNZIndex, finrank_HSpace_even (n := n)]
  exact Submodule.eq_top_of_finrank_eq (hspanfin.symm.trans hcard)

lemma top_le_span_rectNZVec {n : ℕ} [NeZero n] (hn : Even n) :
    ⊤ ≤ Submodule.span F (Set.range (rectNZVec (n := n))) := by
  simpa [span_rectNZVec_eq_top (n := n) hn]

noncomputable def rectNZBasis {n : ℕ} [NeZero n] (hn : Even n) :
    Module.Basis (RectNZIndex n) F (HSpace (n := n)) :=
  Module.Basis.mk (linearIndependent_rectNZVec (n := n)) (top_le_span_rectNZVec (n := n) hn)

def evenBSlice {n : ℕ} (B : BFun n) (t p q' : I n) : Profile n :=
  fun a => B a t p q'

def evenCSlice {n : ℕ} (C : CFun n) (v w r : I n) : Profile n :=
  fun a => C a v w r

lemma bSlice_eq_evenBSlice {n : ℕ} (B : BFun n) (t p q' : I n) :
    bSlice B t p q' = evenBSlice B t p q' := rfl

lemma cSlice_eq_evenCSlice {n : ℕ} (C : CFun n) (v w r : I n) :
    cSlice C v w r = evenCSlice C v w r := rfl

noncomputable def evenHeadB {n : ℕ} [NeZero n] (B : BFun n) : BCoef n × BCoef n :=
  (fun t p q' => (evenPairMap (n := n) (evenBSlice B t p q')).1,
    fun t p q' => (evenPairMap (n := n) (evenBSlice B t p q')).2)

noncomputable def evenHeadC {n : ℕ} [NeZero n] (C : CFun n) : CCoef n × CCoef n :=
  (fun v w r => (evenPairMap (n := n) (evenCSlice C v w r)).1,
    fun v w r => (evenPairMap (n := n) (evenCSlice C v w r)).2)

noncomputable def evenVisibleB {n : ℕ} [NeZero n] (B : BFun n) : BFun n :=
  fun a t p q' => (evenPlaneCoordInv (n := n) ((evenHeadB B).1 t p q', (evenHeadB B).2 t p q')).1 a

noncomputable def evenVisibleC {n : ℕ} [NeZero n] (C : CFun n) : CFun n :=
  fun a v w r => (evenPlaneCoordInv (n := n) ((evenHeadC C).1 v w r, (evenHeadC C).2 v w r)).1 a

noncomputable def evenTailB {n : ℕ} [NeZero n] (B : BFun n) : BFun n :=
  fun a t p q' => B a t p q' + evenVisibleB B a t p q'

noncomputable def evenTailC {n : ℕ} [NeZero n] (C : CFun n) : CFun n :=
  fun a v w r => C a v w r + evenVisibleC C a v w r

noncomputable def evenBuildB {n : ℕ} [NeZero n] (bc : BCoef n × BCoef n) (R : BFun n) : BFun n :=
  (fun a t p q' => (evenPlaneCoordInv (n := n) (bc.1 t p q', bc.2 t p q')).1 a) + R

noncomputable def evenBuildC {n : ℕ} [NeZero n] (bc : CCoef n × CCoef n) (R : CFun n) : CFun n :=
  (fun a v w r => (evenPlaneCoordInv (n := n) (bc.1 v w r, bc.2 v w r)).1 a) + R

lemma evenHeadB_fst_eq_pair_fst_slice {n : ℕ} [NeZero n] (B : BFun n) (t p q' : I n) :
    (evenHeadB B).1 t p q' = (evenPairMap (n := n) (evenBSlice B t p q')).1 := rfl

lemma evenHeadB_snd_eq_pair_snd_slice {n : ℕ} [NeZero n] (B : BFun n) (t p q' : I n) :
    (evenHeadB B).2 t p q' = (evenPairMap (n := n) (evenBSlice B t p q')).2 := rfl

lemma evenHeadC_fst_eq_pair_fst_slice {n : ℕ} [NeZero n] (C : CFun n) (v w r : I n) :
    (evenHeadC C).1 v w r = (evenPairMap (n := n) (evenCSlice C v w r)).1 := rfl

lemma evenHeadC_snd_eq_pair_snd_slice {n : ℕ} [NeZero n] (C : CFun n) (v w r : I n) :
    (evenHeadC C).2 v w r = (evenPairMap (n := n) (evenCSlice C v w r)).2 := rfl

lemma evenVisibleB_slice {n : ℕ} [NeZero n] (B : BFun n) (t p q' : I n) :
    evenBSlice (evenVisibleB B) t p q' =
      (evenPlaneCoordInv (n := n) ((evenHeadB B).1 t p q', (evenHeadB B).2 t p q')).1 := by
  funext a
  rfl

lemma evenVisibleC_slice {n : ℕ} [NeZero n] (C : CFun n) (v w r : I n) :
    evenCSlice (evenVisibleC C) v w r =
      (evenPlaneCoordInv (n := n) ((evenHeadC C).1 v w r, (evenHeadC C).2 v w r)).1 := by
  funext a
  rfl

lemma even_decompose_B {n : ℕ} [NeZero n] (B : BFun n) :
    B = evenVisibleB B + evenTailB B := by
  funext a t p q'
  simp [evenTailB, add_assoc, add_left_comm, add_comm, F_add_self]

lemma even_decompose_C {n : ℕ} [NeZero n] (C : CFun n) :
    C = evenVisibleC C + evenTailC C := by
  funext a v w r
  simp [evenTailC, add_assoc, add_left_comm, add_comm, F_add_self]

lemma evenVisibleB_pair_eq {n : ℕ} [NeZero n] (hn : Even n) (B : BFun n) (t p q' : I n) :
    evenPairMap (n := n) (evenBSlice (evenVisibleB B) t p q') =
      evenPairMap (n := n) (evenBSlice B t p q') := by
  simpa [evenVisibleB_slice, evenHeadB_fst_eq_pair_fst_slice, evenHeadB_snd_eq_pair_snd_slice]
    using evenPlaneCoordMap_inv_apply (n := n) hn
      ((evenHeadB B).1 t p q', (evenHeadB B).2 t p q')

lemma evenVisibleC_pair_eq {n : ℕ} [NeZero n] (hn : Even n) (C : CFun n) (v w r : I n) :
    evenPairMap (n := n) (evenCSlice (evenVisibleC C) v w r) =
      evenPairMap (n := n) (evenCSlice C v w r) := by
  simpa [evenVisibleC_slice, evenHeadC_fst_eq_pair_fst_slice, evenHeadC_snd_eq_pair_snd_slice]
    using evenPlaneCoordMap_inv_apply (n := n) hn
      ((evenHeadC C).1 v w r, (evenHeadC C).2 v w r)

lemma evenTailB_slice_mem_Ueven {n : ℕ} [NeZero n] (hn : Even n) (B : BFun n) (t p q' : I n) :
    evenBSlice (evenTailB B) t p q' ∈ Ueven (n := n) := by
  change evenPairMap (n := n) (evenBSlice (evenTailB B) t p q') = 0
  have hs :
      evenBSlice (evenTailB B) t p q' = evenBSlice B t p q' + evenBSlice (evenVisibleB B) t p q' := by
    funext a
    simp [evenBSlice, evenTailB]
  rw [hs, LinearMap.map_add, evenVisibleB_pair_eq (n := n) hn]
  ext <;> simp [F_add_self]

lemma evenTailC_slice_mem_Ueven {n : ℕ} [NeZero n] (hn : Even n) (C : CFun n) (v w r : I n) :
    evenCSlice (evenTailC C) v w r ∈ Ueven (n := n) := by
  change evenPairMap (n := n) (evenCSlice (evenTailC C) v w r) = 0
  have hs :
      evenCSlice (evenTailC C) v w r = evenCSlice C v w r + evenCSlice (evenVisibleC C) v w r := by
    funext a
    simp [evenCSlice, evenTailC]
  rw [hs, LinearMap.map_add, evenVisibleC_pair_eq (n := n) hn]
  ext <;> simp [F_add_self]

lemma evenHeadB_evenTail_eq_zero {n : ℕ} [NeZero n] (hn : Even n) (B : BFun n) :
    evenHeadB (evenTailB B) = (0, 0) := by
  apply Prod.ext
  · funext t p q'
    have hmem := evenTailB_slice_mem_Ueven (n := n) hn B t p q'
    change evenPairMap (n := n) (evenBSlice (evenTailB B) t p q') = 0 at hmem
    exact congrArg Prod.fst hmem
  · funext t p q'
    have hmem := evenTailB_slice_mem_Ueven (n := n) hn B t p q'
    change evenPairMap (n := n) (evenBSlice (evenTailB B) t p q') = 0 at hmem
    exact congrArg Prod.snd hmem

lemma evenHeadC_evenTail_eq_zero {n : ℕ} [NeZero n] (hn : Even n) (C : CFun n) :
    evenHeadC (evenTailC C) = (0, 0) := by
  apply Prod.ext
  · funext v w r
    have hmem := evenTailC_slice_mem_Ueven (n := n) hn C v w r
    change evenPairMap (n := n) (evenCSlice (evenTailC C) v w r) = 0 at hmem
    exact congrArg Prod.fst hmem
  · funext v w r
    have hmem := evenTailC_slice_mem_Ueven (n := n) hn C v w r
    change evenPairMap (n := n) (evenCSlice (evenTailC C) v w r) = 0 at hmem
    exact congrArg Prod.snd hmem

lemma evenZeroHeadB_slice_mem_Ueven {n : ℕ} [NeZero n] {R : BFun n}
    (hR : evenHeadB R = (0, 0)) (t p q' : I n) :
    evenBSlice R t p q' ∈ Ueven (n := n) := by
  change evenPairMap (n := n) (evenBSlice R t p q') = 0
  ext
  · have hfst := congrArg Prod.fst hR
    simpa [evenHeadB_fst_eq_pair_fst_slice] using congrFun (congrFun (congrFun hfst t) p) q'
  · have hsnd := congrArg Prod.snd hR
    simpa [evenHeadB_snd_eq_pair_snd_slice] using congrFun (congrFun (congrFun hsnd t) p) q'

lemma evenZeroHeadC_slice_mem_Ueven {n : ℕ} [NeZero n] {R : CFun n}
    (hR : evenHeadC R = (0, 0)) (v w r : I n) :
    evenCSlice R v w r ∈ Ueven (n := n) := by
  change evenPairMap (n := n) (evenCSlice R v w r) = 0
  ext
  · have hfst := congrArg Prod.fst hR
    simpa [evenHeadC_fst_eq_pair_fst_slice] using congrFun (congrFun (congrFun hfst v) w) r
  · have hsnd := congrArg Prod.snd hR
    simpa [evenHeadC_snd_eq_pair_snd_slice] using congrFun (congrFun (congrFun hsnd v) w) r

lemma sigma_eq_evenPairMap_fst {n : ℕ} [NeZero n] (x : Profile n) :
    sigma x = (evenPairMap (n := n) x).1 := by
  simpa [evenPairMap, eProfile] using sigma_eq_dot_oneProfile (n := n) x

lemma kappa_eq_evenHeads_fst {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    kappa B C = kappaB (evenHeadB B).1 + kappaC (evenHeadC C).1 := by
  funext u2 u3 u4 u5
  unfold kappa kappaB kappaC
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [show (∑ x : I n, B x (u2 + u3) u4 u5) = sigma (evenBSlice B (u2 + u3) u4 u5) by rfl]
  rw [show (∑ x : I n, B x (u2 + u3 + 1) u4 u5) = sigma (evenBSlice B (u2 + u3 + 1) u4 u5) by rfl]
  rw [show (∑ x : I n, C x u2 u3 (u4 + u5)) = sigma (evenCSlice C u2 u3 (u4 + u5)) by rfl]
  rw [show (∑ x : I n, C x u2 u3 (u4 + u5 + 1)) = sigma (evenCSlice C u2 u3 (u4 + u5 + 1)) by rfl]
  simp [evenHeadB, evenHeadC, sigma_eq_evenPairMap_fst]

lemma kappa_eq_visibleConstraint_evenHeads_fst {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    kappa B C = visibleConstraint ((evenHeadB B).1, (evenHeadC C).1) := by
  funext u2 u3 u4 u5
  rw [kappa_eq_evenHeads_fst (B := B) (C := C)]
  unfold visibleConstraint kappaB kappaC
  simp [Pi.add_apply, add_assoc]

lemma kappa_eq_zero_iff_evenHeadsFst_mem_SSpace {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    kappa B C = 0 ↔ ((evenHeadB B).1, (evenHeadC C).1) ∈ SSpace (n := n) := by
  constructor
  · intro hk
    change visibleConstraintMap (n := n) ((evenHeadB B).1, (evenHeadC C).1) = 0
    change visibleConstraint ((evenHeadB B).1, (evenHeadC C).1) = 0
    simpa [kappa_eq_visibleConstraint_evenHeads_fst (B := B) (C := C)] using hk
  · intro hs
    change visibleConstraintMap (n := n) ((evenHeadB B).1, (evenHeadC C).1) = 0 at hs
    change visibleConstraint ((evenHeadB B).1, (evenHeadC C).1) = 0 at hs
    simpa [kappa_eq_visibleConstraint_evenHeads_fst (B := B) (C := C)] using hs

lemma evenHeadB_evenBuild_eq {n : ℕ} [NeZero n] (hn : Even n) (bc : BCoef n × BCoef n)
    (R : BFun n) (hR : evenHeadB R = (0, 0)) :
    evenHeadB (evenBuildB bc R) = bc := by
  apply Prod.ext
  · funext t p q'
    have hs :
        evenBSlice (evenBuildB bc R) t p q' =
          (evenPlaneCoordInv (n := n) (bc.1 t p q', bc.2 t p q')).1 + evenBSlice R t p q' := by
      funext a
      simp [evenBSlice, evenBuildB]
    have hR0 := evenZeroHeadB_slice_mem_Ueven (n := n) hR t p q'
    change evenPairMap (n := n) (evenBSlice R t p q') = 0 at hR0
    have hpair :
        evenPairMap (n := n) (evenBSlice (evenBuildB bc R) t p q') = (bc.1 t p q', bc.2 t p q') := by
      rw [hs, LinearMap.map_add, hR0, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (n := n) hn (bc.1 t p q', bc.2 t p q')
    exact congrArg Prod.fst hpair
  · funext t p q'
    have hs :
        evenBSlice (evenBuildB bc R) t p q' =
          (evenPlaneCoordInv (n := n) (bc.1 t p q', bc.2 t p q')).1 + evenBSlice R t p q' := by
      funext a
      simp [evenBSlice, evenBuildB]
    have hR0 := evenZeroHeadB_slice_mem_Ueven (n := n) hR t p q'
    change evenPairMap (n := n) (evenBSlice R t p q') = 0 at hR0
    have hpair :
        evenPairMap (n := n) (evenBSlice (evenBuildB bc R) t p q') = (bc.1 t p q', bc.2 t p q') := by
      rw [hs, LinearMap.map_add, hR0, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (n := n) hn (bc.1 t p q', bc.2 t p q')
    exact congrArg Prod.snd hpair

lemma evenHeadC_evenBuild_eq {n : ℕ} [NeZero n] (hn : Even n) (bc : CCoef n × CCoef n)
    (R : CFun n) (hR : evenHeadC R = (0, 0)) :
    evenHeadC (evenBuildC bc R) = bc := by
  apply Prod.ext
  · funext v w r
    have hs :
        evenCSlice (evenBuildC bc R) v w r =
          (evenPlaneCoordInv (n := n) (bc.1 v w r, bc.2 v w r)).1 + evenCSlice R v w r := by
      funext a
      simp [evenCSlice, evenBuildC]
    have hR0 := evenZeroHeadC_slice_mem_Ueven (n := n) hR v w r
    change evenPairMap (n := n) (evenCSlice R v w r) = 0 at hR0
    have hpair :
        evenPairMap (n := n) (evenCSlice (evenBuildC bc R) v w r) = (bc.1 v w r, bc.2 v w r) := by
      rw [hs, LinearMap.map_add, hR0, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (n := n) hn (bc.1 v w r, bc.2 v w r)
    exact congrArg Prod.fst hpair
  · funext v w r
    have hs :
        evenCSlice (evenBuildC bc R) v w r =
          (evenPlaneCoordInv (n := n) (bc.1 v w r, bc.2 v w r)).1 + evenCSlice R v w r := by
      funext a
      simp [evenCSlice, evenBuildC]
    have hR0 := evenZeroHeadC_slice_mem_Ueven (n := n) hR v w r
    change evenPairMap (n := n) (evenCSlice R v w r) = 0 at hR0
    have hpair :
        evenPairMap (n := n) (evenCSlice (evenBuildC bc R) v w r) = (bc.1 v w r, bc.2 v w r) := by
      rw [hs, LinearMap.map_add, hR0, add_zero]
      simpa using evenPlaneCoordMap_inv_apply (n := n) hn (bc.1 v w r, bc.2 v w r)
    exact congrArg Prod.snd hpair

lemma evenTailB_evenBuild_eq {n : ℕ} [NeZero n] (hn : Even n) (bc : BCoef n × BCoef n)
    (R : BFun n) (hR : evenHeadB R = (0, 0)) :
    evenTailB (evenBuildB bc R) = R := by
  have hhead := evenHeadB_evenBuild_eq (n := n) hn bc R hR
  funext a t p q'
  have hvisible :
      evenVisibleB ((fun a t p q' => (evenPlaneCoordInv (n := n) (bc.1 t p q', bc.2 t p q')).1 a) + R)
          a t p q' =
        (evenPlaneCoordInv (n := n) (bc.1 t p q', bc.2 t p q')).1 a := by
    simpa [evenBuildB] using
      (show evenVisibleB (evenBuildB bc R) a t p q' =
          (evenPlaneCoordInv (n := n) (bc.1 t p q', bc.2 t p q')).1 a by
        simp [evenVisibleB, hhead])
  rw [evenTailB, evenBuildB, hvisible]
  simp [add_assoc, add_left_comm, add_comm, F_add_self]

lemma evenTailC_evenBuild_eq {n : ℕ} [NeZero n] (hn : Even n) (bc : CCoef n × CCoef n)
    (R : CFun n) (hR : evenHeadC R = (0, 0)) :
    evenTailC (evenBuildC bc R) = R := by
  have hhead := evenHeadC_evenBuild_eq (n := n) hn bc R hR
  funext a v w r
  have hvisible :
      evenVisibleC ((fun a v w r => (evenPlaneCoordInv (n := n) (bc.1 v w r, bc.2 v w r)).1 a) + R)
          a v w r =
        (evenPlaneCoordInv (n := n) (bc.1 v w r, bc.2 v w r)).1 a := by
    simpa [evenBuildC] using
      (show evenVisibleC (evenBuildC bc R) a v w r =
          (evenPlaneCoordInv (n := n) (bc.1 v w r, bc.2 v w r)).1 a by
        simp [evenVisibleC, hhead])
  rw [evenTailC, evenBuildC, hvisible]
  simp [add_assoc, add_left_comm, add_comm, F_add_self]

lemma evenBuildB_head_tail_eq {n : ℕ} [NeZero n] (B : BFun n) :
    evenBuildB (evenHeadB B) (evenTailB B) = B := by
  simpa [evenBuildB, evenVisibleB] using (even_decompose_B (B := B)).symm

lemma evenBuildC_head_tail_eq {n : ℕ} [NeZero n] (C : CFun n) :
    evenBuildC (evenHeadC C) (evenTailC C) = C := by
  simpa [evenBuildC, evenVisibleC] using (even_decompose_C (C := C)).symm

abbrev EvenZeroHeadB (n : ℕ) [NeZero n] :=
  { R : BFun n // evenHeadB R = (0, 0) }

abbrev EvenZeroHeadC (n : ℕ) [NeZero n] :=
  { R : CFun n // evenHeadC R = (0, 0) }

noncomputable instance evenZeroHeadBFintype {n : ℕ} [NeZero n] : Fintype (EvenZeroHeadB n) := by
  classical
  infer_instance

noncomputable instance evenZeroHeadCFintype {n : ℕ} [NeZero n] : Fintype (EvenZeroHeadC n) := by
  classical
  infer_instance

noncomputable instance uevenFintype {n : ℕ} [NeZero n] : Fintype (Ueven (n := n)) := by
  classical
  infer_instance

noncomputable def evenDecomposeBEquiv {n : ℕ} [NeZero n] (hn : Even n) :
    BFun n ≃ ((BCoef n × BCoef n) × EvenZeroHeadB n) where
  toFun B := (evenHeadB B, ⟨evenTailB B, evenHeadB_evenTail_eq_zero (n := n) hn B⟩)
  invFun x := evenBuildB x.1 x.2.1
  left_inv B := evenBuildB_head_tail_eq (B := B)
  right_inv x := by
    rcases x with ⟨bc, RB⟩
    rcases RB with ⟨R, hR⟩
    apply Prod.ext
    · exact evenHeadB_evenBuild_eq (n := n) hn bc R hR
    · apply Subtype.ext
      exact evenTailB_evenBuild_eq (n := n) hn bc R hR

noncomputable def evenDecomposeCEquiv {n : ℕ} [NeZero n] (hn : Even n) :
    CFun n ≃ ((CCoef n × CCoef n) × EvenZeroHeadC n) where
  toFun C := (evenHeadC C, ⟨evenTailC C, evenHeadC_evenTail_eq_zero (n := n) hn C⟩)
  invFun x := evenBuildC x.1 x.2.1
  left_inv C := evenBuildC_head_tail_eq (C := C)
  right_inv x := by
    rcases x with ⟨bc, RC⟩
    rcases RC with ⟨R, hR⟩
    apply Prod.ext
    · exact evenHeadC_evenBuild_eq (n := n) hn bc R hR
    · apply Subtype.ext
      exact evenTailC_evenBuild_eq (n := n) hn bc R hR

abbrev EvenTailBModel (n : ℕ) [NeZero n] := I n → I n → I n → Ueven (n := n)

abbrev EvenTailCModel (n : ℕ) [NeZero n] := I n → I n → I n → Ueven (n := n)

noncomputable instance evenTailBModelFintype {n : ℕ} [NeZero n] :
    Fintype (EvenTailBModel n) := by
  classical
  infer_instance

noncomputable instance evenTailCModelFintype {n : ℕ} [NeZero n] :
    Fintype (EvenTailCModel n) := by
  classical
  infer_instance

noncomputable instance uEvenDecidableEq {n : ℕ} [NeZero n] :
    DecidableEq (Ueven (n := n)) := by
  classical
  infer_instance

noncomputable def evenZeroHeadBEquivTailModel {n : ℕ} [NeZero n] :
    EvenZeroHeadB n ≃ EvenTailBModel n where
  toFun RB := fun t p q' => ⟨evenBSlice RB.1 t p q',
    evenZeroHeadB_slice_mem_Ueven (n := n) RB.2 t p q'⟩
  invFun X := ⟨fun a t p q' => (X t p q').1 a, by
    apply Prod.ext <;> funext t p q'
    · have hmem : evenPairMap (n := n) ((X t p q').1) = 0 := (X t p q').2
      exact congrArg Prod.fst hmem
    · have hmem : evenPairMap (n := n) ((X t p q').1) = 0 := (X t p q').2
      exact congrArg Prod.snd hmem⟩
  left_inv RB := by
    apply Subtype.ext
    funext a t p q'
    rfl
  right_inv X := by
    funext t p q'
    apply Subtype.ext
    funext a
    rfl

noncomputable def evenZeroHeadCEquivTailModel {n : ℕ} [NeZero n] :
    EvenZeroHeadC n ≃ EvenTailCModel n where
  toFun RC := fun v w r => ⟨evenCSlice RC.1 v w r,
    evenZeroHeadC_slice_mem_Ueven (n := n) RC.2 v w r⟩
  invFun X := ⟨fun a v w r => (X v w r).1 a, by
    apply Prod.ext <;> funext v w r
    · have hmem : evenPairMap (n := n) ((X v w r).1) = 0 := (X v w r).2
      exact congrArg Prod.fst hmem
    · have hmem : evenPairMap (n := n) ((X v w r).1) = 0 := (X v w r).2
      exact congrArg Prod.snd hmem⟩
  left_inv RC := by
    apply Subtype.ext
    funext a v w r
    rfl
  right_inv X := by
    funext v w r
    apply Subtype.ext
    funext a
    rfl

noncomputable def evenTailBModelEquivTriple {n : ℕ} [NeZero n] :
    EvenTailBModel n ≃ ((I n × I n × I n) → Ueven (n := n)) where
  toFun X := fun | ⟨t, p, q'⟩ => X t p q'
  invFun X := fun t p q' => X (t, p, q')
  left_inv X := by
    funext t p q'
    rfl
  right_inv X := by
    funext tpq
    rcases tpq with ⟨t, p, q'⟩
    rfl

noncomputable def evenTailCModelEquivTriple {n : ℕ} [NeZero n] :
    EvenTailCModel n ≃ ((I n × I n × I n) → Ueven (n := n)) where
  toFun X := fun | ⟨v, w, r⟩ => X v w r
  invFun X := fun v w r => X (v, w, r)
  left_inv X := by
    funext v w r
    rfl
  right_inv X := by
    funext vwr
    rcases vwr with ⟨v, w, r⟩
    rfl

lemma natCard_Ueven_even {n : ℕ} [NeZero n] (hn : Even n) :
    Nat.card (Ueven (n := n)) = 2 ^ (n - 2) := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_Ueven (n := n) hn]
  simp [F]

lemma card_triple_I {n : ℕ} [NeZero n] :
    Fintype.card (I n × I n × I n) = n ^ 3 := by
  calc
    Fintype.card (I n × I n × I n) = n * n * n := by
      simp [I, ZMod.card, Nat.mul_assoc]
    _ = n ^ 3 := by ring

lemma natCard_evenTailBModel {n : ℕ} [NeZero n] (hn : Even n) :
    Nat.card (EvenTailBModel n) = 2 ^ ((n - 2) * n ^ 3) := by
  rw [Nat.card_congr (evenTailBModelEquivTriple (n := n))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, card_triple_I]
  rw [← Nat.card_eq_fintype_card (α := Ueven (n := n)), natCard_Ueven_even (n := n) hn]
  simpa [pow_mul]

lemma natCard_evenTailCModel {n : ℕ} [NeZero n] (hn : Even n) :
    Nat.card (EvenTailCModel n) = 2 ^ ((n - 2) * n ^ 3) := by
  rw [Nat.card_congr (evenTailCModelEquivTriple (n := n))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, card_triple_I]
  rw [← Nat.card_eq_fintype_card (α := Ueven (n := n)), natCard_Ueven_even (n := n) hn]
  simpa [pow_mul]

lemma natCard_evenZeroHeadB {n : ℕ} [NeZero n] (hn : Even n) :
    Nat.card (EvenZeroHeadB n) = 2 ^ ((n - 2) * n ^ 3) := by
  rw [Nat.card_congr (evenZeroHeadBEquivTailModel (n := n))]
  exact natCard_evenTailBModel (n := n) hn

lemma natCard_evenZeroHeadC {n : ℕ} [NeZero n] (hn : Even n) :
    Nat.card (EvenZeroHeadC n) = 2 ^ ((n - 2) * n ^ 3) := by
  rw [Nat.card_congr (evenZeroHeadCEquivTailModel (n := n))]
  exact natCard_evenTailCModel (n := n) hn

noncomputable def evenTailQpairModel {n : ℕ} [NeZero n]
    (XB : EvenTailBModel n) (YC : EvenTailCModel n) : F :=
  ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
    (dot (XB (v + w) p q').1 (YC v w (p + q')).1 +
      dot (XB (v + w + 1) p q').1 (YC v w (p + q' + 1)).1)

noncomputable def evenTailSignModel {n : ℕ} [NeZero n]
    (XB : EvenTailBModel n) (YC : EvenTailCModel n) : ℤ :=
  bitSign (evenTailQpairModel XB YC)

noncomputable def evenTailPairModel {n : ℕ} [NeZero n]
    (XB ZB : EvenTailBModel n) : F :=
  ∑ v : I n, ∑ p : I n, ∑ q' : I n, dot (XB v p q').1 (ZB v p q').1

noncomputable def evenTailTModel {n : ℕ} [NeZero n]
    (YC : EvenTailCModel n) : EvenTailBModel n :=
  fun t p q' => ⟨
    (∑ v : I n, (YC v (t - v) (p + q')).1) +
      ∑ v : I n, (YC v (t - (v + 1)) (p + q' + 1)).1,
    by
      refine Submodule.add_mem _ ?_ ?_
      · refine Submodule.sum_mem _ ?_
        intro v hv
        exact (YC v (t - v) (p + q')).2
      · refine Submodule.sum_mem _ ?_
        intro v hv
        exact (YC v (t - (v + 1)) (p + q' + 1)).2⟩

abbrev UevenBasisIndex (n : ℕ) [NeZero n] :=
  Module.Free.ChooseBasisIndex F (Ueven (n := n))

noncomputable instance uevenBasisIndexFintype {n : ℕ} [NeZero n] :
    Fintype (UevenBasisIndex n) := by
  classical
  exact Fintype.ofFinite (UevenBasisIndex n)

noncomputable def uevenBasis {n : ℕ} [NeZero n] :
    Module.Basis (UevenBasisIndex n) F (Ueven (n := n)) :=
  Module.Free.chooseBasis F (Ueven (n := n))

noncomputable def evenTailBModelEquivCoord {n : ℕ} [NeZero n] :
    EvenTailBModel n ≃ (UevenBasisIndex n → BCoef n) where
  toFun XB i := fun t p q' => (uevenBasis (n := n)).equivFun (XB t p q') i
  invFun X := fun t p q' => (uevenBasis (n := n)).equivFun.symm (fun i => X i t p q')
  left_inv XB := by
    funext t p q'
    exact (uevenBasis (n := n)).equivFun.symm_apply_apply (XB t p q')
  right_inv X := by
    funext i t p q'
    exact congrFun
      ((uevenBasis (n := n)).equivFun.apply_symm_apply (fun j => X j t p q')) i

noncomputable def evenTailCModelEquivCoord {n : ℕ} [NeZero n] :
    EvenTailCModel n ≃ (UevenBasisIndex n → CCoef n) where
  toFun YC i := fun v w r => (uevenBasis (n := n)).equivFun (YC v w r) i
  invFun X := fun v w r => (uevenBasis (n := n)).equivFun.symm (fun i => X i v w r)
  left_inv YC := by
    funext v w r
    exact (uevenBasis (n := n)).equivFun.symm_apply_apply (YC v w r)
  right_inv X := by
    funext i v w r
    exact congrFun
      ((uevenBasis (n := n)).equivFun.apply_symm_apply (fun j => X j v w r)) i

lemma evenTailTModel_coord_apply {n : ℕ} [NeZero n]
    (YC : EvenTailCModel n) (i : UevenBasisIndex n) :
    evenTailBModelEquivCoord (n := n) (evenTailTModel YC) i =
      Tfun ((evenTailCModelEquivCoord (n := n) YC) i) := by
  funext t p q'
  let A : Ueven (n := n) := ∑ v : I n, YC v (t - v) (p + q')
  let B : Ueven (n := n) := ∑ v : I n, YC v (t - (v + 1)) (p + q' + 1)
  have hsplit : evenTailTModel YC t p q' = A + B := by
    apply Subtype.ext
    funext a
    simp [A, B, evenTailTModel]
  let L : Ueven (n := n) →ₗ[F] (UevenBasisIndex n →₀ F) := (uevenBasis (n := n)).repr.toLinearMap
  have hA :
      (L A) i = ∑ v : I n, (L (YC v (t - v) (p + q'))) i := by
    simp [A, map_sum]
  have hB :
      (L B) i = ∑ v : I n, (L (YC v (t - (v + 1)) (p + q' + 1))) i := by
    simp [B, map_sum]
  change (L (evenTailTModel YC t p q')) i = _
  rw [hsplit]
  calc
    (L (A + B)) i = (L A + L B) i := by
      exact congrArg (fun f => f i) (L.map_add A B)
    _ = (L A) i + (L B) i := by rfl
    _ = (∑ v : I n, (L (YC v (t - v) (p + q'))) i) +
          ∑ v : I n, (L (YC v (t - (v + 1)) (p + q' + 1))) i := by
            rw [hA, hB]
    _ = Tfun ((evenTailCModelEquivCoord (n := n) YC) i) t p q' := by
          simp [L, Tfun, Cagg, evenTailCModelEquivCoord,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

noncomputable def toggleAtEvenTailBModel {n : ℕ} [NeZero n]
    (u0 : I n × I n × I n) (y0 : Ueven (n := n)) (XB : EvenTailBModel n) : EvenTailBModel n :=
  fun t p q' => XB t p q' + if (t, p, q') = u0 then y0 else 0

noncomputable def toggleEquivEvenTailBModel {n : ℕ} [NeZero n]
    (u0 : I n × I n × I n) (y0 : Ueven (n := n)) : EvenTailBModel n ≃ EvenTailBModel n where
  toFun := toggleAtEvenTailBModel u0 y0
  invFun := toggleAtEvenTailBModel u0 y0
  left_inv XB := by
    funext t p q'
    by_cases h : (t, p, q') = u0
    · have hyy : y0 + y0 = 0 := by
        apply Subtype.ext
        funext a
        simp [F_add_self]
      simpa [toggleAtEvenTailBModel, h, add_assoc] using hyy
    · simp [toggleAtEvenTailBModel, h]
  right_inv XB := by
    funext t p q'
    by_cases h : (t, p, q') = u0
    · have hyy : y0 + y0 = 0 := by
        apply Subtype.ext
        funext a
        simp [F_add_self]
      simpa [toggleAtEvenTailBModel, h, add_assoc] using hyy
    · simp [toggleAtEvenTailBModel, h]

lemma toggleAtEvenTailBModel_apply {n : ℕ} [NeZero n]
    (u0 : I n × I n × I n) (y0 : Ueven (n := n)) (XB : EvenTailBModel n) (t p q' : I n) :
    toggleAtEvenTailBModel u0 y0 XB t p q' = XB t p q' + if (t, p, q') = u0 then y0 else 0 := by
  rfl

lemma Qpair_evenZeroHead_eq_tailModel {n : ℕ} [NeZero n]
    (RB : EvenZeroHeadB n) (RC : EvenZeroHeadC n) :
    Qpair RB.1 RC.1 =
      evenTailQpairModel
        ((evenZeroHeadBEquivTailModel (n := n)) RB)
        ((evenZeroHeadCEquivTailModel (n := n)) RC) := by
  rw [Qpair_eq_sum_dot]
  rfl

lemma kappa_eq_zero_iff_evenBuild_mem_SSpace {n : ℕ} [NeZero n] (hn : Even n)
    (b : BCoef n × BCoef n) (c : CCoef n × CCoef n) (RB : BFun n) (RC : CFun n)
    (hRB : evenHeadB RB = (0, 0)) (hRC : evenHeadC RC = (0, 0)) :
    kappa (evenBuildB b RB) (evenBuildC c RC) = 0 ↔ (b.1, c.1) ∈ SSpace (n := n) := by
  rw [kappa_eq_zero_iff_evenHeadsFst_mem_SSpace]
  simp [evenHeadB_evenBuild_eq (n := n) hn b RB hRB, evenHeadC_evenBuild_eq (n := n) hn c RC hRC]

noncomputable def qEven {n : ℕ} [NeZero n] (b : BCoef n × BCoef n) (c : CCoef n × CCoef n) : F :=
  q b.1 c.1 + q b.1 c.2 + q b.2 c.1

lemma dot_evenPlaneCoordInv_right {n : ℕ} [NeZero n] (hn : Even n) (z : F × F) (y : Profile n) :
    dot (evenPlaneCoordInv (n := n) z).1 y =
      z.1 * (evenPairMap (n := n) y).1 + z.1 * (evenPairMap (n := n) y).2 +
        z.2 * (evenPairMap (n := n) y).1 := by
  rcases z with ⟨a, b⟩
  change
    dot (a • (eProfile (n := n) + fProfile (n := n)) + b • eProfile (n := n)) y =
      a * (evenPairMap (n := n) y).1 + a * (evenPairMap (n := n) y).2 + b * (evenPairMap (n := n) y).1
  rw [dot_add_left, dot_smul_left, dot_smul_left, dot_add_left]
  simp [evenPairMap, dot_eProfile_eProfile_even (n := n) hn, dot_eProfile_fProfile,
    dot_fProfile_fProfile, dot_comm, add_assoc, add_left_comm, add_comm]
  rw [mul_add]
  ac_rfl

lemma dot_evenPlaneCoordInv_left {n : ℕ} [NeZero n] (hn : Even n) (x : Profile n) (z : F × F) :
    dot x (evenPlaneCoordInv (n := n) z).1 =
      (evenPairMap (n := n) x).1 * z.1 + (evenPairMap (n := n) x).2 * z.1 +
        (evenPairMap (n := n) x).1 * z.2 := by
  rw [dot_comm, dot_evenPlaneCoordInv_right (n := n) hn z x]
  simp [mul_comm, add_assoc, add_left_comm, add_comm]

lemma dot_evenPlaneCoordInv_evenPlaneCoordInv {n : ℕ} [NeZero n] (hn : Even n)
    (z₁ z₂ : F × F) :
    dot (evenPlaneCoordInv (n := n) z₁).1 (evenPlaneCoordInv (n := n) z₂).1 =
      z₁.1 * z₂.1 + z₁.1 * z₂.2 + z₁.2 * z₂.1 := by
  have hmap : evenPairMap (n := n) (evenPlaneCoordInv (n := n) z₂).1 = z₂ := by
    simpa [evenPlaneCoordMap] using evenPlaneCoordMap_inv_apply (n := n) hn z₂
  rw [dot_evenPlaneCoordInv_right (n := n) hn]
  rw [hmap]

lemma dot_evenPlaneCoordInv_uEven_eq_zero {n : ℕ} [NeZero n] (hn : Even n) (z : F × F)
    {y : Profile n} (hy : y ∈ Ueven (n := n)) :
    dot (evenPlaneCoordInv (n := n) z).1 y = 0 := by
  change evenPairMap (n := n) y = 0 at hy
  rw [dot_evenPlaneCoordInv_right (n := n) hn z y, hy]
  simp

lemma dot_uEven_evenPlaneCoordInv_eq_zero {n : ℕ} [NeZero n] (hn : Even n) {x : Profile n}
    (hx : x ∈ Ueven (n := n)) (z : F × F) :
    dot x (evenPlaneCoordInv (n := n) z).1 = 0 := by
  rw [dot_comm]
  exact dot_evenPlaneCoordInv_uEven_eq_zero (n := n) hn z hx

lemma dot_nondegenerate_on_Ueven {n : ℕ} [NeZero n] (hn : Even n) {x : Profile n}
    (hxU : x ∈ Ueven (n := n)) (hx : ∀ y : Profile n, y ∈ Ueven (n := n) → dot x y = 0) :
    x = 0 := by
  apply dot_nondegenerate
  intro y
  have hyTop : y ∈ (⊤ : Submodule F (Profile n)) := by simp
  rw [← evenPlane_sup_Ueven_eq_top (n := n) hn] at hyTop
  rcases Submodule.mem_sup.1 hyTop with ⟨e, heP, u, huU, rfl⟩
  rw [dot_add_right, hx u huU]
  let e' : ↥(EvenPlane (n := n)) := ⟨e, heP⟩
  have heq : (evenPlaneCoordInv (n := n) (evenPlaneCoordMap (n := n) e')).1 = e := by
    exact congrArg Subtype.val (evenPlaneCoordInv_map_apply (n := n) hn e')
  rw [← heq]
  simpa using dot_uEven_evenPlaneCoordInv_eq_zero (n := n) hn hxU (evenPlaneCoordMap (n := n) e')

lemma exists_dot_one_on_Ueven {n : ℕ} [NeZero n] (hn : Even n) {x : Ueven (n := n)}
    (hx : x ≠ 0) : ∃ y : Ueven (n := n), dot y.1 x.1 = 1 := by
  by_contra h
  have hx0 : x.1 = 0 := by
    apply dot_nondegenerate_on_Ueven (n := n) hn x.2
    intro y hy
    have hneq1 : dot x.1 y ≠ 1 := by
      intro h1
      exact h ⟨⟨y, hy⟩, by simpa [dot_comm] using h1⟩
    let z : F := dot x.1 y
    have hcases : z = 0 ∨ z = 1 := by
      by_cases hz : z = 0
      · exact Or.inl hz
      · exact Or.inr (F_ne_zero_eq_one _ hz)
    rcases hcases with h0 | h1
    · simpa [z] using h0
    · exact False.elim (hneq1 (by simpa [z] using h1))
  exact hx (Subtype.ext hx0)

lemma evenTailPairModel_zero_right {n : ℕ} [NeZero n] (XB : EvenTailBModel n) :
    evenTailPairModel XB (0 : EvenTailBModel n) = 0 := by
  unfold evenTailPairModel
  simp [dot_zero_right]

lemma evenTailPairModel_toggleAt {n : ℕ} [NeZero n]
    (u0 : I n × I n × I n) (y0 : Ueven (n := n)) (XB MB : EvenTailBModel n)
    (hm : dot y0.1 ((evenTailBModelEquivTriple (n := n) MB) u0).1 = 1) :
    evenTailPairModel (toggleAtEvenTailBModel u0 y0 XB) MB = evenTailPairModel XB MB + 1 := by
  rcases u0 with ⟨t0, p0, q0⟩
  unfold evenTailPairModel
  have hsplit :
      ∀ v p q',
        dot ((toggleAtEvenTailBModel (t0, p0, q0) y0 XB v p q').1) (MB v p q').1 =
          dot (XB v p q').1 (MB v p q').1 +
            dot ((if (v, p, q') = (t0, p0, q0) then y0 else 0).1) (MB v p q').1 := by
    intro v p q'
    rw [toggleAtEvenTailBModel_apply]
    change
      dot ((XB v p q').1 + (if (v, p, q') = (t0, p0, q0) then y0 else 0).1) (MB v p q').1 = _
    rw [dot_add_left]
  simp_rw [hsplit]
  simp_rw [Finset.sum_add_distrib]
  have hs :
      ∑ v : I n, ∑ p : I n, ∑ q' : I n,
        dot ((if (v, p, q') = (t0, p0, q0) then y0 else 0).1) (MB v p q').1 = 1 := by
    rw [Finset.sum_eq_single t0]
    · rw [Finset.sum_eq_single p0]
      · rw [Finset.sum_eq_single q0]
        · simpa using hm
        · intro q' _ hq'
          simp [hq', dot_zero_left]
        · simp
      · intro p _ hp
        simp [hp, dot_zero_left]
      · simp
    · intro v _ hv
      simp [hv, dot_zero_left]
    · simp
  rw [hs]

lemma sum_bitSign_evenTailPairModel {n : ℕ} [NeZero n] (hn : Even n) (MB : EvenTailBModel n) :
    ∑ XB : EvenTailBModel n, bitSign (evenTailPairModel XB MB) =
      if MB = 0 then Fintype.card (EvenTailBModel n) else 0 := by
  classical
  by_cases hm : MB = 0
  · subst MB
    rw [if_pos rfl]
    calc
      ∑ XB : EvenTailBModel n, bitSign (evenTailPairModel XB (0 : EvenTailBModel n))
          = ∑ XB : EvenTailBModel n, (1 : ℤ) := by
              refine Finset.sum_congr rfl ?_
              intro XB hXB
              rw [evenTailPairModel_zero_right, bitSign_zero]
      _ = Fintype.card (EvenTailBModel n) := by simp
  · have hex : ∃ u0 : I n × I n × I n, (evenTailBModelEquivTriple (n := n) MB) u0 ≠ 0 := by
      by_contra h
      apply hm
      apply (evenTailBModelEquivTriple (n := n)).injective
      funext u
      by_cases hu : (evenTailBModelEquivTriple (n := n) MB) u = 0
      · exact hu
      · exact False.elim (h ⟨u, hu⟩)
    rcases hex with ⟨u0, hu0⟩
    rcases exists_dot_one_on_Ueven (n := n) hn hu0 with ⟨y0, hy0⟩
    let S : ℤ := ∑ XB : EvenTailBModel n, bitSign (evenTailPairModel XB MB)
    have htoggle :
        S = ∑ XB : EvenTailBModel n,
          bitSign (evenTailPairModel (toggleAtEvenTailBModel u0 y0 XB) MB) := by
      simpa [S] using
        (((toggleEquivEvenTailBModel (n := n) u0 y0).symm.sum_comp
          (fun XB : EvenTailBModel n => bitSign (evenTailPairModel XB MB))).symm)
    have hneg :
        ∑ XB : EvenTailBModel n, bitSign (evenTailPairModel (toggleAtEvenTailBModel u0 y0 XB) MB)
          = -S := by
      calc
        ∑ XB : EvenTailBModel n, bitSign (evenTailPairModel (toggleAtEvenTailBModel u0 y0 XB) MB)
            = ∑ XB : EvenTailBModel n, -bitSign (evenTailPairModel XB MB) := by
                refine Finset.sum_congr rfl ?_
                intro XB hXB
                rw [evenTailPairModel_toggleAt (n := n) u0 y0 XB MB hy0, bitSign_add_one]
        _ = -S := by simp [S]
    have hs : S = -S := by
      calc
        S = ∑ XB : EvenTailBModel n,
            bitSign (evenTailPairModel (toggleAtEvenTailBModel u0 y0 XB) MB) := htoggle
        _ = -S := hneg
    have hzero : S = 0 := by linarith
    simp [S, hm, hzero]

lemma sum_evenTailLeft_inner_eq {n : ℕ} [NeZero n]
    (XB : EvenTailBModel n) (YC : EvenTailCModel n) (v p q' : I n) :
    (∑ t : I n, dot (XB t p q').1 (YC v (t - v) (p + q')).1) =
      ∑ w : I n, dot (XB (v + w) p q').1 (YC v w (p + q')).1 := by
  symm
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (sum_reindex_addLeft (a := v)
      (f := fun t : I n => dot (XB t p q').1 (YC v (t - v) (p + q')).1))

lemma sum_evenTailRight_inner_eq {n : ℕ} [NeZero n]
    (XB : EvenTailBModel n) (YC : EvenTailCModel n) (v p q' : I n) :
    (∑ t : I n, dot (XB t p q').1 (YC v (t - (v + 1)) (p + q' + 1)).1) =
      ∑ w : I n, dot (XB (v + (w + 1)) p q').1 (YC v w (p + q' + 1)).1 := by
  have hraw :=
    (sum_reindex_addLeft
      (a := v + 1)
      (f := fun t : I n => dot (XB t p q').1 (YC v (t - (v + 1)) (p + q' + 1)).1)).symm
  convert hraw using 1
  · refine Finset.sum_congr rfl ?_
    intro w hw
    have hc : v + (w + 1) - (v + 1) = w := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hc

lemma evenTailPairModel_eq_qpairModel {n : ℕ} [NeZero n]
    (XB : EvenTailBModel n) (YC : EvenTailCModel n) :
    evenTailPairModel XB (evenTailTModel YC) = evenTailQpairModel XB YC := by
  calc
    evenTailPairModel XB (evenTailTModel YC)
        = ∑ t : I n, ∑ p : I n, ∑ q' : I n, ∑ v : I n,
            (dot (XB t p q').1 (YC v (t - v) (p + q')).1 +
              dot (XB t p q').1 (YC v (t - (v + 1)) (p + q' + 1)).1) := by
              unfold evenTailPairModel evenTailTModel
              simp_rw [dot_add_right, dot_sum_right]
              simp_rw [← Finset.sum_add_distrib]
    _ = ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ t : I n,
          (dot (XB t p q').1 (YC v (t - v) (p + q')).1 +
            dot (XB t p q').1 (YC v (t - (v + 1)) (p + q' + 1)).1) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro p hp
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro q' hq
              rw [Finset.sum_comm]
    _ = ∑ p : I n, ∑ q' : I n, ∑ v : I n,
          ((∑ t : I n, dot (XB t p q').1 (YC v (t - v) (p + q')).1) +
            ∑ t : I n, dot (XB t p q').1 (YC v (t - (v + 1)) (p + q' + 1)).1) := by
              simp_rw [Finset.sum_add_distrib]
    _ = ∑ p : I n, ∑ q' : I n, ∑ v : I n,
          ((∑ w : I n, dot (XB (v + w) p q').1 (YC v w (p + q')).1) +
            ∑ w : I n, dot (XB (v + (w + 1)) p q').1 (YC v w (p + q' + 1)).1) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              refine Finset.sum_congr rfl ?_
              intro q' hq
              refine Finset.sum_congr rfl ?_
              intro v hv
              rw [sum_evenTailLeft_inner_eq XB YC v p q', sum_evenTailRight_inner_eq XB YC v p q']
    _ = ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ w : I n,
          (dot (XB (v + w) p q').1 (YC v w (p + q')).1 +
            dot (XB (v + (w + 1)) p q').1 (YC v w (p + q' + 1)).1) := by
              simp_rw [Finset.sum_add_distrib]
    _ = ∑ p : I n, ∑ v : I n, ∑ w : I n, ∑ q' : I n,
          (dot (XB (v + w) p q').1 (YC v w (p + q')).1 +
            dot (XB (v + (w + 1)) p q').1 (YC v w (p + q' + 1)).1) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro v hv
              rw [Finset.sum_comm]
    _ = ∑ v : I n, ∑ p : I n, ∑ w : I n, ∑ q' : I n,
          (dot (XB (v + w) p q').1 (YC v w (p + q')).1 +
            dot (XB (v + (w + 1)) p q').1 (YC v w (p + q' + 1)).1) := by
              rw [Finset.sum_comm]
    _ = ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
          (dot (XB (v + w) p q').1 (YC v w (p + q')).1 +
            dot (XB (v + (w + 1)) p q').1 (YC v w (p + q' + 1)).1) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              rw [Finset.sum_comm]
    _ = evenTailQpairModel XB YC := by
          simp [evenTailQpairModel, add_assoc]

lemma Qpair_evenVisible_evenTail_eq_zero {n : ℕ} [NeZero n] (hn : Even n) (B : BFun n) (C : CFun n) :
    Qpair (evenVisibleB B) (evenTailC C) = 0 := by
  rw [Qpair_eq_sum_dot]
  refine Finset.sum_eq_zero ?_
  intro v hv
  refine Finset.sum_eq_zero ?_
  intro w hw
  refine Finset.sum_eq_zero ?_
  intro p hp
  refine Finset.sum_eq_zero ?_
  intro q' hq
  change
    dot (evenBSlice (evenVisibleB B) (v + w) p q') (evenCSlice (evenTailC C) v w (p + q')) +
      dot (evenBSlice (evenVisibleB B) (v + w + 1) p q') (evenCSlice (evenTailC C) v w (p + q' + 1)) = 0
  rw [evenVisibleB_slice, evenVisibleB_slice]
  have h₁ := evenTailC_slice_mem_Ueven (n := n) hn C v w (p + q')
  have h₂ := evenTailC_slice_mem_Ueven (n := n) hn C v w (p + q' + 1)
  rw [dot_evenPlaneCoordInv_uEven_eq_zero (n := n) hn _ h₁,
    dot_evenPlaneCoordInv_uEven_eq_zero (n := n) hn _ h₂]
  simp

lemma Qpair_evenTail_evenVisible_eq_zero {n : ℕ} [NeZero n] (hn : Even n) (B : BFun n) (C : CFun n) :
    Qpair (evenTailB B) (evenVisibleC C) = 0 := by
  rw [Qpair_eq_sum_dot]
  refine Finset.sum_eq_zero ?_
  intro v hv
  refine Finset.sum_eq_zero ?_
  intro w hw
  refine Finset.sum_eq_zero ?_
  intro p hp
  refine Finset.sum_eq_zero ?_
  intro q' hq
  change
    dot (evenBSlice (evenTailB B) (v + w) p q') (evenCSlice (evenVisibleC C) v w (p + q')) +
      dot (evenBSlice (evenTailB B) (v + w + 1) p q') (evenCSlice (evenVisibleC C) v w (p + q' + 1)) = 0
  rw [evenVisibleC_slice, evenVisibleC_slice]
  have h₁ := evenTailB_slice_mem_Ueven (n := n) hn B (v + w) p q'
  have h₂ := evenTailB_slice_mem_Ueven (n := n) hn B (v + w + 1) p q'
  rw [dot_uEven_evenPlaneCoordInv_eq_zero (n := n) hn h₁ _,
    dot_uEven_evenPlaneCoordInv_eq_zero (n := n) hn h₂ _]
  simp

lemma evenVisibleB_eq_tensor_add {n : ℕ} [NeZero n] (B : BFun n) :
    evenVisibleB B =
      tensorB (eProfile (n := n) + fProfile (n := n)) (evenHeadB B).1 +
        tensorB (eProfile (n := n)) (evenHeadB B).2 := by
  funext a t p q'
  simp [evenVisibleB, evenPlaneCoordInv, tensorB, eProfile, fProfile, oneProfile, Pi.add_apply]
  rw [add_mul]
  ac_rfl

lemma evenVisibleC_eq_tensor_add {n : ℕ} [NeZero n] (C : CFun n) :
    evenVisibleC C =
      tensorC (eProfile (n := n) + fProfile (n := n)) (evenHeadC C).1 +
        tensorC (eProfile (n := n)) (evenHeadC C).2 := by
  funext a v w r
  simp [evenVisibleC, evenPlaneCoordInv, tensorC, eProfile, fProfile, oneProfile, Pi.add_apply]
  rw [add_mul]
  ac_rfl

lemma Qpair_evenVisible_evenVisible {n : ℕ} [NeZero n] (hn : Even n) (B : BFun n) (C : CFun n) :
    Qpair (evenVisibleB B) (evenVisibleC C) = qEven (evenHeadB B) (evenHeadC C) := by
  rw [evenVisibleB_eq_tensor_add, evenVisibleC_eq_tensor_add]
  rw [Qpair_add_left, Qpair_add_right, Qpair_add_right]
  rw [Qpair_tensor, Qpair_tensor, Qpair_tensor, Qpair_tensor]
  unfold qEven
  have h₁ :
      dot (eProfile (n := n) + fProfile (n := n)) (eProfile (n := n) + fProfile (n := n)) = 1 := by
    rw [dot_add_left, dot_add_right, dot_add_right]
    simp [dot_eProfile_eProfile_even (n := n) hn, dot_eProfile_fProfile, dot_fProfile_fProfile,
      dot_comm, F_add_self]
  have h₂ : dot (eProfile (n := n) + fProfile (n := n)) (eProfile (n := n)) = 1 := by
    rw [dot_add_left]
    simp [dot_eProfile_eProfile_even (n := n) hn, dot_eProfile_fProfile, dot_comm]
  have h₃ : dot (eProfile (n := n)) (eProfile (n := n) + fProfile (n := n)) = 1 := by
    rw [dot_add_right]
    simp [dot_eProfile_eProfile_even (n := n) hn, dot_eProfile_fProfile, dot_comm]
  have h₄ : dot (eProfile (n := n)) (eProfile (n := n)) = 0 := dot_eProfile_eProfile_even (n := n) hn
  rw [h₁, h₂, h₃, h₄]
  simp [zero_mul, one_mul, add_assoc, add_left_comm, add_comm]

lemma Qpair_eq_even_split {n : ℕ} [NeZero n] (hn : Even n) (B : BFun n) (C : CFun n) :
    Qpair B C = qEven (evenHeadB B) (evenHeadC C) + Qpair (evenTailB B) (evenTailC C) := by
  have hdecomp : Qpair B C = Qpair (evenVisibleB B + evenTailB B) (evenVisibleC C + evenTailC C) := by
    conv_lhs =>
      rw [even_decompose_B (B := B), even_decompose_C (C := C)]
  calc
    Qpair B C = Qpair (evenVisibleB B + evenTailB B) (evenVisibleC C + evenTailC C) := hdecomp
    _ = Qpair (evenVisibleB B) (evenVisibleC C) + Qpair (evenVisibleB B) (evenTailC C) +
          (Qpair (evenTailB B) (evenVisibleC C) + Qpair (evenTailB B) (evenTailC C)) := by
      rw [Qpair_add_left, Qpair_add_right, Qpair_add_right]
    _ = qEven (evenHeadB B) (evenHeadC C) + 0 + (0 + Qpair (evenTailB B) (evenTailC C)) := by
      rw [Qpair_evenVisible_evenVisible (n := n) hn]
      rw [Qpair_evenVisible_evenTail_eq_zero (n := n) hn]
      rw [Qpair_evenTail_evenVisible_eq_zero (n := n) hn]
    _ = qEven (evenHeadB B) (evenHeadC C) + Qpair (evenTailB B) (evenTailC C) := by
      simp

lemma Qraw_eq_even_split_of_surviving {n : ℕ} [NeZero n] (hn : Even n) {B : BFun n} {C : CFun n}
    (hk : kappa B C = 0) :
    Qraw B C = qEven (evenHeadB B) (evenHeadC C) + Qpair (evenTailB B) (evenTailC C) := by
  rw [Qraw_eq_Qpair_of_kappa_zero hk]
  exact Qpair_eq_even_split (n := n) hn B C

abbrev EvenVisibleData (n : ℕ) [NeZero n] :=
  { bc : (BCoef n × BCoef n) × (CCoef n × CCoef n) // (bc.1.1, bc.2.1) ∈ SSpace (n := n) }

abbrev EvenSurvivingData (n : ℕ) [NeZero n] :=
  EvenVisibleData n × EvenZeroHeadB n × EvenZeroHeadC n

noncomputable instance evenVisibleDataFintype {n : ℕ} [NeZero n] : Fintype (EvenVisibleData n) := by
  classical
  infer_instance

noncomputable instance evenSurvivingDataFintype {n : ℕ} [NeZero n] :
    Fintype (EvenSurvivingData n) := by
  classical
  infer_instance

noncomputable def evenSurvivingToData {n : ℕ} [NeZero n] (hn : Even n) :
    SurvivingBC n → EvenSurvivingData n :=
  fun bc =>
    (⟨(evenHeadB bc.1.1, evenHeadC bc.1.2),
        (kappa_eq_zero_iff_evenHeadsFst_mem_SSpace (B := bc.1.1) (C := bc.1.2)).1 bc.2⟩,
      ⟨evenTailB bc.1.1, evenHeadB_evenTail_eq_zero (n := n) hn bc.1.1⟩,
      ⟨evenTailC bc.1.2, evenHeadC_evenTail_eq_zero (n := n) hn bc.1.2⟩)

noncomputable def evenDataToSurviving {n : ℕ} [NeZero n] (hn : Even n) :
    EvenSurvivingData n → SurvivingBC n
  | (bc, RB, RC) =>
      ⟨(evenBuildB bc.1.1 RB.1, evenBuildC bc.1.2 RC.1),
        (kappa_eq_zero_iff_evenBuild_mem_SSpace (n := n) hn bc.1.1 bc.1.2 RB.1 RC.1 RB.2 RC.2).2
          bc.2⟩

lemma evenDataToSurviving_evenSurvivingToData {n : ℕ} [NeZero n] (hn : Even n)
    (bc : SurvivingBC n) :
    evenDataToSurviving (n := n) hn (evenSurvivingToData (n := n) hn bc) = bc := by
  rcases bc with ⟨⟨B, C⟩, hk⟩
  have hB : evenBuildB (evenHeadB B) (evenTailB B) = B := by
    exact evenBuildB_head_tail_eq (B := B)
  have hC : evenBuildC (evenHeadC C) (evenTailC C) = C := by
    exact evenBuildC_head_tail_eq (C := C)
  apply Subtype.ext
  apply Prod.ext
  · simpa [evenDataToSurviving, evenSurvivingToData] using hB
  · simpa [evenDataToSurviving, evenSurvivingToData] using hC

lemma evenSurvivingToData_evenDataToSurviving {n : ℕ} [NeZero n] (hn : Even n)
    (d : EvenSurvivingData n) :
    evenSurvivingToData (n := n) hn (evenDataToSurviving (n := n) hn d) = d := by
  rcases d with ⟨⟨⟨b, c⟩, hbc⟩, ⟨RB, hRB⟩, ⟨RC, hRC⟩⟩
  apply Prod.ext
  · apply Subtype.ext
    ext <;> simp [evenSurvivingToData, evenDataToSurviving,
      evenHeadB_evenBuild_eq (n := n) hn b RB hRB,
      evenHeadC_evenBuild_eq (n := n) hn c RC hRC]
  · apply Prod.ext
    · apply Subtype.ext
      simp [evenSurvivingToData, evenDataToSurviving,
        evenTailB_evenBuild_eq (n := n) hn b RB hRB]
    · apply Subtype.ext
      simp [evenSurvivingToData, evenDataToSurviving,
        evenTailC_evenBuild_eq (n := n) hn c RC hRC]

noncomputable def evenSurvivingEquiv {n : ℕ} [NeZero n] (hn : Even n) :
    SurvivingBC n ≃ EvenSurvivingData n where
  toFun := evenSurvivingToData (n := n) hn
  invFun := evenDataToSurviving (n := n) hn
  left_inv := evenDataToSurviving_evenSurvivingToData (n := n) hn
  right_inv := evenSurvivingToData_evenDataToSurviving (n := n) hn

noncomputable def evenDataSign {n : ℕ} [NeZero n] (d : EvenSurvivingData n) : ℤ :=
  match d with
  | (bc, RB, RC) => bitSign (qEven bc.1.1 bc.1.2 + Qpair RB.1 RC.1)

noncomputable def evenVisibleSign {n : ℕ} [NeZero n] (bc : EvenVisibleData n) : ℤ :=
  bitSign (qEven bc.1.1 bc.1.2)

noncomputable def evenTailSign {n : ℕ} [NeZero n] (RB : EvenZeroHeadB n) (RC : EvenZeroHeadC n) : ℤ :=
  bitSign (Qpair RB.1 RC.1)

lemma evenTailSign_eq_model {n : ℕ} [NeZero n]
    (RB : EvenZeroHeadB n) (RC : EvenZeroHeadC n) :
    evenTailSign RB RC =
      evenTailSignModel
        ((evenZeroHeadBEquivTailModel (n := n)) RB)
        ((evenZeroHeadCEquivTailModel (n := n)) RC) := by
  simp [evenTailSign, evenTailSignModel, Qpair_evenZeroHead_eq_tailModel]

lemma sum_evenTail_eq_sum_model {n : ℕ} [NeZero n] :
    ∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC =
      ∑ YC : EvenTailCModel n, ∑ XB : EvenTailBModel n, evenTailSignModel XB YC := by
  classical
  calc
    ∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC
        = ∑ YC : EvenTailCModel n,
            ∑ RB : EvenZeroHeadB n,
              evenTailSign RB ((evenZeroHeadCEquivTailModel (n := n)).symm YC) := by
              refine Fintype.sum_equiv (evenZeroHeadCEquivTailModel (n := n)) _ _ ?_
              intro RC
              simp
    _ = ∑ YC : EvenTailCModel n,
          ∑ XB : EvenTailBModel n,
            evenTailSignModel XB YC := by
          refine Finset.sum_congr rfl ?_
          intro YC hYC
          calc
            ∑ RB : EvenZeroHeadB n, evenTailSign RB ((evenZeroHeadCEquivTailModel (n := n)).symm YC)
                = ∑ XB : EvenTailBModel n,
                    evenTailSign
                      ((evenZeroHeadBEquivTailModel (n := n)).symm XB)
                      ((evenZeroHeadCEquivTailModel (n := n)).symm YC) := by
                        refine Fintype.sum_equiv (evenZeroHeadBEquivTailModel (n := n)) _ _ ?_
                        intro RB
                        simp
            _ = ∑ XB : EvenTailBModel n, evenTailSignModel XB YC := by
                  refine Finset.sum_congr rfl ?_
                  intro XB hXB
                  simpa using
                    evenTailSign_eq_model
                      ((evenZeroHeadBEquivTailModel (n := n)).symm XB)
                      ((evenZeroHeadCEquivTailModel (n := n)).symm YC)

abbrev EvenTailKerData (n : ℕ) [NeZero n] := {YC : EvenTailCModel n // evenTailTModel YC = 0}

lemma sum_evenTailSignModel_eq_card_mul_ker {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ YC : EvenTailCModel n, ∑ XB : EvenTailBModel n, evenTailSignModel XB YC =
      (Fintype.card (EvenTailBModel n) : ℤ) * Fintype.card (EvenTailKerData n) := by
  classical
  have hfilter :
      ∑ YC : EvenTailCModel n,
        (if evenTailTModel YC = 0 then (Fintype.card (EvenTailBModel n) : ℤ) else 0) =
      Finset.sum
        (Finset.univ.filter fun YC : EvenTailCModel n => evenTailTModel YC = 0)
        (fun _ => (Fintype.card (EvenTailBModel n) : ℤ)) := by
    rw [Finset.sum_ite]
    simp
  have hcard :
      (Finset.univ.filter fun YC : EvenTailCModel n => evenTailTModel YC = 0).card =
        Fintype.card (EvenTailKerData n) := by
    simpa [EvenTailKerData] using
      (Fintype.card_subtype (fun YC : EvenTailCModel n => evenTailTModel YC = 0)).symm
  calc
    ∑ YC : EvenTailCModel n, ∑ XB : EvenTailBModel n, evenTailSignModel XB YC
        = ∑ YC : EvenTailCModel n,
            ∑ XB : EvenTailBModel n, bitSign (evenTailPairModel XB (evenTailTModel YC)) := by
              refine Finset.sum_congr rfl ?_
              intro YC hYC
              refine Finset.sum_congr rfl ?_
              intro XB hXB
              simp [evenTailSignModel, evenTailPairModel_eq_qpairModel]
    _ = ∑ YC : EvenTailCModel n,
          if evenTailTModel YC = 0 then (Fintype.card (EvenTailBModel n) : ℤ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro YC hYC
            simpa using sum_bitSign_evenTailPairModel (n := n) hn (evenTailTModel YC)
    _ = Finset.sum
          (Finset.univ.filter fun YC : EvenTailCModel n => evenTailTModel YC = 0)
          (fun _ => (Fintype.card (EvenTailBModel n) : ℤ)) := hfilter
    _ = (Fintype.card (EvenTailBModel n) : ℤ) * Fintype.card (EvenTailKerData n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [hcard]
          ring

lemma sum_evenTail_eq_card_mul_ker {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC =
      (Fintype.card (EvenTailBModel n) : ℤ) * Fintype.card (EvenTailKerData n) := by
  rw [sum_evenTail_eq_sum_model]
  exact sum_evenTailSignModel_eq_card_mul_ker (n := n) hn

lemma evenTailTModel_eq_zero_iff_coord {n : ℕ} [NeZero n] (YC : EvenTailCModel n) :
    evenTailTModel YC = 0 ↔
      ∀ i : UevenBasisIndex n, T (n := n) ((evenTailCModelEquivCoord (n := n) YC) i) = 0 := by
  constructor
  · intro h i
    have hi := congrArg (fun XB => evenTailBModelEquivCoord (n := n) XB i) h
    calc
      T (n := n) ((evenTailCModelEquivCoord (n := n) YC) i)
          = evenTailBModelEquivCoord (n := n) (evenTailTModel YC) i := by
              symm
              exact evenTailTModel_coord_apply (n := n) (YC := YC) (i := i)
      _ = 0 := by simpa [evenTailBModelEquivCoord] using hi
  · intro h
    apply (evenTailBModelEquivCoord (n := n)).injective
    funext i
    calc
      evenTailBModelEquivCoord (n := n) (evenTailTModel YC) i
          = T (n := n) ((evenTailCModelEquivCoord (n := n) YC) i) := by
              exact evenTailTModel_coord_apply (n := n) (YC := YC) (i := i)
      _ = 0 := by simpa [evenTailBModelEquivCoord] using h i
      _ = evenTailBModelEquivCoord (n := n) (0 : EvenTailBModel n) i := by
            ext t p q'
            simp [evenTailBModelEquivCoord]

noncomputable def evenTailKerEquivCoordKer {n : ℕ} [NeZero n] :
    EvenTailKerData n ≃ (UevenBasisIndex n → {c : CCoef n // T c = 0}) where
  toFun YC i := ⟨(evenTailCModelEquivCoord (n := n) YC.1) i, by
    simpa using (evenTailTModel_eq_zero_iff_coord (n := n) YC.1).mp YC.2 i⟩
  invFun X := ⟨(evenTailCModelEquivCoord (n := n)).symm (fun i => (X i).1), by
    apply (evenTailTModel_eq_zero_iff_coord (n := n) _).2
    intro i
    simpa using (X i).2⟩
  left_inv YC := by
    apply Subtype.ext
    exact (evenTailCModelEquivCoord (n := n)).left_inv YC.1
  right_inv X := by
    funext i
    apply Subtype.ext
    simpa using congrFun ((evenTailCModelEquivCoord (n := n)).right_inv (fun j => (X j).1)) i

lemma natCard_evenTailKerData {n : ℕ} [NeZero n] (hn : Even n) :
    Nat.card (EvenTailKerData n) = 2 ^ ((n - 2) * (n ^ 3 - n * (n - 1))) := by
  rw [Nat.card_congr (evenTailKerEquivCoordKer (n := n))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  have hker : Fintype.card {c : CCoef n // T c = 0} = 2 ^ (n ^ 3 - n * (n - 1)) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [LinearMap.mem_ker] using natCard_ker_T (n := n)
  rw [hker]
  have hidx : Fintype.card (UevenBasisIndex n) = n - 2 := by
    have hchoose := Module.finrank_eq_card_chooseBasisIndex (R := F) (M := Ueven (n := n))
    rw [finrank_Ueven (n := n) hn] at hchoose
    simpa [UevenBasisIndex] using hchoose.symm
  rw [hidx]
  simpa [Nat.mul_comm (n - 2) (n ^ 3 - n * (n - 1))] using
    (pow_mul 2 (n ^ 3 - n * (n - 1)) (n - 2)).symm

lemma sum_evenTail_eq_closed_form {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC =
      (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))) := by
  rw [sum_evenTail_eq_card_mul_ker (n := n) hn]
  have hB : (Fintype.card (EvenTailBModel n) : ℤ) = (2 : ℤ) ^ ((n - 2) * n ^ 3) := by
    rw [← Nat.card_eq_fintype_card (α := EvenTailBModel n), natCard_evenTailBModel (n := n) hn]
    simpa using (Nat.cast_pow (R := ℤ) 2 ((n - 2) * n ^ 3))
  have hK : (Fintype.card (EvenTailKerData n) : ℤ) =
      (2 : ℤ) ^ ((n - 2) * (n ^ 3 - n * (n - 1))) := by
    rw [← Nat.card_eq_fintype_card (α := EvenTailKerData n), natCard_evenTailKerData (n := n) hn]
    simpa using (Nat.cast_pow (R := ℤ) 2 ((n - 2) * (n ^ 3 - n * (n - 1))))
  rw [hB, hK, ← pow_add]

lemma evenDataSign_eq_mul {n : ℕ} [NeZero n] (d : EvenSurvivingData n) :
    evenDataSign d =
      evenVisibleSign d.1 * evenTailSign d.2.1 d.2.2 := by
  rcases d with ⟨bc, RB, RC⟩
  simp [evenDataSign, evenVisibleSign, evenTailSign, bitSign_add]

lemma sum_survivingBC_eq_sum_evenData {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2) =
      ∑ d : EvenSurvivingData n, evenDataSign d := by
  classical
  have hrew :
      ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2)
        = ∑ d : EvenSurvivingData n,
            bitSign (Qraw (evenDataToSurviving (n := n) hn d).1.1
              (evenDataToSurviving (n := n) hn d).1.2) := by
        refine Fintype.sum_equiv (evenSurvivingEquiv (n := n) hn) _ _ ?_
        intro bc
        have hleft : evenDataToSurviving (n := n) hn ((evenSurvivingEquiv (n := n) hn) bc) = bc := by
          simpa [evenSurvivingEquiv] using evenDataToSurviving_evenSurvivingToData (n := n) hn bc
        simpa [hleft]
  calc
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2)
        = ∑ d : EvenSurvivingData n,
            bitSign (Qraw (evenDataToSurviving (n := n) hn d).1.1
              (evenDataToSurviving (n := n) hn d).1.2) := hrew
    _ = ∑ d : EvenSurvivingData n, evenDataSign d := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rcases d with ⟨⟨⟨b, c⟩, hbc⟩, ⟨RB, hRB⟩, ⟨RC, hRC⟩⟩
          have hk : kappa (evenBuildB b RB) (evenBuildC c RC) = 0 :=
            (kappa_eq_zero_iff_evenBuild_mem_SSpace (n := n) hn b c RB RC hRB hRC).2 hbc
          calc
            bitSign (Qraw (evenBuildB b RB) (evenBuildC c RC))
                = bitSign
                    (qEven (evenHeadB (evenBuildB b RB)) (evenHeadC (evenBuildC c RC)) +
                      Qpair (evenTailB (evenBuildB b RB)) (evenTailC (evenBuildC c RC))) := by
                        rw [Qraw_eq_even_split_of_surviving (n := n) hn
                          (B := evenBuildB b RB) (C := evenBuildC c RC) hk]
            _ = bitSign (qEven b c + Qpair RB RC) := by
                  simp [evenHeadB_evenBuild_eq (n := n) hn b RB hRB,
                    evenHeadC_evenBuild_eq (n := n) hn c RC hRC,
                    evenTailB_evenBuild_eq (n := n) hn b RB hRB,
                    evenTailC_evenBuild_eq (n := n) hn c RC hRC]

lemma sum_evenData_eq_iterated {n : ℕ} [NeZero n] :
    ∑ d : EvenSurvivingData n, evenDataSign d =
      ∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, ∑ bc : EvenVisibleData n,
        evenVisibleSign bc * evenTailSign RB RC := by
  simp_rw [Fintype.sum_prod_type_right]
  simp [evenDataSign_eq_mul, evenVisibleSign, evenTailSign]

lemma sum_evenData_eq_visible_mul_tail {n : ℕ} [NeZero n] :
    ∑ d : EvenSurvivingData n, evenDataSign d =
      (∑ bc : EvenVisibleData n, evenVisibleSign bc) *
        (∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC) := by
  rw [sum_evenData_eq_iterated]
  calc
    ∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, ∑ bc : EvenVisibleData n,
        evenVisibleSign bc * evenTailSign RB RC
      = ∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n,
          (∑ bc : EvenVisibleData n, evenVisibleSign bc) * evenTailSign RB RC := by
            refine Finset.sum_congr rfl ?_
            intro RC hRC
            refine Finset.sum_congr rfl ?_
            intro RB hRB
            rw [← Finset.sum_mul]
    _ = ∑ RC : EvenZeroHeadC n,
          (∑ bc : EvenVisibleData n, evenVisibleSign bc) *
            ∑ RB : EvenZeroHeadB n, evenTailSign RB RC := by
              refine Finset.sum_congr rfl ?_
              intro RC hRC
              rw [← Finset.mul_sum]
    _ = (∑ bc : EvenVisibleData n, evenVisibleSign bc) *
          (∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC) := by
            rw [← Finset.mul_sum]

lemma sum_survivingBC_eq_even_visible_mul_tail {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2) =
      (∑ bc : EvenVisibleData n, evenVisibleSign bc) *
        (∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC) := by
  rw [sum_survivingBC_eq_sum_evenData (n := n) hn, sum_evenData_eq_visible_mul_tail]

noncomputable def evenVisibleToOddFree {n : ℕ} [NeZero n] :
    EvenVisibleData n → OddVisibleData n × BCoef n × CCoef n
  | ⟨bc, hbc⟩ => (⟨(bc.1.1, bc.2.1), hbc⟩, bc.1.2, bc.2.2)

noncomputable def oddFreeToEvenVisible {n : ℕ} [NeZero n] :
    OddVisibleData n × BCoef n × CCoef n → EvenVisibleData n
  | (bc, b₂, c₂) => ⟨((bc.1.1, b₂), (bc.1.2, c₂)), bc.2⟩

lemma oddFreeToEvenVisible_evenVisibleToOddFree {n : ℕ} [NeZero n] (bc : EvenVisibleData n) :
    oddFreeToEvenVisible (n := n) (evenVisibleToOddFree (n := n) bc) = bc := by
  rcases bc with ⟨⟨⟨b₁, b₂⟩, ⟨c₁, c₂⟩⟩, hbc⟩
  rfl

lemma evenVisibleToOddFree_oddFreeToEvenVisible {n : ℕ} [NeZero n]
    (x : OddVisibleData n × BCoef n × CCoef n) :
    evenVisibleToOddFree (n := n) (oddFreeToEvenVisible (n := n) x) = x := by
  rcases x with ⟨⟨⟨b, c⟩, hbc⟩, b₂, c₂⟩
  rfl

noncomputable def evenVisibleEquivOddFree {n : ℕ} [NeZero n] :
    EvenVisibleData n ≃ (OddVisibleData n × BCoef n × CCoef n) where
  toFun := evenVisibleToOddFree (n := n)
  invFun := oddFreeToEvenVisible (n := n)
  left_inv := oddFreeToEvenVisible_evenVisibleToOddFree (n := n)
  right_inv := evenVisibleToOddFree_oddFreeToEvenVisible (n := n)

lemma natCard_evenVisibleData {n : ℕ} [NeZero n] :
    Nat.card (EvenVisibleData n) = 2 ^ (n ^ 3 + n ^ 3) * Nat.card (OddVisibleData n) := by
  have hB : Nat.card (BCoef n) = 2 ^ (n ^ 3) := by
    simpa [Nat.card_eq_fintype_card] using (card_BCoef n)
  rw [Nat.card_congr (evenVisibleEquivOddFree (n := n))]
  rw [Nat.card_prod, Nat.card_prod]
  rw [hB]
  calc
    Nat.card (OddVisibleData n) * (2 ^ (n ^ 3) * 2 ^ (n ^ 3)) =
        Nat.card (OddVisibleData n) * 2 ^ (n ^ 3 + n ^ 3) := by
          rw [← pow_add]
    _ = 2 ^ (n ^ 3 + n ^ 3) * Nat.card (OddVisibleData n) := by
          ac_rfl

lemma evenVisibleSign_eq_odd_free {n : ℕ} [NeZero n] (bc : OddVisibleData n)
    (b₂ : BCoef n) (c₂ : CCoef n) :
    evenVisibleSign (oddFreeToEvenVisible (n := n) (bc, b₂, c₂)) =
      oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2) := by
  simp [evenVisibleSign, oddFreeToEvenVisible, oddVisibleSign, qEven, bitSign_add]

lemma sum_evenVisible_eq_iterated {n : ℕ} [NeZero n] :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc =
      ∑ c₂ : CCoef n, ∑ b₂ : BCoef n, ∑ bc : OddVisibleData n,
        oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2) := by
  classical
  calc
    ∑ bc : EvenVisibleData n, evenVisibleSign bc
        = ∑ x : OddVisibleData n × BCoef n × CCoef n,
            evenVisibleSign (oddFreeToEvenVisible (n := n) x) := by
              refine Fintype.sum_equiv (evenVisibleEquivOddFree (n := n)) _ _ ?_
              intro bc
              simp [evenVisibleEquivOddFree, oddFreeToEvenVisible_evenVisibleToOddFree]
    _ = ∑ yz : BCoef n × CCoef n, ∑ bc : OddVisibleData n,
          evenVisibleSign (oddFreeToEvenVisible (n := n) (bc, yz.1, yz.2)) := by
            simpa using
              (Fintype.sum_prod_type_right'
                (f := fun bc : OddVisibleData n => fun yz : BCoef n × CCoef n =>
                  evenVisibleSign (oddFreeToEvenVisible (n := n) (bc, yz.1, yz.2))))
    _ = ∑ c₂ : CCoef n, ∑ b₂ : BCoef n, ∑ bc : OddVisibleData n,
          oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2) := by
            have hsplit :
                (∑ yz : BCoef n × CCoef n, ∑ bc : OddVisibleData n,
                    evenVisibleSign (oddFreeToEvenVisible (n := n) (bc, yz.1, yz.2)))
                  =
                ∑ c₂ : CCoef n, ∑ b₂ : BCoef n, ∑ bc : OddVisibleData n,
                    evenVisibleSign (oddFreeToEvenVisible (n := n) (bc, b₂, c₂)) := by
                      simpa using
                        (Fintype.sum_prod_type_right'
                          (f := fun b₂ : BCoef n => fun c₂ : CCoef n =>
                            ∑ bc : OddVisibleData n,
                              evenVisibleSign (oddFreeToEvenVisible (n := n) (bc, b₂, c₂))))
            rw [hsplit]
            refine Finset.sum_congr rfl ?_
            intro c₂ hc₂
            refine Finset.sum_congr rfl ?_
            intro b₂ hb₂
            refine Finset.sum_congr rfl ?_
            intro bc hbc
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (evenVisibleSign_eq_odd_free (n := n) bc b₂ c₂)

lemma sum_evenVisible_eq_odd_indicator_weighted {n : ℕ} [NeZero n] :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc =
      ∑ bc : OddVisibleData n,
        oddVisibleSign bc *
          ((((if Tadj bc.1.1 = 0 then Fintype.card (CCoef n) else 0 : ℕ) : ℤ)) *
            (((if T bc.1.2 = 0 then Fintype.card (BCoef n) else 0 : ℕ) : ℤ))) := by
  rw [sum_evenVisible_eq_iterated]
  calc
    ∑ c₂ : CCoef n, ∑ b₂ : BCoef n, ∑ bc : OddVisibleData n,
        oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2)
      =
        ∑ bc : OddVisibleData n, ∑ c₂ : CCoef n, ∑ b₂ : BCoef n,
          oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2) := by
            have hsplit :
                ∑ c₂ : CCoef n, ∑ b₂ : BCoef n, ∑ bc : OddVisibleData n,
                    oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2)
                  =
                ∑ z : BCoef n × CCoef n, ∑ bc : OddVisibleData n,
                    oddVisibleSign bc * bitSign (q bc.1.1 z.2) * bitSign (q z.1 bc.1.2) := by
                      symm
                      simpa using
                        (Fintype.sum_prod_type_right'
                          (f := fun b₂ : BCoef n => fun c₂ : CCoef n =>
                            ∑ bc : OddVisibleData n,
                              oddVisibleSign bc * bitSign (q bc.1.1 c₂) *
                                bitSign (q b₂ bc.1.2)))
            rw [hsplit]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro bc hbc
            simpa using
              (Fintype.sum_prod_type_right'
                (f := fun b₂ : BCoef n => fun c₂ : CCoef n =>
                  oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2)))
    _ = ∑ bc : OddVisibleData n,
          oddVisibleSign bc * ((∑ c₂ : CCoef n, bitSign (q bc.1.1 c₂)) *
            ∑ b₂ : BCoef n, bitSign (q b₂ bc.1.2)) := by
              refine Finset.sum_congr rfl ?_
              intro bc hbc
              calc
                ∑ c₂ : CCoef n, ∑ b₂ : BCoef n,
                    oddVisibleSign bc * bitSign (q bc.1.1 c₂) * bitSign (q b₂ bc.1.2)
                  = ∑ c₂ : CCoef n,
                      (oddVisibleSign bc * bitSign (q bc.1.1 c₂)) *
                        ∑ b₂ : BCoef n, bitSign (q b₂ bc.1.2) := by
                          refine Finset.sum_congr rfl ?_
                          intro c₂ hc₂
                          simpa [mul_assoc] using
                            (Finset.mul_sum
                              (s := (Finset.univ : Finset (BCoef n)))
                              (a := oddVisibleSign bc * bitSign (q bc.1.1 c₂))
                              (f := fun b₂ : BCoef n => bitSign (q b₂ bc.1.2))).symm
                _ = (∑ c₂ : CCoef n, oddVisibleSign bc * bitSign (q bc.1.1 c₂)) *
                      ∑ b₂ : BCoef n, bitSign (q b₂ bc.1.2) := by
                        rw [Finset.sum_mul]
                _ = (oddVisibleSign bc * ∑ c₂ : CCoef n, bitSign (q bc.1.1 c₂)) *
                      ∑ b₂ : BCoef n, bitSign (q b₂ bc.1.2) := by
                        rw [← Finset.mul_sum]
                _ = oddVisibleSign bc * ((∑ c₂ : CCoef n, bitSign (q bc.1.1 c₂)) *
                      ∑ b₂ : BCoef n, bitSign (q b₂ bc.1.2)) := by
                        simp [mul_assoc]
    _ = ∑ bc : OddVisibleData n,
          oddVisibleSign bc *
            ((((if Tadj bc.1.1 = 0 then Fintype.card (CCoef n) else 0 : ℕ) : ℤ)) *
              (((if T bc.1.2 = 0 then Fintype.card (BCoef n) else 0 : ℕ) : ℤ))) := by
            refine Finset.sum_congr rfl ?_
            intro bc hbc
            rw [sum_bitSign_q_right (n := n) bc.1.1, sum_bitSign_q (n := n) bc.1.2]

abbrev EvenVisibleKernelData (n : ℕ) [NeZero n] :=
  { bc : OddVisibleData n // Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0 }

abbrev EvenVisibleKernelHUVData (n : ℕ) [NeZero n] :=
  HSpace (n := n) × (ConstAggUV n × ConstAggUV n)

noncomputable instance hSpaceFintype {n : ℕ} [NeZero n] : Fintype (HSpace (n := n)) := by
  classical
  infer_instance

noncomputable instance evenVisibleKernelHUVDataFintype {n : ℕ} [NeZero n] :
    Fintype (EvenVisibleKernelHUVData n) := by
  classical
  infer_instance

noncomputable def evenVisibleKernelToHUVData {n : ℕ} [NeZero n] (hn : Even n) :
    EvenVisibleKernelData n → EvenVisibleKernelHUVData n
  | ⟨⟨bc, hbc⟩, hb, hc⟩ =>
      let hH : HSpace (n := n) := ⟨visibleHData bc, visibleHData_mem_HSpace (n := n) hbc⟩
      let uK : ConstAggUV n := ⟨visibleUData bc,
        (Tadj_buildB_eq_zero_iff (n := n) hn (visibleHData bc) (visibleUData bc)).1 <| by
          simpa [buildB_visibleData_eq (n := n) (bc := bc) hbc] using hb⟩
      let vK : ConstAggUV n := ⟨visibleVData bc,
        (T_buildC_eq_zero_iff (n := n) hn (visibleHData bc) (visibleVData bc)).1 <| by
          simpa [buildC_visibleData_eq (n := n) (bc := bc) hbc] using hc⟩
      (hH, (uK, vK))

noncomputable def evenVisibleKernelFromHUVData {n : ℕ} [NeZero n] (hn : Even n) :
    EvenVisibleKernelHUVData n → EvenVisibleKernelData n
  | ⟨h, uK, vK⟩ =>
      ⟨⟨(buildB h.1 uK.1, buildC h.1 vK.1), build_mem_SSpace_of_mem_HSpace (n := n) h uK.1 vK.1⟩,
        (Tadj_buildB_eq_zero_iff (n := n) hn h.1 uK.1).2 uK.2,
        (T_buildC_eq_zero_iff (n := n) hn h.1 vK.1).2 vK.2⟩

lemma evenVisibleKernelToHUVData_from {n : ℕ} [NeZero n] (hn : Even n)
    (z : EvenVisibleKernelHUVData n) :
    evenVisibleKernelToHUVData (n := n) hn (evenVisibleKernelFromHUVData (n := n) hn z) = z := by
  rcases z with ⟨⟨h, hh⟩, ⟨⟨u, hu⟩, ⟨v, hv⟩⟩⟩
  let bc : BCoef n × CCoef n := (buildB h u, buildC h v)
  have hbc : bc ∈ SSpace (n := n) := by
    simpa [bc] using build_mem_SSpace_of_mem_HSpace (n := n) ⟨h, hh⟩ u v
  have hb : Tadj bc.1 = 0 := by
    simpa [bc] using (Tadj_buildB_eq_zero_iff (n := n) hn h u).2 hu
  have hc : T bc.2 = 0 := by
    simpa [bc] using (T_buildC_eq_zero_iff (n := n) hn h v).2 hv
  change evenVisibleKernelToHUVData (n := n) hn ⟨⟨bc, hbc⟩, hb, hc⟩
      = (⟨h, hh⟩, (⟨u, hu⟩, ⟨v, hv⟩))
  apply Prod.ext
  · apply Subtype.ext
    simpa [evenVisibleKernelToHUVData, bc] using
      (visibleHData_build_eq (n := n) ⟨h, hh⟩ u v)
  · apply Prod.ext
    · apply Subtype.ext
      simpa [evenVisibleKernelToHUVData, bc] using
        (visibleUData_build_eq (n := n) ⟨h, hh⟩ u v)
    · apply Subtype.ext
      simpa [evenVisibleKernelToHUVData, bc] using
        (visibleVData_build_eq (n := n) ⟨h, hh⟩ u v)

lemma evenVisibleKernelToHUVData_injective {n : ℕ} [NeZero n] (hn : Even n) :
    Function.Injective (evenVisibleKernelToHUVData (n := n) hn) := by
  intro x y hxy
  rcases x with ⟨⟨bcx, hbcx⟩, hbx, hcx⟩
  rcases y with ⟨⟨bcy, hbcy⟩, hby, hcy⟩
  have hh :
      visibleHData bcx = visibleHData bcy := by
    exact congrArg (fun z : EvenVisibleKernelHUVData n => z.1.1) hxy
  have hu :
      visibleUData bcx = visibleUData bcy := by
    exact congrArg (fun z : EvenVisibleKernelHUVData n => z.2.1.1) hxy
  have hv :
      visibleVData bcx = visibleVData bcy := by
    exact congrArg (fun z : EvenVisibleKernelHUVData n => z.2.2.1) hxy
  have hb :
      bcx.1 = bcy.1 := by
    calc
      bcx.1 = buildB (visibleHData bcx) (visibleUData bcx) := by
        symm
        exact buildB_visibleData_eq (n := n) (bc := bcx) hbcx
      _ = buildB (visibleHData bcy) (visibleUData bcy) := by
        rw [hh, hu]
      _ = bcy.1 := by
        exact buildB_visibleData_eq (n := n) (bc := bcy) hbcy
  have hc :
      bcx.2 = bcy.2 := by
    calc
      bcx.2 = buildC (visibleHData bcx) (visibleVData bcx) := by
        symm
        exact buildC_visibleData_eq (n := n) (bc := bcx) hbcx
      _ = buildC (visibleHData bcy) (visibleVData bcy) := by
        rw [hh, hv]
      _ = bcy.2 := by
        exact buildC_visibleData_eq (n := n) (bc := bcy) hbcy
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hb hc

lemma evenVisibleKernelFromHUVData_to {n : ℕ} [NeZero n] (hn : Even n)
    (x : EvenVisibleKernelData n) :
    evenVisibleKernelFromHUVData (n := n) hn (evenVisibleKernelToHUVData (n := n) hn x) = x := by
  apply evenVisibleKernelToHUVData_injective (n := n) hn
  simpa using
    evenVisibleKernelToHUVData_from (n := n) hn (evenVisibleKernelToHUVData (n := n) hn x)

noncomputable def evenVisibleKernelEquivHUVData {n : ℕ} [NeZero n] (hn : Even n) :
    EvenVisibleKernelData n ≃ EvenVisibleKernelHUVData n where
  toFun := evenVisibleKernelToHUVData (n := n) hn
  invFun := evenVisibleKernelFromHUVData (n := n) hn
  left_inv := evenVisibleKernelFromHUVData_to (n := n) hn
  right_inv := evenVisibleKernelToHUVData_from (n := n) hn

lemma evenVisibleKernel_card_le_huv {n : ℕ} [NeZero n] (hn : Even n) :
    Fintype.card (EvenVisibleKernelData n) ≤ Fintype.card (EvenVisibleKernelHUVData n) :=
  Fintype.card_le_of_injective (evenVisibleKernelToHUVData (n := n) hn)
    (evenVisibleKernelToHUVData_injective (n := n) hn)

lemma evenVisibleKernel_card_eq_huv {n : ℕ} [NeZero n] (hn : Even n) :
    Fintype.card (EvenVisibleKernelData n) = Fintype.card (EvenVisibleKernelHUVData n) := by
  exact Fintype.card_congr (evenVisibleKernelEquivHUVData (n := n) hn)

lemma natCard_evenVisibleKernelHUVData {n : ℕ} [NeZero n] :
    Nat.card (EvenVisibleKernelHUVData n) =
      2 ^ (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1))) := by
  change Nat.card (HSpace (n := n) × (ConstAggUV n × ConstAggUV n)) =
    2 ^ (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1)))
  rw [Nat.card_prod, natCard_HSpace_even, natCard_constAggUV_prod, ← pow_add]

lemma evenVisibleKernel_card_le_closed_form {n : ℕ} [NeZero n] (hn : Even n) :
    Fintype.card (EvenVisibleKernelData n) ≤
      2 ^ (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1))) := by
  have hle := evenVisibleKernel_card_le_huv (n := n) hn
  have hcard :
      Fintype.card (EvenVisibleKernelHUVData n) =
        2 ^ (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1))) := by
    rw [← Nat.card_eq_fintype_card (α := EvenVisibleKernelHUVData n)]
    exact natCard_evenVisibleKernelHUVData (n := n)
  rw [hcard] at hle
  exact hle

lemma evenVisibleKernel_closed_form_exponent {n : ℕ} [NeZero n] :
    ((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1)) = 3 * n ^ 2 + 3 - 4 * n := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
  set m : ℕ := k * k
  have hm : k ^ 2 = m := by
    simp [pow_two, m]
  have hsq : (k + 1) ^ 2 = m + 2 * k + 1 := by
    dsimp [m]
    ring_nf
  have hterm : (k + 1) ^ 2 - (k + 1) + 1 = m + k + 1 := by
    rw [hsq]
    omega
  calc
    ((k + 1 - 1) ^ 2) + (((k + 1) ^ 2 - (k + 1) + 1) + ((k + 1) ^ 2 - (k + 1) + 1))
        = m + ((m + k + 1) + (m + k + 1)) := by
          simp [hm, hterm]
    _ = 3 * m + 2 * k + 2 := by omega
    _ = 3 * ((k + 1) ^ 2) + 3 - 4 * (k + 1) := by
          rw [hsq]
          omega

lemma natCard_evenVisibleKernelHUVData_compact {n : ℕ} [NeZero n] :
    Nat.card (EvenVisibleKernelHUVData n) = 2 ^ (3 * n ^ 2 + 3 - 4 * n) := by
  rw [natCard_evenVisibleKernelHUVData, evenVisibleKernel_closed_form_exponent (n := n)]

lemma fintypeCard_evenVisibleKernelHUVData_compact {n : ℕ} [NeZero n] :
    Fintype.card (EvenVisibleKernelHUVData n) = 2 ^ (3 * n ^ 2 + 3 - 4 * n) := by
  rw [← Nat.card_eq_fintype_card (α := EvenVisibleKernelHUVData n)]
  exact natCard_evenVisibleKernelHUVData_compact (n := n)

lemma natCard_evenVisibleKernelData_compact {n : ℕ} [NeZero n] (hn : Even n) :
    Nat.card (EvenVisibleKernelData n) = 2 ^ (3 * n ^ 2 + 3 - 4 * n) := by
  rw [Nat.card_eq_fintype_card, evenVisibleKernel_card_eq_huv (n := n) hn,
    fintypeCard_evenVisibleKernelHUVData_compact (n := n)]

lemma fintypeCard_evenVisibleKernelData_compact {n : ℕ} [NeZero n] (hn : Even n) :
    Fintype.card (EvenVisibleKernelData n) = 2 ^ (3 * n ^ 2 + 3 - 4 * n) := by
  rw [← Nat.card_eq_fintype_card (α := EvenVisibleKernelData n)]
  exact natCard_evenVisibleKernelData_compact (n := n) hn

lemma evenVisibleKernel_card_le_closed_form_compact {n : ℕ} [NeZero n] (hn : Even n) :
    Fintype.card (EvenVisibleKernelData n) ≤ 2 ^ (3 * n ^ 2 + 3 - 4 * n) := by
  rw [← evenVisibleKernel_closed_form_exponent (n := n)]
  exact evenVisibleKernel_card_le_closed_form (n := n) hn

lemma oddVisibleSign_eq_one_of_Tadj_eq_zero {n : ℕ} [NeZero n] (bc : OddVisibleData n)
    (hb : Tadj bc.1.1 = 0) : oddVisibleSign bc = 1 := by
  unfold oddVisibleSign
  rw [q_eq_cPair_Tadj, hb]
  unfold cPair
  simp [bitSign_zero]

lemma oddVisibleSign_eq_one_of_T_eq_zero {n : ℕ} [NeZero n] (bc : OddVisibleData n)
    (hc : T bc.1.2 = 0) : oddVisibleSign bc = 1 := by
  unfold oddVisibleSign
  rw [q_eq_bPair_T, hc]
  unfold bPair
  simp [bitSign_zero]

lemma sum_evenVisible_eq_kernel_visible_count {n : ℕ} [NeZero n] :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc =
      ((((Fintype.card (CCoef n) : ℕ) : ℤ) * (((Fintype.card (BCoef n) : ℕ) : ℤ))) *
        Fintype.card (EvenVisibleKernelData n)) := by
  classical
  let K : ℤ := (((Fintype.card (CCoef n) : ℕ) : ℤ) * (((Fintype.card (BCoef n) : ℕ) : ℤ)))
  let s : Finset (OddVisibleData n) :=
    Finset.univ.filter (fun bc : OddVisibleData n => Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0)
  rw [sum_evenVisible_eq_odd_indicator_weighted (n := n)]
  have hterm :
      ∀ bc : OddVisibleData n,
        oddVisibleSign bc *
            ((((if Tadj bc.1.1 = 0 then Fintype.card (CCoef n) else 0 : ℕ) : ℤ)) *
              (((if T bc.1.2 = 0 then Fintype.card (BCoef n) else 0 : ℕ) : ℤ))) =
          if h : Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0 then K else 0 := by
    intro bc
    by_cases hb : Tadj bc.1.1 = 0
    · by_cases hc : T bc.1.2 = 0
      · have hsign : oddVisibleSign bc = 1 := oddVisibleSign_eq_one_of_Tadj_eq_zero (n := n) bc hb
        have hh : Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0 := ⟨hb, hc⟩
        simp [K, hb, hc, hh, hsign]
      · have hh : ¬ (Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0) := by
          simp [hb, hc]
        simp [K, hb, hc, hh]
    · have hh : ¬ (Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0) := by
        simp [hb]
      simp [K, hb, hh]
  calc
    ∑ bc : OddVisibleData n,
        oddVisibleSign bc *
          ((((if Tadj bc.1.1 = 0 then Fintype.card (CCoef n) else 0 : ℕ) : ℤ)) *
            (((if T bc.1.2 = 0 then Fintype.card (BCoef n) else 0 : ℕ) : ℤ)))
      = ∑ bc : OddVisibleData n, if h : Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0 then K else 0 := by
          refine Finset.sum_congr rfl ?_
          intro bc hbc
          exact hterm bc
    _ = s.sum (fun _ => K) := by
          rw [show s = Finset.univ.filter
            (fun bc : OddVisibleData n => Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0) by rfl]
          have hdep :
              (∑ bc : OddVisibleData n,
                  if h : Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0 then K else 0)
                =
              ∑ bc : OddVisibleData n,
                if Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0 then K else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro bc hbc
                  by_cases hh : Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0 <;> simp [hh]
          rw [hdep]
          rw [← Finset.sum_filter]
    _ = K * Fintype.card (EvenVisibleKernelData n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [← Fintype.card_of_subtype
            (p := fun bc : OddVisibleData n => Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0)
            (s := s)]
          · ring
          · intro bc
            rw [show s = Finset.univ.filter
              (fun bc : OddVisibleData n => Tadj bc.1.1 = 0 ∧ T bc.1.2 = 0) by rfl]
            simp
    _ = ((((Fintype.card (CCoef n) : ℕ) : ℤ) * (((Fintype.card (BCoef n) : ℕ) : ℤ))) *
          Fintype.card (EvenVisibleKernelData n)) := by
            rfl

lemma sum_evenVisible_eq_kernel_visible_closed_form {n : ℕ} [NeZero n] :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc =
      (2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n) := by
  rw [sum_evenVisible_eq_kernel_visible_count]
  have hC : (((Fintype.card (CCoef n) : ℕ) : ℤ)) = (2 : ℤ) ^ (n ^ 3) := by
    rw [card_CCoef]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ 3))
  rw [hC]
  have hp : (2 : ℤ) ^ (n ^ 3) * (2 : ℤ) ^ (n ^ 3) = (2 : ℤ) ^ (n ^ 3 + n ^ 3) := by
    rw [← pow_add]
  calc
    (2 : ℤ) ^ (n ^ 3) * (2 : ℤ) ^ (n ^ 3) * Fintype.card (EvenVisibleKernelData n)
      = ((2 : ℤ) ^ (n ^ 3) * (2 : ℤ) ^ (n ^ 3)) * Fintype.card (EvenVisibleKernelData n) := by
          ac_rfl
    _ = (2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n) := by
          rw [hp]

lemma sum_evenVisible_eq_closed_form_compact {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc =
      (2 : ℤ) ^ (n ^ 3 + n ^ 3) * (2 : ℤ) ^ (3 * n ^ 2 + 3 - 4 * n) := by
  rw [sum_evenVisible_eq_kernel_visible_closed_form,
    fintypeCard_evenVisibleKernelData_compact (n := n) hn]
  have hcast :
      ((2 ^ (3 * n ^ 2 + 3 - 4 * n) : ℕ) : ℤ) = (2 : ℤ) ^ (3 * n ^ 2 + 3 - 4 * n) := by
    simpa using (Nat.cast_pow (R := ℤ) 2 (3 * n ^ 2 + 3 - 4 * n))
  rw [hcast]

lemma sum_evenVisible_le_closed_form {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc ≤
      (2 : ℤ) ^ (n ^ 3 + n ^ 3) *
        (2 : ℤ) ^ (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1))) := by
  rw [sum_evenVisible_eq_kernel_visible_closed_form]
  have hk_nat := evenVisibleKernel_card_le_closed_form (n := n) hn
  have hk :
      (Fintype.card (EvenVisibleKernelData n) : ℤ) ≤
        (2 : ℤ) ^ (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1))) := by
    exact_mod_cast hk_nat
  have hpow : 0 ≤ (2 : ℤ) ^ (n ^ 3 + n ^ 3) := by
    positivity
  exact mul_le_mul_of_nonneg_left hk hpow

lemma sum_evenVisible_le_closed_form_pow {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc ≤
      (2 : ℤ) ^
        ((n ^ 3 + n ^ 3) + (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1)))) := by
  calc
    ∑ bc : EvenVisibleData n, evenVisibleSign bc
        ≤ (2 : ℤ) ^ (n ^ 3 + n ^ 3) *
            (2 : ℤ) ^ (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1))) :=
          sum_evenVisible_le_closed_form (n := n) hn
    _ = (2 : ℤ) ^
          ((n ^ 3 + n ^ 3) + (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1)))) := by
          rw [← pow_add]

lemma sum_evenVisible_closed_form_exponent {n : ℕ} [NeZero n] :
    (n ^ 3 + n ^ 3) + (((n - 1) ^ 2) + ((n ^ 2 - n + 1) + (n ^ 2 - n + 1)))
      = 2 * n ^ 3 + (3 * n ^ 2 + 3 - 4 * n) := by
  rw [evenVisibleKernel_closed_form_exponent (n := n)]
  rw [← two_mul (n ^ 3)]

lemma sum_evenVisible_le_closed_form_compact {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : EvenVisibleData n, evenVisibleSign bc ≤
      (2 : ℤ) ^ (2 * n ^ 3 + (3 * n ^ 2 + 3 - 4 * n)) := by
  rw [← sum_evenVisible_closed_form_exponent (n := n)]
  exact sum_evenVisible_le_closed_form_pow (n := n) hn

lemma sum_survivingBC_eq_even_kernel_visible_mul_tail {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2) =
      ((2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)) *
        (∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC) := by
  rw [sum_survivingBC_eq_even_visible_mul_tail (n := n) hn]
  rw [sum_evenVisible_eq_kernel_visible_closed_form]

lemma sum_survivingBC_eq_even_kernel_visible_mul_closed_tail {n : ℕ} [NeZero n] (hn : Even n) :
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2) =
      ((2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)) *
        (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))) := by
  rw [sum_survivingBC_eq_even_kernel_visible_mul_tail (n := n) hn]
  rw [sum_evenTail_eq_closed_form (n := n) hn]

lemma Delta16_even_special_factorized {n : ℕ} [NeZero n] (hn : Even n) :
    Delta16 n =
      (2 : ℤ) ^ (n ^ 4) *
        (((2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)) *
          (∑ RC : EvenZeroHeadC n, ∑ RB : EvenZeroHeadB n, evenTailSign RB RC)) := by
  rw [delta_after_A (n := n)]
  rw [sum_survivingBC_eq_even_kernel_visible_mul_tail (n := n) hn]

lemma Delta16_even_special_factorized_closed_tail {n : ℕ} [NeZero n] (hn : Even n) :
    Delta16 n =
      (2 : ℤ) ^ (n ^ 4) *
        (((2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)) *
          (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) := by
  rw [delta_after_A (n := n)]
  rw [sum_survivingBC_eq_even_kernel_visible_mul_closed_tail (n := n) hn]

lemma Delta16_even_special_le_closed_form {n : ℕ} [NeZero n] (hn : Even n) :
    Delta16 n ≤
      (2 : ℤ) ^ (n ^ 4) *
        ((2 : ℤ) ^ (2 * n ^ 3 + (3 * n ^ 2 + 3 - 4 * n)) *
          (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) := by
  rw [delta_after_A (n := n)]
  rw [sum_survivingBC_eq_even_kernel_visible_mul_closed_tail (n := n) hn]
  have hk_nat := evenVisibleKernel_card_le_closed_form_compact (n := n) hn
  have hvis :
      (2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n) ≤
        (2 : ℤ) ^ (2 * n ^ 3 + (3 * n ^ 2 + 3 - 4 * n)) := by
    have hk :
        (Fintype.card (EvenVisibleKernelData n) : ℤ) ≤
          (2 : ℤ) ^ (3 * n ^ 2 + 3 - 4 * n) := by
      exact_mod_cast hk_nat
    have hpow : 0 ≤ (2 : ℤ) ^ (n ^ 3 + n ^ 3) := by positivity
    calc
      (2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)
        ≤ (2 : ℤ) ^ (n ^ 3 + n ^ 3) * (2 : ℤ) ^ (3 * n ^ 2 + 3 - 4 * n) :=
          mul_le_mul_of_nonneg_left hk hpow
      _ = (2 : ℤ) ^ (2 * n ^ 3 + (3 * n ^ 2 + 3 - 4 * n)) := by
          rw [← pow_add]
          congr 1
          omega
  have hpow : 0 ≤ (2 : ℤ) ^ (n ^ 4) := by positivity
  have htail : 0 ≤ (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))) := by
    positivity
  calc
    (2 : ℤ) ^ (n ^ 4) *
        (((2 : ℤ) ^ (n ^ 3 + n ^ 3) * Fintype.card (EvenVisibleKernelData n)) *
          (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1)))))
      ≤ (2 : ℤ) ^ (n ^ 4) *
          ((2 : ℤ) ^ (2 * n ^ 3 + (3 * n ^ 2 + 3 - 4 * n)) *
            (2 : ℤ) ^ (((n - 2) * n ^ 3) + ((n - 2) * (n ^ 3 - n * (n - 1))))) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_right hvis htail
            · exact hpow

end No16
