import Core3loop.OperatorT

open scoped BigOperators

namespace Core3loop

noncomputable def scalarBConst {c n : ℕ} (u : ZCoord c n → F) : ScalarBCoef c n :=
  fun _ z => u z

noncomputable def scalarCConst {b n : ℕ} (v : YCoord b n → F) : ScalarCCoef b n :=
  fun y _ => v y

noncomputable def scalarBPref {c n : ℕ} [NeZero n] (h : HRaw n) : ScalarBCoef c n :=
  buildScalarB h 0

noncomputable def scalarCPref {b n : ℕ} [NeZero n] (h : HRaw n) : ScalarCCoef b n :=
  buildScalarC h 0

lemma buildScalarB_eq_scalarBConst_add_scalarBPref {c n : ℕ} [NeZero n]
    (h : HRaw n) (u : ZCoord c n → F) :
    buildScalarB h u = scalarBConst u + scalarBPref h := by
  funext t z
  simp [scalarBConst, scalarBPref, buildScalarB, add_comm, add_left_comm]

lemma buildScalarC_eq_scalarCConst_add_scalarCPref {b n : ℕ} [NeZero n]
    (h : HRaw n) (v : YCoord b n → F) :
    buildScalarC h v = scalarCConst v + scalarCPref h := by
  funext y r
  simp [scalarCConst, scalarCPref, buildScalarC, add_comm, add_left_comm]

noncomputable def scalarYAgg {b n : ℕ} [NeZero n] (v : YCoord b n → F) : I n → F :=
  fun t => ∑ y : YCoord b n, if sumY y = t then v y else 0

lemma Cagg_scalarCConst {b n : ℕ} [NeZero n] (v : YCoord b n → F) (t s : I n) :
    Cagg (b := b) (n := n) (scalarCConst v) t s = scalarYAgg v t := by
  unfold Cagg scalarCConst scalarYAgg
  refine Finset.sum_congr rfl ?_
  intro y hy
  by_cases hyt : sumY y = t <;> simp [hyt]

lemma sum_reindex_addLeft {n : ℕ} [NeZero n] (a : I n) (f : I n → F) :
    ∑ x : I n, f (a + x) = ∑ t : I n, f t := by
  simpa using (Equiv.sum_comp (Equiv.addLeft a) f)

noncomputable def coordSuccEquiv (m n : ℕ) : Coord (m + 1) n ≃ I n × Coord m n where
  toFun u := (u 0, tailCoord u)
  invFun p := composeCoord p.1 p.2
  left_inv := by
    intro u
    funext i
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ j => rfl
  right_inv := by
    intro p
    rcases p with ⟨head, tail⟩
    simp [tailCoord_composeCoord]

lemma sigmaCoord_composeCoord {m n : ℕ} [NeZero n] (head : I n) (tail : Coord m n) :
    sigmaCoord (composeCoord head tail) = head + sigmaCoord tail := by
  unfold sigmaCoord No13Migration.sumCoord
  simpa [composeCoord, add_assoc] using
    (Fin.sum_univ_succ (f := fun i : Fin (m + 1) => composeCoord head tail i))

lemma odd_card_Coord_of_odd {m n : ℕ} [NeZero n] (hn : Odd n) :
    Odd (Fintype.card (Coord m n)) := by
  simpa [card_Coord] using Odd.pow (a := n) (n := m) hn

lemma sum_const_coord_eq_of_odd {m n : ℕ} [NeZero n] (hn : Odd n) (x : F) :
    ∑ u : Coord m n, x = x := by
  have hx : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with rfl | rfl
  · simp
  · rcases odd_card_Coord_of_odd (m := m) (n := n) hn with ⟨k, hk⟩
    calc
      ∑ _u : Coord m n, (1 : F) = (Fintype.card (Coord m n) : F) := by simp
      _ = 1 := by
            have h2 : ((2 : ℕ) : F) = 0 := by decide
            rw [hk, Nat.cast_add, Nat.cast_one, Nat.cast_mul, h2, zero_mul, zero_add]

lemma sum_sigmaCoord_eq_of_odd {m n : ℕ} [NeZero n] (hm : 0 < m) (hn : Odd n) (f : I n → F) :
    ∑ u : Coord m n, f (sigmaCoord u) = ∑ t : I n, f t := by
  rcases Nat.exists_eq_succ_of_ne_zero hm.ne' with ⟨k, rfl⟩
  calc
    ∑ u : Coord (k + 1) n, f (sigmaCoord u)
      = ∑ p : I n × Coord k n, f (sigmaCoord (composeCoord p.1 p.2)) := by
          refine Fintype.sum_equiv (coordSuccEquiv k n) (fun u => f (sigmaCoord u))
            (fun p => f (sigmaCoord (composeCoord p.1 p.2))) ?_
          intro u
          have hu : composeCoord (u 0) (tailCoord u) = u := (coordSuccEquiv k n).left_inv u
          simp [coordSuccEquiv, hu]
    _ = ∑ t : I n, ∑ tail : Coord k n, f (t + sigmaCoord tail) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro t ht
          refine Finset.sum_congr rfl ?_
          intro tail htail
          rw [sigmaCoord_composeCoord]
    _ = ∑ tail : Coord k n, ∑ t : I n, f (t + sigmaCoord tail) := by
          rw [Finset.sum_comm]
    _ = ∑ tail : Coord k n, ∑ t : I n, f t := by
          refine Finset.sum_congr rfl ?_
          intro tail htail
          simpa [add_comm] using sum_reindex_addLeft (n := n) (sigmaCoord tail) f
    _ = ∑ t : I n, f t := by
          exact sum_const_coord_eq_of_odd (m := k) (n := n) hn (∑ t : I n, f t)

lemma sum_sumY_eq_of_odd {b n : ℕ} [NeZero n] (hb : 0 < b) (hn : Odd n) (f : I n → F) :
    ∑ y : YCoord b n, f (sumY y) = ∑ t : I n, f t := by
  simpa [sumY, sigmaCoord] using sum_sigmaCoord_eq_of_odd (m := b) (n := n) hb hn f

lemma sum_sumZ_eq_of_odd {c n : ℕ} [NeZero n] (hc : 0 < c) (hn : Odd n) (f : I n → F) :
    ∑ z : ZCoord c n, f (sumZ z) = ∑ s : I n, f s := by
  simpa [sumZ, sigmaCoord] using sum_sigmaCoord_eq_of_odd (m := c) (n := n) hc hn f

lemma sigma_const_odd {n : ℕ} [NeZero n] (hn : Odd n) (x : F) :
    sigma (fun _ : I n => x) = x := by
  have hx : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with rfl | rfl
  · unfold sigma
    simp
  · rcases hn with ⟨k, hk⟩
    calc
      sigma (fun _ : I n => (1 : F)) = (Fintype.card (I n) : F) := by
        simp [sigma]
      _ = 1 := by
            have hc : Fintype.card (I n) = n := by
              simp [I, ZMod.card]
            have h2 : ((2 : ℕ) : F) = 0 := by decide
            rw [hc, hk, Nat.cast_add, Nat.cast_one, Nat.cast_mul, h2, zero_mul, zero_add]

lemma sum_pair_add_eq_of_odd {n : ℕ} [NeZero n] (hn : Odd n) (g : I n → F) :
    ∑ v : I n, ∑ w : I n, g (v + w) = ∑ t : I n, g t := by
  calc
    ∑ v : I n, ∑ w : I n, g (v + w) = ∑ v : I n, ∑ t : I n, g t := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simpa using sum_reindex_addLeft (n := n) (a := v) (f := g)
    _ = sigma (fun _ : I n => ∑ t : I n, g t) := by
      rfl
    _ = ∑ t : I n, g t := by
      simpa [sigma] using sigma_const_odd (n := n) hn (∑ t : I n, g t)

lemma Cagg_scalarCPref_eq_of_odd {b n : ℕ} [NeZero n] (hb : 0 < b) (hn : Odd n)
    (h : HRaw n) (t s : I n) :
    Cagg (b := b) (n := n) (scalarCPref (b := b) h) t s = prefixR h t s := by
  unfold Cagg scalarCPref buildScalarC
  simp only [Pi.zero_apply, zero_add]
  calc
    ∑ y : YCoord b n, (if sumY y = t then prefixR h (sumY y) s else 0)
      = ∑ y : YCoord b n, (if sumY y = t then prefixR h t s else 0) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          by_cases hyt : sumY y = t <;> simp [hyt]
    _ = ∑ y : YCoord b n, ((if sumY y = t then (1 : F) else 0) * prefixR h t s) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          by_cases hyt : sumY y = t <;> simp [hyt, mul_comm]
    _ = (∑ y : YCoord b n, (if sumY y = t then (1 : F) else 0)) * prefixR h t s := by
          rw [Finset.sum_mul]
    _ = prefixR h t s := by
          have hind :
              ∑ y : YCoord b n, (if sumY y = t then (1 : F) else 0) = 1 := by
            simpa using
              sum_sumY_eq_of_odd (b := b) (n := n) hb hn (fun r => if r = t then (1 : F) else 0)
          rw [hind, one_mul]

lemma prefixR_pair_eq_of_mem_HAdmissible {n : ℕ} [NeZero n] {h : HRaw n}
    (hh : h ∈ HAdmissible (n := n)) (t s : I n) :
    prefixR h t s + prefixR h t (s + 1) = h t s := by
  have hcore := visibleCore_eq_zero_of_mem_HAdmissible (n := n) hh t s
  have hT := prefixT_pair_eq_of_mem_HAdmissible (n := n) hh t s
  have hsum : h t s + (prefixR h t s + prefixR h t (s + 1)) = 0 := by
    simpa [visibleCore, hT, add_assoc, add_left_comm, add_comm] using hcore
  apply add_left_cancel (a := h t s)
  simpa [F_add_self, add_assoc, add_left_comm, add_comm] using hsum

lemma qScalar_add_left {b c n : ℕ} [NeZero n]
    (b₁ b₂ : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qScalar (b₁ + b₂) ccoef = qScalar b₁ ccoef + qScalar b₂ ccoef := by
  unfold qScalar qLeftScalar qRightScalar
  simp [add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma qScalar_add_right {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (c₁ c₂ : ScalarCCoef b n) :
    qScalar bcoef (c₁ + c₂) = qScalar bcoef c₁ + qScalar bcoef c₂ := by
  have hagg : Cagg (b := b) (n := n) (c₁ + c₂) =
      Cagg (b := b) (n := n) c₁ + Cagg (b := b) (n := n) c₂ := by
    funext t r
    exact congrFun (congrFun ((CaggMap (b := b) (n := n)).map_add c₁ c₂) t) r
  unfold qScalar qLeftScalar qRightScalar
  simp [hagg, mul_add, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma qScalar_scalarBConst_scalarCConst_eq_zero {b c n : ℕ} [NeZero n]
    (u : ZCoord c n → F) (v : YCoord b n → F) :
    qScalar (b := b) (c := c) (n := n) (scalarBConst u) (scalarCConst v) = 0 := by
  rw [qScalar]
  have hsame :
      qLeftScalar (b := b) (c := c) (n := n) (scalarBConst u) (scalarCConst v) =
        qRightScalar (b := b) (c := c) (n := n) (scalarBConst u) (scalarCConst v) := by
    have hshift :=
      sum_reindex_addLeft (n := n) (1 : I n)
        (fun t =>
          ∑ z : ZCoord c n, u z * scalarYAgg v (t - 1))
    unfold qLeftScalar qRightScalar scalarBConst
    simpa [Cagg_scalarCConst] using hshift
  rw [hsame]
  simp [F_add_self]

lemma qScalar_scalarBConst_scalarCPref_eq_zero_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hn : Odd n) {h : HRaw n} (hh : h ∈ HAdmissible (n := n))
    (u : ZCoord c n → F) :
    qScalar (b := b) (c := c) (n := n) (scalarBConst u) (scalarCPref (b := b) h) = 0 := by
  unfold qScalar qLeftScalar qRightScalar scalarBConst
  simp_rw [Cagg_scalarCPref_eq_of_odd (b := b) (n := n) hb hn h]
  calc
    (∑ t : I n, ∑ z : ZCoord c n, u z * prefixR h t (sumZ z)) +
        ∑ t : I n, ∑ z : ZCoord c n, u z * prefixR h (t - 1) (sumZ z + 1)
      = (∑ z : ZCoord c n, ∑ t : I n, u z * prefixR h t (sumZ z)) +
          ∑ z : ZCoord c n, ∑ t : I n, u z * prefixR h (t - 1) (sumZ z + 1) := by
            congr 1 <;> rw [Finset.sum_comm]
    _ = ∑ z : ZCoord c n,
          ((∑ t : I n, u z * prefixR h t (sumZ z)) +
            ∑ t : I n, u z * prefixR h (t - 1) (sumZ z + 1)) := by
            rw [← Finset.sum_add_distrib]
    _ = ∑ z : ZCoord c n,
          u z * (∑ t : I n, prefixR h t (sumZ z) + ∑ t : I n, prefixR h (t - 1) (sumZ z + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add]
    _ = ∑ z : ZCoord c n,
          u z * (∑ t : I n, prefixR h t (sumZ z) + ∑ t : I n, prefixR h t (sumZ z + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            congr 1
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (sum_reindex_addLeft (n := n) (a := (1 : I n))
                (f := fun t => prefixR h (t - 1) (sumZ z + 1))).symm
    _ = ∑ z : ZCoord c n,
          u z * ∑ t : I n, (prefixR h t (sumZ z) + prefixR h t (sumZ z + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [Finset.sum_add_distrib]
    _ = ∑ z : ZCoord c n, u z * ∑ t : I n, h t (sumZ z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          congr 1
          refine Finset.sum_congr rfl ?_
          intro t ht
          exact prefixR_pair_eq_of_mem_HAdmissible (n := n) hh t (sumZ z)
    _ = ∑ z : ZCoord c n, u z * colSum h (sumZ z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simp [colSum]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro z hz
          rw [colSum_eq_zero_of_mem_HAdmissible (n := n) hh (sumZ z)]
          simp

lemma qScalar_scalarBPref_scalarCConst_eq_zero_of_odd {b c n : ℕ} [NeZero n]
    (hc : 0 < c) (hn : Odd n) {h : HRaw n} (hh : h ∈ HAdmissible (n := n))
    (v : YCoord b n → F) :
    qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCConst v) = 0 := by
  unfold qScalar qLeftScalar qRightScalar scalarBPref
  simp_rw [Cagg_scalarCConst (b := b) (n := n) v]
  simp only [buildScalarB, Pi.zero_apply, zero_add]
  calc
    (∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * scalarYAgg v t) +
        ∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * scalarYAgg v (t - 1)
      = (∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * scalarYAgg v t) +
          ∑ t : I n, ∑ z : ZCoord c n, prefixT h (t + 1) (sumZ z) * scalarYAgg v t := by
            congr 1
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (sum_reindex_addLeft (n := n) (a := (1 : I n))
                (f := fun t => ∑ z : ZCoord c n, prefixT h t (sumZ z) * scalarYAgg v (t - 1))).symm
    _ = ∑ t : I n,
          ((∑ z : ZCoord c n, prefixT h t (sumZ z) * scalarYAgg v t) +
            ∑ z : ZCoord c n, prefixT h (t + 1) (sumZ z) * scalarYAgg v t) := by
            rw [← Finset.sum_add_distrib]
    _ = ∑ t : I n,
          ∑ z : ZCoord c n,
            (prefixT h t (sumZ z) + prefixT h (t + 1) (sumZ z)) * scalarYAgg v t := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [add_mul]
    _ = ∑ t : I n,
          (∑ z : ZCoord c n, (prefixT h t (sumZ z) + prefixT h (t + 1) (sumZ z))) * scalarYAgg v t := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [← Finset.sum_mul]
    _ = ∑ t : I n, rowSum h t * scalarYAgg v t := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          congr 1
          calc
            ∑ z : ZCoord c n, (prefixT h t (sumZ z) + prefixT h (t + 1) (sumZ z))
              = ∑ s : I n, (prefixT h t s + prefixT h (t + 1) s) := by
                  exact sum_sumZ_eq_of_odd (c := c) (n := n) hc hn
                    (fun s => prefixT h t s + prefixT h (t + 1) s)
            _ = ∑ s : I n, h t s := by
                  refine Finset.sum_congr rfl ?_
                  intro s hs
                  exact prefixT_pair_eq_of_mem_HAdmissible (n := n) hh t s
            _ = rowSum h t := by
                  simp [rowSum]
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro t ht
          rw [rowSum_eq_zero_of_mem_HAdmissible (n := n) hh t]
          simp

lemma qScalar_scalarBPref_scalarCPref_formula_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) {h : HRaw n} (hh : h ∈ HAdmissible (n := n)) :
    qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCPref (b := b) h) =
      ∑ t : I n, ∑ s : I n, h t s * (prefixT h t s + prefixR h t s + 1) := by
  let E : I n → I n → F := fun t s =>
    prefixT h t s * prefixR h t s +
      prefixT h (t + 1) s * prefixR h t (s + 1)
  have hcollapse_z :
      ∑ t : I n, ∑ z : ZCoord c n, E t (sumZ z) =
        ∑ t : I n, ∑ s : I n, E t s := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    simpa [E] using sum_sumZ_eq_of_odd (c := c) (n := n) hc hn (fun s => E t s)
  have hPt :
      ∀ t s : I n, prefixT h (t + 1) s = prefixT h t s + h t s := by
    intro t s
    have hp := prefixT_pair_eq_of_mem_HAdmissible (n := n) hh t s
    apply add_left_cancel (a := prefixT h t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hp
  have hQs :
      ∀ t s : I n, prefixR h t (s + 1) = prefixR h t s + h t s := by
    intro t s
    have hq := prefixR_pair_eq_of_mem_HAdmissible (n := n) hh t s
    apply add_left_cancel (a := prefixR h t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hq
  unfold qScalar qLeftScalar qRightScalar scalarBPref
  simp_rw [Cagg_scalarCPref_eq_of_odd (b := b) (n := n) hb hn h]
  simp only [buildScalarB, Pi.zero_apply, add_zero, zero_add]
  change
    (∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR h t (sumZ z)) +
      ∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR h (t - 1) (sumZ z + 1) =
        ∑ t : I n, ∑ s : I n, h t s * (prefixT h t s + prefixR h t s + 1)
  have hshift :
      ∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR h (t - 1) (sumZ z + 1)
        =
      ∑ t : I n, ∑ z : ZCoord c n, prefixT h (t + 1) (sumZ z) * prefixR h t (sumZ z + 1) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun t => ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR h (t - 1) (sumZ z + 1))).symm
  rw [hshift]
  calc
    (∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR h t (sumZ z)) +
        ∑ t : I n, ∑ z : ZCoord c n, prefixT h (t + 1) (sumZ z) * prefixR h t (sumZ z + 1)
      = ∑ t : I n, ∑ z : ZCoord c n, E t (sumZ z) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [← Finset.sum_add_distrib]
    _ = ∑ t : I n, ∑ s : I n, E t s := hcollapse_z
    _ = ∑ t : I n, ∑ s : I n, h t s * (prefixT h t s + prefixR h t s + 1) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          refine Finset.sum_congr rfl ?_
          intro s hs
          change
            prefixT h t s * prefixR h t s + prefixT h (t + 1) s * prefixR h t (s + 1) =
              h t s * (prefixT h t s + prefixR h t s + 1)
          rw [hPt t s, hQs t s]
          simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm, F_add_self]
          have hsqF : ∀ x : F, x * x = x := by
            intro x
            fin_cases x <;> decide
          have hsq : h t s * h t s = h t s := hsqF (h t s)
          rw [hsq, mul_comm (prefixT h t s) (h t s)]

lemma qScalar_scalarBPref_scalarCPref_formula_mixed_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) {h k : HRaw n}
    (hh : h ∈ HAdmissible (n := n)) (hk : k ∈ HAdmissible (n := n)) :
    qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCPref (b := b) k) =
      ∑ t : I n, ∑ s : I n,
        ((h t s * prefixR k t s) + (prefixT h t s * k t s) + (h t s * k t s)) := by
  let E : I n → I n → F := fun t s =>
    prefixT h t s * prefixR k t s +
      prefixT h (t + 1) s * prefixR k t (s + 1)
  have hcollapse_z :
      ∑ t : I n, ∑ z : ZCoord c n, E t (sumZ z) =
        ∑ t : I n, ∑ s : I n, E t s := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    simpa [E] using sum_sumZ_eq_of_odd (c := c) (n := n) hc hn (fun s => E t s)
  have hPt :
      ∀ t s : I n, prefixT h (t + 1) s = prefixT h t s + h t s := by
    intro t s
    have hp := prefixT_pair_eq_of_mem_HAdmissible (n := n) hh t s
    apply add_left_cancel (a := prefixT h t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hp
  have hQs :
      ∀ t s : I n, prefixR k t (s + 1) = prefixR k t s + k t s := by
    intro t s
    have hq := prefixR_pair_eq_of_mem_HAdmissible (n := n) hk t s
    apply add_left_cancel (a := prefixR k t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hq
  unfold qScalar qLeftScalar qRightScalar scalarBPref
  simp_rw [Cagg_scalarCPref_eq_of_odd (b := b) (n := n) hb hn k]
  simp only [buildScalarB, Pi.zero_apply, add_zero, zero_add]
  change
    (∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR k t (sumZ z)) +
      ∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR k (t - 1) (sumZ z + 1) =
        ∑ t : I n, ∑ s : I n,
          ((h t s * prefixR k t s) + (prefixT h t s * k t s) + (h t s * k t s))
  have hshift :
      ∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR k (t - 1) (sumZ z + 1)
        =
      ∑ t : I n, ∑ z : ZCoord c n, prefixT h (t + 1) (sumZ z) * prefixR k t (sumZ z + 1) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun t => ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR k (t - 1) (sumZ z + 1))).symm
  rw [hshift]
  calc
    (∑ t : I n, ∑ z : ZCoord c n, prefixT h t (sumZ z) * prefixR k t (sumZ z)) +
        ∑ t : I n, ∑ z : ZCoord c n, prefixT h (t + 1) (sumZ z) * prefixR k t (sumZ z + 1)
      = ∑ t : I n, ∑ z : ZCoord c n, E t (sumZ z) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [← Finset.sum_add_distrib]
    _ = ∑ t : I n, ∑ s : I n, E t s := hcollapse_z
    _ = ∑ t : I n, ∑ s : I n,
          ((h t s * prefixR k t s) + (prefixT h t s * k t s) + (h t s * k t s)) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          refine Finset.sum_congr rfl ?_
          intro s hs
          change
            prefixT h t s * prefixR k t s + prefixT h (t + 1) s * prefixR k t (s + 1) =
              (h t s * prefixR k t s) + (prefixT h t s * k t s) + (h t s * k t s)
          rw [hPt t s, hQs t s]
          simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm, F_add_self]

lemma qScalar_build_eq_four_terms {b c n : ℕ} [NeZero n]
    (h : HRaw n) (u : ZCoord c n → F) (v : YCoord b n → F) :
    qScalar (b := b) (c := c) (n := n) (buildScalarB h u) (buildScalarC h v) =
      qScalar (b := b) (c := c) (n := n) (scalarBConst u) (scalarCConst v) +
        qScalar (b := b) (c := c) (n := n) (scalarBConst u) (scalarCPref (b := b) h) +
        qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCConst v) +
        qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCPref (b := b) h) := by
  rw [buildScalarB_eq_scalarBConst_add_scalarBPref, buildScalarC_eq_scalarCConst_add_scalarCPref]
  rw [qScalar_add_left, qScalar_add_right, qScalar_add_right]
  ac_rfl

lemma qScalar_build_eq_three_terms {b c n : ℕ} [NeZero n]
    (h : HRaw n) (u : ZCoord c n → F) (v : YCoord b n → F) :
    qScalar (b := b) (c := c) (n := n) (buildScalarB h u) (buildScalarC h v) =
      qScalar (b := b) (c := c) (n := n) (scalarBConst u) (scalarCPref (b := b) h) +
        qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCConst v) +
        qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCPref (b := b) h) := by
  rw [qScalar_build_eq_four_terms (b := b) (c := c) (n := n) h u v]
  rw [qScalar_scalarBConst_scalarCConst_eq_zero (b := b) (c := c) (n := n)]
  simp [add_assoc, add_left_comm, add_comm]

lemma qScalar_build_eq_prefpref_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) {h : HRaw n} (hh : h ∈ HAdmissible (n := n))
    (u : ZCoord c n → F) (v : YCoord b n → F) :
    qScalar (b := b) (c := c) (n := n) (buildScalarB h u) (buildScalarC h v) =
      qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) h) (scalarCPref (b := b) h) := by
  rw [qScalar_build_eq_three_terms (b := b) (c := c) (n := n) h u v]
  rw [qScalar_scalarBConst_scalarCPref_eq_zero_of_odd (b := b) (c := c) (n := n) hb hn hh]
  rw [qScalar_scalarBPref_scalarCConst_eq_zero_of_odd (b := b) (c := c) (n := n) hc hn hh]
  simp

lemma qScalar_build_formula_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) {h : HRaw n} (hh : h ∈ HAdmissible (n := n))
    (u : ZCoord c n → F) (v : YCoord b n → F) :
    qScalar (b := b) (c := c) (n := n) (buildScalarB h u) (buildScalarC h v) =
      ∑ t : I n, ∑ s : I n, h t s * (prefixT h t s + prefixR h t s + 1) := by
  rw [qScalar_build_eq_prefpref_of_odd (b := b) (c := c) (n := n) hb hc hn hh u v]
  exact qScalar_scalarBPref_scalarCPref_formula_of_odd (b := b) (c := c) (n := n) hb hc hn hh

noncomputable def oddVisibleSign {b c n : ℕ} [NeZero n] (bc : ScalarVisibleCompat b c n) : ℤ :=
  bitSign (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef)

noncomputable def oddHSign {b c n : ℕ} [NeZero n] (h : HAdmissible n) : ℤ :=
  bitSign (qScalar (b := b) (c := c) (n := n)
    (scalarBPref (c := c) h.1) (scalarCPref (b := b) h.1))

lemma oddVisibleSign_fromHUV_eq_oddHSign_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (h : HAdmissible n) (u : ZCoord c n → F) (v : YCoord b n → F) :
    oddVisibleSign (b := b) (c := c) (n := n)
      (dataToScalarVisible (b := b) (c := c) (n := n) hb hc (h, u, v)) =
        oddHSign (b := b) (c := c) (n := n) h := by
  simpa [oddVisibleSign, oddHSign, dataToScalarVisible,
    build_mem_scalarVisibleCompat_of_mem_HAdmissible] using
      congrArg bitSign
        (qScalar_build_eq_prefpref_of_odd (b := b) (c := c) (n := n) hb hc hn h.2 u v)

lemma bitSign_eq_one_iff_eq_zero (x : F) : bitSign x = 1 ↔ x = 0 := by
  by_cases hx : x = 0
  · constructor
    · intro _
      exact hx
    · intro hx'
      subst hx'
      exact No13Migration.bitSign_zero
  · have hx1 : x = 1 := No13Migration.F2_ne_zero_eq_one x hx
    constructor
    · intro h
      subst hx1
      exfalso
      have h' : (-1 : ℤ) = 1 := by
        simpa [No13Migration.bitSign]
          using h
      norm_num at h'
    · intro hx'
      exact False.elim (hx hx')

theorem sum_oddVisible_eq_hAdmissible_sum_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    ∑ bc : ScalarVisibleCompat b c n, oddVisibleSign (b := b) (c := c) (n := n) bc =
      (2 : ℤ) ^ (n ^ b + n ^ c) *
        ∑ h : HAdmissible n, oddHSign (b := b) (c := c) (n := n) h := by
  let e := scalarVisibleEquiv (b := b) (c := c) (n := n) hb hc
  have hrew :
      ∑ bc : ScalarVisibleCompat b c n, oddVisibleSign (b := b) (c := c) (n := n) bc =
        ∑ z : HAdmissible n × (ZCoord c n → F) × (YCoord b n → F),
          oddVisibleSign (b := b) (c := c) (n := n) (e.symm z) := by
    calc
      ∑ bc : ScalarVisibleCompat b c n, oddVisibleSign (b := b) (c := c) (n := n) bc
        = ∑ bc : ScalarVisibleCompat b c n,
            oddVisibleSign (b := b) (c := c) (n := n) (e.symm (e bc)) := by
              refine Finset.sum_congr rfl ?_
              intro bc hbc
              simp [e]
      _ = ∑ z : HAdmissible n × (ZCoord c n → F) × (YCoord b n → F),
            oddVisibleSign (b := b) (c := c) (n := n) (e.symm z) := by
              simpa using
                (Equiv.sum_comp e
                  (fun z : HAdmissible n × (ZCoord c n → F) × (YCoord b n → F) =>
                    oddVisibleSign (b := b) (c := c) (n := n) (e.symm z)))
  rw [hrew]
  rw [Fintype.sum_prod_type_right]
  rw [Fintype.sum_prod_type_right]
  have hz :
      (Fintype.card (ZCoord c n → F) : ℤ) = (2 : ℤ) ^ (n ^ c) := by
    simpa [card_zFunctions (c := c) (n := n)] using
      congrArg (fun x : ℕ => (x : ℤ)) (card_zFunctions (c := c) (n := n))
  have hy :
      (Fintype.card (YCoord b n → F) : ℤ) = (2 : ℤ) ^ (n ^ b) := by
    simpa [card_yFunctions (b := b) (n := n)] using
      congrArg (fun x : ℕ => (x : ℤ)) (card_yFunctions (b := b) (n := n))
  have hsign :
      ∀ (v : YCoord b n → F) (u : ZCoord c n → F) (h : HAdmissible n),
        oddVisibleSign (b := b) (c := c) (n := n)
          (dataToScalarVisible (b := b) (c := c) (n := n) hb hc (h, u, v)) =
            oddHSign (b := b) (c := c) (n := n) h := by
    intro v u h
    exact oddVisibleSign_fromHUV_eq_oddHSign_of_odd (b := b) (c := c) (n := n) hb hc hn h u v
  calc
    ∑ v : YCoord b n → F, ∑ u : ZCoord c n → F, ∑ h : HAdmissible n,
        oddVisibleSign (b := b) (c := c) (n := n)
          (dataToScalarVisible (b := b) (c := c) (n := n) hb hc (h, u, v))
      = ∑ v : YCoord b n → F, ∑ u : ZCoord c n → F, ∑ h : HAdmissible n,
          oddHSign (b := b) (c := c) (n := n) h := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            refine Finset.sum_congr rfl ?_
            intro u hu
            refine Finset.sum_congr rfl ?_
            intro h hh
            exact hsign v u h
    _ = ∑ v : YCoord b n → F, ∑ u : ZCoord c n → F,
          (∑ h : HAdmissible n, oddHSign (b := b) (c := c) (n := n) h) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp
    _ = ∑ v : YCoord b n → F,
          (Fintype.card (ZCoord c n → F) : ℤ) *
            ∑ h : HAdmissible n, oddHSign (b := b) (c := c) (n := n) h := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp
    _ = (Fintype.card (YCoord b n → F) : ℤ) *
          ((Fintype.card (ZCoord c n → F) : ℤ) *
            ∑ h : HAdmissible n, oddHSign (b := b) (c := c) (n := n) h) := by
            simp
    _ = (2 : ℤ) ^ (n ^ b + n ^ c) *
          ∑ h : HAdmissible n, oddHSign (b := b) (c := c) (n := n) h := by
            let S : ℤ := ∑ h : HAdmissible n, oddHSign (b := b) (c := c) (n := n) h
            have hpow :
                (Fintype.card (YCoord b n → F) : ℤ) *
                    ((Fintype.card (ZCoord c n → F) : ℤ) * S)
                  =
                (2 : ℤ) ^ (n ^ b + n ^ c) * S := by
              rw [hy, hz, pow_add]
              ring
            simpa [S] using hpow

abbrev CoreIdx (n : ℕ) [NeZero n] := No13Migration.CoreIdx n

abbrev OddRectIndex (n : ℕ) [NeZero n] := CoreIdx n × CoreIdx n

def pointH {n : ℕ} (t0 s0 : I n) : HRaw n :=
  fun t s => if t = t0 ∧ s = s0 then 1 else 0

def rect {n : ℕ} (a b : I n) : HRaw n :=
  pointH 0 0 + pointH a 0 + pointH 0 b + pointH a b

lemma rect_apply_nonzero_nonzero {n : ℕ} [NeZero n] {a b t s : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) (hs : s ≠ 0) :
    rect a b t s = if t = a ∧ s = b then 1 else 0 := by
  unfold rect pointH
  by_cases hta : t = a
  · by_cases hsb : s = b
    · simp [ha, hb, ht, hs, hta, hsb]
    · simp [ha, hb, ht, hs, hta, hsb]
  · by_cases hsb : s = b
    · simp [ha, hb, ht, hs, hta, hsb]
    · simp [ha, hb, ht, hs, hta, hsb]

lemma rowSum_pointH {n : ℕ} [NeZero n] (t0 s0 : I n) :
    rowSum (pointH t0 s0) = basisProfile t0 := by
  funext t
  unfold rowSum pointH basisProfile
  by_cases ht : t = t0
  · subst ht
    rw [Finset.sum_eq_single s0]
    · simp
    · intro s _ hs
      simp [hs]
    · simp
  · have hzero : ∀ s : I n, (if t = t0 ∧ s = s0 then 1 else 0) = 0 := by
      intro s
      simp [ht]
    simp [hzero, ht]

lemma colSum_pointH {n : ℕ} [NeZero n] (t0 s0 : I n) :
    colSum (pointH t0 s0) = basisProfile s0 := by
  funext s
  unfold colSum pointH basisProfile
  by_cases hs : s = s0
  · subst hs
    rw [Finset.sum_eq_single t0]
    · simp
    · intro t _ ht
      simp [ht]
    · simp
  · have hzero : ∀ t : I n, (if t = t0 ∧ s = s0 then 1 else 0) = 0 := by
      intro t
      simp [hs]
    simp [hzero, hs]

lemma rect_mem_HAdmissible {n : ℕ} [NeZero n] (a b : I n) : rect a b ∈ HAdmissible (n := n) := by
  constructor
  · change rowSumMap (n := n) (rect a b) = 0
    unfold rect
    rw [map_add, map_add, map_add]
    rw [show rowSumMap (n := n) (pointH a b) = basisProfile a by simpa [rowSumMap] using rowSum_pointH a b]
    rw [show rowSumMap (n := n) (pointH a 0) = basisProfile a by simpa [rowSumMap] using rowSum_pointH a 0]
    rw [show rowSumMap (n := n) (pointH 0 b) = basisProfile 0 by simpa [rowSumMap] using rowSum_pointH 0 b]
    rw [show rowSumMap (n := n) (pointH 0 0) = basisProfile 0 by simpa [rowSumMap] using rowSum_pointH 0 0]
    funext t
    simp [basisProfile, F_add_self, add_assoc, add_left_comm, add_comm]
  · change colSumMap (n := n) (rect a b) = 0
    unfold rect
    rw [map_add, map_add, map_add]
    rw [show colSumMap (n := n) (pointH a b) = basisProfile b by simpa [colSumMap] using colSum_pointH a b]
    rw [show colSumMap (n := n) (pointH a 0) = basisProfile 0 by simpa [colSumMap] using colSum_pointH a 0]
    rw [show colSumMap (n := n) (pointH 0 b) = basisProfile b by simpa [colSumMap] using colSum_pointH 0 b]
    rw [show colSumMap (n := n) (pointH 0 0) = basisProfile 0 by simpa [colSumMap] using colSum_pointH 0 0]
    funext s
    simp [basisProfile, F_add_self, add_assoc, add_left_comm, add_comm]

noncomputable def toRefHRaw {n : ℕ} [NeZero n] (h : HRaw n) : No13Migration.HRaw n :=
  fun p => h (p 0) (p 1)

noncomputable def ofRefHRaw {n : ℕ} [NeZero n] (h : No13Migration.HRaw n) : HRaw n :=
  fun t s => h (No13Migration.vec2 t s)

noncomputable def toRefHAdmissible {n : ℕ} [NeZero n] (h : HAdmissible (n := n)) :
    No13Migration.HAdmissible n := by
  refine ⟨toRefHRaw h.1, ?_⟩
  constructor
  · intro t
    simpa [toRefHRaw, colSum, No13Migration.rowSum, No13Migration.vec2] using
      colSum_eq_zero_of_mem_HAdmissible (n := n) h.2 t
  · intro s
    simpa [toRefHRaw, rowSum, No13Migration.colSum, No13Migration.vec2] using
      rowSum_eq_zero_of_mem_HAdmissible (n := n) h.2 s

noncomputable def oddHOfCore {n : ℕ} [NeZero n] (g : CoreIdx n → CoreIdx n → F) : HRaw n :=
  ofRefHRaw (No13Migration.hOfCore g)

lemma oddHOfCore_mem_HAdmissible {n : ℕ} [NeZero n] (g : CoreIdx n → CoreIdx n → F) :
    oddHOfCore g ∈ HAdmissible (n := n) := by
  constructor
  · change rowSum (oddHOfCore g) = 0
    funext t
    simpa [oddHOfCore, ofRefHRaw, rowSum, No13Migration.colSum, No13Migration.vec2] using
      (No13Migration.hOfCore_admissible (n := n) g).2 t
  · change colSum (oddHOfCore g) = 0
    funext s
    simpa [oddHOfCore, ofRefHRaw, colSum, No13Migration.rowSum, No13Migration.vec2] using
      (No13Migration.hOfCore_admissible (n := n) g).1 s

def oddCoreOfH {n : ℕ} [NeZero n] (h : HAdmissible (n := n)) :
    CoreIdx n → CoreIdx n → F :=
  fun s t => h.1 s.1 t.1

lemma oddCoreOfH_oddHOfCore {n : ℕ} [NeZero n] (g : CoreIdx n → CoreIdx n → F) :
    oddCoreOfH (n := n) ⟨oddHOfCore g, oddHOfCore_mem_HAdmissible (n := n) g⟩ = g := by
  funext s t
  simpa [oddCoreOfH, oddHOfCore, ofRefHRaw, No13Migration.vec2] using
    No13Migration.hOfCore_at_st (n := n) g s t

lemma oddHOfCore_oddCoreOfH {n : ℕ} [NeZero n] (h : HAdmissible (n := n)) :
    oddHOfCore (oddCoreOfH (n := n) h) = h.1 := by
  funext t s
  have hcore :=
    congrArg (fun f : No13Migration.HRaw n => f (No13Migration.vec2 t s))
      (No13Migration.hOfCore_coreOfH (n := n) (toRefHAdmissible (n := n) h))
  simpa [oddHOfCore, oddCoreOfH, toRefHRaw, ofRefHRaw, No13Migration.coreOfH] using hcore

def coreSingle {n : ℕ} [NeZero n] (i : OddRectIndex n) : CoreIdx n → CoreIdx n → F :=
  fun s t => if (s, t) = i then 1 else 0

noncomputable def oddRectVec {n : ℕ} [NeZero n] (i : OddRectIndex n) : HAdmissible (n := n) :=
  ⟨oddHOfCore (coreSingle i), oddHOfCore_mem_HAdmissible (n := n) (coreSingle i)⟩

lemma oddCoreOfH_oddRectVec {n : ℕ} [NeZero n] (i j : OddRectIndex n) :
    oddCoreOfH (n := n) (oddRectVec (n := n) j) i.1 i.2 = if i = j then 1 else 0 := by
  have h :=
    congrFun
      (congrFun (oddCoreOfH_oddHOfCore (n := n) (g := coreSingle j)) i.1) i.2
  simpa [coreSingle] using h

lemma oddCoreOfH_rect {n : ℕ} [NeZero n] (a b s t : CoreIdx n) :
    oddCoreOfH (n := n) ⟨rect a.1 b.1, rect_mem_HAdmissible (n := n) a.1 b.1⟩ s t =
      if (s, t) = (a, b) then 1 else 0 := by
  change rect a.1 b.1 s.1 t.1 = if (s, t) = (a, b) then 1 else 0
  rw [rect_apply_nonzero_nonzero (a := a.1) (b := b.1) (t := s.1) (s := t.1) a.2 b.2 s.2 t.2]
  have hp : (s.1 = a.1 ∧ t.1 = b.1) ↔ (s, t) = (a, b) := by
    constructor
    · rintro ⟨hs, ht⟩
      have hs' : s = a := Subtype.ext hs
      have ht' : t = b := Subtype.ext ht
      cases hs'
      cases ht'
      rfl
    · intro h
      cases h
      simp
  simp [hp]

def oddRectSupport {n : ℕ} [NeZero n] (h : HAdmissible (n := n)) : Finset (OddRectIndex n) :=
  Finset.univ.filter (fun i => oddCoreOfH (n := n) h i.1 i.2 = 1)

@[simp] lemma oddRectSupport_oddRectVec {n : ℕ} [NeZero n] (i : OddRectIndex n) :
    oddRectSupport (n := n) (oddRectVec (n := n) i) = {i} := by
  ext j
  simp [oddRectSupport, oddCoreOfH_oddRectVec, eq_comm]

noncomputable def oddCoreLinearMap {n : ℕ} [NeZero n] :
    HAdmissible n →ₗ[F] (CoreIdx n → CoreIdx n → F) where
  toFun := oddCoreOfH (n := n)
  map_add' := by
    intro h k
    funext s t
    rfl
  map_smul' := by
    intro a h
    funext s t
    rfl

noncomputable def oddCoreLinearEquiv {n : ℕ} [NeZero n] :
    HAdmissible n ≃ₗ[F] (CoreIdx n → CoreIdx n → F) :=
  LinearEquiv.ofBijective (oddCoreLinearMap (n := n)) <| by
    constructor
    · intro h k hk
      apply Subtype.ext
      calc
        h.1 = oddHOfCore (oddCoreOfH (n := n) h) := by
          symm
          exact oddHOfCore_oddCoreOfH (n := n) h
        _ = oddHOfCore (oddCoreOfH (n := n) k) := by
          simpa using congrArg (oddHOfCore (n := n)) hk
        _ = k.1 := oddHOfCore_oddCoreOfH (n := n) k
    · intro g
      refine ⟨⟨oddHOfCore g, oddHOfCore_mem_HAdmissible (n := n) g⟩, ?_⟩
      exact oddCoreOfH_oddHOfCore (n := n) g

lemma oddRectVec_eq_rect_hAdmissible {n : ℕ} [NeZero n] (a b : CoreIdx n) :
    oddRectVec (n := n) (a, b) = ⟨rect a.1 b.1, rect_mem_HAdmissible (n := n) a.1 b.1⟩ := by
  apply (oddCoreLinearEquiv (n := n)).injective
  funext s t
  calc
    oddCoreOfH (n := n) (oddRectVec (n := n) (a, b)) s t
      = if (s, t) = (a, b) then 1 else 0 := by
          simpa using oddCoreOfH_oddRectVec (n := n) (i := (s, t)) (j := (a, b))
    _ = oddCoreOfH (n := n) ⟨rect a.1 b.1, rect_mem_HAdmissible (n := n) a.1 b.1⟩ s t := by
          symm
          exact oddCoreOfH_rect (n := n) a b s t

lemma oddRectVec_val_eq_rect {n : ℕ} [NeZero n] (a b : CoreIdx n) :
    (oddRectVec (n := n) (a, b)).1 = rect a.1 b.1 := by
  simpa using congrArg Subtype.val (oddRectVec_eq_rect_hAdmissible (n := n) a b)

lemma rect_row_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (ht0 : t ≠ 0) (hta : t ≠ a) :
    rect a b t s = 0 := by
  unfold rect pointH
  by_cases hs0 : s = 0 <;> by_cases hsb : s = b <;>
    simp [ht0, hta, hs0, hsb]

lemma rect_row_zero_eq {n : ℕ} [NeZero n] {a b s : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b 0 s = if s = 0 then 1 else if s = b then 1 else 0 := by
  unfold rect pointH
  by_cases hs0 : s = 0
  · subst hs0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
    simp [pointH, h0a, h0b, ha]
  · by_cases hsb : s = b
    · subst hsb
      have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
      simp [pointH, h0a, hb]
    · simp [hs0, hsb, ha, hb]

lemma rect_row_a_eq {n : ℕ} [NeZero n] {a b s : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b a s = if s = 0 then 1 else if s = b then 1 else 0 := by
  unfold rect pointH
  by_cases hs0 : s = 0
  · subst hs0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
    simpa [pointH, h0a, h0b, ha, hb]
  · by_cases hsb : s = b
    · subst hsb
      simp [pointH, ha, hb]
    · simp [hs0, hsb, ha, hb]

lemma rect_col_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (hs0 : s ≠ 0) (hsb : s ≠ b) :
    rect a b t s = 0 := by
  unfold rect pointH
  by_cases ht0 : t = 0 <;> by_cases hta : t = a <;>
    simp [hs0, hsb, ht0, hta]

lemma rect_col_zero_eq {n : ℕ} [NeZero n] {a b t : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b t 0 = if t = 0 then 1 else if t = a then 1 else 0 := by
  unfold rect pointH
  by_cases ht0 : t = 0
  · subst ht0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
    simp [pointH, h0a, h0b, ha]
  · by_cases hta : t = a
    · subst hta
      have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
      simp [pointH, ha, h0b]
    · simp [ht0, hta, ha, hb]

lemma rect_col_b_eq {n : ℕ} [NeZero n] {a b t : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b t b = if t = 0 then 1 else if t = a then 1 else 0 := by
  unfold rect pointH
  by_cases ht0 : t = 0
  · subst ht0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    simp [pointH, h0a, ha, hb]
  · by_cases hta : t = a
    · subst hta
      have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
      simp [pointH, h0b, ha, hb]
    · simp [ht0, hta, ha, hb]

lemma prefixT_rect_a_zero_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) a 0 = 1 := by
  unfold prefixT
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_zero_eq (a := a) (b := b) ha hb, hb]
  · intro i hi hi0
    have hit0 : ((i : ℕ) : I n) ≠ 0 := by
      have hi_lt : i < n := Nat.lt_trans (Finset.mem_range.mp hi) (ZMod.val_lt a)
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt hi_lt
      intro h
      have : i = 0 := by
        simpa [hiv] using congrArg ZMod.val h
      exact hi0 this
    have hita : ((i : ℕ) : I n) ≠ a := by
      intro hia
      have hi_lt : i < a.val := Finset.mem_range.mp hi
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt a))
      have hav : a.val = i := by
        rw [← hiv]
        exact congrArg ZMod.val hia.symm
      have : ¬ i < a.val := by omega
      exact this (by simpa [hav] using hi_lt)
    simp [rect_row_other_eq_zero (s := (0 : I n)) hit0 hita]
  · have : a ≠ 0 := ha
    simp [this]

lemma prefixR_rect_zero_b_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) 0 b = 1 := by
  unfold prefixR
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_zero_eq (a := a) (b := b) ha hb]
  · intro j hj hj0
    have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
      have hj_lt : j < n := Nat.lt_trans (Finset.mem_range.mp hj) (ZMod.val_lt b)
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt hj_lt
      intro h
      have : j = 0 := by
        simpa [hjv] using congrArg ZMod.val h
      exact hj0 this
    have hjsb : ((j : ℕ) : I n) ≠ b := by
      intro hjb
      have hj_lt : j < b.val := Finset.mem_range.mp hj
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt b))
      have hbv : b.val = j := by
        rw [← hjv]
        exact congrArg ZMod.val hjb.symm
      have : ¬ j < b.val := by omega
      exact this (by simpa [hbv] using hj_lt)
    simp [rect_row_zero_eq (a := a) (b := b) ha hb, hjs0, hjsb]
  · simp [hb]

lemma prefixT_rect_a_b_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) a b = 1 := by
  unfold prefixT
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_zero_eq (a := a) (b := b) ha hb, hb]
  · intro i hi hi0
    have hit0 : ((i : ℕ) : I n) ≠ 0 := by
      have hi_lt : i < n := Nat.lt_trans (Finset.mem_range.mp hi) (ZMod.val_lt a)
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt hi_lt
      intro h
      have : i = 0 := by
        simpa [hiv] using congrArg ZMod.val h
      exact hi0 this
    have hita : ((i : ℕ) : I n) ≠ a := by
      intro hia
      have hi_lt : i < a.val := Finset.mem_range.mp hi
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt a))
      have hav : a.val = i := by
        rw [← hiv]
        exact congrArg ZMod.val hia.symm
      have : ¬ i < a.val := by omega
      exact this (by simpa [hav] using hi_lt)
    simp [rect_row_other_eq_zero (s := b) hit0 hita]
  · simp [ha]

lemma prefixT_rect_t_zero_eq_indicator {n : ℕ} [NeZero n] {a b t : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) t 0 = if t = 0 then 0 else if t.val ≤ a.val then 1 else 0 := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [prefixT_zero]
  · unfold prefixT
    by_cases hta : t.val ≤ a.val
    · have htpos : 0 < t.val := Nat.pos_of_ne_zero (by
          intro h
          have htzero : ((t.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val t)
          have htz : t = 0 := by
            simpa using ((ZMod.natCast_zmod_val t).symm.trans htzero)
          exact ht0 htz)
      rw [Finset.sum_eq_single 0]
      · simp [rect_row_zero_eq (a := a) (b := b) ha hb, ht0, hta]
      · intro i hi hi0
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hi_lt : i < t.val := Finset.mem_range.mp hi
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_lt_t : i < t.val := Finset.mem_range.mp hi
          have hi_lt_a : i < a.val := lt_of_lt_of_le hi_lt_t hta
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          have : ¬ i < a.val := by omega
          exact this (by simpa [hav] using hi_lt_a)
        simp [rect_row_other_eq_zero (s := (0 : I n)) hit0 hita]
      · simp [htpos]
    · have hat : a.val < t.val := lt_of_not_ge hta
      have h0mem : (0 : ℕ) ∈ Finset.range t.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hat)
      have ha0 : a.val ≠ 0 := by
        intro hav
        have hazero : ((a.val : ℕ) : I n) = 0 := by
          simpa [hav] using (ZMod.natCast_zmod_val a)
        have hza : a = 0 := by
          simpa using ((ZMod.natCast_zmod_val a).symm.trans hazero)
        exact ha hza
      have hamem : a.val ∈ (Finset.range t.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact ha0
        · exact Finset.mem_range.mpr hat
      have hrest :
          Finset.sum (((Finset.range t.val).erase 0).erase a.val)
            (fun i => rect a b (i : I n) 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hi0 : i ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).1
        have hi_lt_t : i < t.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).2)
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita' : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_ne_a : i ≠ a.val := by simpa using (Finset.mem_erase.mp hi).1
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          exact hi_ne_a hav.symm
        simp [rect_row_other_eq_zero (s := (0 : I n)) hit0 hita']
      have hsum0 := (Finset.sum_erase_add (Finset.range t.val) (fun i => rect a b (i : I n) 0) h0mem).symm
      have hsuma := (Finset.sum_erase_add ((Finset.range t.val).erase 0) (fun i => rect a b (i : I n) 0) hamem).symm
      rw [hsum0, hsuma]
      have ha_lt_n : a.val < n := ZMod.val_lt a
      simp [hrest, rect_row_a_eq (a := a) (b := b) ha hb, rect_row_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt ha_lt_n, ha, hb, ht0, hat, add_assoc, F_add_self]

lemma prefixT_rect_t_b_eq_indicator {n : ℕ} [NeZero n] {a b t : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) t b = if t = 0 then 0 else if t.val ≤ a.val then 1 else 0 := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [prefixT_zero]
  · unfold prefixT
    by_cases hta : t.val ≤ a.val
    · have htpos : 0 < t.val := Nat.pos_of_ne_zero (by
          intro h
          have htzero : ((t.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val t)
          have htz : t = 0 := by
            simpa using ((ZMod.natCast_zmod_val t).symm.trans htzero)
          exact ht0 htz)
      rw [Finset.sum_eq_single 0]
      · simp [rect_row_zero_eq (a := a) (b := b) ha hb, ht0, hta]
      · intro i hi hi0
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hi_lt : i < t.val := Finset.mem_range.mp hi
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_lt_t : i < t.val := Finset.mem_range.mp hi
          have hi_lt_a : i < a.val := lt_of_lt_of_le hi_lt_t hta
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          have : ¬ i < a.val := by omega
          exact this (by simpa [hav] using hi_lt_a)
        simp [rect_row_other_eq_zero (s := b) hit0 hita]
      · simp [htpos]
    · have hat : a.val < t.val := lt_of_not_ge hta
      have h0mem : (0 : ℕ) ∈ Finset.range t.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hat)
      have ha0 : a.val ≠ 0 := by
        intro hav
        have hazero : ((a.val : ℕ) : I n) = 0 := by
          simpa [hav] using (ZMod.natCast_zmod_val a)
        have hza : a = 0 := by
          simpa using ((ZMod.natCast_zmod_val a).symm.trans hazero)
        exact ha hza
      have hamem : a.val ∈ (Finset.range t.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact ha0
        · exact Finset.mem_range.mpr hat
      have hrest :
          Finset.sum (((Finset.range t.val).erase 0).erase a.val)
            (fun i => rect a b (i : I n) b) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hi0 : i ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).1
        have hi_lt_t : i < t.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).2)
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita' : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_ne_a : i ≠ a.val := by simpa using (Finset.mem_erase.mp hi).1
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          exact hi_ne_a hav.symm
        simp [rect_row_other_eq_zero (s := b) hit0 hita']
      have hsum0 := (Finset.sum_erase_add (Finset.range t.val) (fun i => rect a b (i : I n) b) h0mem).symm
      have hsuma := (Finset.sum_erase_add ((Finset.range t.val).erase 0) (fun i => rect a b (i : I n) b) hamem).symm
      rw [hsum0, hsuma]
      have ha_lt_n : a.val < n := ZMod.val_lt a
      simp [hrest, rect_row_a_eq (a := a) (b := b) ha hb, rect_row_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt ha_lt_n, ha, hb, ht0, hat, add_assoc, F_add_self]

lemma prefixR_rect_a_b_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) a b = 1 := by
  unfold prefixR
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_a_eq (a := a) ha hb, hb]
  · intro j hj hj0
    have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
      have hj_lt : j < n := Nat.lt_trans (Finset.mem_range.mp hj) (ZMod.val_lt b)
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt hj_lt
      intro h
      have : j = 0 := by
        simpa [hjv] using congrArg ZMod.val h
      exact hj0 this
    have hjsb : ((j : ℕ) : I n) ≠ b := by
      intro hjb
      have hj_lt : j < b.val := Finset.mem_range.mp hj
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt b))
      have hbv : b.val = j := by
        rw [← hjv]
        exact congrArg ZMod.val hjb.symm
      have : ¬ j < b.val := by omega
      exact this (by simpa [hbv] using hj_lt)
    simp [rect_row_a_eq (a := a) ha hb, hjs0, hjsb]
  · simp [hb]

lemma prefixR_rect_zero_s_eq_indicator {n : ℕ} [NeZero n] {a b s : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) 0 s = if s = 0 then 0 else if s.val ≤ b.val then 1 else 0 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [prefixR_zero]
  · unfold prefixR
    by_cases hsb : s.val ≤ b.val
    · have hspos : 0 < s.val := Nat.pos_of_ne_zero (by
          intro h
          have hszero : ((s.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val s)
          have hzs : s = 0 := by
            simpa using ((ZMod.natCast_zmod_val s).symm.trans hszero)
          exact hs0 hzs)
      rw [Finset.sum_eq_single 0]
      · simp [rect_col_zero_eq (a := a) (b := b) ha hb, hs0, hsb]
      · intro j hj hj0
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hj_lt : j < s.val := Finset.mem_range.mp hj
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_lt_s : j < s.val := Finset.mem_range.mp hj
          have hj_lt_b : j < b.val := lt_of_lt_of_le hj_lt_s hsb
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          have : ¬ j < b.val := by omega
          exact this (by simpa [hbv] using hj_lt_b)
        simp [rect_col_other_eq_zero (t := (0 : I n)) hjs0 hjsb]
      · simp [hspos]
    · have hbs : b.val < s.val := lt_of_not_ge hsb
      have h0mem : (0 : ℕ) ∈ Finset.range s.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hbs)
      have hb0 : b.val ≠ 0 := by
        intro hbv
        have hbzero : ((b.val : ℕ) : I n) = 0 := by
          simpa [hbv] using (ZMod.natCast_zmod_val b)
        have hzb : b = 0 := by
          simpa using ((ZMod.natCast_zmod_val b).symm.trans hbzero)
        exact hb hzb
      have hbmem : b.val ∈ (Finset.range s.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact hb0
        · exact Finset.mem_range.mpr hbs
      have hrest :
          Finset.sum (((Finset.range s.val).erase 0).erase b.val)
            (fun j => rect a b 0 (j : I n)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hj0 : j ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).1
        have hj_lt_s : j < s.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).2)
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb' : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_ne_b : j ≠ b.val := by simpa using (Finset.mem_erase.mp hj).1
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          exact hj_ne_b hbv.symm
        simp [rect_col_other_eq_zero (t := (0 : I n)) hjs0 hjsb']
      have hsum0 := (Finset.sum_erase_add (Finset.range s.val) (fun j => rect a b 0 (j : I n)) h0mem).symm
      have hsumb := (Finset.sum_erase_add ((Finset.range s.val).erase 0) (fun j => rect a b 0 (j : I n)) hbmem).symm
      rw [hsum0, hsumb]
      have hb_lt_n : b.val < n := ZMod.val_lt b
      simp [hrest, rect_col_b_eq (a := a) (b := b) ha hb, rect_col_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt hb_lt_n, ha, hb, hs0, hbs, add_assoc, F_add_self]

lemma prefixR_rect_a_s_eq_indicator {n : ℕ} [NeZero n] {a b s : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) a s = if s = 0 then 0 else if s.val ≤ b.val then 1 else 0 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [prefixR_zero]
  · unfold prefixR
    by_cases hsb : s.val ≤ b.val
    · have hspos : 0 < s.val := Nat.pos_of_ne_zero (by
          intro h
          have hszero : ((s.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val s)
          have hzs : s = 0 := by
            simpa using ((ZMod.natCast_zmod_val s).symm.trans hszero)
          exact hs0 hzs)
      rw [Finset.sum_eq_single 0]
      · simp [rect_col_zero_eq (a := a) (b := b) ha hb, hs0, hsb]
      · intro j hj hj0
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hj_lt : j < s.val := Finset.mem_range.mp hj
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_lt_s : j < s.val := Finset.mem_range.mp hj
          have hj_lt_b : j < b.val := lt_of_lt_of_le hj_lt_s hsb
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          have : ¬ j < b.val := by omega
          exact this (by simpa [hbv] using hj_lt_b)
        simp [rect_col_other_eq_zero (t := a) hjs0 hjsb]
      · simp [hspos]
    · have hbs : b.val < s.val := lt_of_not_ge hsb
      have h0mem : (0 : ℕ) ∈ Finset.range s.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hbs)
      have hb0 : b.val ≠ 0 := by
        intro hbv
        have hbzero : ((b.val : ℕ) : I n) = 0 := by
          simpa [hbv] using (ZMod.natCast_zmod_val b)
        have hzb : b = 0 := by
          simpa using ((ZMod.natCast_zmod_val b).symm.trans hbzero)
        exact hb hzb
      have hbmem : b.val ∈ (Finset.range s.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact hb0
        · exact Finset.mem_range.mpr hbs
      have hrest :
          Finset.sum (((Finset.range s.val).erase 0).erase b.val)
            (fun j => rect a b a (j : I n)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hj0 : j ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).1
        have hj_lt_s : j < s.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).2)
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb' : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_ne_b : j ≠ b.val := by simpa using (Finset.mem_erase.mp hj).1
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          exact hj_ne_b hbv.symm
        simp [rect_col_other_eq_zero (t := a) hjs0 hjsb']
      have hsum0 := (Finset.sum_erase_add (Finset.range s.val) (fun j => rect a b a (j : I n)) h0mem).symm
      have hsumb := (Finset.sum_erase_add ((Finset.range s.val).erase 0) (fun j => rect a b a (j : I n)) hbmem).symm
      rw [hsum0, hsumb]
      have hb_lt_n : b.val < n := ZMod.val_lt b
      simp [hrest, rect_col_b_eq (a := a) (b := b) ha hb, rect_col_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt hb_lt_n, ha, hb, hs0, hbs, add_assoc, F_add_self]

lemma prefixR_rect_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (ht0 : t ≠ 0) (hta : t ≠ a) :
    prefixR (rect a b) t s = 0 := by
  unfold prefixR
  refine Finset.sum_eq_zero ?_
  intro j hj
  simp [rect_row_other_eq_zero (s := ((j : ℕ) : I n)) ht0 hta]

lemma prefixT_rect_t_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (hs0 : s ≠ 0) (hsb : s ≠ b) :
    prefixT (rect a b) t s = 0 := by
  unfold prefixT
  refine Finset.sum_eq_zero ?_
  intro i hi
  simp [rect_col_other_eq_zero (t := ((i : ℕ) : I n)) hs0 hsb]

lemma sum_rect_row_zero_mul_eq {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (g : I n → F) :
    ∑ s : I n, rect a b 0 s * g s = g 0 + g b := by
  have h0mem : (0 : I n) ∈ Finset.univ := by simp
  have hbmem : b ∈ Finset.univ.erase (0 : I n) := by simp [hb]
  have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun x => rect a b 0 x * g x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hsin : s ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp hs).2
    have hs0 : s ≠ 0 := by simpa using (Finset.mem_erase.mp hsin).1
    have hsb : s ≠ b := by simpa using (Finset.mem_erase.mp hs).1
    simp [rect_row_zero_eq (a := a) (b := b) ha hb, hs0, hsb]
  calc
    ∑ s : I n, rect a b 0 s * g s
        = Finset.sum (Finset.univ.erase (0 : I n)) (fun s => rect a b 0 s * g s) +
            rect a b 0 0 * g 0 := by
              simpa using (Finset.sum_erase_add Finset.univ (fun s => rect a b 0 s * g s) h0mem).symm
    _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun s => rect a b 0 s * g s) +
          rect a b 0 b * g b) + rect a b 0 0 * g 0 := by
            simpa [add_assoc] using congrArg (fun x => x + rect a b 0 0 * g 0)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun s => rect a b 0 s * g s) hbmem).symm)
    _ = 0 + rect a b 0 b * g b + rect a b 0 0 * g 0 := by simp [hrest]
    _ = g 0 + g b := by
          simp [rect_row_zero_eq (a := a) (b := b) ha hb, hb, add_assoc, add_left_comm, add_comm]

lemma sum_rect_row_a_mul_eq {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (g : I n → F) :
    ∑ s : I n, rect a b a s * g s = g 0 + g b := by
  have h0mem : (0 : I n) ∈ Finset.univ := by simp
  have hbmem : b ∈ Finset.univ.erase (0 : I n) := by simp [hb]
  have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun x => rect a b a x * g x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hsin : s ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp hs).2
    have hs0 : s ≠ 0 := by simpa using (Finset.mem_erase.mp hsin).1
    have hsb : s ≠ b := by simpa using (Finset.mem_erase.mp hs).1
    simp [rect_row_a_eq (a := a) ha hb, hs0, hsb]
  calc
    ∑ s : I n, rect a b a s * g s
        = Finset.sum (Finset.univ.erase (0 : I n)) (fun s => rect a b a s * g s) +
            rect a b a 0 * g 0 := by
              simpa using (Finset.sum_erase_add Finset.univ (fun s => rect a b a s * g s) h0mem).symm
    _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun s => rect a b a s * g s) +
          rect a b a b * g b) + rect a b a 0 * g 0 := by
            simpa [add_assoc] using congrArg (fun x => x + rect a b a 0 * g 0)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun s => rect a b a s * g s) hbmem).symm)
    _ = 0 + rect a b a b * g b + rect a b a 0 * g 0 := by simp [hrest]
    _ = g 0 + g b := by
          simp [rect_row_a_eq (a := a) ha hb, hb, add_assoc, add_left_comm, add_comm]

lemma sum_rect_row_other_mul_eq_zero {n : ℕ} [NeZero n] {a b t : I n}
    (ht0 : t ≠ 0) (hta : t ≠ a) (g : I n → F) :
    ∑ s : I n, rect a b t s * g s = 0 := by
  refine Finset.sum_eq_zero ?_
  intro s hs
  simp [rect_row_other_eq_zero (s := s) ht0 hta]

lemma sum_rect_mul_eq_corners {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (g : I n → I n → F) :
    ∑ t : I n, ∑ s : I n, rect a b t s * g t s = g 0 0 + g 0 b + g a 0 + g a b := by
  have h0mem : (0 : I n) ∈ Finset.univ := by simp
  have hamem : a ∈ Finset.univ.erase (0 : I n) := by simp [ha]
  have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase a) (fun x => ∑ s : I n, rect a b x s * g x s) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have htin : t ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp ht).2
    have ht0 : t ≠ 0 := by simpa using (Finset.mem_erase.mp htin).1
    have hta : t ≠ a := by simpa using (Finset.mem_erase.mp ht).1
    simp [sum_rect_row_other_mul_eq_zero (a := a) (b := b) ht0 hta (g := fun s => g t s)]
  calc
    ∑ t : I n, ∑ s : I n, rect a b t s * g t s
        = Finset.sum (Finset.univ.erase (0 : I n)) (fun t => ∑ s : I n, rect a b t s * g t s) +
            ∑ s : I n, rect a b 0 s * g 0 s := by
              simpa using (Finset.sum_erase_add Finset.univ (fun t => ∑ s : I n, rect a b t s * g t s) h0mem).symm
    _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase a) (fun t => ∑ s : I n, rect a b t s * g t s) +
          ∑ s : I n, rect a b a s * g a s) + ∑ s : I n, rect a b 0 s * g 0 s := by
            simpa [add_assoc] using congrArg (fun x => x + ∑ s : I n, rect a b 0 s * g 0 s)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun t => ∑ s : I n, rect a b t s * g t s) hamem).symm)
    _ = 0 + (∑ s : I n, rect a b a s * g a s) + (∑ s : I n, rect a b 0 s * g 0 s) := by simp [hrest]
    _ = g 0 0 + g 0 b + (g a 0 + g a b) := by
          rw [sum_rect_row_a_mul_eq (a := a) (b := b) ha hb (g := fun s => g a s)]
          rw [sum_rect_row_zero_mul_eq (a := a) (b := b) ha hb (g := fun s => g 0 s)]
          simp [add_assoc, add_left_comm, add_comm]
    _ = g 0 0 + g 0 b + g a 0 + g a b := by
          ac_rfl

lemma sum_rect_mul_prefixR_rect_eq {n : ℕ} [NeZero n]
    {a b c d : I n} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∑ t : I n, ∑ s : I n, rect a b t s * prefixR (rect c d) t s =
      (if b.val ≤ d.val then 1 else 0) + (if a = c then (if b.val ≤ d.val then 1 else 0) else 0) := by
  rw [sum_rect_mul_eq_corners (a := a) (b := b) ha hb (g := fun t s => prefixR (rect c d) t s)]
  by_cases hac : a = c
  · subst hac
    simp [prefixR_zero, prefixR_rect_zero_s_eq_indicator (a := a) (b := d) hc hd,
      prefixR_rect_a_s_eq_indicator (a := a) (b := d) hc hd, hb]
  · have ha0 : a ≠ 0 := ha
    have hother : prefixR (rect c d) a b = 0 := prefixR_rect_other_eq_zero (a := c) (b := d) ha0 hac
    simp [prefixR_zero, prefixR_rect_zero_s_eq_indicator (a := c) (b := d) hc hd, hb, hac, hother]

lemma sum_prefixT_rect_mul_rect_eq {n : ℕ} [NeZero n]
    {a b c d : I n} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∑ t : I n, ∑ s : I n, prefixT (rect a b) t s * rect c d t s =
      (if c.val ≤ a.val then 1 else 0) + (if b = d then (if c.val ≤ a.val then 1 else 0) else 0) := by
  have hsum :
      ∑ t : I n, ∑ s : I n, prefixT (rect a b) t s * rect c d t s =
        prefixT (rect a b) 0 0 + prefixT (rect a b) 0 d + prefixT (rect a b) c 0 + prefixT (rect a b) c d := by
    simpa [mul_comm] using
      (sum_rect_mul_eq_corners (a := c) (b := d) hc hd (g := fun t s => prefixT (rect a b) t s))
  rw [hsum]
  by_cases hbd : b = d
  · subst hbd
    simp [prefixT_zero, prefixT_rect_t_zero_eq_indicator (a := a) (b := b) ha hb,
      prefixT_rect_t_b_eq_indicator (a := a) (b := b) ha hb, hc]
  · have hd0 : d ≠ 0 := hd
    have hdb : d ≠ b := by simpa [eq_comm] using hbd
    have hother : prefixT (rect a b) c d = 0 := prefixT_rect_t_other_eq_zero (a := a) (b := b) hd0 hdb
    simp [prefixT_zero, prefixT_rect_t_zero_eq_indicator (a := a) (b := b) ha hb, hc, hbd, hother]

lemma sum_rect_mul_rect_eq_indicator {n : ℕ} [NeZero n]
    {a b c d : I n} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∑ t : I n, ∑ s : I n, rect a b t s * rect c d t s =
      1 + (if b = d then 1 else 0) + (if a = c then 1 else 0) + (if a = c ∧ b = d then 1 else 0) := by
  rw [sum_rect_mul_eq_corners (a := a) (b := b) ha hb (g := fun t s => rect c d t s)]
  have h00 : rect c d 0 0 = 1 := by
    simp [rect_row_zero_eq (a := c) (b := d) hc hd, hd]
  have h0b : rect c d 0 b = if b = d then 1 else 0 := by
    simp [rect_row_zero_eq (a := c) (b := d) hc hd, hb]
  have ha0 : rect c d a 0 = if a = c then 1 else 0 := by
    simp [rect_col_zero_eq (a := c) (b := d) hc hd, ha]
  have hab : rect c d a b = if a = c ∧ b = d then 1 else 0 := by
    simpa using (rect_apply_nonzero_nonzero (a := c) (b := d) hc hd ha hb)
  simp [h00, h0b, ha0, hab, add_assoc, add_left_comm, add_comm]

lemma sum_coreSingle_support_eq {n : ℕ} [NeZero n] (h : HAdmissible (n := n))
    (i : OddRectIndex n) :
    Finset.sum (oddRectSupport (n := n) h) (fun j => if i = j then (1 : F) else 0) =
      oddCoreOfH (n := n) h i.1 i.2 := by
  by_cases hi : i ∈ oddRectSupport (n := n) h
  · rw [Finset.sum_eq_single_of_mem i hi]
    · have hi_one : oddCoreOfH (n := n) h i.1 i.2 = 1 := by
        exact (Finset.mem_filter.mp hi).2
      rw [hi_one]
      simp
    · intro j hj hij
      simp [show ¬ i = j by simpa [eq_comm] using hij]
  · have hsum0 :
        Finset.sum (oddRectSupport (n := n) h) (fun j => if i = j then (1 : F) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hji : j ≠ i := by
        intro hji
        apply hi
        simpa [hji] using hj
      simp [show ¬ i = j by simpa [eq_comm] using hji]
    rw [hsum0]
    have hi_ne_one : oddCoreOfH (n := n) h i.1 i.2 ≠ 1 := by
      intro hi_one
      apply hi
      simp [oddRectSupport, hi_one]
    set x : F := oddCoreOfH (n := n) h i.1 i.2 with hx
    have hxlt : x.val < 2 := by
      simpa [F] using ZMod.val_lt x
    have hx_cases : x.val = 0 ∨ x.val = 1 := by
      omega
    rcases hx_cases with h0 | h1
    · have hx_zero : x = 0 := by
        apply ZMod.val_injective
        simpa [h0] using (show ZMod.val (0 : F) = 0 by rfl)
      simpa [hx] using hx_zero.symm
    · exfalso
      have hx_one : x = 1 := by
        apply ZMod.val_injective
        simpa [h1] using (show ZMod.val (1 : F) = 1 by rfl)
      exact hi_ne_one (by simpa [hx] using hx_one)

lemma oddRect_sum_support {n : ℕ} [NeZero n] (h : HAdmissible (n := n)) :
    Finset.sum (oddRectSupport (n := n) h) (fun i => oddRectVec (n := n) i) = h := by
  apply (oddCoreLinearEquiv (n := n)).injective
  change oddCoreOfH (n := n) (Finset.sum (oddRectSupport (n := n) h) (fun i => oddRectVec (n := n) i)) =
    oddCoreOfH (n := n) h
  funext s t
  have hsum :
      oddCoreOfH (n := n)
          (Finset.sum (oddRectSupport (n := n) h) (fun i => oddRectVec (n := n) i)) s t =
        Finset.sum (oddRectSupport (n := n) h)
          (fun i => oddCoreOfH (n := n) (oddRectVec (n := n) i) s t) := by
    classical
    induction oddRectSupport (n := n) h using Finset.induction_on with
    | empty =>
        simp [oddCoreOfH]
    | @insert i S hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        calc
          oddCoreOfH (n := n)
              (oddRectVec (n := n) i + Finset.sum S (fun j => oddRectVec (n := n) j)) s t
              =
                oddCoreOfH (n := n) (oddRectVec (n := n) i) s t +
                  oddCoreOfH (n := n) (Finset.sum S (fun j => oddRectVec (n := n) j)) s t := by
                    rfl
          _ = oddCoreOfH (n := n) (oddRectVec (n := n) i) s t +
                Finset.sum S (fun j => oddCoreOfH (n := n) (oddRectVec (n := n) j) s t) := by
                  rw [ih]
  rw [hsum]
  have hpoint :
      ∀ i : OddRectIndex n,
        oddCoreOfH (n := n) (oddRectVec (n := n) i) s t = if (s, t) = i then 1 else 0 := by
    intro i
    simpa using oddCoreOfH_oddRectVec (n := n) (s, t) i
  simpa [hpoint] using sum_coreSingle_support_eq (n := n) h (s, t)

lemma mem_oddRectSupport_iff_core_eq_one {n : ℕ} [NeZero n] (h : HAdmissible (n := n))
    (i : OddRectIndex n) :
    i ∈ oddRectSupport (n := n) h ↔ oddCoreOfH (n := n) h i.1 i.2 = 1 := by
  simp [oddRectSupport]

@[simp] lemma oddRectSupport_zero {n : ℕ} [NeZero n] :
    oddRectSupport (n := n) (0 : HAdmissible (n := n)) = ∅ := by
  ext i
  rw [mem_oddRectSupport_iff_core_eq_one]
  simp [oddCoreOfH]

lemma oddCoreOfH_eq_zero_or_one {n : ℕ} [NeZero n] (h : HAdmissible (n := n))
    (i : OddRectIndex n) :
    oddCoreOfH (n := n) h i.1 i.2 = 0 ∨ oddCoreOfH (n := n) h i.1 i.2 = 1 := by
  let x : F := oddCoreOfH (n := n) h i.1 i.2
  have hxlt : x.val < 2 := by
    simpa [F] using ZMod.val_lt x
  have hx_cases : x.val = 0 ∨ x.val = 1 := by
    omega
  rcases hx_cases with h0 | h1
  · left
    apply ZMod.val_injective
    simpa [x, h0] using (show ZMod.val (0 : F) = 0 by rfl)
  · right
    apply ZMod.val_injective
    simpa [x, h1] using (show ZMod.val (1 : F) = 1 by rfl)

lemma oddCoreOfH_add_oddRectVec {n : ℕ} [NeZero n] (h : HAdmissible (n := n))
    (i j : OddRectIndex n) :
    oddCoreOfH (n := n) (h + oddRectVec (n := n) j) i.1 i.2 =
      oddCoreOfH (n := n) h i.1 i.2 + if i = j then 1 else 0 := by
  have hrect : (oddRectVec (n := n) j).1 i.1 i.2 = if i = j then 1 else 0 := by
    simpa [oddCoreOfH] using oddCoreOfH_oddRectVec (n := n) i j
  change (h + oddRectVec (n := n) j).1 i.1 i.2 =
      h.1 i.1 i.2 + if i = j then 1 else 0
  simpa [hrect]

lemma mem_oddRectSupport_add_oddRectVec_iff {n : ℕ} [NeZero n] (h : HAdmissible (n := n))
    (i j : OddRectIndex n) :
    i ∈ oddRectSupport (n := n) (h + oddRectVec (n := n) j) ↔
      if i = j then i ∉ oddRectSupport (n := n) h else i ∈ oddRectSupport (n := n) h := by
  by_cases hij : i = j
  · subst hij
    rw [mem_oddRectSupport_iff_core_eq_one, mem_oddRectSupport_iff_core_eq_one, oddCoreOfH_add_oddRectVec]
    rcases oddCoreOfH_eq_zero_or_one (n := n) h i with h0 | h1
    · simp [h0]
    · simp [h1]
  · rw [mem_oddRectSupport_iff_core_eq_one, mem_oddRectSupport_iff_core_eq_one, oddCoreOfH_add_oddRectVec]
    simp [hij]

lemma oddRectSupport_add_oddRectVec {n : ℕ} [NeZero n] (h : HAdmissible (n := n))
    (j : OddRectIndex n) :
    oddRectSupport (n := n) (h + oddRectVec (n := n) j) =
      if j ∈ oddRectSupport (n := n) h then (oddRectSupport (n := n) h).erase j
      else insert j (oddRectSupport (n := n) h) := by
  classical
  ext i
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ oddRectSupport (n := n) h
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hi]
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hi]
  · by_cases hj : j ∈ oddRectSupport (n := n) h
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hij, hj]
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hij, hj]

@[simp] lemma oddRectSupport_sum {n : ℕ} [NeZero n] (S : Finset (OddRectIndex n)) :
    oddRectSupport (n := n) (Finset.sum S fun i => oddRectVec (n := n) i) = S := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi]
    rw [add_comm]
    rw [oddRectSupport_add_oddRectVec]
    rw [hS]
    simp [hi]

noncomputable def oddRectSupportEquiv {n : ℕ} [NeZero n] :
    HAdmissible (n := n) ≃ Finset (OddRectIndex n) where
  toFun := oddRectSupport (n := n)
  invFun := fun S => Finset.sum S fun i => oddRectVec (n := n) i
  left_inv := by
    intro h
    simpa using oddRect_sum_support (n := n) h
  right_inv := by
    intro S
    simpa using oddRectSupport_sum (n := n) S

lemma sum_oddHSign_eq_sum_supportSubsets {b c n : ℕ} [NeZero n] :
    (∑ h : HAdmissible n, oddHSign (b := b) (c := c) (n := n) h) =
      ∑ S : Finset (OddRectIndex n),
        oddHSign (b := b) (c := c) (n := n) ((oddRectSupportEquiv (n := n)).symm S) := by
  simpa using
    (((oddRectSupportEquiv (n := n)).symm.sum_comp
      (fun h : HAdmissible n => oddHSign (b := b) (c := c) (n := n) h)).symm)

@[simp] lemma prefixT_zero_fun {n : ℕ} [NeZero n] (t s : I n) :
    prefixT (n := n) (0 : HRaw n) t s = 0 := by
  simp [prefixT]

@[simp] lemma prefixR_zero_fun {n : ℕ} [NeZero n] (t s : I n) :
    prefixR (n := n) (0 : HRaw n) t s = 0 := by
  simp [prefixR]

@[simp] lemma scalarBPref_zero {c n : ℕ} [NeZero n] :
    scalarBPref (c := c) (n := n) (0 : HRaw n) = 0 := by
  funext t z
  simp [scalarBPref, buildScalarB]

@[simp] lemma scalarCPref_zero {b n : ℕ} [NeZero n] :
    scalarCPref (b := b) (n := n) (0 : HRaw n) = 0 := by
  funext y r
  simp [scalarCPref, buildScalarC]

@[simp] lemma qScalar_zero_left {b c n : ℕ} [NeZero n] (ccoef : ScalarCCoef b n) :
    qScalar (b := b) (c := c) (n := n) 0 ccoef = 0 := by
  unfold qScalar qLeftScalar qRightScalar
  simp

@[simp] lemma Cagg_zero {b n : ℕ} [NeZero n] (t r : I n) :
    Cagg (b := b) (n := n) (0 : ScalarCCoef b n) t r = 0 := by
  simp [Cagg]

@[simp] lemma qScalar_zero_right {b c n : ℕ} [NeZero n] (bcoef : ScalarBCoef c n) :
    qScalar (b := b) (c := c) (n := n) bcoef 0 = 0 := by
  unfold qScalar qLeftScalar qRightScalar
  simp

lemma scalarBPref_add {c n : ℕ} [NeZero n] (h k : HRaw n) :
    scalarBPref (c := c) (n := n) (h + k) =
      scalarBPref (c := c) (n := n) h + scalarBPref (c := c) (n := n) k := by
  funext t z
  simp [scalarBPref, buildScalarB, prefixT, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma scalarCPref_add {b n : ℕ} [NeZero n] (h k : HRaw n) :
    scalarCPref (b := b) (n := n) (h + k) =
      scalarCPref (b := b) (n := n) h + scalarCPref (b := b) (n := n) k := by
  funext y r
  simp [scalarCPref, buildScalarC, prefixR, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma scalarBPref_sum_oddRectVec {c n : ℕ} [NeZero n] (S : Finset (OddRectIndex n)) :
    scalarBPref (c := c) (n := n) (Finset.sum S fun i => (oddRectVec (n := n) i).1) =
      Finset.sum S (fun i => scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, scalarBPref_add, hS]

lemma scalarCPref_sum_oddRectVec {b n : ℕ} [NeZero n] (S : Finset (OddRectIndex n)) :
    scalarCPref (b := b) (n := n) (Finset.sum S fun i => (oddRectVec (n := n) i).1) =
      Finset.sum S (fun i => scalarCPref (b := b) (n := n) (oddRectVec (n := n) i).1) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, scalarCPref_add, hS]

lemma qScalar_scalarBPref_sum_oddRectVec_left {b c n : ℕ} [NeZero n]
    (S : Finset (OddRectIndex n)) (k : HRaw n) :
    qScalar (b := b) (c := c) (n := n)
        (scalarBPref (c := c) (n := n) (Finset.sum S fun i => (oddRectVec (n := n) i).1))
        (scalarCPref (b := b) (n := n) k) =
      Finset.sum S (fun i =>
        qScalar (b := b) (c := c) (n := n)
          (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
          (scalarCPref (b := b) (n := n) k)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, scalarBPref_add, qScalar_add_left, hS]

lemma qScalar_scalarBPref_sum_oddRectVec_right {b c n : ℕ} [NeZero n]
    (h : HRaw n) (S : Finset (OddRectIndex n)) :
    qScalar (b := b) (c := c) (n := n)
        (scalarBPref (c := c) (n := n) h)
        (scalarCPref (b := b) (n := n) (Finset.sum S fun i => (oddRectVec (n := n) i).1)) =
      Finset.sum S (fun i =>
        qScalar (b := b) (c := c) (n := n)
          (scalarBPref (c := c) (n := n) h)
          (scalarCPref (b := b) (n := n) (oddRectVec (n := n) i).1)) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, scalarCPref_add, qScalar_add_right, hS]

lemma qScalar_scalarBPref_scalarCPref_eq_sum_support_support {b c n : ℕ} [NeZero n]
    (h k : HAdmissible (n := n)) :
    qScalar (b := b) (c := c) (n := n)
        (scalarBPref (c := c) (n := n) h.1)
        (scalarCPref (b := b) (n := n) k.1) =
      Finset.sum (oddRectSupport (n := n) h) (fun i =>
        Finset.sum (oddRectSupport (n := n) k) (fun j =>
          qScalar (b := b) (c := c) (n := n)
            (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
            (scalarCPref (b := b) (n := n) (oddRectVec (n := n) j).1))) := by
  have hh : h.1 = Finset.sum (oddRectSupport (n := n) h) (fun i => (oddRectVec (n := n) i).1) := by
    symm
    simpa using congrArg Subtype.val (oddRect_sum_support (n := n) h)
  have hk : k.1 = Finset.sum (oddRectSupport (n := n) k) (fun i => (oddRectVec (n := n) i).1) := by
    symm
    simpa using congrArg Subtype.val (oddRect_sum_support (n := n) k)
  rw [hh, hk]
  rw [qScalar_scalarBPref_sum_oddRectVec_left (b := b) (c := c) (n := n)
    (S := oddRectSupport (n := n) h) (k := Finset.sum (oddRectSupport (n := n) k) fun i => (oddRectVec (n := n) i).1)]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [qScalar_scalarBPref_sum_oddRectVec_right (b := b) (c := c) (n := n)
    (h := (oddRectVec (n := n) i).1) (S := oddRectSupport (n := n) k)]

noncomputable def oddRectPair {b c n : ℕ} [NeZero n] (i j : OddRectIndex n) : F :=
  qScalar (b := b) (c := c) (n := n)
    (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
    (scalarCPref (b := b) (n := n) (oddRectVec (n := n) j).1)

lemma qScalar_scalarBPref_scalarCPref_eq_sum_oddRectPair {b c n : ℕ} [NeZero n]
    (h k : HAdmissible (n := n)) :
    qScalar (b := b) (c := c) (n := n)
        (scalarBPref (c := c) (n := n) h.1)
        (scalarCPref (b := b) (n := n) k.1) =
      Finset.sum (oddRectSupport (n := n) h) (fun i =>
        Finset.sum (oddRectSupport (n := n) k) (fun j =>
          oddRectPair (b := b) (c := c) (n := n) i j)) := by
  simpa [oddRectPair] using
    qScalar_scalarBPref_scalarCPref_eq_sum_support_support (b := b) (c := c) (n := n) h k

lemma oddHSign_eq_bitSign_sum_oddRectPair {b c n : ℕ} [NeZero n] (h : HAdmissible (n := n)) :
    oddHSign (b := b) (c := c) (n := n) h =
      bitSign
        (Finset.sum (oddRectSupport (n := n) h) (fun i =>
          Finset.sum (oddRectSupport (n := n) h) (fun j =>
            oddRectPair (b := b) (c := c) (n := n) i j))) := by
  rw [oddHSign, qScalar_scalarBPref_scalarCPref_eq_sum_oddRectPair (b := b) (c := c) (n := n) h h]

lemma oddRectPair_formula_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (i j : OddRectIndex n) :
    oddRectPair (b := b) (c := c) (n := n) i j =
      ((if i.2.1.val ≤ j.2.1.val then 1 else 0) +
        (if i.1.1 = j.1.1 then (if i.2.1.val ≤ j.2.1.val then 1 else 0) else 0)) +
      (((if j.1.1.val ≤ i.1.1.val then 1 else 0) +
        (if i.2.1 = j.2.1 then (if j.1.1.val ≤ i.1.1.val then 1 else 0) else 0)) +
        (1 + (if i.2.1 = j.2.1 then 1 else 0) + (if i.1.1 = j.1.1 then 1 else 0) +
          (if i.1.1 = j.1.1 ∧ i.2.1 = j.2.1 then 1 else 0))) := by
  rcases i with ⟨⟨a, ha⟩, ⟨b0, hb0⟩⟩
  rcases j with ⟨⟨c0, hc0⟩, ⟨d, hd⟩⟩
  have hha : rect a b0 ∈ HAdmissible (n := n) := rect_mem_HAdmissible (n := n) a b0
  have hhc : rect c0 d ∈ HAdmissible (n := n) := rect_mem_HAdmissible (n := n) c0 d
  unfold oddRectPair
  simp_rw [oddRectVec_val_eq_rect]
  rw [qScalar_scalarBPref_scalarCPref_formula_mixed_of_odd
    (b := b) (c := c) (n := n) hb hc hn hha hhc]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_rect_mul_prefixR_rect_eq (a := a) (b := b0) (c := c0) (d := d) ha hb0 hc0 hd]
  rw [sum_prefixT_rect_mul_rect_eq (a := a) (b := b0) (c := c0) (d := d) ha hb0 hc0 hd]
  rw [sum_rect_mul_rect_eq_indicator (a := a) (b := b0) (c := c0) (d := d) ha hb0 hc0 hd]
  simpa [add_assoc, add_left_comm, add_comm]

lemma oddRectPair_symm_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (i j : OddRectIndex n) :
    oddRectPair (b := b) (c := c) (n := n) i j =
      oddRectPair (b := b) (c := c) (n := n) j i := by
  rw [oddRectPair_formula_of_odd (b := b) (c := c) (n := n) hb hc hn i j,
    oddRectPair_formula_of_odd (b := b) (c := c) (n := n) hb hc hn j i]
  rcases i with ⟨⟨a, ha⟩, ⟨b0, hb0⟩⟩
  rcases j with ⟨⟨c0, hc0⟩, ⟨d, hd⟩⟩
  by_cases hac : a = c0
  · subst hac
    by_cases hbd : b0 = d
    · subst hbd
      simp [F_add_self, add_assoc, add_left_comm, add_comm]
    · by_cases hbdle : b0.val ≤ d.val
      · have hbdv : b0.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdblt : ¬ d.val ≤ b0.val := by omega
        simp [hbd, hdb, hbdle, hdblt, F_add_self, add_assoc, add_left_comm, add_comm]
      · have hbdv : b0.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdble : d.val ≤ b0.val := by omega
        simp [hbd, hdb, hbdle, hdble, F_add_self, add_assoc, add_left_comm, add_comm]
  · by_cases hbd : b0 = d
    · subst hbd
      by_cases hcale : c0.val ≤ a.val
      · have hacv : a.val ≠ c0.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
        have hca : ¬ c0 = a := by simpa [eq_comm] using hac
        have hacle : ¬ a.val ≤ c0.val := by omega
        simp [hac, hca, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
      · have hacv : a.val ≠ c0.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
        have hca : ¬ c0 = a := by simpa [eq_comm] using hac
        have hacle : a.val ≤ c0.val := by omega
        simp [hac, hca, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
    · by_cases hbdle : b0.val ≤ d.val
      · have hbdv : b0.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdble : ¬ d.val ≤ b0.val := by omega
        by_cases hcale : c0.val ≤ a.val
        · have hacv : a.val ≠ c0.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : ¬ a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]
        · have hacv : a.val ≠ c0.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]
      · have hbdv : b0.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdble : d.val ≤ b0.val := by omega
        by_cases hcale : c0.val ≤ a.val
        · have hacv : a.val ≠ c0.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : ¬ a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]
        · have hacv : a.val ≠ c0.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]

lemma qScalar_scalarBPref_scalarCPref_rect_eq_zero_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (i : OddRectIndex n) :
    qScalar (b := b) (c := c) (n := n)
      (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
      (scalarCPref (b := b) (n := n) (oddRectVec (n := n) i).1) = 0 := by
  simpa [oddRectPair, F_add_self, add_assoc, add_left_comm, add_comm] using
    (oddRectPair_formula_of_odd (b := b) (c := c) (n := n) hb hc hn i i)

lemma qScalar_scalarBPref_scalarCPref_symm_oddRectVec_right_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (h : HAdmissible (n := n)) (i : OddRectIndex n) :
    qScalar (b := b) (c := c) (n := n)
      (scalarBPref (c := c) (n := n) h.1)
      (scalarCPref (b := b) (n := n) (oddRectVec (n := n) i).1) =
    qScalar (b := b) (c := c) (n := n)
      (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
      (scalarCPref (b := b) (n := n) h.1) := by
  rw [qScalar_scalarBPref_scalarCPref_eq_sum_oddRectPair (b := b) (c := c) (n := n) h
    (oddRectVec (n := n) i)]
  rw [qScalar_scalarBPref_scalarCPref_eq_sum_oddRectPair (b := b) (c := c) (n := n)
    (oddRectVec (n := n) i) h]
  simp only [oddRectSupport_oddRectVec, Finset.sum_singleton]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa [oddRectPair] using
    (oddRectPair_symm_of_odd (b := b) (c := c) (n := n) hb hc hn j i)

lemma oddHSign_add_oddRectVec_iff_qsymm {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (h : HAdmissible (n := n)) (i : OddRectIndex n)
    (hsymm :
      qScalar (b := b) (c := c) (n := n)
        (scalarBPref (c := c) (n := n) h.1)
        (scalarCPref (b := b) (n := n) (oddRectVec (n := n) i).1) =
      qScalar (b := b) (c := c) (n := n)
        (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
        (scalarCPref (b := b) (n := n) h.1)) :
    oddHSign (b := b) (c := c) (n := n) (h + oddRectVec (n := n) i) =
      oddHSign (b := b) (c := c) (n := n) h := by
  unfold oddHSign
  have hadd :
      qScalar (b := b) (c := c) (n := n)
          (scalarBPref (c := c) (n := n) (h + oddRectVec (n := n) i).1)
          (scalarCPref (b := b) (n := n) (h + oddRectVec (n := n) i).1) =
        qScalar (b := b) (c := c) (n := n)
            (scalarBPref (c := c) (n := n) h.1)
            (scalarCPref (b := b) (n := n) h.1) +
          qScalar (b := b) (c := c) (n := n)
            (scalarBPref (c := c) (n := n) h.1)
            (scalarCPref (b := b) (n := n) (oddRectVec (n := n) i).1) +
          qScalar (b := b) (c := c) (n := n)
            (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
            (scalarCPref (b := b) (n := n) h.1) +
          qScalar (b := b) (c := c) (n := n)
            (scalarBPref (c := c) (n := n) (oddRectVec (n := n) i).1)
            (scalarCPref (b := b) (n := n) (oddRectVec (n := n) i).1) := by
    change
      qScalar (b := b) (c := c) (n := n)
        (scalarBPref (c := c) (n := n) (h.1 + (oddRectVec (n := n) i).1))
        (scalarCPref (b := b) (n := n) (h.1 + (oddRectVec (n := n) i).1)) = _
    rw [scalarBPref_add, scalarCPref_add, qScalar_add_left, qScalar_add_right, qScalar_add_right]
    ac_rfl
  rw [hadd, hsymm,
    qScalar_scalarBPref_scalarCPref_rect_eq_zero_of_odd (b := b) (c := c) (n := n) hb hc hn i]
  simp [bitSign, add_assoc, add_left_comm, add_comm, F_add_self]

lemma oddHSign_oddRectVec_eq_one {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (i : OddRectIndex n) :
    oddHSign (b := b) (c := c) (n := n) (oddRectVec (n := n) i) = 1 := by
  unfold oddHSign
  rw [qScalar_scalarBPref_scalarCPref_rect_eq_zero_of_odd (b := b) (c := c) (n := n) hb hc hn i]
  exact No13Migration.bitSign_zero

lemma oddHSign_add_oddRectVec_eq_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (h : HAdmissible (n := n)) (i : OddRectIndex n) :
    oddHSign (b := b) (c := c) (n := n) (h + oddRectVec (n := n) i) =
      oddHSign (b := b) (c := c) (n := n) h := by
  refine oddHSign_add_oddRectVec_iff_qsymm (b := b) (c := c) (n := n) hb hc hn h i ?_
  exact qScalar_scalarBPref_scalarCPref_symm_oddRectVec_right_of_odd
    (b := b) (c := c) (n := n) hb hc hn h i

@[simp] lemma oddHSign_zero_eq_one {b c n : ℕ} [NeZero n] :
    oddHSign (b := b) (c := c) (n := n) (0 : HAdmissible (n := n)) = 1 := by
  unfold oddHSign
  simp [qScalar, qLeftScalar, qRightScalar, scalarBPref, scalarCPref,
    buildScalarB, buildScalarC, prefixT, prefixR, No13Migration.bitSign_zero]

lemma oddHSign_sum_oddRectVec_eq_one_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (S : Finset (OddRectIndex n)) :
    oddHSign (b := b) (c := c) (n := n)
      (Finset.sum S (fun i => oddRectVec (n := n) i)) = 1 := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi]
    calc
      oddHSign (b := b) (c := c) (n := n)
          (oddRectVec (n := n) i + Finset.sum S (fun j => oddRectVec (n := n) j))
        =
      oddHSign (b := b) (c := c) (n := n)
          ((Finset.sum S (fun j => oddRectVec (n := n) j)) + oddRectVec (n := n) i) := by
            simp [add_comm]
      _ =
      oddHSign (b := b) (c := c) (n := n)
          (Finset.sum S (fun j => oddRectVec (n := n) j)) := by
            exact oddHSign_add_oddRectVec_eq_of_odd (b := b) (c := c) (n := n) hb hc hn _ i
      _ = 1 := hS

lemma oddHSign_eq_one_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (h : HAdmissible (n := n)) :
    oddHSign (b := b) (c := c) (n := n) h = 1 := by
  rw [← oddRect_sum_support (n := n) h]
  exact oddHSign_sum_oddRectVec_eq_one_of_odd (b := b) (c := c) (n := n) hb hc hn
    (oddRectSupport (n := n) h)

theorem qScalar_eq_zero_on_visible_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (bc : ScalarVisibleCompat b c n) :
    qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef = 0 := by
  let d := scalarVisibleToData (b := b) (c := c) (n := n) hb hc bc
  have hbc :
      dataToScalarVisible (b := b) (c := c) (n := n) hb hc d = bc := by
    simpa [d] using dataToScalarVisible_left_inv (b := b) (c := c) (n := n) hb hc bc
  have hsign :
      oddVisibleSign (b := b) (c := c) (n := n) bc = 1 := by
    rw [← hbc]
    rw [oddVisibleSign_fromHUV_eq_oddHSign_of_odd (b := b) (c := c) (n := n) hb hc hn
      d.1 d.2.1 d.2.2]
    exact oddHSign_eq_one_of_odd (b := b) (c := c) (n := n) hb hc hn d.1
  exact (bitSign_eq_one_iff_eq_zero
    (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef)).1 <| by
      simpa [oddVisibleSign] using hsign

lemma sum_oddHSign_eq_natCard_HAdmissible_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    ∑ h : HAdmissible (n := n), oddHSign (b := b) (c := c) (n := n) h =
      (Nat.card (HAdmissible (n := n)) : ℤ) := by
  simp [oddHSign_eq_one_of_odd (b := b) (c := c) (n := n) hb hc hn]

theorem sum_oddVisible_eq_natCard_scalarVisibleCompat_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    ∑ bc : ScalarVisibleCompat b c n, oddVisibleSign (b := b) (c := c) (n := n) bc =
      (Nat.card (ScalarVisibleCompat b c n) : ℤ) := by
  rw [sum_oddVisible_eq_hAdmissible_sum_of_odd (b := b) (c := c) (n := n) hb hc hn]
  rw [sum_oddHSign_eq_natCard_HAdmissible_of_odd (b := b) (c := c) (n := n) hb hc hn]
  simp only [Nat.card_eq_fintype_card]
  rw [card_HAdmissible (n := n), card_scalarVisibleSpace_closed (b := b) (c := c) (n := n) hb hc]
  simpa [add_assoc, add_left_comm, add_comm] using
    (pow_add (2 : ℤ) (n ^ b + n ^ c) ((n - 1) ^ 2)).symm

theorem sum_oddVisible_eq_closed_form_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    ∑ bc : ScalarVisibleCompat b c n, oddVisibleSign (b := b) (c := c) (n := n) bc =
      (2 : ℤ) ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
  rw [sum_oddVisible_eq_natCard_scalarVisibleCompat_of_odd (b := b) (c := c) (n := n) hb hc hn]
  simpa [Nat.card_eq_fintype_card] using
    congrArg (fun x : ℕ => (x : ℤ))
      (card_scalarVisibleSpace_closed (b := b) (c := c) (n := n) hb hc)

end Core3loop
