import Core3loop.AeqOne
import Core3loop.EvenCase
import Core3loop.Exponents

open scoped BigOperators

namespace Core3loop

lemma QpairABC_eq_qScalar_of_a_eq_one {b c n : ℕ} [NeZero n]
    (B : BFieldABC 1 c n) (C : CFieldABC 1 b n) :
    QpairABC (a := 1) (b := b) (c := c) (n := n) B C =
      qScalar (b := b) (c := c) (n := n)
        (bFieldEquivScalarBCoef (c := c) (n := n) B)
        (cFieldEquivScalarCCoef (b := b) (n := n) C) := by
  let bcoef := bFieldEquivScalarBCoef (c := c) (n := n) B
  let ccoef := cFieldEquivScalarCCoef (b := b) (n := n) C
  unfold QpairABC
  calc
    ∑ u : Site 1 b c n, pairBC_abc (a := 1) (b := b) (c := c) (n := n) B C u
        =
          ∑ yz : YCoord b n × ZCoord c n,
            ∑ x : XCoord 1 n,
              pairBC_abc (a := 1) (b := b) (c := c) (n := n) B C (x, yz.1, yz.2) := by
              simpa [Site] using
                (Fintype.sum_prod_type_right
                  (f := fun u : XCoord 1 n × (YCoord b n × ZCoord c n) =>
                    pairBC_abc (a := 1) (b := b) (c := c) (n := n) B C
                      (u.1, u.2.1, u.2.2)))
    _ =
      ∑ yz : YCoord b n × ZCoord c n,
        pairBC_abc (a := 1) (b := b) (c := c) (n := n) B C
          (xCoordZero (n := n), yz.1, yz.2) := by
            refine Finset.sum_congr rfl ?_
            intro yz hyz
            exact sum_XCoord_one (n := n)
              (f := fun x : XCoord 1 n =>
                pairBC_abc (a := 1) (b := b) (c := c) (n := n) B C (x, yz.1, yz.2))
    _ =
      ∑ z : ZCoord c n, ∑ y : YCoord b n,
        (bcoef (sumY y) z * ccoef y (sumZ z) +
          bcoef (sumY y + 1) z * ccoef y (sumZ z + 1)) := by
          simpa [bcoef, ccoef, pairBC_abc, bFieldEquivScalarBCoef, cFieldEquivScalarCCoef] using
            (Fintype.sum_prod_type_right
              (f := fun yz : YCoord b n × ZCoord c n =>
                pairBC_abc (a := 1) (b := b) (c := c) (n := n) B C
                  (xCoordZero (n := n), yz.1, yz.2)))
    _ =
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        (bcoef (sumY y) z * ccoef y (sumZ z) +
          bcoef (sumY y + 1) z * ccoef y (sumZ z + 1)) := by
          rw [Finset.sum_comm]
    _ =
      (∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y) z * ccoef y (sumZ z)) +
        ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
          simp_rw [Finset.sum_add_distrib]
    _ = qLeftScalar (b := b) (c := c) (n := n) bcoef ccoef +
          qRightScalar (b := b) (c := c) (n := n) bcoef ccoef := by
            rw [← qLeftScalar_eq_sum_yz (b := b) (c := c) (n := n) bcoef ccoef,
              ← qRightScalar_eq_sum_yz (b := b) (c := c) (n := n) bcoef ccoef]
    _ = qScalar (b := b) (c := c) (n := n) bcoef ccoef := by
          rfl

lemma sum_survivingBC_eq_sum_visible_bitSign_of_a_eq_one {b c n : ℕ} [NeZero n] :
    ∑ bc : SurvivingBC 1 b c n,
      bitSign (QpairABC (a := 1) (b := b) (c := c) (n := n) bc.1.1 bc.1.2) =
        ∑ bc : ScalarVisibleCompat b c n,
          bitSign (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef) := by
  classical
  simpa [QpairABC_eq_qScalar_of_a_eq_one] using
    (Equiv.sum_comp (survivingBCEquivScalarVisible (b := b) (c := c) (n := n))
      (fun bc : ScalarVisibleCompat b c n =>
        bitSign (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef)))

theorem card_survivingBC_generic_visible_space {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (SurvivingBC 1 b c n) = 2 ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
  rw [Fintype.card_congr (survivingBCEquivScalarVisible (b := b) (c := c) (n := n))]
  exact card_scalarVisibleSpace_closed (b := b) (c := c) (n := n) hb hc

theorem DeltaABC_eq_sum_visible_bitSign_of_a_eq_one {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    DeltaABC 1 b c n =
      (2 : ℤ) ^ (n ^ (b + c)) *
        ∑ bc : ScalarVisibleCompat b c n,
          bitSign (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef) := by
  rw [DeltaABC_after_A (a := 1) (b := b) (c := c) (n := n) (by omega) hb hc]
  rw [sum_survivingBC_eq_sum_visible_bitSign_of_a_eq_one (b := b) (c := c) (n := n)]

theorem DeltaABC_closed_of_a_eq_one_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    DeltaABC 1 b c n =
      (2 : ℤ) ^ (n ^ (b + c) + n ^ b + n ^ c + (n - 1) ^ 2) := by
  rw [DeltaABC_eq_sum_visible_bitSign_of_a_eq_one (b := b) (c := c) (n := n) hb hc]
  rw [show
      (∑ bc : ScalarVisibleCompat b c n,
        bitSign (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef)) =
        ∑ bc : ScalarVisibleCompat b c n, oddVisibleSign (b := b) (c := c) (n := n) bc by
      rfl]
  rw [sum_oddVisible_eq_closed_form_of_odd (b := b) (c := c) (n := n) hb hc hn]
  rw [← pow_add]
  congr 1
  omega

theorem DeltaABC_generic_closed_of_a_eq_one_of_odd {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    DeltaABC 1 b c n = (2 : ℤ) ^ genericDeltaExponent 1 b c n := by
  rw [DeltaABC_closed_of_a_eq_one_of_odd (b := b) (c := c) (n := n) hb hc hn]
  congr 1
  exact (genericDeltaExponent_a_eq_one (b := b) (c := c) (n := n) hb hc).symm

lemma qScalar_scalarBConst_scalarCPref_eq_zero_of_b_eq_one {c n : ℕ} [NeZero n]
    {h : HRaw n} (hh : h ∈ HAdmissible (n := n)) (u : ZCoord c n → F) :
    qScalar (b := 1) (c := c) (n := n)
      (scalarBConst (c := c) u)
      (scalarCPref (b := 1) (n := n) h) = 0 := by
  have hleft :
      qLeftScalar (b := 1) (c := c) (n := n)
          (scalarBConst (c := c) u)
          (scalarCPref (b := 1) (n := n) h) =
        ∑ t : I n, ∑ z : ZCoord c n, u z * prefixR h t (sumZ z) := by
    unfold qLeftScalar scalarBConst
    refine Finset.sum_congr rfl ?_
    intro t ht
    refine Finset.sum_congr rfl ?_
    intro z hz
    rw [Cagg_scalarCPref_eq_of_b_eq_one]
  have hright_raw :
      qRightScalar (b := 1) (c := c) (n := n)
          (scalarBConst (c := c) u)
          (scalarCPref (b := 1) (n := n) h) =
        ∑ t : I n, ∑ z : ZCoord c n, u z * prefixR h (t - 1) (sumZ z + 1) := by
    unfold qRightScalar scalarBConst
    refine Finset.sum_congr rfl ?_
    intro t ht
    refine Finset.sum_congr rfl ?_
    intro z hz
    rw [Cagg_scalarCPref_eq_of_b_eq_one]
  have hright :
      qRightScalar (b := 1) (c := c) (n := n)
          (scalarBConst (c := c) u)
          (scalarCPref (b := 1) (n := n) h) =
        ∑ t : I n, ∑ z : ZCoord c n, u z * prefixR h t (sumZ z + 1) := by
    rw [hright_raw]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun t : I n => ∑ z : ZCoord c n,
          u z * prefixR h (t - 1) (sumZ z + 1))).symm
  rw [qScalar, hleft, hright]
  calc
    (∑ t : I n, ∑ z : ZCoord c n, u z * prefixR h t (sumZ z)) +
        ∑ t : I n, ∑ z : ZCoord c n, u z * prefixR h t (sumZ z + 1)
        =
      (∑ z : ZCoord c n, ∑ t : I n, u z * prefixR h t (sumZ z)) +
        ∑ z : ZCoord c n, ∑ t : I n, u z * prefixR h t (sumZ z + 1) := by
          rw [Finset.sum_comm]
          congr 1
          rw [Finset.sum_comm]
    _ =
      ∑ z : ZCoord c n,
        ((∑ t : I n, u z * prefixR h t (sumZ z)) +
          ∑ t : I n, u z * prefixR h t (sumZ z + 1)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ z : ZCoord c n, u z *
        (∑ t : I n, (prefixR h t (sumZ z) + prefixR h t (sumZ z + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
          congr 1
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
          rfl
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro z hz
          simp [colSum_eq_zero_of_mem_HAdmissible (n := n) hh (sumZ z)]

lemma qScalar_scalarBPref_scalarCConst_eq_zero_of_c_eq_one {b n : ℕ} [NeZero n]
    {h : HRaw n} (hh : h ∈ HAdmissible (n := n)) (v : YCoord b n → F) :
    qScalar (b := b) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) h)
      (scalarCConst (b := b) v) = 0 := by
  let ez : I n ≃ ZCoord 1 n := (zCoordEquivI_of_c_eq_one (n := n)).symm
  have hleft :
      qLeftScalar (b := b) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCConst (b := b) v) =
        ∑ t : I n, ∑ s : I n, prefixT h t s * scalarYAgg (b := b) (n := n) v t := by
    unfold qLeftScalar scalarBPref
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          buildScalarB h 0 t z * Cagg (b := b) (n := n) (scalarCConst (b := b) v) t (sumZ z)
          =
        ∑ s : I n,
          buildScalarB h 0 t (ez s) *
            Cagg (b := b) (n := n) (scalarCConst (b := b) v) t (sumZ (ez s)) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    buildScalarB h 0 t z *
                      Cagg (b := b) (n := n) (scalarCConst (b := b) v) t (sumZ z))).symm)
      _ = ∑ s : I n, prefixT h t s * scalarYAgg (b := b) (n := n) v t := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [buildScalarB, hsum, Cagg_scalarCConst]
            simp
  have hright_raw :
      qRightScalar (b := b) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCConst (b := b) v) =
        ∑ t : I n, ∑ s : I n, prefixT h t s * scalarYAgg (b := b) (n := n) v (t - 1) := by
    unfold qRightScalar scalarBPref
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          buildScalarB h 0 t z *
            Cagg (b := b) (n := n) (scalarCConst (b := b) v) (t - 1) (sumZ z + 1)
          =
        ∑ s : I n,
          buildScalarB h 0 t (ez s) *
            Cagg (b := b) (n := n) (scalarCConst (b := b) v) (t - 1) (sumZ (ez s) + 1) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    buildScalarB h 0 t z *
                      Cagg (b := b) (n := n) (scalarCConst (b := b) v) (t - 1) (sumZ z + 1))).symm)
      _ = ∑ s : I n, prefixT h t s * scalarYAgg (b := b) (n := n) v (t - 1) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [buildScalarB, hsum, Cagg_scalarCConst]
            simp
  have hright :
      qRightScalar (b := b) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCConst (b := b) v) =
        ∑ t : I n, ∑ s : I n, prefixT h (t + 1) s * scalarYAgg (b := b) (n := n) v t := by
    rw [hright_raw]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun t : I n => ∑ s : I n,
          prefixT h t s * scalarYAgg (b := b) (n := n) v (t - 1))).symm
  rw [qScalar, hleft, hright]
  calc
    (∑ t : I n, ∑ s : I n, prefixT h t s * scalarYAgg (b := b) (n := n) v t) +
        ∑ t : I n, ∑ s : I n, prefixT h (t + 1) s * scalarYAgg (b := b) (n := n) v t
        =
      ∑ t : I n,
        ((∑ s : I n, prefixT h t s * scalarYAgg (b := b) (n := n) v t) +
          ∑ s : I n, prefixT h (t + 1) s * scalarYAgg (b := b) (n := n) v t) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ t : I n,
        (∑ s : I n, (prefixT h t s + prefixT h (t + 1) s)) *
          scalarYAgg (b := b) (n := n) v t := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
          congr 1
          rw [Finset.sum_add_distrib]
    _ = ∑ t : I n, scalarYAgg (b := b) (n := n) v t *
        (∑ s : I n, (prefixT h t s + prefixT h (t + 1) s)) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [mul_comm]
    _ = ∑ t : I n, scalarYAgg (b := b) (n := n) v t * ∑ s : I n, h t s := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact prefixT_pair_eq_of_mem_HAdmissible (n := n) hh t s
    _ = ∑ t : I n, scalarYAgg (b := b) (n := n) v t * rowSum h t := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rfl
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro t ht
          simp [rowSum_eq_zero_of_mem_HAdmissible (n := n) hh t]

lemma qScalar_right_scalarCPref_eq_zero_of_even_gt_one {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) (bcoef : ScalarBCoef c n) (h : HRaw n) :
    qScalar (b := b) (c := c) (n := n) bcoef (scalarCPref (b := b) (n := n) h) = 0 := by
  rw [qScalar_eq_bPair_TScalar]
  have hT : (TScalar (b := b) (c := c) (n := n)) (scalarCPref (b := b) (n := n) h) = 0 := by
    funext t z
    simpa [TScalar, scalarCPref, scalarYAgg] using
      TScalar_buildScalarC_even (b := b) (c := c) (n := n) hn hb2 h (fun _ => (0 : F)) t z
  rw [hT]
  simp [bPairScalar]

lemma qScalar_left_scalarBPref_eq_zero_of_even_gt_one {b c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) (h : HRaw n) (ccoef : ScalarCCoef b n) :
    qScalar (b := b) (c := c) (n := n) (scalarBPref (c := c) (n := n) h) ccoef = 0 := by
  rw [qScalar_eq_cPair_TAdjScalar]
  have hT :
      (TAdjScalar (b := b) (c := c) (n := n)) (scalarBPref (c := c) (n := n) h) = 0 := by
    funext y r
    simpa [TAdjScalar, scalarBPref, scalarZAgg] using
      TAdjScalar_buildScalarB_even (b := b) (c := c) (n := n) hn hc2 h (fun _ => (0 : F)) y r
  rw [hT]
  simp [cPairScalar]

theorem qScalar_eq_zero_on_visible_of_even_all_ge_two {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) (hc2 : 1 < c)
    (bc : ScalarVisibleCompat b c n) :
    qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef = 0 := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  let h : HRaw n := visibleHData (b := b) (c := c) (n := n) hc bc
  let u : ZCoord c n → F := visibleUData bc
  let v : YCoord b n → F := visibleVData bc
  rw [← buildScalarB_visibleData_eq (b := b) (c := c) (n := n) hb hc bc]
  rw [← buildScalarC_visibleData_eq (b := b) (c := c) (n := n) hc bc]
  rw [qScalar_build_eq_three_terms (b := b) (c := c) (n := n) h u v]
  rw [qScalar_right_scalarCPref_eq_zero_of_even_gt_one
    (b := b) (c := c) (n := n) hn hb2 (scalarBConst (c := c) u) h]
  rw [qScalar_left_scalarBPref_eq_zero_of_even_gt_one
    (b := b) (c := c) (n := n) hn hc2 h (scalarCConst (b := b) v)]
  rw [qScalar_right_scalarCPref_eq_zero_of_even_gt_one
    (b := b) (c := c) (n := n) hn hb2 (scalarBPref (c := c) (n := n) h) h]
  simp

theorem qScalar_eq_zero_on_visible_of_even_b_eq_one {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) (bc : ScalarVisibleCompat 1 c n) :
    qScalar (b := 1) (c := c) (n := n) bc.bcoef bc.ccoef = 0 := by
  have hc : 0 < c := by omega
  let h : HRaw n := visibleHData (b := 1) (c := c) (n := n) hc bc
  let u : ZCoord c n → F := visibleUData bc
  let v : YCoord 1 n → F := visibleVData bc
  have hh : h ∈ HAdmissible (n := n) := by
    exact visibleHData_mem_HAdmissible (b := 1) (c := c) (n := n) (by omega) hc bc
  rw [← buildScalarB_visibleData_eq (b := 1) (c := c) (n := n) (by omega) hc bc]
  rw [← buildScalarC_visibleData_eq (b := 1) (c := c) (n := n) hc bc]
  rw [qScalar_build_eq_three_terms (b := 1) (c := c) (n := n) h u v]
  rw [qScalar_scalarBConst_scalarCPref_eq_zero_of_b_eq_one (c := c) (n := n) hh u]
  rw [qScalar_left_scalarBPref_eq_zero_of_even_gt_one
    (b := 1) (c := c) (n := n) hn hc2 h (scalarCConst (b := 1) v)]
  rw [qScalar_left_scalarBPref_eq_zero_of_even_gt_one
    (b := 1) (c := c) (n := n) hn hc2 h (scalarCPref (b := 1) (n := n) h)]
  simp

theorem qScalar_eq_zero_on_visible_of_even_c_eq_one {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) (bc : ScalarVisibleCompat b 1 n) :
    qScalar (b := b) (c := 1) (n := n) bc.bcoef bc.ccoef = 0 := by
  let h : HRaw n := visibleHData (b := b) (c := 1) (n := n) (by omega) bc
  let u : ZCoord 1 n → F := visibleUData bc
  let v : YCoord b n → F := visibleVData bc
  have hh : h ∈ HAdmissible (n := n) := by
    exact visibleHData_mem_HAdmissible (b := b) (c := 1) (n := n) (by omega) (by omega) bc
  rw [← buildScalarB_visibleData_eq (b := b) (c := 1) (n := n) (by omega) (by omega) bc]
  rw [← buildScalarC_visibleData_eq (b := b) (c := 1) (n := n) (by omega) bc]
  rw [qScalar_build_eq_three_terms (b := b) (c := 1) (n := n) h u v]
  rw [qScalar_right_scalarCPref_eq_zero_of_even_gt_one
    (b := b) (c := 1) (n := n) hn hb2 (scalarBConst (c := 1) u) h]
  rw [qScalar_scalarBPref_scalarCConst_eq_zero_of_c_eq_one (b := b) (n := n) hh v]
  rw [qScalar_right_scalarCPref_eq_zero_of_even_gt_one
    (b := b) (c := 1) (n := n) hn hb2 (scalarBPref (c := 1) (n := n) h) h]
  simp

theorem qScalar_eq_zero_on_visible_of_even {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Even n) (bc : ScalarVisibleCompat b c n) :
    qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef = 0 := by
  have hb_cases : b = 1 ∨ 1 < b := by omega
  have hc_cases : c = 1 ∨ 1 < c := by omega
  rcases hb_cases with rfl | hb2
  · rcases hc_cases with rfl | hc2
    · exact qScalar_eq_zero_on_visible_of_eq_one_eq_one (n := n) bc
    · exact qScalar_eq_zero_on_visible_of_even_b_eq_one (c := c) (n := n) hn hc2 bc
  · rcases hc_cases with rfl | hc2
    · exact qScalar_eq_zero_on_visible_of_even_c_eq_one (b := b) (n := n) hn hb2 bc
    · exact qScalar_eq_zero_on_visible_of_even_all_ge_two
        (b := b) (c := c) (n := n) hn hb2 hc2 bc

theorem sum_visible_bitSign_eq_card_of_even {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Even n) :
    ∑ bc : ScalarVisibleCompat b c n,
      bitSign (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef) =
        Fintype.card (ScalarVisibleCompat b c n) := by
  classical
  calc
    ∑ bc : ScalarVisibleCompat b c n,
        bitSign (qScalar (b := b) (c := c) (n := n) bc.bcoef bc.ccoef)
        =
      ∑ _bc : ScalarVisibleCompat b c n, (1 : ℤ) := by
          refine Finset.sum_congr rfl ?_
          intro bc hbc
          exact (bitSign_eq_one_iff_eq_zero _).2
            (qScalar_eq_zero_on_visible_of_even (b := b) (c := c) (n := n) hb hc hn bc)
    _ = Fintype.card (ScalarVisibleCompat b c n) := by
          simp

theorem DeltaABC_generic_closed_of_a_eq_one_of_even {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Even n) :
    DeltaABC 1 b c n = (2 : ℤ) ^ genericDeltaExponent 1 b c n := by
  rw [DeltaABC_eq_sum_visible_bitSign_of_a_eq_one (b := b) (c := c) (n := n) hb hc]
  rw [sum_visible_bitSign_eq_card_of_even (b := b) (c := c) (n := n) hb hc hn]
  have hcard :
      (Fintype.card (ScalarVisibleCompat b c n) : ℤ) =
        (2 : ℤ) ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
    rw [card_scalarVisibleSpace_closed (b := b) (c := c) (n := n) hb hc]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ b + n ^ c + (n - 1) ^ 2))
  rw [hcard, ← pow_add]
  simpa [add_assoc, add_left_comm, add_comm] using
    (genericDeltaExponent_a_eq_one (b := b) (c := c) (n := n) hb hc).symm

theorem DeltaABC_generic_closed_of_a_eq_one {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    DeltaABC 1 b c n = (2 : ℤ) ^ genericDeltaExponent 1 b c n := by
  by_cases hn : Even n
  · exact DeltaABC_generic_closed_of_a_eq_one_of_even (b := b) (c := c) (n := n) hb hc hn
  · exact DeltaABC_generic_closed_of_a_eq_one_of_odd
      (b := b) (c := c) (n := n) hb hc ((Nat.not_even_iff_odd).1 hn)

theorem sum_visible_bitSign_eq_card_of_eq_one_eq_one {n : ℕ} [NeZero n] :
    ∑ bc : ScalarVisibleCompat 1 1 n,
      bitSign (qScalar (b := 1) (c := 1) (n := n) bc.bcoef bc.ccoef) =
        Fintype.card (ScalarVisibleCompat 1 1 n) := by
  classical
  calc
    ∑ bc : ScalarVisibleCompat 1 1 n,
        bitSign (qScalar (b := 1) (c := 1) (n := n) bc.bcoef bc.ccoef)
        =
      ∑ _bc : ScalarVisibleCompat 1 1 n, (1 : ℤ) := by
          refine Finset.sum_congr rfl ?_
          intro bc hbc
          exact (bitSign_eq_one_iff_eq_zero _).2
            (qScalar_eq_zero_on_visible_of_eq_one_eq_one (n := n) bc)
    _ = Fintype.card (ScalarVisibleCompat 1 1 n) := by
          simp

theorem DeltaABC_generic_closed_of_a_eq_one_of_eq_one_eq_one {n : ℕ} [NeZero n] :
    DeltaABC 1 1 1 n = (2 : ℤ) ^ genericDeltaExponent 1 1 1 n := by
  rw [DeltaABC_eq_sum_visible_bitSign_of_a_eq_one (b := 1) (c := 1) (n := n) (by omega) (by omega)]
  rw [sum_visible_bitSign_eq_card_of_eq_one_eq_one (n := n)]
  have hcard :
      (Fintype.card (ScalarVisibleCompat 1 1 n) : ℤ) =
        (2 : ℤ) ^ (n ^ 1 + n ^ 1 + (n - 1) ^ 2) := by
    rw [card_scalarVisibleSpace_closed (b := 1) (c := 1) (n := n) (by omega) (by omega)]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ 1 + n ^ 1 + (n - 1) ^ 2))
  rw [hcard, ← pow_add]
  simpa [add_assoc, add_left_comm, add_comm] using
    (genericDeltaExponent_a_eq_one (b := 1) (c := 1) (n := n) (by omega) (by omega)).symm

end Core3loop
