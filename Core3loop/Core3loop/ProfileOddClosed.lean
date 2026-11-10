import Core3loop.ProfileOddCoords
import Core3loop.ProfileKernelFactor

open scoped BigOperators

namespace Core3loop

abbrev CoordHeadABC (b c n : ℕ) :=
  ScalarBCoef c n × ScalarBCoef c n × ScalarCCoef b n × ScalarCCoef b n

abbrev CoordDataABC (b c n m : ℕ) :=
  (Fin m → ScalarBCoef c n) × (Fin m → ScalarBCoef c n) ×
    (Fin m → ScalarCCoef b n) × (Fin m → ScalarCCoef b n)

noncomputable instance scalarBCoefFintype {c n : ℕ} [NeZero n] :
    Fintype (ScalarBCoef c n) := by
  dsimp [ScalarBCoef]
  infer_instance

noncomputable instance scalarCCoefFintype {b n : ℕ} [NeZero n] :
    Fintype (ScalarCCoef b n) := by
  dsimp [ScalarCCoef]
  infer_instance

noncomputable instance coordHeadABCFintype {b c n : ℕ} [NeZero n] :
    Fintype (CoordHeadABC b c n) := by
  dsimp [CoordHeadABC]
  infer_instance

noncomputable instance coordDataABCFintype {b c n m : ℕ} [NeZero n] :
    Fintype (CoordDataABC b c n m) := by
  dsimp [CoordDataABC]
  infer_instance

abbrev coordHeadBUABC {b c n : ℕ} (h : CoordHeadABC b c n) : ScalarBCoef c n := h.1

abbrev coordHeadBVABC {b c n : ℕ} (h : CoordHeadABC b c n) : ScalarBCoef c n := h.2.1

abbrev coordHeadCUABC {b c n : ℕ} (h : CoordHeadABC b c n) : ScalarCCoef b n := h.2.2.1

abbrev coordHeadCVABC {b c n : ℕ} (h : CoordHeadABC b c n) : ScalarCCoef b n := h.2.2.2

abbrev coordBUABC {b c n m : ℕ} (d : CoordDataABC b c n m) : Fin m → ScalarBCoef c n := d.1

abbrev coordBVABC {b c n m : ℕ} (d : CoordDataABC b c n m) : Fin m → ScalarBCoef c n := d.2.1

abbrev coordCUABC {b c n m : ℕ} (d : CoordDataABC b c n m) : Fin m → ScalarCCoef b n := d.2.2.1

abbrev coordCVABC {b c n m : ℕ} (d : CoordDataABC b c n m) : Fin m → ScalarCCoef b n := d.2.2.2

noncomputable def coordHeadSignABC {b c n : ℕ} [NeZero n] (h : CoordHeadABC b c n) : ℤ :=
  bitSign
    (qScalar (b := b) (c := c) (n := n) (coordHeadBUABC h) (coordHeadCVABC h) +
      qScalar (b := b) (c := c) (n := n) (coordHeadBVABC h) (coordHeadCUABC h))

noncomputable def coordDataSignABC {b c n m : ℕ} [NeZero n] (d : CoordDataABC b c n m) : ℤ :=
  bitSign
    (∑ i : Fin m,
      (qScalar (b := b) (c := c) (n := n) (coordBUABC d i) (coordCVABC d i) +
        qScalar (b := b) (c := c) (n := n) (coordBVABC d i) (coordCUABC d i)))

noncomputable def coordDataSuccEquivABC {b c n m : ℕ} :
    CoordDataABC b c n (m + 1) ≃ CoordHeadABC b c n × CoordDataABC b c n m where
  toFun d :=
    ((coordBUABC d 0, coordBVABC d 0, coordCUABC d 0, coordCVABC d 0),
      (Fin.tail (coordBUABC d), Fin.tail (coordBVABC d),
        Fin.tail (coordCUABC d), Fin.tail (coordCVABC d)))
  invFun x :=
    ((Fin.cons (coordHeadBUABC x.1) (coordBUABC x.2)),
      (Fin.cons (coordHeadBVABC x.1) (coordBVABC x.2)),
      (Fin.cons (coordHeadCUABC x.1) (coordCUABC x.2)),
      (Fin.cons (coordHeadCVABC x.1) (coordCVABC x.2)))
  left_inv d := by
    rcases d with ⟨BU, BV, CU, CV⟩
    change
      ((Fin.cons (BU 0) (Fin.tail BU)),
        (Fin.cons (BV 0) (Fin.tail BV)),
        (Fin.cons (CU 0) (Fin.tail CU)),
        (Fin.cons (CV 0) (Fin.tail CV))) = (BU, BV, CU, CV)
    simp [Fin.cons_self_tail]
  right_inv x := by
    rcases x with ⟨⟨BU, BV, CU, CV⟩, ⟨BUt, BVt, CUt, CVt⟩⟩
    ext <;> simp [coordBUABC, coordBVABC, coordCUABC, coordCVABC,
      coordHeadBUABC, coordHeadBVABC, coordHeadCUABC, coordHeadCVABC, Fin.tail_cons]

lemma coordDataSignABC_succ {b c n m : ℕ} [NeZero n]
    (h : CoordHeadABC b c n) (d : CoordDataABC b c n m) :
    coordDataSignABC ((coordDataSuccEquivABC (b := b) (c := c) (n := n) (m := m)).symm (h, d)) =
      coordHeadSignABC h * coordDataSignABC d := by
  rcases h with ⟨BU, BV, CU, CV⟩
  rcases d with ⟨BUt, BVt, CUt, CVt⟩
  simpa [coordDataSignABC, coordHeadSignABC, coordDataSuccEquivABC, Fin.sum_univ_succ, add_assoc]
    using
      (No13Migration.bitSign_add
        (qScalar (b := b) (c := c) (n := n) BU CV +
          qScalar (b := b) (c := c) (n := n) BV CU)
        (∑ i : Fin m,
          (qScalar (b := b) (c := c) (n := n) (BUt i) (CVt i) +
            qScalar (b := b) (c := c) (n := n) (BVt i) (CUt i))))

noncomputable def ordinaryPairValueABC {b c n : ℕ} [NeZero n] : ℤ :=
  ∑ bcoef : ScalarBCoef c n, ∑ bcoef' : ScalarBCoef c n,
    ∑ ccoef : ScalarCCoef b n, ∑ ccoef' : ScalarCCoef b n,
      bitSign (qScalar (b := b) (c := c) (n := n) bcoef ccoef' +
        qScalar (b := b) (c := c) (n := n) bcoef' ccoef)

def ordinaryPairExponentABC (b c n : ℕ) : ℕ :=
  2 * (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1))

lemma sum_coordHeadSignABC_eq_ordinaryPairValueABC {b c n : ℕ} [NeZero n] :
    ∑ h : CoordHeadABC b c n, coordHeadSignABC h = ordinaryPairValueABC (b := b) (c := c) (n := n) := by
  calc
    ∑ h : CoordHeadABC b c n, coordHeadSignABC h
        = ∑ bcoef : ScalarBCoef c n,
            ∑ r : ScalarBCoef c n × (ScalarCCoef b n × ScalarCCoef b n),
              bitSign
                (qScalar (b := b) (c := c) (n := n) bcoef r.2.2 +
                  qScalar (b := b) (c := c) (n := n) r.1 r.2.1) := by
            simpa [CoordHeadABC, coordHeadSignABC] using
              (Fintype.sum_prod_type'
                (f := fun bcoef : ScalarBCoef c n =>
                  fun r : ScalarBCoef c n × (ScalarCCoef b n × ScalarCCoef b n) =>
                    bitSign
                      (qScalar (b := b) (c := c) (n := n) bcoef r.2.2 +
                        qScalar (b := b) (c := c) (n := n) r.1 r.2.1)))
    _ =
      ∑ bcoef : ScalarBCoef c n, ∑ bcoef' : ScalarBCoef c n,
        ∑ r : ScalarCCoef b n × ScalarCCoef b n,
          bitSign
            (qScalar (b := b) (c := c) (n := n) bcoef r.2 +
              qScalar (b := b) (c := c) (n := n) bcoef' r.1) := by
            refine Finset.sum_congr rfl ?_
            intro bcoef hbcoef
            simpa using
              (Fintype.sum_prod_type'
                (f := fun bcoef' : ScalarBCoef c n =>
                  fun r : ScalarCCoef b n × ScalarCCoef b n =>
                    bitSign
                      (qScalar (b := b) (c := c) (n := n) bcoef r.2 +
                        qScalar (b := b) (c := c) (n := n) bcoef' r.1)))
    _ = ordinaryPairValueABC (b := b) (c := c) (n := n) := by
          unfold ordinaryPairValueABC
          refine Finset.sum_congr rfl ?_
          intro bcoef hbcoef
          refine Finset.sum_congr rfl ?_
          intro bcoef' hbcoef'
          simpa using
            (Fintype.sum_prod_type'
              (f := fun ccoef : ScalarCCoef b n =>
                fun ccoef' : ScalarCCoef b n =>
                  bitSign
                    (qScalar (b := b) (c := c) (n := n) bcoef ccoef' +
                      qScalar (b := b) (c := c) (n := n) bcoef' ccoef)))

lemma ordinaryPairValueABC_eq_closed_form {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    ordinaryPairValueABC (b := b) (c := c) (n := n) =
      (2 : ℤ) ^ ordinaryPairExponentABC b c n := by
  simpa [ordinaryPairValueABC, ordinaryPairExponentABC] using
    (ordinary_pair_sum_closed (b := b) (c := c) (n := n) hb hc)

lemma sum_coordDataSignABC_eq_pow {b c n : ℕ} [NeZero n] :
    ∀ m : ℕ, ∑ d : CoordDataABC b c n m, coordDataSignABC d =
      (ordinaryPairValueABC (b := b) (c := c) (n := n)) ^ m
  | 0 => by
      haveI : Subsingleton (CoordDataABC b c n 0) := by
        dsimp [CoordDataABC]
        infer_instance
      have hcard : Fintype.card (CoordDataABC b c n 0) = 1 := by
        exact Fintype.card_ofSubsingleton (default : CoordDataABC b c n 0)
      simp [coordDataSignABC, No13Migration.bitSign_zero, hcard]
  | m + 1 => by
      calc
        ∑ d : CoordDataABC b c n (m + 1), coordDataSignABC d
            =
          ∑ x : CoordHeadABC b c n × CoordDataABC b c n m,
            coordDataSignABC
              ((coordDataSuccEquivABC (b := b) (c := c) (n := n) (m := m)).symm x) := by
                refine Fintype.sum_equiv (coordDataSuccEquivABC (b := b) (c := c) (n := n) (m := m))
                  (fun d => coordDataSignABC d)
                  (fun x =>
                    coordDataSignABC
                      ((coordDataSuccEquivABC (b := b) (c := c) (n := n) (m := m)).symm x)) ?_
                intro d
                simp
        _ =
          ∑ x : CoordHeadABC b c n × CoordDataABC b c n m,
            coordHeadSignABC x.1 * coordDataSignABC x.2 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rcases x with ⟨h, d⟩
              simpa using coordDataSignABC_succ (b := b) (c := c) (n := n) (m := m) h d
        _ =
          ∑ h : CoordHeadABC b c n, ∑ d : CoordDataABC b c n m,
            coordHeadSignABC h * coordDataSignABC d := by
              simpa using
                (Fintype.sum_prod_type'
                  (f := fun h : CoordHeadABC b c n =>
                    fun d : CoordDataABC b c n m =>
                      coordHeadSignABC h * coordDataSignABC d))
        _ =
          ∑ h : CoordHeadABC b c n,
            coordHeadSignABC h * ∑ d : CoordDataABC b c n m, coordDataSignABC d := by
              refine Finset.sum_congr rfl ?_
              intro h hh
              rw [← Finset.mul_sum]
        _ =
          (∑ h : CoordHeadABC b c n, coordHeadSignABC h) *
            ∑ d : CoordDataABC b c n m, coordDataSignABC d := by
              rw [Finset.sum_mul]
        _ =
          ordinaryPairValueABC (b := b) (c := c) (n := n) *
            (ordinaryPairValueABC (b := b) (c := c) (n := n)) ^ m := by
              rw [sum_coordHeadSignABC_eq_ordinaryPairValueABC, sum_coordDataSignABC_eq_pow]
        _ =
          (ordinaryPairValueABC (b := b) (c := c) (n := n)) ^ (m + 1) := by
              simp [pow_succ, mul_comm]

noncomputable def coordDataPackEquivABC {b c n m : ℕ} :
    ((Fin m → ScalarBCoef c n) × (Fin m → ScalarBCoef c n)) ×
      ((Fin m → ScalarCCoef b n) × (Fin m → ScalarCCoef b n)) ≃
        CoordDataABC b c n m where
  toFun x := (x.1.1, x.1.2, x.2.1, x.2.2)
  invFun d := ((coordBUABC d, coordBVABC d), (coordCUABC d, coordCVABC d))
  left_inv x := by
    rcases x with ⟨⟨BU, BV⟩, CU, CV⟩
    rfl
  right_inv d := by
    rcases d with ⟨BU, BV, CU, CV⟩
    rfl

noncomputable def woddCoordDataEquivABC {a b c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    BWoddBCoefABC a c n × CWoddCCoefABC a b n ≃ CoordDataABC b c n m :=
  (Equiv.prodCongr
      (oddCoordBCoefEquivBWoddBCoefABC (a := a) (c := c) (n := n) (m := m) hm)
      (oddCoordCCoefEquivCWoddCCoefABC (a := a) (b := b) (n := n) (m := m) hm)).trans
    (coordDataPackEquivABC (b := b) (c := c) (n := n) (m := m))

lemma oddPureTailSignSumABC_eq_sum_coordDataSignABC {a b c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) =
      ∑ d : CoordDataABC b c n m, coordDataSignABC d := by
  unfold oddPureTailSignSumABC
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (woddCoordDataEquivABC (a := a) (b := b) (c := c) (n := n) (m := m) hm)
    (fun x => bitSign (qProfileABC (a := a) (b := b) (c := c) (n := n) x.1.1 x.2.1))
    (fun d => coordDataSignABC d) ?_
  intro x
  rcases x with ⟨bτ, cτ⟩
  simpa [coordDataSignABC, woddCoordDataEquivABC, coordDataPackEquivABC] using
    congrArg bitSign
      (qProfileABC_eq_sum_qScalar_of_odd_coords
        (a := a) (b := b) (c := c) (n := n) (m := m) hm bτ cτ)

lemma oddPureTailSignSumABC_eq_ordinaryPairValueABC_pow {a b c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) =
      (ordinaryPairValueABC (b := b) (c := c) (n := n)) ^ m := by
  rw [oddPureTailSignSumABC_eq_sum_coordDataSignABC (a := a) (b := b) (c := c) (n := n) (m := m) hm]
  exact sum_coordDataSignABC_eq_pow (b := b) (c := c) (n := n) m

lemma oddPureTailSignSumABC_eq_closed_form {a b c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) (hb : 0 < b) (hc : 0 < c) :
    oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) =
      (2 : ℤ) ^ (ordinaryPairExponentABC b c n * m) := by
  rw [oddPureTailSignSumABC_eq_ordinaryPairValueABC_pow
    (a := a) (b := b) (c := c) (n := n) (m := m) hm]
  rw [ordinaryPairValueABC_eq_closed_form (b := b) (c := c) (n := n) hb hc, pow_mul]

end Core3loop
