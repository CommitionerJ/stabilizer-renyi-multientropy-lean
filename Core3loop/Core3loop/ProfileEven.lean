import Core3loop.ProfileEvenKernel

open scoped BigOperators

namespace Core3loop

noncomputable def evenHeadBPairABC {a c n : ℕ} [NeZero n] (bcoef : BCoefABC a c n) :
    ScalarBCoef c n × ScalarBCoef c n :=
  (fun t z => (evenPairMap (a := a) (n := n) (bcoef t z)).1,
    fun t z => (evenPairMap (a := a) (n := n) (bcoef t z)).2)

noncomputable def evenHeadCPairABC {a b n : ℕ} [NeZero n] (ccoef : CCoefABC a b n) :
    ScalarCCoef b n × ScalarCCoef b n :=
  (fun y r => (evenPairMap (a := a) (n := n) (ccoef y r)).1,
    fun y r => (evenPairMap (a := a) (n := n) (ccoef y r)).2)

lemma fst_evenHeadBPairABC_eq_sigmaBCoefABC {a c n : ℕ} [NeZero n] (bcoef : BCoefABC a c n) :
    (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1 =
      sigmaBCoefABC (a := a) (c := c) (n := n) bcoef := by
  funext t z
  simpa [evenHeadBPairABC, sigmaBCoefABC, evenPairMap, eProfile] using
    (sigma_eq_dot_oneProfile (a := a) (n := n) (bcoef t z)).symm

lemma fst_evenHeadCPairABC_eq_sigmaCCoefABC {a b n : ℕ} [NeZero n] (ccoef : CCoefABC a b n) :
    (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1 =
      sigmaCCoefABC (a := a) (b := b) (n := n) ccoef := by
  funext y r
  simpa [evenHeadCPairABC, sigmaCCoefABC, evenPairMap, eProfile] using
    (sigma_eq_dot_oneProfile (a := a) (n := n) (ccoef y r)).symm

noncomputable def evenVisibleBCoefABC {a c n : ℕ} [NeZero n] (bcoef : BCoefABC a c n) :
    BCoefABC a c n :=
  fun t z =>
    (evenPlaneCoordInv (a := a) (n := n)
      ((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1 t z,
        (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).2 t z)).1

noncomputable def evenVisibleCCoefABC {a b n : ℕ} [NeZero n] (ccoef : CCoefABC a b n) :
    CCoefABC a b n :=
  fun y r =>
    (evenPlaneCoordInv (a := a) (n := n)
      ((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1 y r,
        (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).2 y r)).1

noncomputable def evenTailBCoefABC {a c n : ℕ} [NeZero n] (bcoef : BCoefABC a c n) :
    BCoefABC a c n :=
  fun t z => bcoef t z + evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef t z

noncomputable def evenTailCCoefABC {a b n : ℕ} [NeZero n] (ccoef : CCoefABC a b n) :
    CCoefABC a b n :=
  fun y r => ccoef y r + evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y r

lemma evenPair_evenVisibleBCoefABC_eq {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (bcoef : BCoefABC a c n) (t : I n) (z : ZCoord c n) :
    evenPairMap (a := a) (n := n)
      (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef t z)
      =
    ((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1 t z,
      (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).2 t z) := by
  simpa [evenVisibleBCoefABC] using
    evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2
      (((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1 t z),
        ((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).2 t z))

lemma evenPair_evenVisibleCCoefABC_eq {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (ccoef : CCoefABC a b n) (y : YCoord b n) (r : I n) :
    evenPairMap (a := a) (n := n)
      (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y r)
      =
    ((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1 y r,
      (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).2 y r) := by
  simpa [evenVisibleCCoefABC] using
    evenPlaneCoordMap_inv_apply (a := a) (n := n) hn ha2
      (((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1 y r),
        ((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).2 y r))

lemma evenTailBCoefABC_mem_Ueven {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (bcoef : BCoefABC a c n) (t : I n) (z : ZCoord c n) :
    evenTailBCoefABC (a := a) (c := c) (n := n) bcoef t z ∈ Ueven (a := a) (n := n) := by
  change evenPairMap (a := a) (n := n)
      (bcoef t z + evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef t z) = 0
  rw [LinearMap.map_add, evenPair_evenVisibleBCoefABC_eq (a := a) (c := c) (n := n) hn ha2 bcoef t z]
  change evenPairMap (a := a) (n := n) (bcoef t z) +
      ((evenPairMap (a := a) (n := n) (bcoef t z)).1,
        (evenPairMap (a := a) (n := n) (bcoef t z)).2) = 0
  ext <;> simp [F_add_self]

lemma evenTailCCoefABC_mem_Ueven {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (ccoef : CCoefABC a b n) (y : YCoord b n) (r : I n) :
    evenTailCCoefABC (a := a) (b := b) (n := n) ccoef y r ∈ Ueven (a := a) (n := n) := by
  change evenPairMap (a := a) (n := n)
      (ccoef y r + evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y r) = 0
  rw [LinearMap.map_add, evenPair_evenVisibleCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 ccoef y r]
  change evenPairMap (a := a) (n := n) (ccoef y r) +
      ((evenPairMap (a := a) (n := n) (ccoef y r)).1,
        (evenPairMap (a := a) (n := n) (ccoef y r)).2) = 0
  ext <;> simp [F_add_self]

lemma evenVisibleBCoefABC_add_evenTailBCoefABC {a c n : ℕ} [NeZero n] (bcoef : BCoefABC a c n) :
    evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef +
      evenTailBCoefABC (a := a) (c := c) (n := n) bcoef = bcoef := by
  funext t z p
  simp [evenTailBCoefABC, add_assoc, add_left_comm, add_comm, F_add_self]

lemma evenVisibleCCoefABC_add_evenTailCCoefABC {a b n : ℕ} [NeZero n] (ccoef : CCoefABC a b n) :
    evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef +
      evenTailCCoefABC (a := a) (b := b) (n := n) ccoef = ccoef := by
  funext y r p
  simp [evenTailCCoefABC, add_assoc, add_left_comm, add_comm, F_add_self]

noncomputable def evenTailBModelOfBCoefABC {a c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (bcoef : BCoefABC a c n) : EvenTailBModelABC a c n :=
  fun t z =>
    ⟨evenTailBCoefABC (a := a) (c := c) (n := n) bcoef t z,
      evenTailBCoefABC_mem_Ueven (a := a) (c := c) (n := n) hn ha2 bcoef t z⟩

noncomputable def evenTailCModelOfCCoefABC {a b n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (ccoef : CCoefABC a b n) : EvenTailCModelABC a b n :=
  fun y r =>
    ⟨evenTailCCoefABC (a := a) (b := b) (n := n) ccoef y r,
      evenTailCCoefABC_mem_Ueven (a := a) (b := b) (n := n) hn ha2 ccoef y r⟩

lemma sum_sumYZ_mul_eq_qLeftScalar {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y) z * ccoef y (sumZ z) =
      qLeftScalar (b := b) (c := c) (n := n) bcoef ccoef := by
  unfold qLeftScalar Cagg
  calc
    ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y) z * ccoef y (sumZ z)
      = ∑ z : ZCoord c n, ∑ y : YCoord b n, bcoef (sumY y) z * ccoef y (sumZ z) := by
          rw [Finset.sum_comm]
    _ = ∑ z : ZCoord c n, ∑ t : I n, ∑ y : YCoord b n,
          if sumY y = t then bcoef t z * ccoef y (sumZ z) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y hy
          have hsingle :
              (∑ t : I n, if sumY y = t then bcoef t z * ccoef y (sumZ z) else 0) =
                bcoef (sumY y) z * ccoef y (sumZ z) := by
            classical
            simpa [eq_comm] using
              (Fintype.sum_eq_single (a := sumY y)
                (f := fun t : I n =>
                  if sumY y = t then bcoef t z * ccoef y (sumZ z) else 0)
                (fun t hty => by simp [hty, eq_comm]))
          symm
          exact hsingle
    _ = ∑ z : ZCoord c n, ∑ t : I n,
          bcoef t z * ∑ y : YCoord b n, if sumY y = t then ccoef y (sumZ z) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          refine Finset.sum_congr rfl ?_
          intro t ht
          symm
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro y hy
          by_cases hyt : sumY y = t <;> simp [hyt, mul_assoc]
    _ = ∑ t : I n, ∑ z : ZCoord c n,
          bcoef t z * ∑ y : YCoord b n, if sumY y = t then ccoef y (sumZ z) else 0 := by
          rw [Finset.sum_comm]

lemma sum_sumYZ_shift_mul_eq_qRightScalar {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) =
      qRightScalar (b := b) (c := c) (n := n) bcoef ccoef := by
  unfold qRightScalar Cagg
  calc
    ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1)
      = ∑ z : ZCoord c n, ∑ y : YCoord b n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
          rw [Finset.sum_comm]
    _ = ∑ z : ZCoord c n, ∑ s : I n, ∑ y : YCoord b n,
          if sumY y = s then bcoef (s + 1) z * ccoef y (sumZ z + 1) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro y hy
          have hsingle :
              (∑ s : I n, if sumY y = s then bcoef (s + 1) z * ccoef y (sumZ z + 1) else 0) =
                bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
            classical
            simpa [eq_comm] using
              (Fintype.sum_eq_single (a := sumY y)
                (f := fun s : I n =>
                  if sumY y = s then bcoef (s + 1) z * ccoef y (sumZ z + 1) else 0)
                (fun s hsy => by simp [hsy, eq_comm]))
          symm
          exact hsingle
    _ = ∑ z : ZCoord c n, ∑ s : I n,
          bcoef (s + 1) z * ∑ y : YCoord b n, if sumY y = s then ccoef y (sumZ z + 1) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          refine Finset.sum_congr rfl ?_
          intro s hs
          symm
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro y hy
          by_cases hys : sumY y = s <;> simp [hys, mul_assoc]
    _ = ∑ z : ZCoord c n, ∑ t : I n,
          bcoef t z * ∑ y : YCoord b n, if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          simpa [add_assoc, add_comm] using
            (sum_reindex_addLeft (n := n) (a := (1 : I n))
              (f := fun t : I n =>
                bcoef t z * ∑ y : YCoord b n,
                  if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0))
    _ = ∑ t : I n, ∑ z : ZCoord c n,
          bcoef t z * ∑ y : YCoord b n, if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0 := by
          rw [Finset.sum_comm]

noncomputable def qEvenABC {b c n : ℕ} [NeZero n]
    (bhead : ScalarBCoef c n × ScalarBCoef c n)
    (chead : ScalarCCoef b n × ScalarCCoef b n) : F :=
  qScalar (b := b) (c := c) (n := n) bhead.1 chead.1 +
    qScalar (b := b) (c := c) (n := n) bhead.1 chead.2 +
      qScalar (b := b) (c := c) (n := n) bhead.2 chead.1

lemma qProfileABC_evenVisibleBCoefABC_evenVisibleCCoefABC_eq_qEvenABC_of_even
    {a b c n : ℕ} [NeZero n] (hn : Even n) (ha2 : 2 ≤ a)
    (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef)
      (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef)
      =
    qEvenABC (b := b) (c := c) (n := n)
      (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef)
      (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef) := by
  let b1 := (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1
  let b2 := (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).2
  let c1 := (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1
  let c2 := (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).2
  have hleft :
      qLeftProfileABC (a := a) (b := b) (c := c) (n := n)
        (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef)
        (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef)
        =
      qLeftScalar (b := b) (c := c) (n := n) b1 c1 +
        qLeftScalar (b := b) (c := c) (n := n) b1 c2 +
          qLeftScalar (b := b) (c := c) (n := n) b2 c1 := by
    unfold qLeftProfileABC
    calc
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
          dotProfile (a := a) (n := n)
            (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y) z)
            (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z))
        =
          ∑ y : YCoord b n, ∑ z : ZCoord c n,
            (b1 (sumY y) z * c1 y (sumZ z) +
              b1 (sumY y) z * c2 y (sumZ z) +
                b2 (sumY y) z * c1 y (sumZ z)) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              refine Finset.sum_congr rfl ?_
              intro z hz
              have hdot :
                  dotProfile (a := a) (n := n)
                    (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y) z)
                    (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z))
                    =
                  b1 (sumY y) z *
                      (evenPairMap (a := a) (n := n)
                        (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z))).1 +
                    b1 (sumY y) z *
                      (evenPairMap (a := a) (n := n)
                        (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z))).2 +
                      b2 (sumY y) z *
                        (evenPairMap (a := a) (n := n)
                          (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z))).1 := by
                simpa [evenVisibleBCoefABC, evenHeadBPairABC, b1, b2] using
                  (dot_evenPlaneCoordInv_right (a := a) (n := n) hn ha2
                    (b1 (sumY y) z, b2 (sumY y) z)
                    (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z)))
              rw [hdot]
              rw [evenPair_evenVisibleCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 ccoef y (sumZ z)]
      _ =
          (∑ y : YCoord b n, ∑ z : ZCoord c n, b1 (sumY y) z * c1 y (sumZ z)) +
            (∑ y : YCoord b n, ∑ z : ZCoord c n, b1 (sumY y) z * c2 y (sumZ z)) +
              ∑ y : YCoord b n, ∑ z : ZCoord c n, b2 (sumY y) z * c1 y (sumZ z) := by
                simp_rw [Finset.sum_add_distrib]
      _ =
          qLeftScalar (b := b) (c := c) (n := n) b1 c1 +
            qLeftScalar (b := b) (c := c) (n := n) b1 c2 +
              qLeftScalar (b := b) (c := c) (n := n) b2 c1 := by
                rw [sum_sumYZ_mul_eq_qLeftScalar (b := b) (c := c) (n := n) b1 c1,
                  sum_sumYZ_mul_eq_qLeftScalar (b := b) (c := c) (n := n) b1 c2,
                  sum_sumYZ_mul_eq_qLeftScalar (b := b) (c := c) (n := n) b2 c1]
  have hright :
      qRightProfileABC (a := a) (b := b) (c := c) (n := n)
        (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef)
        (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef)
        =
      qRightScalar (b := b) (c := c) (n := n) b1 c1 +
        qRightScalar (b := b) (c := c) (n := n) b1 c2 +
          qRightScalar (b := b) (c := c) (n := n) b2 c1 := by
    unfold qRightProfileABC
    calc
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
          dotProfile (a := a) (n := n)
            (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y + 1) z)
            (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1))
        =
          ∑ y : YCoord b n, ∑ z : ZCoord c n,
            (b1 (sumY y + 1) z * c1 y (sumZ z + 1) +
              b1 (sumY y + 1) z * c2 y (sumZ z + 1) +
                b2 (sumY y + 1) z * c1 y (sumZ z + 1)) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              refine Finset.sum_congr rfl ?_
              intro z hz
              have hdot :
                  dotProfile (a := a) (n := n)
                    (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y + 1) z)
                    (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1))
                    =
                  b1 (sumY y + 1) z *
                      (evenPairMap (a := a) (n := n)
                        (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1))).1 +
                    b1 (sumY y + 1) z *
                      (evenPairMap (a := a) (n := n)
                        (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1))).2 +
                      b2 (sumY y + 1) z *
                        (evenPairMap (a := a) (n := n)
                          (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1))).1 := by
                simpa [evenVisibleBCoefABC, evenHeadBPairABC, b1, b2] using
                  (dot_evenPlaneCoordInv_right (a := a) (n := n) hn ha2
                    (b1 (sumY y + 1) z, b2 (sumY y + 1) z)
                    (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1)))
              rw [hdot]
              rw [evenPair_evenVisibleCCoefABC_eq (a := a) (b := b) (n := n) hn ha2 ccoef y (sumZ z + 1)]
      _ =
          (∑ y : YCoord b n, ∑ z : ZCoord c n, b1 (sumY y + 1) z * c1 y (sumZ z + 1)) +
            (∑ y : YCoord b n, ∑ z : ZCoord c n, b1 (sumY y + 1) z * c2 y (sumZ z + 1)) +
              ∑ y : YCoord b n, ∑ z : ZCoord c n, b2 (sumY y + 1) z * c1 y (sumZ z + 1) := by
                simp_rw [Finset.sum_add_distrib]
      _ =
          qRightScalar (b := b) (c := c) (n := n) b1 c1 +
            qRightScalar (b := b) (c := c) (n := n) b1 c2 +
              qRightScalar (b := b) (c := c) (n := n) b2 c1 := by
                rw [sum_sumYZ_shift_mul_eq_qRightScalar (b := b) (c := c) (n := n) b1 c1,
                  sum_sumYZ_shift_mul_eq_qRightScalar (b := b) (c := c) (n := n) b1 c2,
                  sum_sumYZ_shift_mul_eq_qRightScalar (b := b) (c := c) (n := n) b2 c1]
  unfold qProfileABC qEvenABC qScalar
  rw [hleft, hright]
  ac_rfl

lemma qProfileABC_evenVisibleBCoefABC_evenTailCCoefABC_eq_zero_of_even
    {a b c n : ℕ} [NeZero n] (hn : Even n) (ha2 : 2 ≤ a)
    (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef)
      (evenTailCCoefABC (a := a) (b := b) (n := n) ccoef)
      = 0 := by
  unfold qProfileABC qLeftProfileABC qRightProfileABC
  have hleft :
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y) z)
          (evenTailCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    simpa [evenVisibleBCoefABC, evenHeadBPairABC] using
      dot_evenPlaneCoordInv_uEven_eq_zero (a := a) (n := n) hn ha2
        (((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1 (sumY y) z),
          ((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).2 (sumY y) z))
        (evenTailCCoefABC_mem_Ueven (a := a) (b := b) (n := n) hn ha2 ccoef y (sumZ z))
  have hright :
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          (evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y + 1) z)
          (evenTailCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    simpa [evenVisibleBCoefABC, evenHeadBPairABC] using
      dot_evenPlaneCoordInv_uEven_eq_zero (a := a) (n := n) hn ha2
        (((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1 (sumY y + 1) z),
          ((evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).2 (sumY y + 1) z))
        (evenTailCCoefABC_mem_Ueven (a := a) (b := b) (n := n) hn ha2 ccoef y (sumZ z + 1))
  rw [hleft, hright]
  simp

lemma qProfileABC_evenTailBCoefABC_evenVisibleCCoefABC_eq_zero_of_even
    {a b c n : ℕ} [NeZero n] (hn : Even n) (ha2 : 2 ≤ a)
    (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (evenTailBCoefABC (a := a) (c := c) (n := n) bcoef)
      (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef)
      = 0 := by
  unfold qProfileABC qLeftProfileABC qRightProfileABC
  have hleft :
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          (evenTailBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y) z)
          (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    simpa [evenVisibleCCoefABC, evenHeadCPairABC] using
      dot_uEven_evenPlaneCoordInv_eq_zero (a := a) (n := n) hn ha2
        (evenTailBCoefABC_mem_Ueven (a := a) (c := c) (n := n) hn ha2 bcoef (sumY y) z)
        (((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1 y (sumZ z)),
          ((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).2 y (sumZ z)))
  have hright :
      ∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n)
          (evenTailBCoefABC (a := a) (c := c) (n := n) bcoef (sumY y + 1) z)
          (evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef y (sumZ z + 1)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    simpa [evenVisibleCCoefABC, evenHeadCPairABC] using
      dot_uEven_evenPlaneCoordInv_eq_zero (a := a) (n := n) hn ha2
        (evenTailBCoefABC_mem_Ueven (a := a) (c := c) (n := n) hn ha2 bcoef (sumY y + 1) z)
        (((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1 y (sumZ z + 1)),
          ((evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).2 y (sumZ z + 1)))
  rw [hleft, hright]
  simp

theorem qProfileABC_eq_qEvenABC_add_tail_of_even
    {a b c n : ℕ} [NeZero n] (hn : Even n) (ha2 : 2 ≤ a)
    (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef =
      qEvenABC (b := b) (c := c) (n := n)
        (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef)
        (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef) +
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (evenTailBCoefABC (a := a) (c := c) (n := n) bcoef)
        (evenTailCCoefABC (a := a) (b := b) (n := n) ccoef) := by
  let bν := evenVisibleBCoefABC (a := a) (c := c) (n := n) bcoef
  let cν := evenVisibleCCoefABC (a := a) (b := b) (n := n) ccoef
  let bτ := evenTailBCoefABC (a := a) (c := c) (n := n) bcoef
  let cτ := evenTailCCoefABC (a := a) (b := b) (n := n) ccoef
  have hbdecomp : bν + bτ = bcoef := by
    simpa [bν, bτ] using
      evenVisibleBCoefABC_add_evenTailBCoefABC (a := a) (c := c) (n := n) bcoef
  have hcdecomp : cν + cτ = ccoef := by
    simpa [cν, cτ] using
      evenVisibleCCoefABC_add_evenTailCCoefABC (a := a) (b := b) (n := n) ccoef
  calc
    qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef
      =
        qProfileABC (a := a) (b := b) (c := c) (n := n) (bν + bτ) (cν + cτ) := by
          rw [hbdecomp, hcdecomp]
    _ =
        qProfileABC (a := a) (b := b) (c := c) (n := n) bν cν +
          qProfileABC (a := a) (b := b) (c := c) (n := n) bν cτ +
            qProfileABC (a := a) (b := b) (c := c) (n := n) bτ cν +
              qProfileABC (a := a) (b := b) (c := c) (n := n) bτ cτ := by
                rw [qProfileABC_add_left, qProfileABC_add_right, qProfileABC_add_right]
                ac_rfl
    _ =
        qEvenABC (b := b) (c := c) (n := n)
          (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef)
          (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef) +
        qProfileABC (a := a) (b := b) (c := c) (n := n) bτ cτ := by
          rw [qProfileABC_evenVisibleBCoefABC_evenVisibleCCoefABC_eq_qEvenABC_of_even
            (a := a) (b := b) (c := c) (n := n) hn ha2 bcoef ccoef]
          rw [qProfileABC_evenVisibleBCoefABC_evenTailCCoefABC_eq_zero_of_even
            (a := a) (b := b) (c := c) (n := n) hn ha2 bcoef ccoef]
          rw [qProfileABC_evenTailBCoefABC_evenVisibleCCoefABC_eq_zero_of_even
            (a := a) (b := b) (c := c) (n := n) hn ha2 bcoef ccoef]
          simp [bν, cν, bτ, cτ]
    _ =
        qEvenABC (b := b) (c := c) (n := n)
          (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef)
          (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef) +
        qProfileABC (a := a) (b := b) (c := c) (n := n)
          (evenTailBCoefABC (a := a) (c := c) (n := n) bcoef)
          (evenTailCCoefABC (a := a) (b := b) (n := n) ccoef) := by
            simp [bτ, cτ]

end Core3loop
