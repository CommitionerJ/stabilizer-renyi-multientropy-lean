import Core3loop.ProfileFibers
import Core3loop.OddCase

open scoped BigOperators

namespace Core3loop

noncomputable def sigmaBCoefABC {a c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) : ScalarBCoef c n :=
  fun t z => sigmaProfile (a := a) (n := n) (bcoef t z)

noncomputable def sigmaCCoefABC {a b n : ℕ} [NeZero n]
    (ccoef : CCoefABC a b n) : ScalarCCoef b n :=
  fun y r => sigmaProfile (a := a) (n := n) (ccoef y r)

noncomputable def profileLiftScalarBCoefABC {a c n : ℕ}
    (bcoef : ScalarBCoef c n) : BCoefABC a c n :=
  fun t z => bcoef t z • oneProfile (a := a) (n := n)

noncomputable def profileLiftScalarCCoefABC {a b n : ℕ}
    (ccoef : ScalarCCoef b n) : CCoefABC a b n :=
  fun y r => ccoef y r • oneProfile (a := a) (n := n)

noncomputable def profileTailBCoefABC {a c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) : BCoefABC a c n :=
  fun t z => bcoef t z + profileLiftScalarBCoefABC (a := a) (c := c) (n := n)
    (sigmaBCoefABC (a := a) (c := c) (n := n) bcoef) t z

noncomputable def profileTailCCoefABC {a b n : ℕ} [NeZero n]
    (ccoef : CCoefABC a b n) : CCoefABC a b n :=
  fun y r => ccoef y r + profileLiftScalarCCoefABC (a := a) (b := b) (n := n)
    (sigmaCCoefABC (a := a) (b := b) (n := n) ccoef) y r

lemma profileLiftScalarBCoefABC_add_profileTailBCoefABC {a c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) :
    profileLiftScalarBCoefABC (a := a) (c := c) (n := n)
        (sigmaBCoefABC (a := a) (c := c) (n := n) bcoef) +
      profileTailBCoefABC (a := a) (c := c) (n := n) bcoef = bcoef := by
  funext t z p
  simp [profileLiftScalarBCoefABC, profileTailBCoefABC, sigmaBCoefABC,
    add_assoc, add_left_comm, add_comm, F_add_self]

lemma profileLiftScalarCCoefABC_add_profileTailCCoefABC {a b n : ℕ} [NeZero n]
    (ccoef : CCoefABC a b n) :
    profileLiftScalarCCoefABC (a := a) (b := b) (n := n)
        (sigmaCCoefABC (a := a) (b := b) (n := n) ccoef) +
      profileTailCCoefABC (a := a) (b := b) (n := n) ccoef = ccoef := by
  funext y r p
  simp [profileLiftScalarCCoefABC, profileTailCCoefABC, sigmaCCoefABC,
    add_assoc, add_left_comm, add_comm, F_add_self]

lemma dotProfile_smul_oneProfile_left {a n : ℕ} [NeZero n] (u : F) (x : ProfileABC a n) :
    dotProfile (a := a) (n := n) (u • oneProfile (a := a) (n := n)) x = u * sigmaProfile x := by
  rw [dot_smul_left, dot_comm, sigma_eq_dot_oneProfile]

lemma dotProfile_oneProfile_smul_right {a n : ℕ} [NeZero n] (x : ProfileABC a n) (u : F) :
    dotProfile (a := a) (n := n) x (u • oneProfile (a := a) (n := n)) = sigmaProfile x * u := by
  rw [sigma_eq_dot_oneProfile, dot_smul_right]

lemma dotProfile_smul_oneProfile_smul_oneProfile_of_odd {a n : ℕ} [NeZero n]
    (hn : Odd n) (u v : F) :
    dotProfile (a := a) (n := n) (u • oneProfile (a := a) (n := n))
      (v • oneProfile (a := a) (n := n)) = u * v := by
  rw [dot_smul_left, dot_smul_right, dot_self_eq_sigma,
    sigma_oneProfile_eq_one_of_odd (a := a) (n := n) (odd_card_XCoord_of_odd (a := a) hn)]
  simp

lemma profileTailBCoefABC_mem_Wodd_of_odd {a c n : ℕ} [NeZero n]
    (hn : Odd n) (bcoef : BCoefABC a c n) (t : I n) (z : ZCoord c n) :
    profileTailBCoefABC (a := a) (c := c) (n := n) bcoef t z ∈ Wodd (a := a) (n := n) := by
  have hone :
      sigmaProfile (a := a) (n := n) (oneProfile (a := a) (n := n)) = 1 :=
    sigma_oneProfile_eq_one_of_odd (a := a) (n := n) (odd_card_XCoord_of_odd (a := a) hn)
  change sigmaProfile (a := a) (n := n)
      (profileTailBCoefABC (a := a) (c := c) (n := n) bcoef t z) = 0
  unfold profileTailBCoefABC profileLiftScalarBCoefABC sigmaBCoefABC
  calc
    sigmaProfile (a := a) (n := n)
        (bcoef t z + sigmaProfile (a := a) (n := n) (bcoef t z) • oneProfile (a := a) (n := n))
      = sigmaProfile (a := a) (n := n) (bcoef t z) +
          sigmaProfile (a := a) (n := n)
            (sigmaProfile (a := a) (n := n) (bcoef t z) • oneProfile (a := a) (n := n)) := by
              unfold sigmaProfile
              simp [Finset.sum_add_distrib]
    _ = sigmaProfile (a := a) (n := n) (bcoef t z) +
          sigmaProfile (a := a) (n := n) (bcoef t z) := by
            have hs :
                sigmaProfile (a := a) (n := n)
                  (sigmaProfile (a := a) (n := n) (bcoef t z) • oneProfile (a := a) (n := n))
                  = sigmaProfile (a := a) (n := n) (bcoef t z) := by
              rw [sigma_eq_dot_oneProfile, dot_smul_left, dot_self_eq_sigma, hone]
              simp
            rw [hs]
    _ = 0 := F_add_self _

lemma profileTailCCoefABC_mem_Wodd_of_odd {a b n : ℕ} [NeZero n]
    (hn : Odd n) (ccoef : CCoefABC a b n) (y : YCoord b n) (r : I n) :
    profileTailCCoefABC (a := a) (b := b) (n := n) ccoef y r ∈ Wodd (a := a) (n := n) := by
  have hone :
      sigmaProfile (a := a) (n := n) (oneProfile (a := a) (n := n)) = 1 :=
    sigma_oneProfile_eq_one_of_odd (a := a) (n := n) (odd_card_XCoord_of_odd (a := a) hn)
  change sigmaProfile (a := a) (n := n)
      (profileTailCCoefABC (a := a) (b := b) (n := n) ccoef y r) = 0
  unfold profileTailCCoefABC profileLiftScalarCCoefABC sigmaCCoefABC
  calc
    sigmaProfile (a := a) (n := n)
        (ccoef y r + sigmaProfile (a := a) (n := n) (ccoef y r) • oneProfile (a := a) (n := n))
      = sigmaProfile (a := a) (n := n) (ccoef y r) +
          sigmaProfile (a := a) (n := n)
            (sigmaProfile (a := a) (n := n) (ccoef y r) • oneProfile (a := a) (n := n)) := by
              unfold sigmaProfile
              simp [Finset.sum_add_distrib]
    _ = sigmaProfile (a := a) (n := n) (ccoef y r) +
          sigmaProfile (a := a) (n := n) (ccoef y r) := by
            have hs :
                sigmaProfile (a := a) (n := n)
                  (sigmaProfile (a := a) (n := n) (ccoef y r) • oneProfile (a := a) (n := n))
                  = sigmaProfile (a := a) (n := n) (ccoef y r) := by
              rw [sigma_eq_dot_oneProfile, dot_smul_left, dot_self_eq_sigma, hone]
              simp
            rw [hs]
    _ = 0 := F_add_self _

lemma qLeftProfileABC_add_left {a b c n : ℕ} [NeZero n]
    (b1 b2 : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qLeftProfileABC (a := a) (b := b) (c := c) (n := n) (b1 + b2) ccoef =
      qLeftProfileABC (a := a) (b := b) (c := c) (n := n) b1 ccoef +
        qLeftProfileABC (a := a) (b := b) (c := c) (n := n) b2 ccoef := by
  unfold qLeftProfileABC
  simp [dot_add_left, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma qLeftProfileABC_add_right {a b c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) (c1 c2 : CCoefABC a b n) :
    qLeftProfileABC (a := a) (b := b) (c := c) (n := n) bcoef (c1 + c2) =
      qLeftProfileABC (a := a) (b := b) (c := c) (n := n) bcoef c1 +
        qLeftProfileABC (a := a) (b := b) (c := c) (n := n) bcoef c2 := by
  unfold qLeftProfileABC
  simp [dot_add_right, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma qRightProfileABC_add_left {a b c n : ℕ} [NeZero n]
    (b1 b2 : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qRightProfileABC (a := a) (b := b) (c := c) (n := n) (b1 + b2) ccoef =
      qRightProfileABC (a := a) (b := b) (c := c) (n := n) b1 ccoef +
        qRightProfileABC (a := a) (b := b) (c := c) (n := n) b2 ccoef := by
  unfold qRightProfileABC
  simp [dot_add_left, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma qRightProfileABC_add_right {a b c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) (c1 c2 : CCoefABC a b n) :
    qRightProfileABC (a := a) (b := b) (c := c) (n := n) bcoef (c1 + c2) =
      qRightProfileABC (a := a) (b := b) (c := c) (n := n) bcoef c1 +
        qRightProfileABC (a := a) (b := b) (c := c) (n := n) bcoef c2 := by
  unfold qRightProfileABC
  simp [dot_add_right, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma qProfileABC_add_left {a b c n : ℕ} [NeZero n]
    (b1 b2 : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n) (b1 + b2) ccoef =
      qProfileABC (a := a) (b := b) (c := c) (n := n) b1 ccoef +
        qProfileABC (a := a) (b := b) (c := c) (n := n) b2 ccoef := by
  unfold qProfileABC
  rw [qLeftProfileABC_add_left, qRightProfileABC_add_left]
  ac_rfl

lemma qProfileABC_add_right {a b c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) (c1 c2 : CCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef (c1 + c2) =
      qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef c1 +
        qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef c2 := by
  unfold qProfileABC
  rw [qLeftProfileABC_add_right, qRightProfileABC_add_right]
  ac_rfl

lemma qLeftProfileABC_liftScalarBCoefABC_liftScalarCCoefABC_eq_qLeftScalar_of_odd
    {a b c n : ℕ} [NeZero n] (hn : Odd n)
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qLeftProfileABC (a := a) (b := b) (c := c) (n := n)
      (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bcoef)
      (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) ccoef)
      =
    qLeftScalar (b := b) (c := c) (n := n) bcoef ccoef := by
  unfold qLeftProfileABC qLeftScalar Cagg profileLiftScalarBCoefABC profileLiftScalarCCoefABC
  calc
    ∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n) (bcoef (sumY y) z • oneProfile (a := a) (n := n))
          (ccoef y (sumZ z) • oneProfile (a := a) (n := n))
      =
        ∑ y : YCoord b n, ∑ z : ZCoord c n,
          bcoef (sumY y) z * ccoef y (sumZ z) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [dotProfile_smul_oneProfile_smul_oneProfile_of_odd (a := a) (n := n) hn]
    _ = ∑ z : ZCoord c n, ∑ y : YCoord b n,
          bcoef (sumY y) z * ccoef y (sumZ z) := by
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

lemma qRightProfileABC_liftScalarBCoefABC_liftScalarCCoefABC_eq_qRightScalar_of_odd
    {a b c n : ℕ} [NeZero n] (hn : Odd n)
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qRightProfileABC (a := a) (b := b) (c := c) (n := n)
      (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bcoef)
      (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) ccoef)
      =
    qRightScalar (b := b) (c := c) (n := n) bcoef ccoef := by
  unfold qRightProfileABC qRightScalar Cagg profileLiftScalarBCoefABC profileLiftScalarCCoefABC
  calc
    ∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n) (bcoef (sumY y + 1) z • oneProfile (a := a) (n := n))
          (ccoef y (sumZ z + 1) • oneProfile (a := a) (n := n))
      =
        ∑ y : YCoord b n, ∑ z : ZCoord c n,
          bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [dotProfile_smul_oneProfile_smul_oneProfile_of_odd (a := a) (n := n) hn]
    _ = ∑ z : ZCoord c n, ∑ y : YCoord b n,
          bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
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

lemma qProfileABC_liftScalarBCoefABC_liftScalarCCoefABC_eq_qScalar_of_odd
    {a b c n : ℕ} [NeZero n] (hn : Odd n)
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bcoef)
      (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) ccoef)
      =
    qScalar (b := b) (c := c) (n := n) bcoef ccoef := by
  unfold qProfileABC qScalar
  rw [qLeftProfileABC_liftScalarBCoefABC_liftScalarCCoefABC_eq_qLeftScalar_of_odd
    (a := a) (b := b) (c := c) (n := n) hn]
  rw [qRightProfileABC_liftScalarBCoefABC_liftScalarCCoefABC_eq_qRightScalar_of_odd
    (a := a) (b := b) (c := c) (n := n) hn]

lemma qProfileABC_liftScalarBCoefABC_tail_eq_zero_of_odd {a b c n : ℕ} [NeZero n]
    (hn : Odd n) (bcoef : ScalarBCoef c n) (ccoef : CCoefABC a b n)
    (hccoef : ∀ y r, ccoef y r ∈ Wodd (a := a) (n := n)) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bcoef) ccoef = 0 := by
  have hleft :
      qLeftProfileABC (a := a) (b := b) (c := c) (n := n)
        (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bcoef) ccoef = 0 := by
    unfold qLeftProfileABC profileLiftScalarBCoefABC
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    have hs : sigmaProfile (a := a) (n := n) (ccoef y (sumZ z)) = 0 :=
      sigma_eq_zero_of_mem_Wodd (a := a) (n := n) (hccoef y (sumZ z))
    rw [dotProfile_smul_oneProfile_left, hs]
    simp
  have hright :
      qRightProfileABC (a := a) (b := b) (c := c) (n := n)
        (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bcoef) ccoef = 0 := by
    unfold qRightProfileABC profileLiftScalarBCoefABC
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    have hs : sigmaProfile (a := a) (n := n) (ccoef y (sumZ z + 1)) = 0 :=
      sigma_eq_zero_of_mem_Wodd (a := a) (n := n) (hccoef y (sumZ z + 1))
    rw [dotProfile_smul_oneProfile_left, hs]
    simp
  unfold qProfileABC
  rw [hleft, hright]
  simp

lemma qProfileABC_tail_liftScalarCCoefABC_eq_zero_of_odd {a b c n : ℕ} [NeZero n]
    (hn : Odd n) (bcoef : BCoefABC a c n) (ccoef : ScalarCCoef b n)
    (hbcoef : ∀ t z, bcoef t z ∈ Wodd (a := a) (n := n)) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      bcoef (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) ccoef) = 0 := by
  have hleft :
      qLeftProfileABC (a := a) (b := b) (c := c) (n := n)
        bcoef (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) ccoef) = 0 := by
    unfold qLeftProfileABC profileLiftScalarCCoefABC
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    have hs : sigmaProfile (a := a) (n := n) (bcoef (sumY y) z) = 0 :=
      sigma_eq_zero_of_mem_Wodd (a := a) (n := n) (hbcoef (sumY y) z)
    rw [dotProfile_oneProfile_smul_right, hs]
    simp
  have hright :
      qRightProfileABC (a := a) (b := b) (c := c) (n := n)
        bcoef (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) ccoef) = 0 := by
    unfold qRightProfileABC profileLiftScalarCCoefABC
    refine Finset.sum_eq_zero ?_
    intro y hy
    refine Finset.sum_eq_zero ?_
    intro z hz
    have hs : sigmaProfile (a := a) (n := n) (bcoef (sumY y + 1) z) = 0 :=
      sigma_eq_zero_of_mem_Wodd (a := a) (n := n) (hbcoef (sumY y + 1) z)
    rw [dotProfile_oneProfile_smul_right, hs]
    simp
  unfold qProfileABC
  rw [hleft, hright]
  simp

theorem qProfileABC_eq_qScalar_add_tail_of_odd {a b c n : ℕ} [NeZero n]
    (hn : Odd n) (bcoef : BCoefABC a c n) (ccoef : CCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef =
      qScalar (b := b) (c := c) (n := n)
        (sigmaBCoefABC (a := a) (c := c) (n := n) bcoef)
        (sigmaCCoefABC (a := a) (b := b) (n := n) ccoef) +
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (profileTailBCoefABC (a := a) (c := c) (n := n) bcoef)
        (profileTailCCoefABC (a := a) (b := b) (n := n) ccoef) := by
  let bσ := sigmaBCoefABC (a := a) (c := c) (n := n) bcoef
  let cσ := sigmaCCoefABC (a := a) (b := b) (n := n) ccoef
  let bτ := profileTailBCoefABC (a := a) (c := c) (n := n) bcoef
  let cτ := profileTailCCoefABC (a := a) (b := b) (n := n) ccoef
  have hbdecomp :
      profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bσ + bτ = bcoef := by
    simp [bσ, bτ, profileLiftScalarBCoefABC_add_profileTailBCoefABC]
  have hcdecomp :
      profileLiftScalarCCoefABC (a := a) (b := b) (n := n) cσ + cτ = ccoef := by
    simp [cσ, cτ, profileLiftScalarCCoefABC_add_profileTailCCoefABC]
  have hlift :
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bσ)
        (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) cσ) =
      qScalar (b := b) (c := c) (n := n) bσ cσ :=
    qProfileABC_liftScalarBCoefABC_liftScalarCCoefABC_eq_qScalar_of_odd
      (a := a) (b := b) (c := c) (n := n) hn bσ cσ
  have hzeroC :
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bσ) cτ = 0 :=
    qProfileABC_liftScalarBCoefABC_tail_eq_zero_of_odd (a := a) (b := b) (c := c) (n := n)
      hn bσ cτ (fun y r => by
        simpa [cτ] using
          profileTailCCoefABC_mem_Wodd_of_odd (a := a) (b := b) (n := n) hn ccoef y r)
  have hzeroB :
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        bτ (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) cσ) = 0 :=
    qProfileABC_tail_liftScalarCCoefABC_eq_zero_of_odd (a := a) (b := b) (c := c) (n := n)
      hn bτ cσ (fun t z => by
        simpa [bτ] using
          profileTailBCoefABC_mem_Wodd_of_odd (a := a) (c := c) (n := n) hn bcoef t z)
  calc
    qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef
      =
        qProfileABC (a := a) (b := b) (c := c) (n := n)
          (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bσ + bτ)
          (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) cσ + cτ) := by
            rw [← hbdecomp, ← hcdecomp]
    _ =
        qProfileABC (a := a) (b := b) (c := c) (n := n)
            (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bσ)
            (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) cσ) +
          qProfileABC (a := a) (b := b) (c := c) (n := n)
            (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bσ) cτ +
          qProfileABC (a := a) (b := b) (c := c) (n := n)
            bτ (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) cσ) +
          qProfileABC (a := a) (b := b) (c := c) (n := n) bτ cτ := by
            rw [qProfileABC_add_left, qProfileABC_add_right, qProfileABC_add_right]
            ac_rfl
    _ =
        qScalar (b := b) (c := c) (n := n) bσ cσ +
          qProfileABC (a := a) (b := b) (c := c) (n := n) bτ cτ := by
            rw [hlift, hzeroC, hzeroB]
            simp
    _ =
        qScalar (b := b) (c := c) (n := n)
          (sigmaBCoefABC (a := a) (c := c) (n := n) bcoef)
          (sigmaCCoefABC (a := a) (b := b) (n := n) ccoef) +
        qProfileABC (a := a) (b := b) (c := c) (n := n)
          (profileTailBCoefABC (a := a) (c := c) (n := n) bcoef)
          (profileTailCCoefABC (a := a) (b := b) (n := n) ccoef) := by
            simp [bσ, cσ, bτ, cτ]

lemma coeffFromBC_abc_eq_sigmaBCoef_sigmaCCoef {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) (y : YCoord b n) (z : ZCoord c n) :
    coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C (y, z) =
      sigmaBCoefABC (a := a) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B) (sumY y) z +
      sigmaBCoefABC (a := a) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B) (sumY y + 1) z +
      sigmaCCoefABC (a := a) (b := b) (n := n)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C) y (sumZ z) +
      sigmaCCoefABC (a := a) (b := b) (n := n)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C) y (sumZ z + 1) := by
  unfold coeffFromBC_abc No13Migration.coeffFromBC_abc_real sigmaBCoefABC sigmaCCoefABC
  let A : XCoord a n → F := fun p => B (p, sumY y, z)
  let B' : XCoord a n → F := fun p => B (p, sumY y + 1, z)
  let C' : XCoord a n → F := fun p => C (p, y, sumZ z)
  let D : XCoord a n → F := fun p => C (p, y, sumZ z + 1)
  change ∑ p : XCoord a n, (((A p + B' p) + C' p) + D p) =
    (∑ p : XCoord a n, A p) + (∑ p : XCoord a n, B' p) +
      (∑ p : XCoord a n, C' p) + (∑ p : XCoord a n, D p)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]

noncomputable def scalarVisibleCompatOfSurvivingBC {a b c n : ℕ} [NeZero n]
    (bc : SurvivingBC a b c n) : ScalarVisibleCompat b c n where
  bcoef := sigmaBCoefABC (a := a) (c := c) (n := n)
    (bFieldEquivBCoefABC (a := a) (c := c) (n := n) bc.1.1)
  ccoef := sigmaCCoefABC (a := a) (b := b) (n := n)
    (cFieldEquivCCoefABC (a := a) (b := b) (n := n) bc.1.2)
  compat y z := by
    have h := congrFun bc.2 (y, z)
    rw [coeffFromBC_abc_eq_sigmaBCoef_sigmaCCoef (a := a) (b := b) (c := c) (n := n)
      bc.1.1 bc.1.2 y z] at h
    exact h

theorem qProfileABC_eq_tail_of_surviving_of_odd {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (bc : SurvivingBC a b c n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (bFieldEquivBCoefABC (a := a) (c := c) (n := n) bc.1.1)
      (cFieldEquivCCoefABC (a := a) (b := b) (n := n) bc.1.2)
      =
    qProfileABC (a := a) (b := b) (c := c) (n := n)
      (profileTailBCoefABC (a := a) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) bc.1.1))
      (profileTailCCoefABC (a := a) (b := b) (n := n)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) bc.1.2)) := by
  have hzero :
      qScalar (b := b) (c := c) (n := n)
        (sigmaBCoefABC (a := a) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) bc.1.1))
        (sigmaCCoefABC (a := a) (b := b) (n := n)
          (cFieldEquivCCoefABC (a := a) (b := b) (n := n) bc.1.2)) = 0 := by
    simpa [scalarVisibleCompatOfSurvivingBC] using
    qScalar_eq_zero_on_visible_of_odd (b := b) (c := c) (n := n) hb hc hn
      (scalarVisibleCompatOfSurvivingBC (a := a) (b := b) (c := c) (n := n) bc)
  rw [qProfileABC_eq_qScalar_add_tail_of_odd (a := a) (b := b) (c := c) (n := n) hn, hzero]
  simp

theorem QpairABC_eq_qProfileABC_tail_of_surviving_of_odd {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (bc : SurvivingBC a b c n) :
    QpairABC (a := a) (b := b) (c := c) (n := n) bc.1.1 bc.1.2 =
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (profileTailBCoefABC (a := a) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) bc.1.1))
        (profileTailCCoefABC (a := a) (b := b) (n := n)
          (cFieldEquivCCoefABC (a := a) (b := b) (n := n) bc.1.2)) := by
  rw [QpairABC_eq_qProfileABC]
  exact qProfileABC_eq_tail_of_surviving_of_odd (a := a) (b := b) (c := c) (n := n)
    hb hc hn bc

end Core3loop
