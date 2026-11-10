import Core3loop.ProfileKernels

namespace Core3loop

abbrev BWoddBCoefABC (a c n : ℕ) [NeZero n] :=
  { bcoef : BCoefABC a c n // ∀ t z, bcoef t z ∈ Wodd (a := a) (n := n) }

abbrev CWoddCCoefABC (a b n : ℕ) [NeZero n] :=
  { ccoef : CCoefABC a b n // ∀ y r, ccoef y r ∈ Wodd (a := a) (n := n) }

lemma sigmaBCoefABC_add {a c n : ℕ} [NeZero n]
    (b₁ b₂ : BCoefABC a c n) :
    sigmaBCoefABC (a := a) (c := c) (n := n) (b₁ + b₂) =
      sigmaBCoefABC (a := a) (c := c) (n := n) b₁ +
        sigmaBCoefABC (a := a) (c := c) (n := n) b₂ := by
  funext t z
  change ∑ p : XCoord a n, (b₁ t z + b₂ t z) p =
    (∑ p : XCoord a n, b₁ t z p) + ∑ p : XCoord a n, b₂ t z p
  simp [Pi.add_apply, Finset.sum_add_distrib]

lemma sigmaCCoefABC_add {a b n : ℕ} [NeZero n]
    (c₁ c₂ : CCoefABC a b n) :
    sigmaCCoefABC (a := a) (b := b) (n := n) (c₁ + c₂) =
      sigmaCCoefABC (a := a) (b := b) (n := n) c₁ +
        sigmaCCoefABC (a := a) (b := b) (n := n) c₂ := by
  funext y r
  change ∑ p : XCoord a n, (c₁ y r + c₂ y r) p =
    (∑ p : XCoord a n, c₁ y r p) + ∑ p : XCoord a n, c₂ y r p
  simp [Pi.add_apply, Finset.sum_add_distrib]

lemma sigmaBCoefABC_profileLiftScalar_of_odd {a c n : ℕ} [NeZero n]
    (hn : Odd n) (bcoef : ScalarBCoef c n) :
    sigmaBCoefABC (a := a) (c := c) (n := n)
      (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) bcoef) = bcoef := by
  funext t z
  change sigmaProfileMap (a := a) (n := n)
      (bcoef t z • oneProfile (a := a) (n := n)) = bcoef t z
  rw [LinearMap.map_smul]
  simp [sigmaProfileMap,
    sigma_oneProfile_eq_one_of_odd (a := a) (n := n) (odd_card_XCoord_of_odd (a := a) hn)]

lemma sigmaCCoefABC_profileLiftScalar_of_odd {a b n : ℕ} [NeZero n]
    (hn : Odd n) (ccoef : ScalarCCoef b n) :
    sigmaCCoefABC (a := a) (b := b) (n := n)
      (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) ccoef) = ccoef := by
  funext y r
  change sigmaProfileMap (a := a) (n := n)
      (ccoef y r • oneProfile (a := a) (n := n)) = ccoef y r
  rw [LinearMap.map_smul]
  simp [sigmaProfileMap,
    sigma_oneProfile_eq_one_of_odd (a := a) (n := n) (odd_card_XCoord_of_odd (a := a) hn)]

lemma sigmaBCoefABC_eq_zero_of_mem_BWodd {a c n : ℕ} [NeZero n]
    (bτ : BWoddBCoefABC a c n) :
    sigmaBCoefABC (a := a) (c := c) (n := n) bτ.1 = 0 := by
  funext t z
  exact sigma_eq_zero_of_mem_Wodd (a := a) (n := n) (bτ.2 t z)

lemma sigmaCCoefABC_eq_zero_of_mem_CWodd {a b n : ℕ} [NeZero n]
    (cτ : CWoddCCoefABC a b n) :
    sigmaCCoefABC (a := a) (b := b) (n := n) cτ.1 = 0 := by
  funext y r
  exact sigma_eq_zero_of_mem_Wodd (a := a) (n := n) (cτ.2 y r)

lemma bProfileLinearMap_apply_eq_sigmaBCoefABC {a c n : ℕ} [NeZero n]
    (bcoef : BCoefABC a c n) (t : I n) (z : ZCoord c n) :
    No13Migration.bProfileLinearMap_abc_real (a := a) (c := c) (n := n)
      ((bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm bcoef) t z =
        sigmaBCoefABC (a := a) (c := c) (n := n) bcoef t z +
          sigmaBCoefABC (a := a) (c := c) (n := n) bcoef (t + 1) z := by
  change ∑ p : XCoord a n, (((bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm bcoef)
      (p, t, z) +
        ((bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm bcoef) (p, t + 1, z)) =
      (∑ p : XCoord a n, bcoef t z p) + ∑ p : XCoord a n, bcoef (t + 1) z p
  simp [bFieldEquivBCoefABC, Finset.sum_add_distrib]

lemma cProfileLinearMap_apply_eq_sigmaCCoefABC {a b n : ℕ} [NeZero n]
    (ccoef : CCoefABC a b n) (y : YCoord b n) (r : I n) :
    No13Migration.cProfileLinearMap_abc_real (a := a) (b := b) (n := n)
      ((cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm ccoef) y r =
        sigmaCCoefABC (a := a) (b := b) (n := n) ccoef y r +
          sigmaCCoefABC (a := a) (b := b) (n := n) ccoef y (r + 1) := by
  change ∑ p : XCoord a n, (((cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm ccoef)
      (p, y, r) +
        ((cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm ccoef) (p, y, r + 1)) =
      (∑ p : XCoord a n, ccoef y r p) + ∑ p : XCoord a n, ccoef y (r + 1) p
  simp [cFieldEquivCCoefABC, Finset.sum_add_distrib]

lemma bProfileKernel_sigma_succ_eq {a c n : ℕ} [NeZero n]
    (kB : BProfileKernelABC a c n) (t : I n) (z : ZCoord c n) :
    sigmaBCoefABC (a := a) (c := c) (n := n)
      (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) (t + 1) z =
      sigmaBCoefABC (a := a) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) t z := by
  have hk : No13Migration.bProfileLinearMap_abc_real (a := a) (c := c) (n := n)
      ((bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1)) t z = 0 := by
    simpa using congrFun (congrFun (LinearMap.mem_ker.mp kB.2) t) z
  rw [bProfileLinearMap_apply_eq_sigmaBCoefABC
    (a := a) (c := c) (n := n)
    (bcoef := bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1)] at hk
  simpa using (eq_neg_of_add_eq_zero_left hk).symm

lemma cProfileKernel_sigma_succ_eq {a b n : ℕ} [NeZero n]
    (kC : CProfileKernelABC a b n) (y : YCoord b n) (r : I n) :
    sigmaCCoefABC (a := a) (b := b) (n := n)
      (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y (r + 1) =
      sigmaCCoefABC (a := a) (b := b) (n := n)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y r := by
  have hk : No13Migration.cProfileLinearMap_abc_real (a := a) (b := b) (n := n)
      ((cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1)) y r = 0 := by
    simpa using congrFun (congrFun (LinearMap.mem_ker.mp kC.2) y) r
  rw [cProfileLinearMap_apply_eq_sigmaCCoefABC
    (a := a) (b := b) (n := n)
    (ccoef := cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1)] at hk
  simpa using (eq_neg_of_add_eq_zero_left hk).symm

lemma bProfileKernel_sigma_eq_zero {a c n : ℕ} [NeZero n]
    (kB : BProfileKernelABC a c n) (t : I n) (z : ZCoord c n) :
    sigmaBCoefABC (a := a) (c := c) (n := n)
      (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) t z =
      sigmaBCoefABC (a := a) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) 0 z := by
  have hrec :
      ∀ k : ℕ, k < n →
        sigmaBCoefABC (a := a) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) (k : I n) z =
        sigmaBCoefABC (a := a) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) 0 z := by
    intro k hk
    induction' k with k ih
    · simp
    · have hk' : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hs :=
        bProfileKernel_sigma_succ_eq (a := a) (c := c) (n := n) kB (k : I n) z
      rw [show (k : I n) + 1 = ((k + 1 : ℕ) : I n) by simp [hk']] at hs
      rw [hs, ih hk']
  have ht : t.val < n := by
    simpa using ZMod.val_lt t
  simpa [ZMod.natCast_zmod_val t] using hrec t.val ht

lemma cProfileKernel_sigma_eq_zero {a b n : ℕ} [NeZero n]
    (kC : CProfileKernelABC a b n) (y : YCoord b n) (r : I n) :
    sigmaCCoefABC (a := a) (b := b) (n := n)
      (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y r =
      sigmaCCoefABC (a := a) (b := b) (n := n)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y 0 := by
  have hrec :
      ∀ k : ℕ, k < n →
        sigmaCCoefABC (a := a) (b := b) (n := n)
          (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y (k : I n) =
        sigmaCCoefABC (a := a) (b := b) (n := n)
          (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y 0 := by
    intro k hk
    induction' k with k ih
    · simp
    · have hk' : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hs :=
        cProfileKernel_sigma_succ_eq (a := a) (b := b) (n := n) kC y (k : I n)
      rw [show (k : I n) + 1 = ((k + 1 : ℕ) : I n) by simp [hk']] at hs
      rw [hs, ih hk']
  have hr : r.val < n := by
    simpa using ZMod.val_lt r
  simpa [ZMod.natCast_zmod_val r] using hrec r.val hr

noncomputable def bKernelConstPartOfOdd {a c n : ℕ} [NeZero n]
    (kB : BProfileKernelABC a c n) : ZCoord c n → F :=
  fun z =>
    sigmaBCoefABC (a := a) (c := c) (n := n)
      (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) 0 z

noncomputable def cKernelConstPartOfOdd {a b n : ℕ} [NeZero n]
    (kC : CProfileKernelABC a b n) : YCoord b n → F :=
  fun y =>
    sigmaCCoefABC (a := a) (b := b) (n := n)
      (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y 0

noncomputable def bKernelTailPartOfOdd {a c n : ℕ} [NeZero n]
    (hn : Odd n) (kB : BProfileKernelABC a c n) : BWoddBCoefABC a c n :=
  ⟨profileTailBCoefABC (a := a) (c := c) (n := n)
      (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1),
    fun t z => profileTailBCoefABC_mem_Wodd_of_odd
      (a := a) (c := c) (n := n) hn
      (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) t z⟩

noncomputable def cKernelTailPartOfOdd {a b n : ℕ} [NeZero n]
    (hn : Odd n) (kC : CProfileKernelABC a b n) : CWoddCCoefABC a b n :=
  ⟨profileTailCCoefABC (a := a) (b := b) (n := n)
      (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1),
    fun y r => profileTailCCoefABC_mem_Wodd_of_odd
      (a := a) (b := b) (n := n) hn
      (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) y r⟩

lemma bKernelConstPart_profile_eq {a c n : ℕ} [NeZero n]
    (kB : BProfileKernelABC a c n) :
    scalarBConst (bKernelConstPartOfOdd (a := a) (c := c) (n := n) kB) =
      sigmaBCoefABC (a := a) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) := by
  funext t z
  simpa [bKernelConstPartOfOdd, scalarBConst] using
    (bProfileKernel_sigma_eq_zero (a := a) (c := c) (n := n) kB t z).symm

lemma cKernelConstPart_profile_eq {a b n : ℕ} [NeZero n]
    (kC : CProfileKernelABC a b n) :
    scalarCConst (cKernelConstPartOfOdd (a := a) (b := b) (n := n) kC) =
      sigmaCCoefABC (a := a) (b := b) (n := n)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) := by
  funext y r
  simpa [cKernelConstPartOfOdd, scalarCConst] using
    (cProfileKernel_sigma_eq_zero (a := a) (b := b) (n := n) kC y r).symm

noncomputable def bProfileKernelOfConstTailOfOdd {a c n : ℕ} [NeZero n]
    (hn : Odd n) (u : ZCoord c n → F) (bτ : BWoddBCoefABC a c n) :
    BProfileKernelABC a c n := by
  refine ⟨(bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm
    (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1), ?_⟩
  apply LinearMap.mem_ker.mpr
  ext t z
  rw [bProfileLinearMap_apply_eq_sigmaBCoefABC
    (a := a) (c := c) (n := n)
    (bcoef := profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1)]
  rw [sigmaBCoefABC_add,
    sigmaBCoefABC_profileLiftScalar_of_odd (a := a) (c := c) (n := n) hn,
    sigmaBCoefABC_eq_zero_of_mem_BWodd (a := a) (c := c) (n := n) bτ]
  simp [scalarBConst, F_add_self]

noncomputable def cProfileKernelOfConstTailOfOdd {a b n : ℕ} [NeZero n]
    (hn : Odd n) (v : YCoord b n → F) (cτ : CWoddCCoefABC a b n) :
    CProfileKernelABC a b n := by
  refine ⟨(cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm
    (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1), ?_⟩
  apply LinearMap.mem_ker.mpr
  ext y r
  rw [cProfileLinearMap_apply_eq_sigmaCCoefABC
    (a := a) (b := b) (n := n)
    (ccoef := profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1)]
  rw [sigmaCCoefABC_add,
    sigmaCCoefABC_profileLiftScalar_of_odd (a := a) (b := b) (n := n) hn,
    sigmaCCoefABC_eq_zero_of_mem_CWodd (a := a) (b := b) (n := n) cτ]
  simp [scalarCConst, F_add_self]

noncomputable def bProfileKernelEquivConstTailOfOdd {a c n : ℕ} [NeZero n]
    (hn : Odd n) :
    BProfileKernelABC a c n ≃ (ZCoord c n → F) × BWoddBCoefABC a c n where
  toFun := fun kB =>
    (bKernelConstPartOfOdd (a := a) (c := c) (n := n) kB,
      bKernelTailPartOfOdd (a := a) (c := c) (n := n) hn kB)
  invFun := fun p =>
    bProfileKernelOfConstTailOfOdd (a := a) (c := c) (n := n) hn p.1 p.2
  left_inv := by
    intro kB
    apply Subtype.ext
    apply (bFieldEquivBCoefABC (a := a) (c := c) (n := n)).injective
    have hs :
        scalarBConst (bKernelConstPartOfOdd (a := a) (c := c) (n := n) kB) =
          sigmaBCoefABC (a := a) (c := c) (n := n)
            (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1) :=
      bKernelConstPart_profile_eq (a := a) (c := c) (n := n) kB
    simpa [bProfileKernelOfConstTailOfOdd, bKernelTailPartOfOdd, hs] using
      profileLiftScalarBCoefABC_add_profileTailBCoefABC
        (a := a) (c := c) (n := n)
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1)
  right_inv := by
    intro p
    rcases p with ⟨u, bτ⟩
    apply Prod.ext
    · funext z
      have hs :
          sigmaBCoefABC (a := a) (c := c) (n := n)
            (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1)
            =
          scalarBConst u := by
            rw [sigmaBCoefABC_add,
              sigmaBCoefABC_profileLiftScalar_of_odd (a := a) (c := c) (n := n) hn,
              sigmaBCoefABC_eq_zero_of_mem_BWodd (a := a) (c := c) (n := n) bτ]
            simp
      simpa [bKernelConstPartOfOdd, scalarBConst] using congrFun (congrFun hs 0) z
    · apply Subtype.ext
      funext t z p
      have hs :
          sigmaBCoefABC (a := a) (c := c) (n := n)
            (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1)
            =
          scalarBConst u := by
            rw [sigmaBCoefABC_add,
              sigmaBCoefABC_profileLiftScalar_of_odd (a := a) (c := c) (n := n) hn,
              sigmaBCoefABC_eq_zero_of_mem_BWodd (a := a) (c := c) (n := n) bτ]
            simp
      have hstz : sigmaBCoefABC (a := a) (c := c) (n := n)
          (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1) t z =
            u z := by
        simpa [scalarBConst] using congrFun (congrFun hs t) z
      have hs' :
          sigmaBCoefABC (a := a) (c := c) (n := n)
            (bτ.1 + profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u)) =
          scalarBConst u := by
        rw [sigmaBCoefABC_add,
          sigmaBCoefABC_eq_zero_of_mem_BWodd (a := a) (c := c) (n := n) bτ,
          sigmaBCoefABC_profileLiftScalar_of_odd (a := a) (c := c) (n := n) hn]
        simp
      have hs'tz : sigmaBCoefABC (a := a) (c := c) (n := n)
          (bτ.1 + profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u)) t z =
            u z := by
        simpa [scalarBConst] using congrFun (congrFun hs' t) z
      change
        (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) t z p + bτ.1 t z p) +
            profileLiftScalarBCoefABC (a := a) (c := c) (n := n)
              (sigmaBCoefABC (a := a) (c := c) (n := n)
                (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1)) t z p
          =
        bτ.1 t z p
      simp [profileLiftScalarBCoefABC, scalarBConst, oneProfile]
      calc
        u z + bτ.1 t z p +
            sigmaBCoefABC (a := a) (c := c) (n := n)
              (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1) t z
            = u z + bτ.1 t z p + u z := by
                rw [hstz]
        _ = (u z + u z) + bτ.1 t z p := by
          ac_rfl
        _ = bτ.1 t z p := by
          simp [F_add_self]

noncomputable def cProfileKernelEquivConstTailOfOdd {a b n : ℕ} [NeZero n]
    (hn : Odd n) :
    CProfileKernelABC a b n ≃ (YCoord b n → F) × CWoddCCoefABC a b n where
  toFun := fun kC =>
    (cKernelConstPartOfOdd (a := a) (b := b) (n := n) kC,
      cKernelTailPartOfOdd (a := a) (b := b) (n := n) hn kC)
  invFun := fun p =>
    cProfileKernelOfConstTailOfOdd (a := a) (b := b) (n := n) hn p.1 p.2
  left_inv := by
    intro kC
    apply Subtype.ext
    apply (cFieldEquivCCoefABC (a := a) (b := b) (n := n)).injective
    have hs :
        scalarCConst (cKernelConstPartOfOdd (a := a) (b := b) (n := n) kC) =
          sigmaCCoefABC (a := a) (b := b) (n := n)
            (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1) :=
      cKernelConstPart_profile_eq (a := a) (b := b) (n := n) kC
    simpa [cProfileKernelOfConstTailOfOdd, cKernelTailPartOfOdd, hs] using
      profileLiftScalarCCoefABC_add_profileTailCCoefABC
        (a := a) (b := b) (n := n)
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1)
  right_inv := by
    intro p
    rcases p with ⟨v, cτ⟩
    apply Prod.ext
    · funext y
      have hs :
          sigmaCCoefABC (a := a) (b := b) (n := n)
            (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1)
            =
          scalarCConst v := by
            rw [sigmaCCoefABC_add,
              sigmaCCoefABC_profileLiftScalar_of_odd (a := a) (b := b) (n := n) hn,
              sigmaCCoefABC_eq_zero_of_mem_CWodd (a := a) (b := b) (n := n) cτ]
            simp
      simpa [cKernelConstPartOfOdd, scalarCConst] using congrFun (congrFun hs y) 0
    · apply Subtype.ext
      funext y r p
      have hs :
          sigmaCCoefABC (a := a) (b := b) (n := n)
            (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1)
            =
          scalarCConst v := by
            rw [sigmaCCoefABC_add,
              sigmaCCoefABC_profileLiftScalar_of_odd (a := a) (b := b) (n := n) hn,
              sigmaCCoefABC_eq_zero_of_mem_CWodd (a := a) (b := b) (n := n) cτ]
            simp
      have hsyr : sigmaCCoefABC (a := a) (b := b) (n := n)
          (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1) y r =
            v y := by
        simpa [scalarCConst] using congrFun (congrFun hs y) r
      have hs' :
          sigmaCCoefABC (a := a) (b := b) (n := n)
            (cτ.1 + profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v)) =
          scalarCConst v := by
        rw [sigmaCCoefABC_add,
          sigmaCCoefABC_eq_zero_of_mem_CWodd (a := a) (b := b) (n := n) cτ,
          sigmaCCoefABC_profileLiftScalar_of_odd (a := a) (b := b) (n := n) hn]
        simp
      have hs'yr : sigmaCCoefABC (a := a) (b := b) (n := n)
          (cτ.1 + profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v)) y r =
            v y := by
        simpa [scalarCConst] using congrFun (congrFun hs' y) r
      change
        (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) y r p + cτ.1 y r p) +
            profileLiftScalarCCoefABC (a := a) (b := b) (n := n)
              (sigmaCCoefABC (a := a) (b := b) (n := n)
                (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1)) y r p
          =
        cτ.1 y r p
      simp [profileLiftScalarCCoefABC, scalarCConst, oneProfile]
      calc
        v y + cτ.1 y r p +
            sigmaCCoefABC (a := a) (b := b) (n := n)
              (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1) y r
            = v y + cτ.1 y r p + v y := by
                rw [hsyr]
        _ = (v y + v y) + cτ.1 y r p := by
          ac_rfl
        _ = cτ.1 y r p := by
          simp [F_add_self]

noncomputable def kernelPairEquivConstTailOfOdd {a b c n : ℕ} [NeZero n]
    (hn : Odd n) :
    KernelPairABC a b c n ≃
      ((ZCoord c n → F) × BWoddBCoefABC a c n) ×
        ((YCoord b n → F) × CWoddCCoefABC a b n) :=
  Equiv.prodCongr
    (bProfileKernelEquivConstTailOfOdd (a := a) (c := c) (n := n) hn)
    (cProfileKernelEquivConstTailOfOdd (a := a) (b := b) (n := n) hn)

end Core3loop
