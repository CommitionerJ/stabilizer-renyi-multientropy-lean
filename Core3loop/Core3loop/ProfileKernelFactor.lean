import Core3loop.ProfileKernelSplit

open scoped BigOperators

namespace Core3loop

instance BWoddBCoefABC_finite {a c n : ℕ} [NeZero n] :
    Finite (BWoddBCoefABC a c n) :=
  Finite.of_injective (Subtype.val : BWoddBCoefABC a c n → BCoefABC a c n)
    (fun _ _ h => Subtype.ext h)

noncomputable instance BWoddBCoefABC_fintype {a c n : ℕ} [NeZero n] :
    Fintype (BWoddBCoefABC a c n) :=
  Fintype.ofFinite _

instance CWoddCCoefABC_finite {a b n : ℕ} [NeZero n] :
    Finite (CWoddCCoefABC a b n) :=
  Finite.of_injective (Subtype.val : CWoddCCoefABC a b n → CCoefABC a b n)
    (fun _ _ h => Subtype.ext h)

noncomputable instance CWoddCCoefABC_fintype {a b n : ℕ} [NeZero n] :
    Fintype (CWoddCCoefABC a b n) :=
  Fintype.ofFinite _

lemma profileTailBCoefABC_add {a c n : ℕ} [NeZero n]
    (b₁ b₂ : BCoefABC a c n) :
    profileTailBCoefABC (a := a) (c := c) (n := n) (b₁ + b₂) =
      profileTailBCoefABC (a := a) (c := c) (n := n) b₁ +
        b₂ +
        profileLiftScalarBCoefABC (a := a) (c := c) (n := n)
          (sigmaBCoefABC (a := a) (c := c) (n := n) b₂) := by
  funext t z p
  simp [profileTailBCoefABC, sigmaBCoefABC_add, profileLiftScalarBCoefABC, oneProfile, mul_add,
    add_assoc, add_left_comm, add_comm]

lemma profileTailCCoefABC_add {a b n : ℕ} [NeZero n]
    (c₁ c₂ : CCoefABC a b n) :
    profileTailCCoefABC (a := a) (b := b) (n := n) (c₁ + c₂) =
      profileTailCCoefABC (a := a) (b := b) (n := n) c₁ +
        c₂ +
        profileLiftScalarCCoefABC (a := a) (b := b) (n := n)
          (sigmaCCoefABC (a := a) (b := b) (n := n) c₂) := by
  funext y r p
  simp [profileTailCCoefABC, sigmaCCoefABC_add, profileLiftScalarCCoefABC, oneProfile, mul_add,
    add_assoc, add_left_comm, add_comm]

noncomputable def baseBCoefOfHAdmissible
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : BCoefABC a c n :=
  bcoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h
    (baseBProfileFiberOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h)

noncomputable def baseCCoefOfHAdmissible
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : CCoefABC a b n :=
  ccoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h
    (baseCProfileFiberOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h)

noncomputable def baseBTailOfHAdmissible
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : BCoefABC a c n :=
  profileTailBCoefABC (a := a) (c := c) (n := n)
    (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h)

noncomputable def baseCTailOfHAdmissible
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : CCoefABC a b n :=
  profileTailCCoefABC (a := a) (b := b) (n := n)
    (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h)

lemma bcoefOfHAdmissibleFiber_of_kernel_eq_base_add
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kB : BProfileKernelABC a c n) :
    bcoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h
      (bProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kB) =
      bFieldEquivBCoefABC (a := a) (c := c) (n := n) kB.1 +
        baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h := by
  funext t z p
  simp [bcoefOfHAdmissibleFiber, baseBCoefOfHAdmissible, bProfileFiberOfKernel,
    bProfileFiberEquivKerOfHAdmissible, bProfileFiberEquivEqBaseOfHAdmissible,
    No13Migration.fiberEquivKer_bProfileABC_real, bFieldEquivBCoefABC]

lemma ccoefOfHAdmissibleFiber_of_kernel_eq_base_add
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kC : CProfileKernelABC a b n) :
    ccoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h
      (cProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kC) =
      cFieldEquivCCoefABC (a := a) (b := b) (n := n) kC.1 +
        baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h := by
  funext y r p
  simp [ccoefOfHAdmissibleFiber, baseCCoefOfHAdmissible, cProfileFiberOfKernel,
    cProfileFiberEquivKerOfHAdmissible, cProfileFiberEquivEqBaseOfHAdmissible,
    No13Migration.fiberEquivKer_cProfileABC_real, cFieldEquivCCoefABC]

lemma qProfileTailOfHAdmissibleKernels_eq_profileTailFibers
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kB : BProfileKernelABC a c n) (kC : CProfileKernelABC a b n) :
    qProfileTailOfHAdmissibleKernels (a := a) (b := b) (c := c) (n := n) hb hc h kB kC =
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (profileTailBCoefABC (a := a) (c := c) (n := n)
          (bcoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h
            (bProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kB)))
        (profileTailCCoefABC (a := a) (b := b) (n := n)
          (ccoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h
            (cProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kC))) := by
  let Bf := bProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kB
  let Cf := cProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kC
  let xh : SurvivingSigmaHAdmissibleABC a b c n hb hc := ⟨h, (Bf, Cf)⟩
  let xp : SurvivingSigmaABC a b c n :=
    (profileSigmaEquivHAdmissibleSigma (a := a) (b := b) (c := c) (n := n) hb hc).symm xh
  have hxp :
      xp = ⟨hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h, (Bf, Cf)⟩ := by
    rfl
  have hright :=
    congrArg
      (fun x : SurvivingSigmaABC a b c n =>
        qProfileABC (a := a) (b := b) (c := c) (n := n)
          (profileTailBCoefABC (a := a) (c := c) (n := n)
            (bFieldEquivBCoefABC (a := a) (c := c) (n := n) x.2.1.1))
          (profileTailCCoefABC (a := a) (b := b) (n := n)
            (cFieldEquivCCoefABC (a := a) (b := b) (n := n) x.2.2.1)))
      ((survivingBCEquivProfileSigma (a := a) (b := b) (c := c) (n := n)).right_inv xp)
  simpa [xp, xh, hxp, qProfileTailOfHAdmissibleKernels, survivingBCOfHAdmissibleKernels,
    survivingBCOfHAdmissibleFibers, survivingBCEquivHAdmissibleSigma, survivingBCEquivProfileSigma,
    profileSigmaEquivHAdmissibleSigma, hAdmissibleToProfileCompatABC,
    profileCompatABCEquivHAdmissible, bcoefOfHAdmissibleFiber, ccoefOfHAdmissibleFiber,
    bProfileFiberOfKernel, cProfileFiberOfKernel, Bf, Cf] using hright

lemma profileTail_base_add_constTailB_of_odd
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n))
    (u : ZCoord c n → F) (bτ : BWoddBCoefABC a c n) :
    profileTailBCoefABC (a := a) (c := c) (n := n)
      (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h +
        (profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1)) =
      baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1 := by
  have hbzero : sigmaBCoefABC (a := a) (c := c) (n := n) bτ.1 = 0 := by
    exact sigmaBCoefABC_eq_zero_of_mem_BWodd (a := a) (c := c) (n := n) bτ
  ext t z p
  simp [baseBTailOfHAdmissible, profileTailBCoefABC, sigmaBCoefABC_add,
    sigmaBCoefABC_profileLiftScalar_of_odd, scalarBConst, profileLiftScalarBCoefABC,
    add_assoc, add_left_comm, add_comm, oneProfile, hbzero, hn]
  calc
    u z +
        (u z +
          (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h t z p +
            (sigmaBCoefABC (a := a) (c := c) (n := n)
              (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) t z +
              bτ.1 t z p))) =
        (u z + u z) +
          (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h t z p +
            (sigmaBCoefABC (a := a) (c := c) (n := n)
              (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) t z +
              bτ.1 t z p)) := by
          ac_rfl
    _ =
        baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h t z p +
          (sigmaBCoefABC (a := a) (c := c) (n := n)
            (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) t z +
            bτ.1 t z p) := by
          simp [F_add_self]

lemma profileTail_base_add_constTailC_of_odd
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n))
    (v : YCoord b n → F) (cτ : CWoddCCoefABC a b n) :
    profileTailCCoefABC (a := a) (b := b) (n := n)
      (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h +
        (profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1)) =
      baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1 := by
  have hczero : sigmaCCoefABC (a := a) (b := b) (n := n) cτ.1 = 0 := by
    exact sigmaCCoefABC_eq_zero_of_mem_CWodd (a := a) (b := b) (n := n) cτ
  ext y r p
  simp [baseCTailOfHAdmissible, profileTailCCoefABC, sigmaCCoefABC_add,
    sigmaCCoefABC_profileLiftScalar_of_odd, scalarCConst, profileLiftScalarCCoefABC,
    add_assoc, add_left_comm, add_comm, oneProfile, hczero, hn]
  calc
    v y +
        (v y +
          (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h y r p +
            (sigmaCCoefABC (a := a) (b := b) (n := n)
              (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) y r +
              cτ.1 y r p))) =
        (v y + v y) +
          (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h y r p +
            (sigmaCCoefABC (a := a) (b := b) (n := n)
              (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) y r +
              cτ.1 y r p)) := by
          ac_rfl
    _ =
        baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h y r p +
          (sigmaCCoefABC (a := a) (b := b) (n := n)
            (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) y r +
            cτ.1 y r p) := by
          simp [F_add_self]

noncomputable def qProfileTailOfHAdmissibleConstTail
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n))
    (pB : (ZCoord c n → F) × BWoddBCoefABC a c n)
    (pC : (YCoord b n → F) × CWoddCCoefABC a b n) : F :=
  qProfileTailOfHAdmissibleKernels (a := a) (b := b) (c := c) (n := n) hb hc h
    ((bProfileKernelEquivConstTailOfOdd (a := a) (c := c) (n := n) hn).symm pB)
    ((cProfileKernelEquivConstTailOfOdd (a := a) (b := b) (n := n) hn).symm pC)

lemma qProfileTailOfHAdmissibleConstTail_eq_baseTail_add_tails_of_odd
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n))
    (u : ZCoord c n → F) (bτ : BWoddBCoefABC a c n)
    (v : YCoord b n → F) (cτ : CWoddCCoefABC a b n) :
    qProfileTailOfHAdmissibleConstTail (a := a) (b := b) (c := c) (n := n) hb hc hn h
      (u, bτ) (v, cτ) =
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
        (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1) := by
  unfold qProfileTailOfHAdmissibleConstTail
  rw [qProfileTailOfHAdmissibleKernels_eq_profileTailFibers
    (a := a) (b := b) (c := c) (n := n) hb hc h]
  have hbk :
      bFieldEquivBCoefABC (a := a) (c := c) (n := n)
        ((bProfileKernelEquivConstTailOfOdd (a := a) (c := c) (n := n) hn).symm (u, bτ)).1 =
        profileLiftScalarBCoefABC (a := a) (c := c) (n := n) (scalarBConst u) + bτ.1 := by
    rfl
  have hck :
      cFieldEquivCCoefABC (a := a) (b := b) (n := n)
        ((cProfileKernelEquivConstTailOfOdd (a := a) (b := b) (n := n) hn).symm (v, cτ)).1 =
        profileLiftScalarCCoefABC (a := a) (b := b) (n := n) (scalarCConst v) + cτ.1 := by
    rfl
  rw [bcoefOfHAdmissibleFiber_of_kernel_eq_base_add (a := a) (b := b) (c := c) (n := n) hb hc h
      ((bProfileKernelEquivConstTailOfOdd (a := a) (c := c) (n := n) hn).symm (u, bτ))]
  rw [ccoefOfHAdmissibleFiber_of_kernel_eq_base_add (a := a) (b := b) (c := c) (n := n) hb hc h
      ((cProfileKernelEquivConstTailOfOdd (a := a) (b := b) (n := n) hn).symm (v, cτ))]
  rw [hbk, hck]
  simpa [add_assoc, add_left_comm, add_comm] using
    congrArg₂
      (fun B C =>
        qProfileABC (a := a) (b := b) (c := c) (n := n) B C)
      (profileTail_base_add_constTailB_of_odd
        (a := a) (b := b) (c := c) (n := n) hb hc hn h u bτ)
      (profileTail_base_add_constTailC_of_odd
        (a := a) (b := b) (c := c) (n := n) hb hc hn h v cτ)

noncomputable def hAdmissibleOddConstTailSignSumABC
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n)) : ℤ :=
  ∑ pB : (ZCoord c n → F) × BWoddBCoefABC a c n,
    ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
      bitSign (qProfileTailOfHAdmissibleConstTail
        (a := a) (b := b) (c := c) (n := n) hb hc hn h pB pC)

noncomputable def hAdmissibleOddTailSignSumABC
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : ℤ :=
  ∑ bτ : BWoddBCoefABC a c n,
    ∑ cτ : CWoddCCoefABC a b n,
      bitSign
        (qProfileABC (a := a) (b := b) (c := c) (n := n)
          (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
          (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1))

noncomputable def oddPureTailSignSumABC
    {a b c n : ℕ} [NeZero n] : ℤ :=
  ∑ bτ : BWoddBCoefABC a c n,
    ∑ cτ : CWoddCCoefABC a b n,
      bitSign (qProfileABC (a := a) (b := b) (c := c) (n := n) bτ.1 cτ.1)

noncomputable def baseBTailBWoddOfHAdmissible
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n)) :
    BWoddBCoefABC a c n :=
  ⟨baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h,
    fun t z =>
      profileTailBCoefABC_mem_Wodd_of_odd
        (a := a) (c := c) (n := n) hn
        (baseBCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) t z⟩

noncomputable def baseCTailBWoddOfHAdmissible
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n)) :
    CWoddCCoefABC a b n :=
  ⟨baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h,
    fun y r =>
      profileTailCCoefABC_mem_Wodd_of_odd
        (a := a) (b := b) (n := n) hn
        (baseCCoefOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h) y r⟩

noncomputable def addBaseBWoddEquiv
    {a c n : ℕ} [NeZero n] (base : BWoddBCoefABC a c n) :
    BWoddBCoefABC a c n ≃ BWoddBCoefABC a c n where
  toFun := fun bτ =>
    ⟨base.1 + bτ.1, fun t z =>
      (Wodd (a := a) (n := n)).add_mem (base.2 t z) (bτ.2 t z)⟩
  invFun := fun bτ =>
    ⟨base.1 + bτ.1, fun t z =>
      (Wodd (a := a) (n := n)).add_mem (base.2 t z) (bτ.2 t z)⟩
  left_inv := by
    intro bτ
    apply Subtype.ext
    funext t z p
    calc
      base.1 t z p + (base.1 t z p + bτ.1 t z p)
          = (base.1 t z p + base.1 t z p) + bτ.1 t z p := by
              ac_rfl
      _ = bτ.1 t z p := by
            simp [F_add_self]
  right_inv := by
    intro bτ
    apply Subtype.ext
    funext t z p
    calc
      base.1 t z p + (base.1 t z p + bτ.1 t z p)
          = (base.1 t z p + base.1 t z p) + bτ.1 t z p := by
              ac_rfl
      _ = bτ.1 t z p := by
            simp [F_add_self]

noncomputable def addBaseCWoddEquiv
    {a b n : ℕ} [NeZero n] (base : CWoddCCoefABC a b n) :
    CWoddCCoefABC a b n ≃ CWoddCCoefABC a b n where
  toFun := fun cτ =>
    ⟨base.1 + cτ.1, fun y r =>
      (Wodd (a := a) (n := n)).add_mem (base.2 y r) (cτ.2 y r)⟩
  invFun := fun cτ =>
    ⟨base.1 + cτ.1, fun y r =>
      (Wodd (a := a) (n := n)).add_mem (base.2 y r) (cτ.2 y r)⟩
  left_inv := by
    intro cτ
    apply Subtype.ext
    funext y r p
    calc
      base.1 y r p + (base.1 y r p + cτ.1 y r p)
          = (base.1 y r p + base.1 y r p) + cτ.1 y r p := by
              ac_rfl
      _ = cτ.1 y r p := by
            simp [F_add_self]
  right_inv := by
    intro cτ
    apply Subtype.ext
    funext y r p
    calc
      base.1 y r p + (base.1 y r p + cτ.1 y r p)
          = (base.1 y r p + base.1 y r p) + cτ.1 y r p := by
              ac_rfl
      _ = cτ.1 y r p := by
            simp [F_add_self]

lemma hAdmissibleOddTailSignSumABC_eq_oddPureTailSignSumABC_of_odd
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n)) :
    hAdmissibleOddTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h =
      oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) := by
  let baseB :=
    baseBTailBWoddOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc hn h
  let baseC :=
    baseCTailBWoddOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc hn h
  let eB := addBaseBWoddEquiv (a := a) (c := c) (n := n) baseB
  let eC := addBaseCWoddEquiv (a := a) (b := b) (n := n) baseC
  unfold hAdmissibleOddTailSignSumABC oddPureTailSignSumABC
  calc
    ∑ bτ : BWoddBCoefABC a c n,
        ∑ cτ : CWoddCCoefABC a b n,
          bitSign
            (qProfileABC (a := a) (b := b) (c := c) (n := n)
              (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
              (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1))
      =
        ∑ bτ : BWoddBCoefABC a c n,
          ∑ cτ : CWoddCCoefABC a b n,
            bitSign
              (qProfileABC (a := a) (b := b) (c := c) (n := n)
                (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
                cτ.1) := by
          refine Finset.sum_congr rfl ?_
          intro bτ hbτ
          simpa [eC, addBaseCWoddEquiv, baseC, baseCTailBWoddOfHAdmissible] using
            (Equiv.sum_comp eC
              (fun cτ' : CWoddCCoefABC a b n =>
                bitSign
                  (qProfileABC (a := a) (b := b) (c := c) (n := n)
                    (baseBTailOfHAdmissible
                      (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
                    cτ'.1)))
    _ = oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) := by
          simpa [eB, addBaseBWoddEquiv, baseB, baseBTailBWoddOfHAdmissible,
            oddPureTailSignSumABC] using
            (Equiv.sum_comp eB
              (fun bτ' : BWoddBCoefABC a c n =>
                ∑ cτ : CWoddCCoefABC a b n,
                  bitSign
                    (qProfileABC (a := a) (b := b) (c := c) (n := n)
                      bτ'.1 cτ.1)))

lemma hAdmissibleOddConstTailSignSumABC_eq_headFactor_mul_tailSignSumABC_of_odd
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n)) :
    hAdmissibleOddConstTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc hn h =
      (2 : ℤ) ^ (n ^ b + n ^ c) *
        hAdmissibleOddTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  unfold hAdmissibleOddConstTailSignSumABC hAdmissibleOddTailSignSumABC
  have hrew :
      (∑ pB : (ZCoord c n → F) × BWoddBCoefABC a c n,
          ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
            bitSign
              (qProfileTailOfHAdmissibleConstTail
                (a := a) (b := b) (c := c) (n := n) hb hc hn h pB pC)) =
        ∑ bτ : BWoddBCoefABC a c n,
          ∑ u : ZCoord c n → F,
            ∑ cτ : CWoddCCoefABC a b n,
              ∑ v : YCoord b n → F,
                bitSign
                  (qProfileTailOfHAdmissibleConstTail
                    (a := a) (b := b) (c := c) (n := n) hb hc hn h
                    (u, bτ) (v, cτ)) := by
    calc
      (∑ pB : (ZCoord c n → F) × BWoddBCoefABC a c n,
          ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
            bitSign
              (qProfileTailOfHAdmissibleConstTail
                (a := a) (b := b) (c := c) (n := n) hb hc hn h pB pC)) =
        ∑ bτ : BWoddBCoefABC a c n,
          ∑ u : ZCoord c n → F,
            ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
              bitSign
                (qProfileTailOfHAdmissibleConstTail
                  (a := a) (b := b) (c := c) (n := n) hb hc hn h (u, bτ) pC) := by
            simpa using
              (Fintype.sum_prod_type_right
                (f := fun pB : (ZCoord c n → F) × BWoddBCoefABC a c n =>
                  ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
                    bitSign
                      (qProfileTailOfHAdmissibleConstTail
                        (a := a) (b := b) (c := c) (n := n) hb hc hn h pB pC)))
      _ =
        ∑ bτ : BWoddBCoefABC a c n,
          ∑ u : ZCoord c n → F,
            ∑ cτ : CWoddCCoefABC a b n,
              ∑ v : YCoord b n → F,
                bitSign
                  (qProfileTailOfHAdmissibleConstTail
                    (a := a) (b := b) (c := c) (n := n) hb hc hn h
                    (u, bτ) (v, cτ)) := by
            refine Finset.sum_congr rfl ?_
            intro bτ hbτ
            refine Finset.sum_congr rfl ?_
            intro u hu
            simpa using
              (Fintype.sum_prod_type_right
                (f := fun pC : (YCoord b n → F) × CWoddCCoefABC a b n =>
                  bitSign
                    (qProfileTailOfHAdmissibleConstTail
                      (a := a) (b := b) (c := c) (n := n) hb hc hn h
                      (u, bτ) pC)))
  rw [hrew]
  have hz :
      (Fintype.card (ZCoord c n → F) : ℤ) = (2 : ℤ) ^ (n ^ c) := by
    simpa [card_zFunctions (c := c) (n := n)] using
      congrArg (fun x : ℕ => (x : ℤ)) (card_zFunctions (c := c) (n := n))
  have hy :
      (Fintype.card (YCoord b n → F) : ℤ) = (2 : ℤ) ^ (n ^ b) := by
    simpa [card_yFunctions (b := b) (n := n)] using
      congrArg (fun x : ℕ => (x : ℤ)) (card_yFunctions (b := b) (n := n))
  have hsign :
      ∀ (v : YCoord b n → F) (bτ : BWoddBCoefABC a c n)
        (u : ZCoord c n → F) (cτ : CWoddCCoefABC a b n),
        bitSign
          (qProfileTailOfHAdmissibleConstTail
            (a := a) (b := b) (c := c) (n := n) hb hc hn h
            (u, bτ) (v, cτ))
            =
        bitSign
          (qProfileABC (a := a) (b := b) (c := c) (n := n)
            (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
            (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1)) := by
    intro v bτ u cτ
    rw [qProfileTailOfHAdmissibleConstTail_eq_baseTail_add_tails_of_odd
      (a := a) (b := b) (c := c) (n := n) hb hc hn h u bτ v cτ]
  calc
    ∑ bτ : BWoddBCoefABC a c n,
        ∑ u : ZCoord c n → F,
          ∑ cτ : CWoddCCoefABC a b n,
            ∑ v : YCoord b n → F,
              bitSign
                (qProfileTailOfHAdmissibleConstTail
                  (a := a) (b := b) (c := c) (n := n) hb hc hn h
                  (u, bτ) (v, cτ))
      =
        ∑ bτ : BWoddBCoefABC a c n,
          ∑ u : ZCoord c n → F,
            ∑ cτ : CWoddCCoefABC a b n,
              ∑ v : YCoord b n → F,
                bitSign
                  (qProfileABC (a := a) (b := b) (c := c) (n := n)
                    (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
                    (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1)) := by
          refine Finset.sum_congr rfl ?_
          intro bτ hbτ
          refine Finset.sum_congr rfl ?_
          intro u hu
          refine Finset.sum_congr rfl ?_
          intro cτ hcτ
          refine Finset.sum_congr rfl ?_
          intro v hv
          exact hsign v bτ u cτ
    _ =
        ∑ bτ : BWoddBCoefABC a c n,
          ∑ u : ZCoord c n → F,
            ∑ cτ : CWoddCCoefABC a b n,
              (Fintype.card (YCoord b n → F) : ℤ) *
                bitSign
                  (qProfileABC (a := a) (b := b) (c := c) (n := n)
                    (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
                    (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1)) := by
          refine Finset.sum_congr rfl ?_
          intro bτ hbτ
          refine Finset.sum_congr rfl ?_
          intro u hu
          refine Finset.sum_congr rfl ?_
          intro cτ hcτ
          simp
    _ =
        ∑ bτ : BWoddBCoefABC a c n,
          ∑ u : ZCoord c n → F,
            (Fintype.card (YCoord b n → F) : ℤ) *
              ∑ cτ : CWoddCCoefABC a b n,
                bitSign
                  (qProfileABC (a := a) (b := b) (c := c) (n := n)
                    (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
                    (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1)) := by
          refine Finset.sum_congr rfl ?_
          intro bτ hbτ
          refine Finset.sum_congr rfl ?_
          intro u hu
          rw [← Finset.mul_sum]
    _ =
        ∑ bτ : BWoddBCoefABC a c n,
          (Fintype.card (ZCoord c n → F) : ℤ) *
            ((Fintype.card (YCoord b n → F) : ℤ) *
              ∑ cτ : CWoddCCoefABC a b n,
                bitSign
                  (qProfileABC (a := a) (b := b) (c := c) (n := n)
                    (baseBTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + bτ.1)
                    (baseCTailOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h + cτ.1))) := by
          refine Finset.sum_congr rfl ?_
          intro bτ hbτ
          simp
    _ =
        (2 : ℤ) ^ (n ^ b + n ^ c) *
          hAdmissibleOddTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
          let S : ℤ := hAdmissibleOddTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h
          have hpow :
              (Fintype.card (ZCoord c n → F) : ℤ) *
                  ((Fintype.card (YCoord b n → F) : ℤ) * S) =
                (2 : ℤ) ^ (n ^ b + n ^ c) * S := by
            rw [hy, hz, pow_add]
            ring
          simpa [S, hAdmissibleOddTailSignSumABC, Finset.mul_sum, mul_assoc] using hpow

lemma hAdmissibleOddKernelTailSignSumABC_eq_constTailSignSumABC_of_odd
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) (h : HAdmissible (n := n)) :
    hAdmissibleOddKernelTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h =
      hAdmissibleOddConstTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc hn h := by
  unfold hAdmissibleOddKernelTailSignSumABC hAdmissibleOddConstTailSignSumABC
    qProfileTailOfHAdmissibleConstTail
  let eB := bProfileKernelEquivConstTailOfOdd (a := a) (c := c) (n := n) hn
  let eC := cProfileKernelEquivConstTailOfOdd (a := a) (b := b) (n := n) hn
  calc
    ∑ kB : BProfileKernelABC a c n,
        ∑ kC : CProfileKernelABC a b n,
          bitSign (qProfileTailOfHAdmissibleKernels
            (a := a) (b := b) (c := c) (n := n) hb hc h kB kC)
      =
        ∑ kB : BProfileKernelABC a c n,
          ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
            bitSign (qProfileTailOfHAdmissibleKernels
              (a := a) (b := b) (c := c) (n := n) hb hc h kB (eC.symm pC)) := by
          refine Finset.sum_congr rfl ?_
          intro kB hkB
          simpa [eC] using
            (Equiv.sum_comp eC
              (fun pC : (YCoord b n → F) × CWoddCCoefABC a b n =>
                bitSign (qProfileTailOfHAdmissibleKernels
                  (a := a) (b := b) (c := c) (n := n) hb hc h kB (eC.symm pC))))
    _ =
        ∑ pB : (ZCoord c n → F) × BWoddBCoefABC a c n,
          ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
            bitSign (qProfileTailOfHAdmissibleKernels
              (a := a) (b := b) (c := c) (n := n) hb hc h (eB.symm pB) (eC.symm pC)) := by
          simpa [eB] using
            (Equiv.sum_comp eB
              (fun pB : (ZCoord c n → F) × BWoddBCoefABC a c n =>
                ∑ pC : (YCoord b n → F) × CWoddCCoefABC a b n,
                  bitSign (qProfileTailOfHAdmissibleKernels
                    (a := a) (b := b) (c := c) (n := n) hb hc h (eB.symm pB) (eC.symm pC))))

theorem DeltaABC_after_A_eq_sum_hAdmissibleOddConstTailSignSums_of_odd
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c)) *
        ∑ h : HAdmissible (n := n),
          hAdmissibleOddConstTailSignSumABC
            (a := a) (b := b) (c := c) (n := n) hb hc hn h := by
  rw [DeltaABC_after_A_eq_sum_hAdmissibleOddKernelTailSignSums_of_odd
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn]
  have hsum :
      (∑ h : HAdmissible (n := n),
        hAdmissibleOddKernelTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h)
        =
      ∑ h : HAdmissible (n := n),
        hAdmissibleOddConstTailSignSumABC
          (a := a) (b := b) (c := c) (n := n) hb hc hn h := by
    refine Finset.sum_congr rfl ?_
    intro h hh
    exact hAdmissibleOddKernelTailSignSumABC_eq_constTailSignSumABC_of_odd
      (a := a) (b := b) (c := c) (n := n) hb hc hn h
  rw [hsum]

theorem DeltaABC_after_A_eq_sum_hAdmissibleOddTailSignSums_of_odd
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c) + n ^ b + n ^ c) *
        ∑ h : HAdmissible (n := n),
          hAdmissibleOddTailSignSumABC
            (a := a) (b := b) (c := c) (n := n) hb hc h := by
  rw [DeltaABC_after_A_eq_sum_hAdmissibleOddConstTailSignSums_of_odd
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn]
  have hsum :
      (∑ h : HAdmissible (n := n),
        hAdmissibleOddConstTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc hn h) =
      (2 : ℤ) ^ (n ^ b + n ^ c) *
        ∑ h : HAdmissible (n := n),
          hAdmissibleOddTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
    calc
      ∑ h : HAdmissible (n := n),
          hAdmissibleOddConstTailSignSumABC
            (a := a) (b := b) (c := c) (n := n) hb hc hn h
        =
          ∑ h : HAdmissible (n := n),
            (2 : ℤ) ^ (n ^ b + n ^ c) *
              hAdmissibleOddTailSignSumABC
                (a := a) (b := b) (c := c) (n := n) hb hc h := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            exact hAdmissibleOddConstTailSignSumABC_eq_headFactor_mul_tailSignSumABC_of_odd
              (a := a) (b := b) (c := c) (n := n) hb hc hn h
      _ =
          (2 : ℤ) ^ (n ^ b + n ^ c) *
            ∑ h : HAdmissible (n := n),
              hAdmissibleOddTailSignSumABC
                (a := a) (b := b) (c := c) (n := n) hb hc h := by
            rw [← Finset.mul_sum]
  rw [hsum]
  rw [← mul_assoc, ← pow_add]
  simp [add_assoc]

lemma sum_hAdmissibleOddTailSignSums_eq_card_mul_oddPureTailSignSumABC_of_odd
    {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    (∑ h : HAdmissible (n := n),
      hAdmissibleOddTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h) =
      (Fintype.card (HAdmissible (n := n)) : ℤ) *
        oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) := by
  calc
    (∑ h : HAdmissible (n := n),
      hAdmissibleOddTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h) =
        ∑ h : HAdmissible (n := n),
          oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            exact hAdmissibleOddTailSignSumABC_eq_oddPureTailSignSumABC_of_odd
              (a := a) (b := b) (c := c) (n := n) hb hc hn h
    _ =
        (Fintype.card (HAdmissible (n := n)) : ℤ) *
          oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) := by
            simp

theorem DeltaABC_after_A_eq_pow_mul_oddPureTailSignSumABC_of_odd
    {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c) + n ^ b + n ^ c + (n - 1) ^ 2) *
        oddPureTailSignSumABC (a := a) (b := b) (c := c) (n := n) := by
  rw [DeltaABC_after_A_eq_sum_hAdmissibleOddTailSignSums_of_odd
    (a := a) (b := b) (c := c) (n := n) ha hb hc hn]
  rw [sum_hAdmissibleOddTailSignSums_eq_card_mul_oddPureTailSignSumABC_of_odd
    (a := a) (b := b) (c := c) (n := n) hb hc hn]
  have hcard :
      (Fintype.card (HAdmissible (n := n)) : ℤ) = (2 : ℤ) ^ ((n - 1) ^ 2) := by
    exact_mod_cast (card_HAdmissible (n := n))
  rw [hcard]
  rw [← mul_assoc, ← pow_add]

end Core3loop
