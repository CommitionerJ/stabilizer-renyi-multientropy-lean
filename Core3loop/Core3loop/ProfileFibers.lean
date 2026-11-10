import Core3loop.ProfilePair
import Core3loop.VisibleSpace

namespace Core3loop

abbrev BProfileABC (c n : ℕ) := No13Migration.BProfileRawABC c n
abbrev CProfileABC (b n : ℕ) := No13Migration.CProfileRawABC b n

abbrev ProfileCompatABC (b c n : ℕ) [NeZero n] := No13Migration.ProfileCompatABC b c n

noncomputable def toNo13HRaw {n : ℕ} [NeZero n] (h : HRaw n) : No13Migration.HRaw n :=
  fun p => h (p 0) (p 1)

noncomputable def ofNo13HRaw {n : ℕ} [NeZero n] (h : No13Migration.HRaw n) : HRaw n :=
  fun t s => h (No13Migration.vec2 t s)

noncomputable def no13HAdmissibleEquivHAdmissible {n : ℕ} [NeZero n] :
    No13Migration.HAdmissible n ≃ HAdmissible (n := n) where
  toFun h := by
    refine ⟨ofNo13HRaw h.1, ?_⟩
    constructor
    · change rowSum (ofNo13HRaw h.1) = 0
      funext t
      simpa [rowSum, ofNo13HRaw, No13Migration.colSum, No13Migration.vec2] using h.2.2 t
    · change colSum (ofNo13HRaw h.1) = 0
      funext s
      simpa [colSum, ofNo13HRaw, No13Migration.rowSum, No13Migration.vec2] using h.2.1 s
  invFun h := by
    refine ⟨toNo13HRaw h.1, ?_⟩
    constructor
    · intro t
      simpa [toNo13HRaw, colSum, No13Migration.rowSum, No13Migration.vec2] using
        colSum_eq_zero_of_mem_HAdmissible (n := n) h.2 t
    · intro s
      simpa [toNo13HRaw, rowSum, No13Migration.colSum, No13Migration.vec2] using
        rowSum_eq_zero_of_mem_HAdmissible (n := n) h.2 s
  left_inv h := by
    apply Subtype.ext
    funext p
    simpa [toNo13HRaw, ofNo13HRaw] using congrArg h.1 (No13Migration.vec2_eta p)
  right_inv h := by
    apply Subtype.ext
    funext t s
    simp [toNo13HRaw, ofNo13HRaw, No13Migration.vec2]

noncomputable def profileCompatABCEquivHAdmissible {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    ProfileCompatABC b c n ≃ HAdmissible (n := n) :=
  (No13Migration.profileCompatABC_equiv_HAdmissible (b := b) (c := c) (n := n) hb hc).trans
    (no13HAdmissibleEquivHAdmissible (n := n))

noncomputable def hAdmissibleToProfileCompatABC {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    ProfileCompatABC b c n :=
  (profileCompatABCEquivHAdmissible (b := b) (c := c) (n := n) hb hc).symm h

abbrev BProfileFiberABC {a c n : ℕ} [NeZero n] (f : BProfileABC c n) :=
  No13Migration.BProfileFiberABC_real (a := a) (c := c) (n := n) f

abbrev CProfileFiberABC {a b n : ℕ} [NeZero n] (g : CProfileABC b n) :=
  No13Migration.CProfileFiberABC_real (a := a) (b := b) (n := n) g

abbrev SurvivingSigmaABC (a b c n : ℕ) [NeZero n] :=
  No13Migration.SurvivingSigmaABC_real a b c n

abbrev BProfileFiberOfHABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :=
  BProfileFiberABC (a := a) (c := c)
    ((hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h).1.1)

abbrev CProfileFiberOfHABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :=
  CProfileFiberABC (a := a) (b := b)
    ((hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h).1.2)

abbrev FiberPairOfHABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :=
  BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h ×
    CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h

abbrev SurvivingSigmaHAdmissibleABC (a b c n : ℕ) [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :=
  Σ h : HAdmissible (n := n),
    FiberPairOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h

noncomputable abbrev survivingBCEquivProfileSigma {a b c n : ℕ} [NeZero n] :
    SurvivingBC a b c n ≃ SurvivingSigmaABC a b c n :=
  No13Migration.survivingBC_abc_real_equiv_sigma (a := a) (b := b) (c := c) (n := n)

noncomputable def profileSigmaEquivHAdmissibleSigma {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    SurvivingSigmaABC a b c n ≃ SurvivingSigmaHAdmissibleABC a b c n hb hc :=
  Equiv.sigmaCongrLeft' (profileCompatABCEquivHAdmissible (b := b) (c := c) (n := n) hb hc)

noncomputable def survivingBCEquivHAdmissibleSigma {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    SurvivingBC a b c n ≃ SurvivingSigmaHAdmissibleABC a b c n hb hc :=
  (survivingBCEquivProfileSigma (a := a) (b := b) (c := c) (n := n)).trans
    (profileSigmaEquivHAdmissibleSigma (a := a) (b := b) (c := c) (n := n) hb hc)

noncomputable instance instFintypeBProfileFiberOfHABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    Fintype (BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) := by
  change Fintype
    (BProfileFiberABC (a := a) (c := c)
      ((hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h).1.1))
  infer_instance

noncomputable instance instFintypeCProfileFiberOfHABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    Fintype (CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) := by
  change Fintype
    (CProfileFiberABC (a := a) (b := b)
      ((hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h).1.2))
  infer_instance

noncomputable instance instFintypeFiberProductOfHABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    Fintype (FiberPairOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) := by
  infer_instance

noncomputable def survivingBCOfHAdmissibleFibers {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (Bf : BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h)
    (Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) :
    SurvivingBC a b c n :=
  (survivingBCEquivHAdmissibleSigma (a := a) (b := b) (c := c) (n := n) hb hc).symm ⟨h, (Bf, Cf)⟩

noncomputable def qpairOfHAdmissibleFibers {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (Bf : BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h)
    (Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) : F := by
  let bc := survivingBCOfHAdmissibleFibers (a := a) (b := b) (c := c) (n := n) hb hc h Bf Cf
  exact QpairABC (a := a) (b := b) (c := c) (n := n) bc.1.1 bc.1.2

noncomputable def bcoefOfHAdmissibleFiber {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (Bf : BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) :
    BCoefABC a c n :=
  bFieldEquivBCoefABC (a := a) (c := c) (n := n) Bf.1

noncomputable def ccoefOfHAdmissibleFiber {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) :
    CCoefABC a b n :=
  cFieldEquivCCoefABC (a := a) (b := b) (n := n) Cf.1

lemma qpairOfHAdmissibleFibers_eq_qProfileABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (Bf : BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h)
    (Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) :
    qpairOfHAdmissibleFibers (a := a) (b := b) (c := c) (n := n) hb hc h Bf Cf =
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (bcoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h Bf)
        (ccoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h Cf) := by
  rcases Bf with ⟨B, hB⟩
  rcases Cf with ⟨C, hC⟩
  let xh : SurvivingSigmaHAdmissibleABC a b c n hb hc := ⟨h, (⟨B, hB⟩, ⟨C, hC⟩)⟩
  let xp : SurvivingSigmaABC a b c n :=
    (profileSigmaEquivHAdmissibleSigma (a := a) (b := b) (c := c) (n := n) hb hc).symm xh
  have hxp :
      xp = ⟨hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h,
        (⟨B, hB⟩, ⟨C, hC⟩)⟩ := by
    rfl
  have hright :=
    congrArg
      (fun x : SurvivingSigmaABC a b c n =>
        qProfileABC (a := a) (b := b) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) x.2.1.1)
          (cFieldEquivCCoefABC (a := a) (b := b) (n := n) x.2.2.1))
      ((survivingBCEquivProfileSigma (a := a) (b := b) (c := c) (n := n)).right_inv xp)
  simpa [xp, xh, hxp, survivingBCOfHAdmissibleFibers, survivingBCEquivHAdmissibleSigma,
    survivingBCEquivProfileSigma, profileSigmaEquivHAdmissibleSigma, hAdmissibleToProfileCompatABC,
    profileCompatABCEquivHAdmissible, qpairOfHAdmissibleFibers, bcoefOfHAdmissibleFiber,
    ccoefOfHAdmissibleFiber, QpairABC_eq_qProfileABC] using hright

noncomputable def hAdmissibleFiberSignSumABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : ℤ :=
  ∑ Bf : BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
    ∑ Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
      bitSign (qpairOfHAdmissibleFibers (a := a) (b := b) (c := c) (n := n) hb hc h Bf Cf)

noncomputable def hAdmissibleProfileFiberSignSumABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : ℤ :=
  ∑ Bf : BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
    ∑ Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
      bitSign
        (qProfileABC (a := a) (b := b) (c := c) (n := n)
          (bcoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h Bf)
          (ccoefOfHAdmissibleFiber (a := a) (b := b) (c := c) (n := n) hb hc h Cf))

lemma hAdmissibleFiberSignSumABC_eq_hAdmissibleProfileFiberSignSumABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h =
      hAdmissibleProfileFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  unfold hAdmissibleFiberSignSumABC hAdmissibleProfileFiberSignSumABC
  refine Finset.sum_congr rfl ?_
  intro Bf hBf
  refine Finset.sum_congr rfl ?_
  intro Cf hCf
  rw [qpairOfHAdmissibleFibers_eq_qProfileABC (a := a) (b := b) (c := c) (n := n) hb hc h Bf Cf]

lemma sum_fiberPair_eq_hAdmissibleFiberSignSumABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    (∑ p : FiberPairOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
      bitSign (qpairOfHAdmissibleFibers
        (a := a) (b := b) (c := c) (n := n) hb hc h p.1 p.2))
      =
    hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  unfold hAdmissibleFiberSignSumABC FiberPairOfHABC
  rw [Fintype.sum_prod_type]

lemma sum_survivingBC_eq_sum_hAdmissibleFiberSignSums {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    ∑ bc : SurvivingBC a b c n, bitSign (QpairABC (a := a) (b := b) (c := c) (n := n) bc.1.1 bc.1.2) =
      ∑ h : HAdmissible (n := n),
        hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  classical
  let e := survivingBCEquivHAdmissibleSigma (a := a) (b := b) (c := c) (n := n) hb hc
  calc
    ∑ bc : SurvivingBC a b c n, bitSign (QpairABC (a := a) (b := b) (c := c) (n := n) bc.1.1 bc.1.2)
      =
        ∑ x : SurvivingSigmaHAdmissibleABC a b c n hb hc,
          bitSign (qpairOfHAdmissibleFibers
            (a := a) (b := b) (c := c) (n := n) hb hc x.1 x.2.1 x.2.2) := by
          simpa [e, qpairOfHAdmissibleFibers, survivingBCOfHAdmissibleFibers] using
            (Equiv.sum_comp e
              (fun x : SurvivingSigmaHAdmissibleABC a b c n hb hc =>
                bitSign (qpairOfHAdmissibleFibers
                  (a := a) (b := b) (c := c) (n := n) hb hc x.1 x.2.1 x.2.2)))
    _ =
        ∑ h : HAdmissible (n := n),
          ∑ p : FiberPairOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
            bitSign (qpairOfHAdmissibleFibers
              (a := a) (b := b) (c := c) (n := n) hb hc h p.1 p.2) := by
            let f :
                (h : HAdmissible (n := n)) →
                  FiberPairOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h → ℤ :=
              fun h p =>
                bitSign (qpairOfHAdmissibleFibers
                  (a := a) (b := b) (c := c) (n := n) hb hc h p.1 p.2)
            change
              ∑ x :
                  Sigma fun h : HAdmissible (n := n) =>
                    FiberPairOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
                f x.1 x.2
                =
              ∑ h : HAdmissible (n := n), ∑ p, f h p
            exact Fintype.sum_sigma' f
    _ =
        ∑ h : HAdmissible (n := n),
          hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            exact sum_fiberPair_eq_hAdmissibleFiberSignSumABC
              (a := a) (b := b) (c := c) (n := n) hb hc h

theorem card_profileCompatABC_closed {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ProfileCompatABC b c n) = 2 ^ ((n - 1) ^ 2) := by
  simpa [ProfileCompatABC] using
    No13Migration.card_ProfileCompatABC_closed (b := b) (c := c) (n := n) hb hc

theorem card_profileCompatABC_eq_card_HAdmissible {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (ProfileCompatABC b c n) = Fintype.card (HAdmissible (n := n)) := by
  exact Fintype.card_congr (profileCompatABCEquivHAdmissible (b := b) (c := c) (n := n) hb hc)

lemma natCard_survivingBC_eq_sum_profileFiberProducts {a b c n : ℕ} [NeZero n] :
    Nat.card (SurvivingBC a b c n) =
      ∑ fg : ProfileCompatABC b c n,
        Nat.card (BProfileFiberABC (a := a) (c := c) fg.1.1) *
          Nat.card (CProfileFiberABC (a := a) (b := b) fg.1.2) := by
  calc
    Nat.card (SurvivingBC a b c n) = Nat.card (SurvivingSigmaABC a b c n) := by
      exact Nat.card_congr (survivingBCEquivProfileSigma (a := a) (b := b) (c := c) (n := n))
    _ =
        ∑ fg : ProfileCompatABC b c n,
          Nat.card (BProfileFiberABC (a := a) (c := c) fg.1.1) *
            Nat.card (CProfileFiberABC (a := a) (b := b) fg.1.2) := by
              simpa [SurvivingSigmaABC, ProfileCompatABC, BProfileFiberABC, CProfileFiberABC] using
                No13Migration.Nat.card_survivingSigmaABC_real_eq_sum_profileFiberProducts
                  (a := a) (b := b) (c := c) (n := n)

lemma natCard_profileFiberProducts_of_hAdmissible {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    Nat.card (BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) *
        Nat.card (CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h)
      =
        (2 : ℕ) ^
          ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
            (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
  simpa [BProfileFiberOfHABC, CProfileFiberOfHABC, hAdmissibleToProfileCompatABC] using
    No13Migration.Nat.card_profileFiberABC_real_product_constant
      (a := a) (b := b) (c := c) (n := n) ha
      (hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h)

lemma natCard_survivingBC_eq_sum_hAdmissibleFiberProducts {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Nat.card (SurvivingBC a b c n) =
      ∑ h : HAdmissible (n := n),
        Nat.card (BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) *
          Nat.card (CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) := by
  calc
    Nat.card (SurvivingBC a b c n) =
      Nat.card (SurvivingSigmaHAdmissibleABC a b c n hb hc) := by
        exact Nat.card_congr
          (survivingBCEquivHAdmissibleSigma (a := a) (b := b) (c := c) (n := n) hb hc)
    _ =
      ∑ h : HAdmissible (n := n),
        Nat.card (BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) *
          Nat.card (CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h) := by
            simpa [SurvivingSigmaHAdmissibleABC, Nat.card_prod] using
              (Nat.card_sigma
                (α := HAdmissible (n := n))
                (β := fun h : HAdmissible (n := n) =>
                  BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h ×
                    CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h))

theorem DeltaABC_after_A_eq_sum_hAdmissibleFiberSignSums {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c)) *
        ∑ h : HAdmissible (n := n),
          hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  rw [DeltaABC_after_A (a := a) (b := b) (c := c) (n := n) ha hb hc]
  rw [sum_survivingBC_eq_sum_hAdmissibleFiberSignSums (a := a) (b := b) (c := c) (n := n) hb hc]

theorem DeltaABC_after_A_eq_sum_hAdmissibleProfileFiberSignSums {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c)) *
        ∑ h : HAdmissible (n := n),
          hAdmissibleProfileFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  rw [DeltaABC_after_A_eq_sum_hAdmissibleFiberSignSums (a := a) (b := b) (c := c) (n := n) ha hb hc]
  have hsum :
      (∑ h : HAdmissible (n := n),
        hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h)
        =
      ∑ h : HAdmissible (n := n),
        hAdmissibleProfileFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
    refine Finset.sum_congr rfl ?_
    intro h hh
    exact hAdmissibleFiberSignSumABC_eq_hAdmissibleProfileFiberSignSumABC
      (a := a) (b := b) (c := c) (n := n) hb hc h
  rw [hsum]

theorem natCard_survivingBC_eq_card_profileCompat_mul_pow {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) :
    Nat.card (SurvivingBC a b c n) =
      Nat.card (ProfileCompatABC b c n) *
        (2 : ℕ) ^
          ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
            (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
  calc
    Nat.card (SurvivingBC a b c n) = Nat.card (SurvivingSigmaABC a b c n) := by
      exact Nat.card_congr (survivingBCEquivProfileSigma (a := a) (b := b) (c := c) (n := n))
    _ =
        Nat.card (ProfileCompatABC b c n) *
          (2 : ℕ) ^
            ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
              (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
              simpa [SurvivingSigmaABC, ProfileCompatABC] using
                No13Migration.Nat.card_survivingSigmaABC_real_eq_card_profileCompat_mul_pow
                  (a := a) (b := b) (c := c) (n := n) ha

theorem natCard_survivingBC_eq_natCard_HAdmissible_mul_pow {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Nat.card (SurvivingBC a b c n) =
      Nat.card (HAdmissible (n := n)) *
        (2 : ℕ) ^
          ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
            (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
  rw [natCard_survivingBC_eq_card_profileCompat_mul_pow (a := a) (b := b) (c := c) (n := n) ha]
  congr 1
  exact Nat.card_congr (profileCompatABCEquivHAdmissible (b := b) (c := c) (n := n) hb hc)

theorem card_survivingBC_eq_card_profileCompat_mul_pow {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) :
    Fintype.card (SurvivingBC a b c n) =
      Fintype.card (ProfileCompatABC b c n) *
        2 ^
          ((n ^ (a + c) - (n ^ (c + 1) - n ^ c)) +
            (n ^ (a + b) - (n ^ (b + 1) - n ^ b))) := by
  simpa [Nat.card_eq_fintype_card] using
    natCard_survivingBC_eq_card_profileCompat_mul_pow
      (a := a) (b := b) (c := c) (n := n) ha

end Core3loop
