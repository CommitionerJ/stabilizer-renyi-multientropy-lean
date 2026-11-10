import Core3loop.ProfileOdd

open scoped BigOperators

namespace Core3loop

abbrev BProfileKernelABC (a c n : ℕ) [NeZero n] :=
  ↥(LinearMap.ker (No13Migration.bProfileLinearMap_abc_real (a := a) (c := c) (n := n)))

abbrev CProfileKernelABC (a b n : ℕ) [NeZero n] :=
  ↥(LinearMap.ker (No13Migration.cProfileLinearMap_abc_real (a := a) (b := b) (n := n)))

abbrev KernelPairABC (a b c n : ℕ) [NeZero n] :=
  BProfileKernelABC a c n × CProfileKernelABC a b n

instance bProfileKernelABC_finite {a c n : ℕ} [NeZero n] :
    Finite (BProfileKernelABC a c n) :=
  Finite.of_injective (Subtype.val : BProfileKernelABC a c n → BFieldABC a c n)
    (fun _ _ h => Subtype.ext h)

noncomputable instance bProfileKernelABC_fintype {a c n : ℕ} [NeZero n] :
    Fintype (BProfileKernelABC a c n) :=
  Fintype.ofFinite _

instance cProfileKernelABC_finite {a b n : ℕ} [NeZero n] :
    Finite (CProfileKernelABC a b n) :=
  Finite.of_injective (Subtype.val : CProfileKernelABC a b n → CFieldABC a b n)
    (fun _ _ h => Subtype.ext h)

noncomputable instance cProfileKernelABC_fintype {a b n : ℕ} [NeZero n] :
    Fintype (CProfileKernelABC a b n) :=
  Fintype.ofFinite _

noncomputable def baseBProfileFiberOfHAdmissible {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  let fg := hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h
  refine ⟨No13Migration.BfieldABC_of_admissibleProfile (a := a) (c := c) (n := n) fg.1.1 fg.2.1, ?_⟩
  ext s z
  simpa [fg, No13Migration.bProfileLinearMap_abc_real] using
    No13Migration.bKernelABC_real_BfieldABC_of_admissibleProfile
      (a := a) (c := c) (n := n) fg.1.1 fg.2.1 s z

  noncomputable def baseCProfileFiberOfHAdmissible {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  let fg := hAdmissibleToProfileCompatABC (b := b) (c := c) (n := n) hb hc h
  refine ⟨No13Migration.CfieldABC_of_admissibleProfile
    (a := a) (b := b) (n := n) fg.1.2 fg.2.2.1, ?_⟩
  ext y r
  simpa [fg, No13Migration.cProfileLinearMap_abc_real] using
    No13Migration.cKernelABC_real_CfieldABC_of_admissibleProfile
      (a := a) (b := b) (n := n) fg.1.2 fg.2.2.1 y r

noncomputable def bProfileFiberEquivEqBaseOfHAdmissible {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h
      ≃
    { B : BFieldABC a c n //
        No13Migration.bProfileLinearMap_abc_real (a := a) (c := c) (n := n) B =
          No13Migration.bProfileLinearMap_abc_real (a := a) (c := c) (n := n)
            (baseBProfileFiberOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).1 } where
  toFun := fun Bf =>
    ⟨Bf.1, Bf.2.trans (baseBProfileFiberOfHAdmissible
      (a := a) (b := b) (c := c) (n := n) hb hc h).2.symm⟩
  invFun := fun Bf =>
    ⟨Bf.1, Bf.2.trans (baseBProfileFiberOfHAdmissible
      (a := a) (b := b) (c := c) (n := n) hb hc h).2⟩
  left_inv := by
    intro Bf
    rfl
  right_inv := by
    intro Bf
    rfl

noncomputable def cProfileFiberEquivEqBaseOfHAdmissible {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h
      ≃
    { C : CFieldABC a b n //
        No13Migration.cProfileLinearMap_abc_real (a := a) (b := b) (n := n) C =
          No13Migration.cProfileLinearMap_abc_real (a := a) (b := b) (n := n)
            (baseCProfileFiberOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).1 } where
  toFun := fun Cf =>
    ⟨Cf.1, Cf.2.trans (baseCProfileFiberOfHAdmissible
      (a := a) (b := b) (c := c) (n := n) hb hc h).2.symm⟩
  invFun := fun Cf =>
    ⟨Cf.1, Cf.2.trans (baseCProfileFiberOfHAdmissible
      (a := a) (b := b) (c := c) (n := n) hb hc h).2⟩
  left_inv := by
    intro Cf
    rfl
  right_inv := by
    intro Cf
    rfl

noncomputable def bProfileFiberEquivKerOfHAdmissible {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h ≃
      BProfileKernelABC a c n :=
  (bProfileFiberEquivEqBaseOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).trans
    (No13Migration.fiberEquivKer_bProfileABC_real (a := a) (c := c) (n := n)
      (baseBProfileFiberOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).1)

noncomputable def cProfileFiberEquivKerOfHAdmissible {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h ≃
      CProfileKernelABC a b n :=
  (cProfileFiberEquivEqBaseOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).trans
    (No13Migration.fiberEquivKer_cProfileABC_real (a := a) (b := b) (n := n)
      (baseCProfileFiberOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).1)

noncomputable def fiberPairEquivKernelPairOfHAdmissible {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    FiberPairOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h ≃ KernelPairABC a b c n :=
  Equiv.prodCongr
    (bProfileFiberEquivKerOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h)
    (cProfileFiberEquivKerOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h)

noncomputable def bProfileFiberOfKernel {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kB : BProfileKernelABC a c n) :
    BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h :=
  (bProfileFiberEquivKerOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).symm kB

noncomputable def cProfileFiberOfKernel {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kC : CProfileKernelABC a b n) :
    CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h :=
  (cProfileFiberEquivKerOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h).symm kC

noncomputable def survivingBCOfHAdmissibleKernels {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kB : BProfileKernelABC a c n) (kC : CProfileKernelABC a b n) :
    SurvivingBC a b c n :=
  survivingBCOfHAdmissibleFibers (a := a) (b := b) (c := c) (n := n) hb hc h
    (bProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kB)
    (cProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kC)

noncomputable def qpairOfHAdmissibleKernels {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kB : BProfileKernelABC a c n) (kC : CProfileKernelABC a b n) : F :=
  qpairOfHAdmissibleFibers (a := a) (b := b) (c := c) (n := n) hb hc h
    (bProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kB)
    (cProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kC)

noncomputable def hAdmissibleKernelSignSumABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : ℤ :=
  ∑ kB : BProfileKernelABC a c n,
    ∑ kC : CProfileKernelABC a b n,
      bitSign (qpairOfHAdmissibleKernels
        (a := a) (b := b) (c := c) (n := n) hb hc h kB kC)

lemma hAdmissibleFiberSignSumABC_eq_hAdmissibleKernelSignSumABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) :
    hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h =
      hAdmissibleKernelSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  unfold hAdmissibleFiberSignSumABC hAdmissibleKernelSignSumABC
  let eB := bProfileFiberEquivKerOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h
  let eC := cProfileFiberEquivKerOfHAdmissible (a := a) (b := b) (c := c) (n := n) hb hc h
  calc
    ∑ Bf : BProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
        ∑ Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
          bitSign (qpairOfHAdmissibleFibers
            (a := a) (b := b) (c := c) (n := n) hb hc h Bf Cf)
      =
        ∑ kB : BProfileKernelABC a c n,
          ∑ Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
            bitSign (qpairOfHAdmissibleFibers
              (a := a) (b := b) (c := c) (n := n) hb hc h
              (bProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kB) Cf) := by
          simpa [eB, bProfileFiberOfKernel] using
            (Equiv.sum_comp eB
              (fun kB : BProfileKernelABC a c n =>
                ∑ Cf : CProfileFiberOfHABC (a := a) (b := b) (c := c) (n := n) hb hc h,
                  bitSign (qpairOfHAdmissibleFibers
                    (a := a) (b := b) (c := c) (n := n) hb hc h
                    (bProfileFiberOfKernel (a := a) (b := b) (c := c) (n := n) hb hc h kB) Cf)))
    _ =
        ∑ kB : BProfileKernelABC a c n,
          ∑ kC : CProfileKernelABC a b n,
            bitSign (qpairOfHAdmissibleKernels
              (a := a) (b := b) (c := c) (n := n) hb hc h kB kC) := by
          refine Finset.sum_congr rfl ?_
          intro kB hkB
          simpa [eC, qpairOfHAdmissibleKernels, cProfileFiberOfKernel] using
            (Equiv.sum_comp eC
              (fun kC : CProfileKernelABC a b n =>
                bitSign (qpairOfHAdmissibleKernels
                  (a := a) (b := b) (c := c) (n := n) hb hc h kB kC)))

theorem DeltaABC_after_A_eq_sum_hAdmissibleKernelSignSums {a b c n : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c)) *
        ∑ h : HAdmissible (n := n),
          hAdmissibleKernelSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  rw [DeltaABC_after_A_eq_sum_hAdmissibleFiberSignSums
    (a := a) (b := b) (c := c) (n := n) ha hb hc]
  have hsum :
      (∑ h : HAdmissible (n := n),
        hAdmissibleFiberSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h)
        =
      ∑ h : HAdmissible (n := n),
        hAdmissibleKernelSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
    refine Finset.sum_congr rfl ?_
    intro h hh
    exact hAdmissibleFiberSignSumABC_eq_hAdmissibleKernelSignSumABC
      (a := a) (b := b) (c := c) (n := n) hb hc h
  rw [hsum]

noncomputable def qProfileTailOfHAdmissibleKernels {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n))
    (kB : BProfileKernelABC a c n) (kC : CProfileKernelABC a b n) : F :=
  let bc := survivingBCOfHAdmissibleKernels (a := a) (b := b) (c := c) (n := n) hb hc h kB kC
  qProfileABC (a := a) (b := b) (c := c) (n := n)
    (profileTailBCoefABC (a := a) (c := c) (n := n)
      (bFieldEquivBCoefABC (a := a) (c := c) (n := n) bc.1.1))
    (profileTailCCoefABC (a := a) (b := b) (n := n)
      (cFieldEquivCCoefABC (a := a) (b := b) (n := n) bc.1.2))

lemma qpairOfHAdmissibleKernels_eq_qProfileTailOfHAdmissibleKernels_of_odd
    {a b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (h : HAdmissible (n := n)) (kB : BProfileKernelABC a c n) (kC : CProfileKernelABC a b n) :
    qpairOfHAdmissibleKernels (a := a) (b := b) (c := c) (n := n) hb hc h kB kC =
      qProfileTailOfHAdmissibleKernels (a := a) (b := b) (c := c) (n := n) hb hc h kB kC := by
  change
    QpairABC (a := a) (b := b) (c := c) (n := n)
      (survivingBCOfHAdmissibleKernels
        (a := a) (b := b) (c := c) (n := n) hb hc h kB kC).1.1
      (survivingBCOfHAdmissibleKernels
        (a := a) (b := b) (c := c) (n := n) hb hc h kB kC).1.2
    =
    qProfileTailOfHAdmissibleKernels
      (a := a) (b := b) (c := c) (n := n) hb hc h kB kC
  simpa [qProfileTailOfHAdmissibleKernels] using
    QpairABC_eq_qProfileABC_tail_of_surviving_of_odd
      (a := a) (b := b) (c := c) (n := n) hb hc hn
      (survivingBCOfHAdmissibleKernels
        (a := a) (b := b) (c := c) (n := n) hb hc h kB kC)

noncomputable def hAdmissibleOddKernelTailSignSumABC {a b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (h : HAdmissible (n := n)) : ℤ :=
  ∑ kB : BProfileKernelABC a c n,
    ∑ kC : CProfileKernelABC a b n,
      bitSign (qProfileTailOfHAdmissibleKernels
        (a := a) (b := b) (c := c) (n := n) hb hc h kB kC)

lemma hAdmissibleKernelSignSumABC_eq_oddKernelTailSignSumABC_of_odd
    {a b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) (hn : Odd n)
    (h : HAdmissible (n := n)) :
    hAdmissibleKernelSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h =
      hAdmissibleOddKernelTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  unfold hAdmissibleKernelSignSumABC hAdmissibleOddKernelTailSignSumABC
  refine Finset.sum_congr rfl ?_
  intro kB hkB
  refine Finset.sum_congr rfl ?_
  intro kC hkC
  rw [qpairOfHAdmissibleKernels_eq_qProfileTailOfHAdmissibleKernels_of_odd
    (a := a) (b := b) (c := c) (n := n) hb hc hn h kB kC]

theorem DeltaABC_after_A_eq_sum_hAdmissibleOddKernelTailSignSums_of_odd
    {a b c n : ℕ} [NeZero n] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    DeltaABC a b c n =
      (2 : ℤ) ^ (n ^ (b + c)) *
        ∑ h : HAdmissible (n := n),
          hAdmissibleOddKernelTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
  rw [DeltaABC_after_A_eq_sum_hAdmissibleKernelSignSums
    (a := a) (b := b) (c := c) (n := n) ha hb hc]
  have hsum :
      (∑ h : HAdmissible (n := n),
        hAdmissibleKernelSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h)
        =
      ∑ h : HAdmissible (n := n),
        hAdmissibleOddKernelTailSignSumABC (a := a) (b := b) (c := c) (n := n) hb hc h := by
    refine Finset.sum_congr rfl ?_
    intro h hh
    exact hAdmissibleKernelSignSumABC_eq_oddKernelTailSignSumABC_of_odd
      (a := a) (b := b) (c := c) (n := n) hb hc hn h
  rw [hsum]

end Core3loop
