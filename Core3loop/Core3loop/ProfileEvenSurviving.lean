import Core3loop.ProfileEvenData
import Core3loop.ProfilePair

open scoped BigOperators

namespace Core3loop

structure EvenVisibleDataABC (b c n : ℕ) [NeZero n] where
  bc : ScalarVisibleCompat b c n
  btwo : ScalarBCoef c n
  ctwo : ScalarCCoef b n

structure EvenSurvivingDataABC (a b c n : ℕ) [NeZero n] where
  visible : EvenVisibleDataABC b c n
  XB : EvenTailBModelABC a c n
  YC : EvenTailCModelABC a b n

noncomputable def evenVisibleDataABCEquivTuple {b c n : ℕ} [NeZero n] :
    EvenVisibleDataABC b c n ≃
      (ScalarVisibleCompat b c n × ScalarBCoef c n) × ScalarCCoef b n where
  toFun x := ((x.bc, x.btwo), x.ctwo)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable instance instFintypeEvenVisibleDataABC {b c n : ℕ} [NeZero n] :
    Fintype (EvenVisibleDataABC b c n) :=
  Fintype.ofEquiv (((ScalarVisibleCompat b c n × ScalarBCoef c n) × ScalarCCoef b n))
    (evenVisibleDataABCEquivTuple (b := b) (c := c) (n := n)).symm

noncomputable def evenSurvivingDataABCEquivTuple {a b c n : ℕ} [NeZero n] :
    EvenSurvivingDataABC a b c n ≃
      (EvenVisibleDataABC b c n × EvenTailBModelABC a c n) × EvenTailCModelABC a b n where
  toFun x := ((x.visible, x.XB), x.YC)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable instance instFintypeEvenSurvivingDataABC {a b c n : ℕ} [NeZero n] :
    Fintype (EvenSurvivingDataABC a b c n) :=
  Fintype.ofEquiv
    (((EvenVisibleDataABC b c n × EvenTailBModelABC a c n) × EvenTailCModelABC a b n))
    (evenSurvivingDataABCEquivTuple (a := a) (b := b) (c := c) (n := n)).symm

@[ext] theorem EvenVisibleDataABC.ext {b c n : ℕ} [NeZero n]
    {x y : EvenVisibleDataABC b c n}
    (hbc : x.bc = y.bc) (hbtwo : x.btwo = y.btwo) (hctwo : x.ctwo = y.ctwo) :
    x = y := by
  cases x
  cases y
  cases hbc
  cases hbtwo
  cases hctwo
  rfl

@[ext] theorem EvenSurvivingDataABC.ext {a b c n : ℕ} [NeZero n]
    {x y : EvenSurvivingDataABC a b c n}
    (hvisible : x.visible = y.visible) (hXB : x.XB = y.XB) (hYC : x.YC = y.YC) :
    x = y := by
  cases x
  cases y
  cases hvisible
  cases hXB
  cases hYC
  rfl

noncomputable def evenVisibleSignABC {b c n : ℕ} [NeZero n]
    (d : EvenVisibleDataABC b c n) : ℤ :=
  bitSign
    (qEvenABC (b := b) (c := c) (n := n)
      (d.bc.bcoef, d.btwo) (d.bc.ccoef, d.ctwo))

noncomputable def evenTailSignABC {a b c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) (YC : EvenTailCModelABC a b n) : ℤ :=
  bitSign
    (qProfileABC (a := a) (b := b) (c := c) (n := n)
      (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB)
      (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC))

noncomputable def evenDataSignABC {a b c n : ℕ} [NeZero n]
    (d : EvenSurvivingDataABC a b c n) : ℤ :=
  bitSign
    (qEvenABC (b := b) (c := c) (n := n)
        (d.visible.bc.bcoef, d.visible.btwo)
        (d.visible.bc.ccoef, d.visible.ctwo) +
      qProfileABC (a := a) (b := b) (c := c) (n := n)
        (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) d.XB)
        (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) d.YC))

lemma evenDataSignABC_eq_mul {a b c n : ℕ} [NeZero n]
    (d : EvenSurvivingDataABC a b c n) :
    evenDataSignABC (a := a) (b := b) (c := c) (n := n) d =
      evenVisibleSignABC (b := b) (c := c) (n := n) d.visible *
        evenTailSignABC (a := a) (b := b) (c := c) (n := n) d.XB d.YC := by
  unfold evenDataSignABC evenVisibleSignABC evenTailSignABC
  simpa using
    No13Migration.bitSign_add
      (qEvenABC (b := b) (c := c) (n := n)
        (d.visible.bc.bcoef, d.visible.btwo)
        (d.visible.bc.ccoef, d.visible.ctwo))
      (qProfileABC (a := a) (b := b) (c := c) (n := n)
        (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) d.XB)
        (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) d.YC))

lemma bKernelABC_real_eq_sigmaBCoefABC_adjacent {a c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (s : I n) (z : ZCoord c n) :
    No13Migration.bKernelABC_real (a := a) (c := c) (n := n) B s z =
      sigmaBCoefABC (a := a) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B) s z +
        sigmaBCoefABC (a := a) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B) (s + 1) z := by
  unfold No13Migration.bKernelABC_real sigmaBCoefABC sigmaProfile bFieldEquivBCoefABC
  rw [Finset.sum_add_distrib]
  simp [add_assoc, add_left_comm, add_comm]

lemma cKernelABC_real_eq_sigmaCCoefABC_adjacent {a b n : ℕ} [NeZero n]
    (C : CFieldABC a b n) (y : YCoord b n) (r : I n) :
    No13Migration.cKernelABC_real (a := a) (b := b) (n := n) C y r =
      sigmaCCoefABC (a := a) (b := b) (n := n)
          (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C) y r +
        sigmaCCoefABC (a := a) (b := b) (n := n)
          (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C) y (r + 1) := by
  unfold No13Migration.cKernelABC_real sigmaCCoefABC sigmaProfile cFieldEquivCCoefABC
  rw [Finset.sum_add_distrib]
  simp [add_assoc, add_left_comm, add_comm]

lemma coeffFromBC_abc_eq_zero_iff_evenHeadCompat {a b c n : ℕ} [NeZero n]
    (B : BFieldABC a c n) (C : CFieldABC a b n) :
    coeffFromBC_abc (a := a) (b := b) (c := c) (n := n) B C = 0 ↔
      ∀ y z,
        (evenHeadBPairABC (a := a) (c := c) (n := n)
          (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B)).1 (sumY y) z +
          (evenHeadBPairABC (a := a) (c := c) (n := n)
            (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B)).1 (sumY y + 1) z +
          (evenHeadCPairABC (a := a) (b := b) (n := n)
            (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C)).1 y (sumZ z) +
          (evenHeadCPairABC (a := a) (b := b) (n := n)
            (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C)).1 y (sumZ z + 1) = 0 := by
  change
    No13Migration.coeffFromBC_abc_real (a := a) (b := b) (c := c) (n := n) B C = 0 ↔ _
  constructor
  · intro h y z
    have hyz :=
      (No13Migration.coeffFromBC_abc_real_eq_zero_iff
        (a := a) (b := b) (c := c) (n := n) B C).mp h (y, z)
    have hsum :
        No13Migration.bKernelABC_real (a := a) (c := c) (n := n) B (sumY y) z +
            No13Migration.cKernelABC_real (a := a) (b := b) (n := n) C y (sumZ z) = 0 := by
      exact (No13Migration.F2_add_eq_zero_iff_eq' _ _).2 hyz
    simpa [add_assoc, fst_evenHeadBPairABC_eq_sigmaBCoefABC,
      fst_evenHeadCPairABC_eq_sigmaCCoefABC,
      bKernelABC_real_eq_sigmaBCoefABC_adjacent,
      cKernelABC_real_eq_sigmaCCoefABC_adjacent] using hsum
  · intro h
    exact (No13Migration.coeffFromBC_abc_real_eq_zero_iff
      (a := a) (b := b) (c := c) (n := n) B C).2 <| by
        intro yz
        have hsum := h yz.1 yz.2
        exact (No13Migration.F2_add_eq_zero_iff_eq' _ _).1 <| by
          simpa [add_assoc, fst_evenHeadBPairABC_eq_sigmaBCoefABC,
            fst_evenHeadCPairABC_eq_sigmaCCoefABC,
            bKernelABC_real_eq_sigmaBCoefABC_adjacent,
            cKernelABC_real_eq_sigmaCCoefABC_adjacent] using hsum

noncomputable def evenSurvivingToDataABC {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    SurvivingBC a b c n → EvenSurvivingDataABC a b c n
  | ⟨bc, hbc⟩ =>
      let bcoef := bFieldEquivBCoefABC (a := a) (c := c) (n := n) bc.1
      let ccoef := cFieldEquivCCoefABC (a := a) (b := b) (n := n) bc.2
      let bhead := evenHeadBPairABC (a := a) (c := c) (n := n) bcoef
      let chead := evenHeadCPairABC (a := a) (b := b) (n := n) ccoef
      let vis : EvenVisibleDataABC b c n := {
        bc := {
          bcoef := bhead.1
          ccoef := chead.1
          compat := by
            intro y z
            exact (coeffFromBC_abc_eq_zero_iff_evenHeadCompat
              (a := a) (b := b) (c := c) (n := n) bc.1 bc.2).mp hbc y z
        }
        btwo := bhead.2
        ctwo := chead.2
      }
      {
        visible := vis
        XB := evenTailBModelOfBCoefABC (a := a) (c := c) (n := n) hn ha2 bcoef
        YC := evenTailCModelOfCCoefABC (a := a) (b := b) (n := n) hn ha2 ccoef
      }

noncomputable def evenDataToSurvivingABC {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    EvenSurvivingDataABC a b c n → SurvivingBC a b c n
  | ⟨vis, XB, YC⟩ =>
      let bcoef := evenBuildBCoefABC (a := a) (c := c) (n := n)
        (vis.bc.bcoef, vis.btwo) XB
      let ccoef := evenBuildCCoefABC (a := a) (b := b) (n := n)
        (vis.bc.ccoef, vis.ctwo) YC
      let B := (bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm bcoef
      let C := (cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm ccoef
      ⟨(B, C), by
        have hbhead :
            (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef).1 = vis.bc.bcoef := by
          simpa [bcoef] using congrArg Prod.fst
            (evenHeadBPairABC_evenBuildBCoefABC_eq
              (a := a) (c := c) (n := n) hn ha2 (vis.bc.bcoef, vis.btwo) XB)
        have hchead :
            (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef).1 = vis.bc.ccoef := by
          simpa [ccoef] using congrArg Prod.fst
            (evenHeadCPairABC_evenBuildCCoefABC_eq
              (a := a) (b := b) (n := n) hn ha2 (vis.bc.ccoef, vis.ctwo) YC)
        exact (coeffFromBC_abc_eq_zero_iff_evenHeadCompat
          (a := a) (b := b) (c := c) (n := n) B C).2 <| by
            intro y z
            simpa [B, C, bcoef, ccoef, hbhead, hchead] using vis.bc.compat y z⟩

lemma evenDataToSurvivingABC_evenSurvivingToDataABC {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (bc : SurvivingBC a b c n) :
    evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2
      (evenSurvivingToDataABC (a := a) (b := b) (c := c) (n := n) hn ha2 bc) = bc := by
  rcases bc with ⟨⟨B, C⟩, hbc⟩
  apply Subtype.ext
  apply Prod.ext
  · apply (bFieldEquivBCoefABC (a := a) (c := c) (n := n)).injective
    simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
      evenBuildBCoefABC_head_tail_eq (a := a) (c := c) (n := n) hn ha2
        (bFieldEquivBCoefABC (a := a) (c := c) (n := n) B)
  · apply (cFieldEquivCCoefABC (a := a) (b := b) (n := n)).injective
    simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
      evenBuildCCoefABC_head_tail_eq (a := a) (b := b) (n := n) hn ha2
        (cFieldEquivCCoefABC (a := a) (b := b) (n := n) C)

lemma evenSurvivingToDataABC_evenDataToSurvivingABC {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (d : EvenSurvivingDataABC a b c n) :
    evenSurvivingToDataABC (a := a) (b := b) (c := c) (n := n) hn ha2
      (evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2 d) = d := by
  rcases d with ⟨vis, XB, YC⟩
  rcases vis with ⟨bc, btwo, ctwo⟩
  apply EvenSurvivingDataABC.ext
  · apply EvenVisibleDataABC.ext
    · apply ScalarVisibleCompat.ext
      · simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
          congrArg Prod.fst
            (evenHeadBPairABC_evenBuildBCoefABC_eq
              (a := a) (c := c) (n := n) hn ha2 (bc.bcoef, btwo) XB)
      · simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
          congrArg Prod.fst
            (evenHeadCPairABC_evenBuildCCoefABC_eq
              (a := a) (b := b) (n := n) hn ha2 (bc.ccoef, ctwo) YC)
    · simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
        congrArg Prod.snd
          (evenHeadBPairABC_evenBuildBCoefABC_eq
            (a := a) (c := c) (n := n) hn ha2 (bc.bcoef, btwo) XB)
    · simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
        congrArg Prod.snd
          (evenHeadCPairABC_evenBuildCCoefABC_eq
            (a := a) (b := b) (n := n) hn ha2 (bc.ccoef, ctwo) YC)
  · simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
      evenTailBModelOfBCoefABC_evenBuildBCoefABC_eq
        (a := a) (c := c) (n := n) hn ha2 (bc.bcoef, btwo) XB
  · simpa [evenSurvivingToDataABC, evenDataToSurvivingABC] using
      evenTailCModelOfCCoefABC_evenBuildCCoefABC_eq
        (a := a) (b := b) (n := n) hn ha2 (bc.ccoef, ctwo) YC

noncomputable def evenSurvivingEquivABC {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    SurvivingBC a b c n ≃ EvenSurvivingDataABC a b c n where
  toFun := evenSurvivingToDataABC (a := a) (b := b) (c := c) (n := n) hn ha2
  invFun := evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2
  left_inv := evenDataToSurvivingABC_evenSurvivingToDataABC
    (a := a) (b := b) (c := c) (n := n) hn ha2
  right_inv := evenSurvivingToDataABC_evenDataToSurvivingABC
    (a := a) (b := b) (c := c) (n := n) hn ha2

lemma qpair_evenDataToSurvivingABC_eq_head_add_tail {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (d : EvenSurvivingDataABC a b c n) :
    QpairABC (a := a) (b := b) (c := c) (n := n)
        (evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2 d).1.1
        (evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2 d).1.2
      =
        qEvenABC (b := b) (c := c) (n := n)
          (d.visible.bc.bcoef, d.visible.btwo)
          (d.visible.bc.ccoef, d.visible.ctwo) +
        qProfileABC (a := a) (b := b) (c := c) (n := n)
          (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) d.XB)
          (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) d.YC) := by
  rcases d with ⟨vis, XB, YC⟩
  rcases vis with ⟨bc, btwo, ctwo⟩
  let bcoef := evenBuildBCoefABC (a := a) (c := c) (n := n) (bc.bcoef, btwo) XB
  let ccoef := evenBuildCCoefABC (a := a) (b := b) (n := n) (bc.ccoef, ctwo) YC
  have hbhead :
      evenHeadBPairABC (a := a) (c := c) (n := n) bcoef = (bc.bcoef, btwo) := by
    simpa [bcoef] using
      evenHeadBPairABC_evenBuildBCoefABC_eq
        (a := a) (c := c) (n := n) hn ha2 (bc.bcoef, btwo) XB
  have hchead :
      evenHeadCPairABC (a := a) (b := b) (n := n) ccoef = (bc.ccoef, ctwo) := by
    simpa [ccoef] using
      evenHeadCPairABC_evenBuildCCoefABC_eq
        (a := a) (b := b) (n := n) hn ha2 (bc.ccoef, ctwo) YC
  have hbtail :
      evenTailBCoefABC (a := a) (c := c) (n := n) bcoef =
        evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB := by
    simpa [bcoef] using
      evenTailBCoefABC_evenBuildBCoefABC_eq
        (a := a) (c := c) (n := n) hn ha2 (bc.bcoef, btwo) XB
  have hctail :
      evenTailCCoefABC (a := a) (b := b) (n := n) ccoef =
        evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC := by
    simpa [ccoef] using
      evenTailCCoefABC_evenBuildCCoefABC_eq
        (a := a) (b := b) (n := n) hn ha2 (bc.ccoef, ctwo) YC
  have hq :
      QpairABC (a := a) (b := b) (c := c) (n := n)
          ((bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm bcoef)
          ((cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm ccoef)
        =
      qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef := by
    simpa [bcoef, ccoef] using
      QpairABC_eq_qProfileABC (a := a) (b := b) (c := c) (n := n)
        ((bFieldEquivBCoefABC (a := a) (c := c) (n := n)).symm bcoef)
        ((cFieldEquivCCoefABC (a := a) (b := b) (n := n)).symm ccoef)
  calc
    QpairABC (a := a) (b := b) (c := c) (n := n)
        (evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2
          ⟨⟨bc, btwo, ctwo⟩, XB, YC⟩).1.1
        (evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2
          ⟨⟨bc, btwo, ctwo⟩, XB, YC⟩).1.2
      =
        qProfileABC (a := a) (b := b) (c := c) (n := n) bcoef ccoef := by
          simpa [evenDataToSurvivingABC, bcoef, ccoef] using hq
    _ =
        qEvenABC (b := b) (c := c) (n := n)
            (evenHeadBPairABC (a := a) (c := c) (n := n) bcoef)
            (evenHeadCPairABC (a := a) (b := b) (n := n) ccoef) +
          qProfileABC (a := a) (b := b) (c := c) (n := n)
            (evenTailBCoefABC (a := a) (c := c) (n := n) bcoef)
            (evenTailCCoefABC (a := a) (b := b) (n := n) ccoef) := by
              simpa using
                qProfileABC_eq_qEvenABC_add_tail_of_even
                  (a := a) (b := b) (c := c) (n := n) hn ha2 bcoef ccoef
    _ =
        qEvenABC (b := b) (c := c) (n := n) (bc.bcoef, btwo) (bc.ccoef, ctwo) +
          qProfileABC (a := a) (b := b) (c := c) (n := n)
            (evenTailBCoefOfModelABC (a := a) (c := c) (n := n) XB)
            (evenTailCCoefOfModelABC (a := a) (b := b) (n := n) YC) := by
              simp [hbhead, hchead, hbtail, hctail]

lemma evenDataSignABC_eq_qpair_sign {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (d : EvenSurvivingDataABC a b c n) :
    evenDataSignABC (a := a) (b := b) (c := c) (n := n) d =
      bitSign
        (QpairABC (a := a) (b := b) (c := c) (n := n)
          (evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2 d).1.1
          (evenDataToSurvivingABC (a := a) (b := b) (c := c) (n := n) hn ha2 d).1.2) := by
  rw [qpair_evenDataToSurvivingABC_eq_head_add_tail
    (a := a) (b := b) (c := c) (n := n) hn ha2 d]
  rfl

lemma sum_survivingBC_eq_sum_evenDataABC_of_even {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    ∑ bc : SurvivingBC a b c n,
      bitSign (QpairABC (a := a) (b := b) (c := c) (n := n) bc.1.1 bc.1.2)
      =
        ∑ d : EvenSurvivingDataABC a b c n,
          evenDataSignABC (a := a) (b := b) (c := c) (n := n) d := by
  classical
  let e := evenSurvivingEquivABC (a := a) (b := b) (c := c) (n := n) hn ha2
  calc
    ∑ bc : SurvivingBC a b c n,
        bitSign (QpairABC (a := a) (b := b) (c := c) (n := n) bc.1.1 bc.1.2)
      =
        ∑ d : EvenSurvivingDataABC a b c n,
          bitSign
            (QpairABC (a := a) (b := b) (c := c) (n := n)
              (e.symm d).1.1 (e.symm d).1.2) := by
                simpa [e] using
                  (Equiv.sum_comp e
                    (fun d : EvenSurvivingDataABC a b c n =>
                      bitSign
                        (QpairABC (a := a) (b := b) (c := c) (n := n)
                          (e.symm d).1.1 (e.symm d).1.2)))
    _ =
        ∑ d : EvenSurvivingDataABC a b c n,
          evenDataSignABC (a := a) (b := b) (c := c) (n := n) d := by
            refine Finset.sum_congr rfl ?_
            intro d hd
            simpa [e] using
              (evenDataSignABC_eq_qpair_sign
                (a := a) (b := b) (c := c) (n := n) hn ha2 d).symm

end Core3loop
