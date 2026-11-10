import Core3loop.OperatorT
import Core3loop.EvenCase
import Core3loop.ProfileKernelSplit
import No16.OddCase

open scoped BigOperators

namespace Core3loop

noncomputable def xCoordEquivNo16I {a n : ℕ} [NeZero n] :
    XCoord a n ≃ No16.I (ProfileCard a n) :=
  Fintype.equivOfCardEq (by
    rw [card_XCoord]
    simp [ProfileCard, No16.I])

noncomputable def profileEquivNo16 {a n : ℕ} [NeZero n] :
    ProfileABC a n ≃ No16.Profile (ProfileCard a n) where
  toFun := fun x i => x ((xCoordEquivNo16I (a := a) (n := n)).symm i)
  invFun := fun y p => y ((xCoordEquivNo16I (a := a) (n := n)) p)
  left_inv := by
    intro x
    funext p
    simp
  right_inv := by
    intro y
    funext i
    simp

lemma sigmaProfile_eq_no16_sigma {a n : ℕ} [NeZero n] (x : ProfileABC a n) :
    sigmaProfile (a := a) (n := n) x =
      No16.sigma ((profileEquivNo16 (a := a) (n := n)) x) := by
  change ∑ p : XCoord a n, x p =
    ∑ i : No16.I (ProfileCard a n), x ((xCoordEquivNo16I (a := a) (n := n)).symm i)
  symm
  simpa using
    (Function.Bijective.sum_comp
      (xCoordEquivNo16I (a := a) (n := n)).symm.bijective
      (fun p : XCoord a n => x p))

lemma dotProfile_eq_no16_dot {a n : ℕ} [NeZero n] (x y : ProfileABC a n) :
    dotProfile (a := a) (n := n) x y =
      No16.dot ((profileEquivNo16 (a := a) (n := n)) x)
        ((profileEquivNo16 (a := a) (n := n)) y) := by
  change ∑ p : XCoord a n, x p * y p =
    ∑ i : No16.I (ProfileCard a n),
      x ((xCoordEquivNo16I (a := a) (n := n)).symm i) *
        y ((xCoordEquivNo16I (a := a) (n := n)).symm i)
  symm
  simpa using
    (Function.Bijective.sum_comp
      (xCoordEquivNo16I (a := a) (n := n)).symm.bijective
      (fun p : XCoord a n => x p * y p))

lemma mem_Wodd_iff_mem_no16_Wodd {a n : ℕ} [NeZero n] (x : ProfileABC a n) :
    x ∈ Wodd (a := a) (n := n) ↔
      (profileEquivNo16 (a := a) (n := n) x) ∈ No16.Wodd (n := ProfileCard a n) := by
  constructor
  · intro hx
    change No16.sigmaMap (n := ProfileCard a n) ((profileEquivNo16 (a := a) (n := n)) x) = 0
    rw [show No16.sigmaMap (n := ProfileCard a n)
        ((profileEquivNo16 (a := a) (n := n)) x) =
          No16.sigma ((profileEquivNo16 (a := a) (n := n)) x) by rfl]
    rw [← sigmaProfile_eq_no16_sigma (a := a) (n := n) x]
    exact sigma_eq_zero_of_mem_Wodd hx
  · intro hx
    change sigmaProfileMap (a := a) (n := n) x = 0
    rw [show sigmaProfileMap (a := a) (n := n) x = sigmaProfile (a := a) (n := n) x by rfl]
    rw [sigmaProfile_eq_no16_sigma (a := a) (n := n) x]
    exact No16.sigma_eq_zero_of_mem_Wodd hx

noncomputable def profileWoddEquivNo16Wodd {a n : ℕ} [NeZero n] :
    ↥(Wodd (a := a) (n := n)) ≃ ↥(No16.Wodd (n := ProfileCard a n)) where
  toFun := fun x =>
    ⟨(profileEquivNo16 (a := a) (n := n)) x.1,
      (mem_Wodd_iff_mem_no16_Wodd (a := a) (n := n) x.1).1 x.2⟩
  invFun := fun x =>
    ⟨(profileEquivNo16 (a := a) (n := n)).symm x.1,
      (mem_Wodd_iff_mem_no16_Wodd (a := a) (n := n)
        ((profileEquivNo16 (a := a) (n := n)).symm x.1)).2 (by
          simpa using x.2)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simpa using (profileEquivNo16 (a := a) (n := n)).left_inv x.1
  right_inv := by
    intro x
    apply Subtype.ext
    simpa using (profileEquivNo16 (a := a) (n := n)).right_inv x.1

noncomputable def xCoordEquivNo16IOfEq {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    XCoord a n ≃ No16.I (2 * m + 1) :=
  Fintype.equivOfCardEq (by
    calc
      Fintype.card (XCoord a n) = ProfileCard a n := by
        rw [card_XCoord, ProfileCard]
      _ = 2 * m + 1 := hm
      _ = Fintype.card (No16.I (2 * m + 1)) := by
        simp [No16.I])

noncomputable def profileEquivNo16OfEq {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    ProfileABC a n ≃ No16.Profile (2 * m + 1) where
  toFun := fun x i => x ((xCoordEquivNo16IOfEq (a := a) (n := n) (m := m) hm).symm i)
  invFun := fun y p => y ((xCoordEquivNo16IOfEq (a := a) (n := n) (m := m) hm) p)
  left_inv := by
    intro x
    funext p
    simp
  right_inv := by
    intro y
    funext i
    simp

lemma sigmaProfile_eq_no16_sigma_ofEq {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) (x : ProfileABC a n) :
    sigmaProfile (a := a) (n := n) x =
      No16.sigma ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x) := by
  change ∑ p : XCoord a n, x p =
    ∑ i : No16.I (2 * m + 1), x ((xCoordEquivNo16IOfEq (a := a) (n := n) (m := m) hm).symm i)
  symm
  simpa using
    (Function.Bijective.sum_comp
      (xCoordEquivNo16IOfEq (a := a) (n := n) (m := m) hm).symm.bijective
      (fun p : XCoord a n => x p))

lemma dotProfile_eq_no16_dot_ofEq {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) (x y : ProfileABC a n) :
    dotProfile (a := a) (n := n) x y =
      No16.dot ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x)
        ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) y) := by
  change ∑ p : XCoord a n, x p * y p =
    ∑ i : No16.I (2 * m + 1),
      x ((xCoordEquivNo16IOfEq (a := a) (n := n) (m := m) hm).symm i) *
        y ((xCoordEquivNo16IOfEq (a := a) (n := n) (m := m) hm).symm i)
  symm
  simpa using
    (Function.Bijective.sum_comp
      (xCoordEquivNo16IOfEq (a := a) (n := n) (m := m) hm).symm.bijective
      (fun p : XCoord a n => x p * y p))

lemma mem_Wodd_iff_mem_no16_WoddOfEq {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) (x : ProfileABC a n) :
    x ∈ Wodd (a := a) (n := n) ↔
      (profileEquivNo16OfEq (a := a) (n := n) (m := m) hm x) ∈ No16.Wodd (n := 2 * m + 1) := by
  constructor
  · intro hx
    change No16.sigmaMap (n := 2 * m + 1)
      ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x) = 0
    rw [show No16.sigmaMap (n := 2 * m + 1)
        ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x) =
          No16.sigma ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x) by rfl]
    rw [← sigmaProfile_eq_no16_sigma_ofEq (a := a) (n := n) (m := m) hm x]
    exact sigma_eq_zero_of_mem_Wodd hx
  · intro hx
    change sigmaProfileMap (a := a) (n := n) x = 0
    rw [show sigmaProfileMap (a := a) (n := n) x = sigmaProfile (a := a) (n := n) x by rfl]
    rw [sigmaProfile_eq_no16_sigma_ofEq (a := a) (n := n) (m := m) hm x]
    exact No16.sigma_eq_zero_of_mem_Wodd hx

noncomputable def profileWoddEquivNo16WoddOfEq {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    ↥(Wodd (a := a) (n := n)) ≃ ↥(No16.Wodd (n := 2 * m + 1)) where
  toFun := fun x =>
    ⟨(profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x.1, by
      change ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x.1) ∈ No16.Wodd (n := 2 * m + 1)
      exact (mem_Wodd_iff_mem_no16_WoddOfEq (a := a) (n := n) (m := m) hm x.1).1 x.2⟩
  invFun := fun x =>
    ⟨(profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).symm x.1, by
      change ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).symm x.1) ∈ Wodd (a := a) (n := n)
      have hx :
          (profileEquivNo16OfEq (a := a) (n := n) (m := m) hm)
            ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).symm x.1)
            ∈ No16.Wodd (n := 2 * m + 1) := by
        simpa using x.2
      exact (mem_Wodd_iff_mem_no16_WoddOfEq (a := a) (n := n) (m := m) hm
        ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).symm x.1)).2 hx⟩
  left_inv := by
    intro x
    apply Subtype.ext
    change ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).symm
      ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm) x.1)) = x.1
    simpa using (profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).left_inv x.1
  right_inv := by
    intro x
    apply Subtype.ext
    change ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm)
      ((profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).symm x.1)) = x.1
    simpa using (profileEquivNo16OfEq (a := a) (n := n) (m := m) hm).right_inv x.1

noncomputable def oddCoordPairEquivWoddABC {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    ↥(Wodd (a := a) (n := n)) ≃ ((Fin m → F) × (Fin m → F)) :=
  (profileWoddEquivNo16WoddOfEq (a := a) (n := n) (m := m) hm).trans
    (by simpa using (No16.oddCoordPairEquivWodd (m := m)))

noncomputable def oddUCoordProfile {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (x : ↥(Wodd (a := a) (n := n))) (i : Fin m) : F :=
  (oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm x).1 i

noncomputable def oddVCoordProfile {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (x : ↥(Wodd (a := a) (n := n))) (i : Fin m) : F :=
  (oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm x).2 i

noncomputable def oddWoddCoordPairing {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (x y : ↥(Wodd (a := a) (n := n))) : F :=
  Finset.univ.sum fun i : Fin m =>
    (oddUCoordProfile (a := a) (n := n) (m := m) hm x i *
        oddVCoordProfile (a := a) (n := n) (m := m) hm y i) +
      (oddVCoordProfile (a := a) (n := n) (m := m) hm x i *
        oddUCoordProfile (a := a) (n := n) (m := m) hm y i)

lemma dotProfile_oddSymplectic_coords {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (x y : ↥(Wodd (a := a) (n := n))) :
    dotProfile (a := a) (n := n) x.1 y.1 =
      oddWoddCoordPairing (a := a) (n := n) (m := m) hm x y := by
  let e := profileWoddEquivNo16WoddOfEq (a := a) (n := n) (m := m) hm
  have hdot :=
    No16.dot_oddSymplectic_coords (m := m) (e x) (e y)
  have hleft :
      No16.dot ((e x : ↥(No16.Wodd (n := 2 * m + 1))) : No16.Profile (2 * m + 1))
        ((e y : ↥(No16.Wodd (n := 2 * m + 1))) : No16.Profile (2 * m + 1)) =
        dotProfile (a := a) (n := n) x.1 y.1 := by
    simpa [e, profileWoddEquivNo16WoddOfEq] using
      (dotProfile_eq_no16_dot_ofEq (a := a) (n := n) (m := m) hm x.1 y.1).symm
  rw [← hleft]
  simpa [oddWoddCoordPairing, oddUCoordProfile, oddVCoordProfile,
    oddCoordPairEquivWoddABC, e]
    using hdot

abbrev OddCoordScalarBCoef (c n m : ℕ) := Fin m → ScalarBCoef c n

abbrev OddCoordScalarCCoef (b n m : ℕ) := Fin m → ScalarCCoef b n

noncomputable def oddUScalarBCoefABC {a c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (bτ : BWoddBCoefABC a c n) (i : Fin m) : ScalarBCoef c n :=
  fun t z =>
    oddUCoordProfile (a := a) (n := n) (m := m) hm
      ⟨bτ.1 t z, bτ.2 t z⟩ i

noncomputable def oddVScalarBCoefABC {a c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (bτ : BWoddBCoefABC a c n) (i : Fin m) : ScalarBCoef c n :=
  fun t z =>
    oddVCoordProfile (a := a) (n := n) (m := m) hm
      ⟨bτ.1 t z, bτ.2 t z⟩ i

noncomputable def oddUScalarCCoefABC {a b n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (cτ : CWoddCCoefABC a b n) (i : Fin m) : ScalarCCoef b n :=
  fun y r =>
    oddUCoordProfile (a := a) (n := n) (m := m) hm
      ⟨cτ.1 y r, cτ.2 y r⟩ i

noncomputable def oddVScalarCCoefABC {a b n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (cτ : CWoddCCoefABC a b n) (i : Fin m) : ScalarCCoef b n :=
  fun y r =>
    oddVCoordProfile (a := a) (n := n) (m := m) hm
      ⟨cτ.1 y r, cτ.2 y r⟩ i

noncomputable def oddCoordBCoefEquivBWoddBCoefABC {a c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    BWoddBCoefABC a c n ≃ (OddCoordScalarBCoef c n m × OddCoordScalarBCoef c n m) where
  toFun := fun bτ =>
    (oddUScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ,
      oddVScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ)
  invFun := fun UV =>
    ⟨(fun t z =>
        ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
          ((fun i => UV.1 i t z), (fun i => UV.2 i t z))).1),
      fun t z =>
        ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
          ((fun i => UV.1 i t z), (fun i => UV.2 i t z))).2⟩
  left_inv := by
    intro bτ
    apply Subtype.ext
    funext t z
    change
      (((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm)
            ⟨bτ.1 t z, bτ.2 t z⟩)).1) = bτ.1 t z
    exact congrArg Subtype.val
      ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).left_inv
        ⟨bτ.1 t z, bτ.2 t z⟩)
  right_inv := by
    intro UV
    apply Prod.ext
    · funext i t z
      change
        (oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
            ((fun j => UV.1 j t z), fun j => UV.2 j t z))).1 i = UV.1 i t z
      exact congrFun
        (congrArg Prod.fst
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).right_inv
            ((fun j => UV.1 j t z), fun j => UV.2 j t z))) i
    · funext i t z
      change
        (oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
            ((fun j => UV.1 j t z), fun j => UV.2 j t z))).2 i = UV.2 i t z
      exact congrFun
        (congrArg Prod.snd
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).right_inv
            ((fun j => UV.1 j t z), fun j => UV.2 j t z))) i

noncomputable def oddCoordCCoefEquivCWoddCCoefABC {a b n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1) :
    CWoddCCoefABC a b n ≃ (OddCoordScalarCCoef b n m × OddCoordScalarCCoef b n m) where
  toFun := fun cτ =>
    (oddUScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ,
      oddVScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ)
  invFun := fun UV =>
    ⟨(fun y r =>
        ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
          ((fun i => UV.1 i y r), (fun i => UV.2 i y r))).1),
      fun y r =>
        ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
          ((fun i => UV.1 i y r), (fun i => UV.2 i y r))).2⟩
  left_inv := by
    intro cτ
    apply Subtype.ext
    funext y r
    change
      (((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm)
            ⟨cτ.1 y r, cτ.2 y r⟩)).1) = cτ.1 y r
    exact congrArg Subtype.val
      ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).left_inv
        ⟨cτ.1 y r, cτ.2 y r⟩)
  right_inv := by
    intro UV
    apply Prod.ext
    · funext i y r
      change
        (oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
            ((fun j => UV.1 j y r), fun j => UV.2 j y r))).1 i = UV.1 i y r
      exact congrFun
        (congrArg Prod.fst
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).right_inv
            ((fun j => UV.1 j y r), fun j => UV.2 j y r))) i
    · funext i y r
      change
        (oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).symm
            ((fun j => UV.1 j y r), fun j => UV.2 j y r))).2 i = UV.2 i y r
      exact congrFun
        (congrArg Prod.snd
          ((oddCoordPairEquivWoddABC (a := a) (n := n) (m := m) hm).right_inv
            ((fun j => UV.1 j y r), fun j => UV.2 j y r))) i

noncomputable def oddTailCoordQSumABC
    {a b c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (bτ : BWoddBCoefABC a c n) (cτ : CWoddCCoefABC a b n) : F :=
  Finset.univ.sum fun i : Fin m =>
    (qScalar
        (b := b) (c := c) (n := n)
        (oddUScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
        (oddVScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i)) +
      (qScalar
        (b := b) (c := c) (n := n)
        (oddVScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
        (oddUScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i))

lemma qProfileABC_eq_sum_qScalar_of_odd_coords
    {a b c n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 1)
    (bτ : BWoddBCoefABC a c n) (cτ : CWoddCCoefABC a b n) :
    qProfileABC (a := a) (b := b) (c := c) (n := n) bτ.1 cτ.1 =
      oddTailCoordQSumABC (a := a) (b := b) (c := c) (n := n) (m := m) hm bτ cτ := by
  unfold qProfileABC qLeftProfileABC qRightProfileABC oddTailCoordQSumABC qScalar
  calc
    (∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n) (bτ.1 (sumY y) z) (cτ.1 y (sumZ z))) +
      (∑ y : YCoord b n, ∑ z : ZCoord c n,
        dotProfile (a := a) (n := n) (bτ.1 (sumY y + 1) z) (cτ.1 y (sumZ z + 1)))
      =
      (∑ y : YCoord b n, ∑ z : ZCoord c n,
          ∑ i : Fin m,
            ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
              oddVCoordProfile (a := a) (n := n) (m := m) hm
                ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i) +
             (oddVCoordProfile (a := a) (n := n) (m := m) hm
                ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
              oddUCoordProfile (a := a) (n := n) (m := m) hm
                ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i))) +
      (∑ y : YCoord b n, ∑ z : ZCoord c n,
          ∑ i : Fin m,
            ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
              oddVCoordProfile (a := a) (n := n) (m := m) hm
                ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i) +
             (oddVCoordProfile (a := a) (n := n) (m := m) hm
                ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
              oddUCoordProfile (a := a) (n := n) (m := m) hm
                ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i))) := by
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [dotProfile_oddSymplectic_coords (a := a) (n := n) (m := m) hm
            ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩
            ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩]
          simp [oddWoddCoordPairing]
        · refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [dotProfile_oddSymplectic_coords (a := a) (n := n) (m := m) hm
            ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩
            ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩]
          simp [oddWoddCoordPairing]
    _ =
      (∑ i : Fin m, ∑ y : YCoord b n, ∑ z : ZCoord c n,
          ((oddUCoordProfile (a := a) (n := n) (m := m) hm
              ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
            oddVCoordProfile (a := a) (n := n) (m := m) hm
              ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i) +
           (oddVCoordProfile (a := a) (n := n) (m := m) hm
              ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
            oddUCoordProfile (a := a) (n := n) (m := m) hm
              ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i))) +
      (∑ i : Fin m, ∑ y : YCoord b n, ∑ z : ZCoord c n,
          ((oddUCoordProfile (a := a) (n := n) (m := m) hm
              ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
            oddVCoordProfile (a := a) (n := n) (m := m) hm
              ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i) +
           (oddVCoordProfile (a := a) (n := n) (m := m) hm
              ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
            oddUCoordProfile (a := a) (n := n) (m := m) hm
              ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i))) := by
        congr 1
        · calc
            ∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ i : Fin m,
                ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
                  oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i) +
                 (oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
                  oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i))
                =
              ∑ y : YCoord b n, ∑ i : Fin m, ∑ z : ZCoord c n,
                ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
                  oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i) +
                 (oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
                  oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i)) := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [Finset.sum_comm]
            _ =
              ∑ i : Fin m, ∑ y : YCoord b n, ∑ z : ZCoord c n,
                ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
                  oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i) +
                 (oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
                  oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i)) := by
                    rw [Finset.sum_comm]
        · calc
            ∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ i : Fin m,
                ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
                  oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i) +
                 (oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
                  oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i))
                =
              ∑ y : YCoord b n, ∑ i : Fin m, ∑ z : ZCoord c n,
                ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
                  oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i) +
                 (oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
                  oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i)) := by
                    refine Finset.sum_congr rfl ?_
                    intro y hy
                    rw [Finset.sum_comm]
            _ =
              ∑ i : Fin m, ∑ y : YCoord b n, ∑ z : ZCoord c n,
                ((oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
                  oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i) +
                 (oddVCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
                  oddUCoordProfile (a := a) (n := n) (m := m) hm
                    ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i)) := by
                    rw [Finset.sum_comm]
    _ =
      ∑ i : Fin m,
        ((∑ y : YCoord b n, ∑ z : ZCoord c n,
            (oddUCoordProfile (a := a) (n := n) (m := m) hm
              ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
              oddVCoordProfile (a := a) (n := n) (m := m) hm
                ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i +
              oddUCoordProfile (a := a) (n := n) (m := m) hm
                ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
                oddVCoordProfile (a := a) (n := n) (m := m) hm
                  ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i)) +
          (∑ y : YCoord b n, ∑ z : ZCoord c n,
            (oddVCoordProfile (a := a) (n := n) (m := m) hm
              ⟨bτ.1 (sumY y) z, bτ.2 (sumY y) z⟩ i *
              oddUCoordProfile (a := a) (n := n) (m := m) hm
                ⟨cτ.1 y (sumZ z), cτ.2 y (sumZ z)⟩ i +
              oddVCoordProfile (a := a) (n := n) (m := m) hm
                ⟨bτ.1 (sumY y + 1) z, bτ.2 (sumY y + 1) z⟩ i *
              oddUCoordProfile (a := a) (n := n) (m := m) hm
                  ⟨cτ.1 y (sumZ z + 1), cτ.2 y (sumZ z + 1)⟩ i))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp_rw [Finset.sum_add_distrib]
        ac_rfl
    _ =
      oddTailCoordQSumABC (a := a) (b := b) (c := c) (n := n) (m := m) hm bτ cτ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        change
          (∑ y : YCoord b n, ∑ z : ZCoord c n,
              (oddUScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i (sumY y) z *
                oddVScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i y (sumZ z) +
               oddUScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i (sumY y + 1) z *
                oddVScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i y (sumZ z + 1))) +
            ∑ y : YCoord b n, ∑ z : ZCoord c n,
              (oddVScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i (sumY y) z *
                oddUScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i y (sumZ z) +
               oddVScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i (sumY y + 1) z *
                oddUScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i y (sumZ z + 1))
            =
          qScalar (b := b) (c := c) (n := n)
            (oddUScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
            (oddVScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i) +
          qScalar (b := b) (c := c) (n := n)
            (oddVScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
            (oddUScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i)
        simp_rw [Finset.sum_add_distrib]
        rw [← qLeftScalar_eq_sum_yz (b := b) (c := c) (n := n)
              (oddUScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
              (oddVScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i),
            ← qRightScalar_eq_sum_yz (b := b) (c := c) (n := n)
              (oddUScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
              (oddVScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i),
            ← qLeftScalar_eq_sum_yz (b := b) (c := c) (n := n)
              (oddVScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
              (oddUScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i),
            ← qRightScalar_eq_sum_yz (b := b) (c := c) (n := n)
              (oddVScalarBCoefABC (a := a) (c := c) (n := n) (m := m) hm bτ i)
              (oddUScalarCCoefABC (a := a) (b := b) (n := n) (m := m) hm cτ i)]
        rw [qScalar, qScalar]

end Core3loop
