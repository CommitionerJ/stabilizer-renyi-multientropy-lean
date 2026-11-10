import Core3loop.ProfileEvenPair
import Core3loop.ProfileOddClosed

open scoped BigOperators

namespace Core3loop

abbrev UevenBasisIndexABC (a n : ℕ) [NeZero n] :=
  Module.Free.ChooseBasisIndex F (Ueven (a := a) (n := n))

noncomputable instance uevenBasisIndexABCFintype {a n : ℕ} [NeZero n] :
    Fintype (UevenBasisIndexABC a n) := by
  classical
  exact Fintype.ofFinite (UevenBasisIndexABC a n)

noncomputable def uevenBasisABC {a n : ℕ} [NeZero n] :
    Module.Basis (UevenBasisIndexABC a n) F (Ueven (a := a) (n := n)) :=
  Module.Free.chooseBasis F (Ueven (a := a) (n := n))

noncomputable def evenTailBModelEquivCoordABC {a c n : ℕ} [NeZero n] :
    EvenTailBModelABC a c n ≃ (UevenBasisIndexABC a n → ScalarBCoef c n) where
  toFun XB i := fun t z => (uevenBasisABC (a := a) (n := n)).equivFun (XB t z) i
  invFun X := fun t z =>
    (uevenBasisABC (a := a) (n := n)).equivFun.symm (fun i => X i t z)
  left_inv XB := by
    funext t z
    exact (uevenBasisABC (a := a) (n := n)).equivFun.symm_apply_apply (XB t z)
  right_inv X := by
    funext i t z
    exact congrFun
      ((uevenBasisABC (a := a) (n := n)).equivFun.apply_symm_apply (fun j => X j t z)) i

noncomputable def evenTailCModelEquivCoordABC {a b n : ℕ} [NeZero n] :
    EvenTailCModelABC a b n ≃ (UevenBasisIndexABC a n → ScalarCCoef b n) where
  toFun YC i := fun y r => (uevenBasisABC (a := a) (n := n)).equivFun (YC y r) i
  invFun X := fun y r =>
    (uevenBasisABC (a := a) (n := n)).equivFun.symm (fun i => X i y r)
  left_inv YC := by
    funext y r
    exact (uevenBasisABC (a := a) (n := n)).equivFun.symm_apply_apply (YC y r)
  right_inv X := by
    funext i y r
    exact congrFun
      ((uevenBasisABC (a := a) (n := n)).equivFun.apply_symm_apply (fun j => X j y r)) i

noncomputable def evenTailTModelABC {a b c n : ℕ} [NeZero n]
    (YC : EvenTailCModelABC a b n) : EvenTailBModelABC a c n :=
  (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n)).symm
    (fun i =>
      TScalar (b := b) (c := c) (n := n)
        ((evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC) i))

lemma evenTailTModelABC_coord_apply {a b c n : ℕ} [NeZero n]
    (YC : EvenTailCModelABC a b n) (i : UevenBasisIndexABC a n) :
    evenTailBModelEquivCoordABC (a := a) (c := c) (n := n)
      (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC) i =
        TScalar (b := b) (c := c) (n := n)
          ((evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC) i) := by
  simpa [evenTailTModelABC] using
    congrFun
      ((evenTailBModelEquivCoordABC (a := a) (c := c) (n := n)).right_inv
        (fun j =>
          TScalar (b := b) (c := c) (n := n)
            ((evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC) j))) i

noncomputable def evenTailSignModelABC {a b c n : ℕ} [NeZero n]
    (XB : EvenTailBModelABC a c n) (YC : EvenTailCModelABC a b n) : ℤ :=
  bitSign
    (evenTailPairModelABC (a := a) (c := c) (n := n) XB
      (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC))

abbrev EvenTailKerDataABC (a b c n : ℕ) [NeZero n] :=
  { YC : EvenTailCModelABC a b n //
      evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0 }

noncomputable instance evenTailKerDataABCFintype {a b c n : ℕ} [NeZero n] :
    Fintype (EvenTailKerDataABC a b c n) := by
  classical
  infer_instance

noncomputable instance kerTScalarSubtypeFintype {b c n : ℕ} [NeZero n] :
    Fintype { ccoef : ScalarCCoef b n //
      TScalar (b := b) (c := c) (n := n) ccoef = 0 } := by
  classical
  infer_instance

lemma sum_evenTailSignModelABC_eq_card_mul_ker {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
      evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC =
        (Fintype.card (EvenTailBModelABC a c n) : ℤ) *
          Fintype.card (EvenTailKerDataABC a b c n) := by
  classical
  have hfilter :
      ∑ YC : EvenTailCModelABC a b n,
        (if evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0 then
          (Fintype.card (EvenTailBModelABC a c n) : ℤ) else 0) =
      Finset.sum
        (Finset.univ.filter fun YC : EvenTailCModelABC a b n =>
          evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0)
        (fun _ => (Fintype.card (EvenTailBModelABC a c n) : ℤ)) := by
    rw [Finset.sum_ite]
    simp
  have hcard :
      (Finset.univ.filter fun YC : EvenTailCModelABC a b n =>
          evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0).card =
        Fintype.card (EvenTailKerDataABC a b c n) := by
    simpa [EvenTailKerDataABC] using
      (Fintype.card_subtype
        (fun YC : EvenTailCModelABC a b n =>
          evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0)).symm
  calc
    ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
        evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC
      =
        ∑ YC : EvenTailCModelABC a b n,
          ∑ XB : EvenTailBModelABC a c n,
            bitSign
              (evenTailPairModelABC (a := a) (c := c) (n := n) XB
                (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC)) := by
            rfl
    _ =
        ∑ YC : EvenTailCModelABC a b n,
          if evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0 then
            (Fintype.card (EvenTailBModelABC a c n) : ℤ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro YC hYC
            simpa using
              sum_bitSign_evenTailPairModelABC (a := a) (c := c) (n := n) hn ha2
                (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC)
    _ =
        Finset.sum
          (Finset.univ.filter fun YC : EvenTailCModelABC a b n =>
            evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0)
          (fun _ => (Fintype.card (EvenTailBModelABC a c n) : ℤ)) := hfilter
    _ =
        (Fintype.card (EvenTailBModelABC a c n) : ℤ) *
          Fintype.card (EvenTailKerDataABC a b c n) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
            ring

lemma evenTailTModelABC_eq_zero_iff_coord {a b c n : ℕ} [NeZero n]
    (YC : EvenTailCModelABC a b n) :
    evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC = 0 ↔
      ∀ i : UevenBasisIndexABC a n,
        TScalar (b := b) (c := c) (n := n)
          ((evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC) i) = 0 := by
  constructor
  · intro h i
    have hi := congrArg
      (fun XB =>
        evenTailBModelEquivCoordABC (a := a) (c := c) (n := n) XB i) h
    calc
      TScalar (b := b) (c := c) (n := n)
          ((evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC) i)
        =
          evenTailBModelEquivCoordABC (a := a) (c := c) (n := n)
            (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC) i := by
              symm
              exact evenTailTModelABC_coord_apply (a := a) (b := b) (c := c) (n := n) YC i
      _ = 0 := by simpa [evenTailBModelEquivCoordABC] using hi
  · intro h
    apply (evenTailBModelEquivCoordABC (a := a) (c := c) (n := n)).injective
    funext i
    calc
      evenTailBModelEquivCoordABC (a := a) (c := c) (n := n)
          (evenTailTModelABC (a := a) (b := b) (c := c) (n := n) YC) i
        =
          TScalar (b := b) (c := c) (n := n)
            ((evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC) i) := by
              exact evenTailTModelABC_coord_apply (a := a) (b := b) (c := c) (n := n) YC i
      _ = 0 := by simpa [evenTailBModelEquivCoordABC] using h i
      _ =
          evenTailBModelEquivCoordABC (a := a) (c := c) (n := n)
            (0 : EvenTailBModelABC a c n) i := by
              funext t z
              simp [evenTailBModelEquivCoordABC]

noncomputable def evenTailKerEquivCoordKerABC {a b c n : ℕ} [NeZero n] :
    EvenTailKerDataABC a b c n ≃
      (UevenBasisIndexABC a n → { ccoef : ScalarCCoef b n //
        TScalar (b := b) (c := c) (n := n) ccoef = 0 }) where
  toFun YC i :=
    ⟨(evenTailCModelEquivCoordABC (a := a) (b := b) (n := n) YC.1) i, by
      simpa using
        (evenTailTModelABC_eq_zero_iff_coord (a := a) (b := b) (c := c) (n := n) YC.1).mp
          YC.2 i⟩
  invFun X :=
    ⟨(evenTailCModelEquivCoordABC (a := a) (b := b) (n := n)).symm (fun i => (X i).1), by
      apply (evenTailTModelABC_eq_zero_iff_coord (a := a) (b := b) (c := c) (n := n) _).2
      intro i
      simpa using (X i).2⟩
  left_inv YC := by
    apply Subtype.ext
    exact (evenTailCModelEquivCoordABC (a := a) (b := b) (n := n)).left_inv YC.1
  right_inv X := by
    funext i
    apply Subtype.ext
    simpa using congrFun
      ((evenTailCModelEquivCoordABC (a := a) (b := b) (n := n)).right_inv
        (fun j => (X j).1)) i

lemma natCard_evenTailKerDataABC_of_even {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    Nat.card (EvenTailKerDataABC a b c n) =
      2 ^ ((n ^ (a - 1) - 2) * (n ^ (b + 1) - n * (n - 1))) := by
  rw [Nat.card_congr (evenTailKerEquivCoordKerABC (a := a) (b := b) (c := c) (n := n))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  have hker :
      Fintype.card { ccoef : ScalarCCoef b n //
          TScalar (b := b) (c := c) (n := n) ccoef = 0 } =
        2 ^ (n ^ (b + 1) - n * (n - 1)) := by
    rw [← Nat.card_eq_fintype_card]
    simpa [LinearMap.mem_ker] using
      natCard_ker_TScalar (b := b) (c := c) (n := n) hb hc
  rw [hker]
  have hidx : Fintype.card (UevenBasisIndexABC a n) = n ^ (a - 1) - 2 := by
    have hchoose := Module.finrank_eq_card_chooseBasisIndex (R := F) (M := Ueven (a := a) (n := n))
    rw [finrank_Ueven_of_even_n (a := a) (n := n) hn ha2] at hchoose
    simpa [UevenBasisIndexABC] using hchoose.symm
  rw [hidx]
  simpa [Nat.mul_comm (n ^ (a - 1) - 2) (n ^ (b + 1) - n * (n - 1))] using
    (pow_mul 2 (n ^ (b + 1) - n * (n - 1)) (n ^ (a - 1) - 2)).symm

theorem card_evenTailKerDataABC_of_even {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    Fintype.card (EvenTailKerDataABC a b c n) =
      2 ^ ((n ^ (a - 1) - 2) * (n ^ (b + 1) - n * (n - 1))) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_evenTailKerDataABC_of_even (a := a) (b := b) (c := c) (n := n) hn ha2 hb hc

theorem sum_evenTailSignModelABC_eq_closed_form_of_even {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
      evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC =
        (2 : ℤ) ^
          (((n ^ (a - 1) - 2) * n ^ (c + 1)) +
            ((n ^ (a - 1) - 2) * (n ^ (b + 1) - n * (n - 1)))) := by
  rw [sum_evenTailSignModelABC_eq_card_mul_ker (a := a) (b := b) (c := c) (n := n) hn ha2]
  have hB : (Fintype.card (EvenTailBModelABC a c n) : ℤ) =
      (2 : ℤ) ^ ((n ^ (a - 1) - 2) * n ^ (c + 1)) := by
    rw [card_evenTailBModelABC_of_even (a := a) (c := c) (n := n) hn ha2]
    simpa using (Nat.cast_pow (R := ℤ) 2 ((n ^ (a - 1) - 2) * n ^ (c + 1)))
  have hK : (Fintype.card (EvenTailKerDataABC a b c n) : ℤ) =
      (2 : ℤ) ^ ((n ^ (a - 1) - 2) * (n ^ (b + 1) - n * (n - 1))) := by
    rw [card_evenTailKerDataABC_of_even (a := a) (b := b) (c := c) (n := n) hn ha2 hb hc]
    simpa using
      (Nat.cast_pow (R := ℤ) 2 ((n ^ (a - 1) - 2) * (n ^ (b + 1) - n * (n - 1))))
  rw [hB, hK, ← pow_add]

def evenTailPairCountABC (a n : ℕ) [NeZero n] : ℕ :=
  (ProfileCard a n - 2) / 2

lemma exists_profileCard_eq_two_mul_add_two_of_even {a n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    ∃ m, ProfileCard a n = 2 * m + 2 := by
  have hEven : Even (ProfileCard a n) := by
    simpa [ProfileCard, card_XCoord] using
      even_card_XCoord_of_even (a := a) (n := n) hn ha2
  rcases hEven with ⟨k, hk⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn2 : 2 ≤ n := by
    rcases hn with ⟨m, hm⟩
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm0
      apply NeZero.ne n
      simp [hm, hm0]
    omega
  have hexp : 1 ≤ a - 1 := by omega
  have hpow : 2 ≤ ProfileCard a n := by
    have hle : n ^ 1 ≤ n ^ (a - 1) := by
      exact Nat.pow_le_pow_right hnpos hexp
    have hle' : n ≤ n ^ (a - 1) := by
      simpa [pow_one] using hle
    simpa [ProfileCard] using le_trans hn2 hle'
  have hk1 : 1 ≤ k := by
    omega
  refine ⟨k - 1, ?_⟩
  omega

lemma evenTailPairCountABC_eq_of_even_witness {a n m : ℕ} [NeZero n]
    (hm : ProfileCard a n = 2 * m + 2) :
    evenTailPairCountABC a n = m := by
  unfold evenTailPairCountABC
  rw [hm]
  omega

lemma evenTailClosedExponent_eq_ordinaryPairExponent_mul_pairCount
    {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb : 0 < b) :
    ((n ^ (a - 1) - 2) * n ^ (c + 1)) +
        ((n ^ (a - 1) - 2) * (n ^ (b + 1) - n * (n - 1))) =
      ordinaryPairExponentABC b c n * evenTailPairCountABC a n := by
  rcases exists_profileCard_eq_two_mul_add_two_of_even (a := a) (n := n) hn ha2 with ⟨m, hm⟩
  have hcount : evenTailPairCountABC a n = m := by
    exact evenTailPairCountABC_eq_of_even_witness (a := a) (n := n) hm
  have hdim : n ^ (a - 1) - 2 = 2 * m := by
    have hm' : n ^ (a - 1) = 2 * m + 2 := by
      simpa [ProfileCard] using hm
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
  have hpowb : n ≤ n ^ b := by
    simpa [pow_one] using (Nat.pow_le_pow_right hnpos hb1)
  have hble' : n - 1 ≤ n ^ b := by
    exact le_trans (Nat.sub_le _ _) hpowb
  have hble : n * (n - 1) ≤ n ^ (b + 1) := by
    calc
      n * (n - 1) ≤ n * n ^ b := Nat.mul_le_mul_left _ hble'
      _ = n ^ (b + 1) := by
        rw [pow_succ, Nat.mul_comm]
  rw [hcount, hdim, ordinaryPairExponentABC]
  calc
    (2 * m) * n ^ (c + 1) + (2 * m) * (n ^ (b + 1) - n * (n - 1))
        = (2 * m) * (n ^ (c + 1) + (n ^ (b + 1) - n * (n - 1))) := by
            rw [← Nat.mul_add]
    _ = (2 * m) * ((n ^ (b + 1) - n * (n - 1)) + n ^ (c + 1)) := by
          rw [Nat.add_comm]
    _ = (2 * m) * (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1)) := by
          congr 1
          omega
    _ = (2 * (n ^ (b + 1) + n ^ (c + 1) - n * (n - 1))) * m := by
          ac_rfl

theorem sum_evenTailSignModelABC_eq_closed_form_pairCount_of_even {a b c n : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    ∑ YC : EvenTailCModelABC a b n, ∑ XB : EvenTailBModelABC a c n,
      evenTailSignModelABC (a := a) (b := b) (c := c) (n := n) XB YC =
        (2 : ℤ) ^ (ordinaryPairExponentABC b c n * evenTailPairCountABC a n) := by
  rw [sum_evenTailSignModelABC_eq_closed_form_of_even
    (a := a) (b := b) (c := c) (n := n) hn ha2 hb hc]
  congr 1
  exact evenTailClosedExponent_eq_ordinaryPairExponent_mul_pairCount
    (a := a) (b := b) (c := c) (n := n) hn ha2 hb

end Core3loop
