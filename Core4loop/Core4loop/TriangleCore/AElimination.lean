import Core4loop.TriangleCore.Root

open scoped BigOperators

namespace Core4loop
namespace TriangleCore

lemma sum_if_mul_eq_mul_subtype_tri {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (c : ℤ) (f : α → ℤ) :
    (∑ x : α, if p x then c * f x else 0) =
      c * ∑ x : {x // p x}, f x.1 := by
  classical
  calc
    (∑ x : α, if p x then c * f x else 0)
        = ∑ x ∈ (Finset.univ : Finset α) with p x, c * f x := by
            rw [Finset.sum_filter]
    _ = ∑ x : {x // p x}, c * f x.1 := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset α)) (p := p)
                (f := fun x => c * f x)).symm
    _ = c * ∑ x : {x // p x}, f x.1 := by
            rw [Finset.mul_sum]

noncomputable def coeffApplyTriA {n s t : ℕ} [NeZero n]
    (K : TriRootTarget n s t) (A : TriAFun n s t) : F :=
  coeffApply (triAFunEquiv n s t K) (triAFunEquiv n s t A)

lemma coeffApplyTriA_eq_sum {n s t : ℕ} [NeZero n]
    (K : TriRootTarget n s t) (A : TriAFun n s t) :
    coeffApplyTriA K A =
      ∑ y : TriYVec n s, ∑ z : TriZVec n t, A y z * K y z := by
  classical
  unfold coeffApplyTriA coeffApply
  change
    (∑ u : TriYVec n s × TriZVec n t,
        (triAFunEquiv n s t A) u * (triAFunEquiv n s t K) u) =
      ∑ y : TriYVec n s, ∑ z : TriZVec n t, A y z * K y z
  rw [Fintype.sum_prod_type]
  rfl

lemma triAFunEquiv_eq_zero_iff {n s t : ℕ} (K : TriRootTarget n s t) :
    triAFunEquiv n s t K = 0 ↔ K = 0 := by
  constructor
  · intro h
    funext y z
    have hv := congrFun h (y, z)
    simpa [triAFunEquiv] using hv
  · intro h
    rw [h]
    rfl

noncomputable def signedCoeffSumTriA {n s t : ℕ} [NeZero n]
    (K : TriRootTarget n s t) : ℤ :=
  ∑ A : TriAFun n s t, bitSign (coeffApplyTriA K A)

theorem signedCoeffSumTriA_formula {n s t : ℕ} [NeZero n]
    (K : TriRootTarget n s t) :
    signedCoeffSumTriA K =
      if K = 0 then (2 : ℤ) ^ (n ^ (s + t)) else 0 := by
  let e := triAFunEquiv n s t
  let Kp := e K
  have hsum :
      signedCoeffSumTriA K = signedCoeffSum Kp := by
    unfold signedCoeffSumTriA signedCoeffSum coeffApplyTriA
    exact Fintype.sum_equiv e
      (fun A : TriAFun n s t => bitSign (coeffApply Kp (e A)))
      (fun f : TriYVec n s × TriZVec n t → F => bitSign (coeffApply Kp f))
      (fun A => rfl)
  rw [hsum, signedCoeffSum_formula]
  by_cases hK : K = 0
  · have hKp : Kp = 0 := by
      funext u
      rcases u with ⟨y, z⟩
      simp [Kp, e, hK, triAFunEquiv]
    rw [if_pos hKp, if_pos hK, card_triAIndex]
  · have hKp : Kp ≠ 0 := by
      intro hzero
      exact hK ((triAFunEquiv_eq_zero_iff K).1 (by simpa [Kp, e] using hzero))
    rw [if_neg hKp, if_neg hK]

theorem signedCoeffSumTriA_add_const {n s t : ℕ} [NeZero n]
    (K : TriRootTarget n s t) (q : F) :
    (∑ A : TriAFun n s t, bitSign (coeffApplyTriA K A + q)) =
      if K = 0 then (2 : ℤ) ^ (n ^ (s + t)) * bitSign q else 0 := by
  calc
    (∑ A : TriAFun n s t, bitSign (coeffApplyTriA K A + q))
        = ∑ A : TriAFun n s t, bitSign (coeffApplyTriA K A) * bitSign q := by
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [bitSign_add]
    _ = signedCoeffSumTriA K * bitSign q := by
            unfold signedCoeffSumTriA
            rw [Finset.sum_mul]
    _ = (if K = 0 then (2 : ℤ) ^ (n ^ (s + t)) else 0) * bitSign q := by
            rw [signedCoeffSumTriA_formula]
    _ = if K = 0 then (2 : ℤ) ^ (n ^ (s + t)) * bitSign q else 0 := by
            by_cases hK : K = 0 <;> simp [hK]

noncomputable def TriQraw {n r s t : ℕ} [NeZero n]
    (B : TriBFun n r t) (C : TriCFun n r s) : F :=
  ∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
    (B p (vecSum y) z * C p y (vecSum z) +
      B p (vecSum y + 1) z * C p y (vecSum z + 1))

lemma tri_sum_index_A_mul {ι : Type*} [Fintype ι] {n s t : ℕ} [NeZero n]
    (A : TriAFun n s t) (L : ι → TriRootTarget n s t) :
    (∑ i : ι, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
        A y z * L i y z) =
      ∑ y : TriYVec n s, ∑ z : TriZVec n t,
        A y z * ∑ i : ι, L i y z := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [Finset.mul_sum]

theorem triGraphExponent_split {n r s t : ℕ} [NeZero n]
    (A : TriAFun n s t) (B : TriBFun n r t) (C : TriCFun n r s) :
    triGraphExponent ({ A := A, B := B, C := C } : TriNF n r s t) =
      coeffApplyTriA (K_yz (n := n) (r := r) (s := s) (t := t) (B, C)) A
        + TriQraw B C := by
  let L : TriPVec n r → TriRootTarget n s t := fun p y z =>
    (B p (vecSum y) z + B p (vecSum y + 1) z) +
      (C p y (vecSum z) + C p y (vecSum z + 1))
  let R : TriPVec n r → TriRootTarget n s t := fun p y z =>
    B p (vecSum y) z * C p y (vecSum z) +
      B p (vecSum y + 1) z * C p y (vecSum z + 1)
  calc
    triGraphExponent ({ A := A, B := B, C := C } : TriNF n r s t)
        = ∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
            (A y z * L p y z + R p y z) := by
            unfold triGraphExponent
            refine Finset.sum_congr rfl ?_
            intro p _
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            simp [triGraphPhase, triAlpha, triBeta, triGamma, triDelta, triEta, L, R]
            ring
    _ = (∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
            A y z * L p y z)
        + (∑ p : TriPVec n r, ∑ y : TriYVec n s, ∑ z : TriZVec n t,
            R p y z) := by
            simp only [Finset.sum_add_distrib]
    _ = (∑ y : TriYVec n s, ∑ z : TriZVec n t,
            A y z * ∑ p : TriPVec n r, L p y z)
        + TriQraw B C := by
            rw [tri_sum_index_A_mul]
            rfl
    _ = coeffApplyTriA (K_yz (n := n) (r := r) (s := s) (t := t) (B, C)) A
        + TriQraw B C := by
            rw [coeffApplyTriA_eq_sum]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            unfold L
            congr 1
            simp [K_yz, TriKBMap, TriKCMap, Finset.sum_add_distrib]

theorem sum_A_TriangleCore_afterA {n r s t : ℕ} [NeZero n]
    (B : TriBFun n r t) (C : TriCFun n r s) :
    (∑ A : TriAFun n s t,
      bitSign (triGraphExponent
        ({ A := A, B := B, C := C } : TriNF n r s t))) =
      if K_yz (n := n) (r := r) (s := s) (t := t) (B, C) = 0
      then (2 : ℤ) ^ (n ^ (s + t)) * bitSign (TriQraw B C)
      else 0 := by
  calc
    (∑ A : TriAFun n s t,
      bitSign (triGraphExponent
        ({ A := A, B := B, C := C } : TriNF n r s t)))
        = ∑ A : TriAFun n s t,
            bitSign
              (coeffApplyTriA
                (K_yz (n := n) (r := r) (s := s) (t := t) (B, C)) A
                + TriQraw B C) := by
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [triGraphExponent_split]
    _ = _ := signedCoeffSumTriA_add_const
      (K_yz (n := n) (r := r) (s := s) (t := t) (B, C)) (TriQraw B C)

abbrev SurvivingYZ (n r s t : ℕ) [NeZero n] :=
  { x : TriBFun n r t × TriCFun n r s //
      K_yz (n := n) (r := r) (s := s) (t := t) x = 0 }

theorem DeltaTriangleCore_afterA {n r s t : ℕ} [NeZero n] :
    DeltaTriangleCore r s t n =
      ∑ B : TriBFun n r t, ∑ C : TriCFun n r s,
        if K_yz (n := n) (r := r) (s := s) (t := t) (B, C) = 0
        then (2 : ℤ) ^ (n ^ (s + t)) * bitSign (TriQraw B C)
        else 0 := by
  unfold DeltaTriangleCore
  let e := triNFEquivProd n r s t
  calc
    (∑ nf : TriNF n r s t, bitSign (triGraphExponent nf))
        = ∑ x : TriAFun n s t × TriBFun n r t × TriCFun n r s,
            bitSign (triGraphExponent (e.symm x)) := by
            exact Fintype.sum_equiv e
              (fun nf : TriNF n r s t => bitSign (triGraphExponent nf))
              (fun x : TriAFun n s t × TriBFun n r t × TriCFun n r s =>
                bitSign (triGraphExponent (e.symm x)))
              (fun nf => by simp [e])
    _ = ∑ A : TriAFun n s t, ∑ B : TriBFun n r t, ∑ C : TriCFun n r s,
          bitSign (triGraphExponent
            ({ A := A, B := B, C := C } : TriNF n r s t)) := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [Fintype.sum_prod_type]
            rfl
    _ = ∑ B : TriBFun n r t, ∑ C : TriCFun n r s,
        if K_yz (n := n) (r := r) (s := s) (t := t) (B, C) = 0
        then (2 : ℤ) ^ (n ^ (s + t)) * bitSign (TriQraw B C)
        else 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro B _
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro C _
            exact sum_A_TriangleCore_afterA B C

theorem DeltaTriangleCore_survivors {n r s t : ℕ} [NeZero n] :
    DeltaTriangleCore r s t n =
      (2 : ℤ) ^ (n ^ (s + t)) *
        ∑ x : SurvivingYZ n r s t, bitSign (TriQraw x.1.1 x.1.2) := by
  rw [DeltaTriangleCore_afterA]
  let scale : ℤ := (2 : ℤ) ^ (n ^ (s + t))
  let f : TriBFun n r t × TriCFun n r s → ℤ :=
    fun x => bitSign (TriQraw x.1 x.2)
  let p : TriBFun n r t × TriCFun n r s → Prop :=
    fun x => K_yz (n := n) (r := r) (s := s) (t := t) x = 0
  have hprod :
      (∑ B : TriBFun n r t, ∑ C : TriCFun n r s,
        if K_yz (n := n) (r := r) (s := s) (t := t) (B, C) = 0
        then scale * bitSign (TriQraw B C)
        else 0)
      =
      ∑ x : TriBFun n r t × TriCFun n r s,
        if p x then scale * f x else 0 := by
    rw [Fintype.sum_prod_type]
  rw [hprod, sum_if_mul_eq_mul_subtype_tri p scale f]

end TriangleCore
end Core4loop
