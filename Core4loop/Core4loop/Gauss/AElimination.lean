import Core4loop.RootSpaces.KRange
import Core4loop.Sign

namespace Core4loop

noncomputable def coeffApplyA {n b c d : ℕ} [NeZero n]
    (K : RootTarget n b c d) (A : AFun4 n b c d) : F :=
  coeffApply (aFun4Equiv n b c d K) (aFun4Equiv n b c d A)

noncomputable def signedCoeffSumA {n b c d : ℕ} [NeZero n]
    (K : RootTarget n b c d) : ℤ :=
  ∑ A : AFun4 n b c d, bitSign (coeffApplyA K A)

lemma coeffApplyA_eq_sum {n b c d : ℕ} [NeZero n]
    (K : RootTarget n b c d) (A : AFun4 n b c d) :
    coeffApplyA K A =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d, A y z w * K y z w := by
  classical
  unfold coeffApplyA coeffApply
  change
    (∑ u : YVec n b × ZVec n c × WVec n d,
        (aFun4Equiv n b c d A) u * (aFun4Equiv n b c d K) u) =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d, A y z w * K y z w
  rw [Fintype.sum_prod_type]
  congr
  funext y
  rw [Fintype.sum_prod_type]
  rfl

lemma aFun4Equiv_eq_zero_iff {n b c d : ℕ} (K : RootTarget n b c d) :
    aFun4Equiv n b c d K = 0 ↔ K = 0 := by
  constructor
  · intro h
    funext y z w
    have hv := congrFun h (y, z, w)
    simpa [aFun4Equiv] using hv
  · intro h
    rw [h]
    rfl

theorem signedCoeffSumA_formula {n b c d : ℕ} [NeZero n]
    (K : RootTarget n b c d) :
    signedCoeffSumA K = if K = 0 then (2 : ℤ) ^ (n ^ (b + c + d)) else 0 := by
  let e := aFun4Equiv n b c d
  let Kp := e K
  have hsum :
      signedCoeffSumA K = signedCoeffSum Kp := by
    unfold signedCoeffSumA signedCoeffSum coeffApplyA
    exact Fintype.sum_equiv e
      (fun A : AFun4 n b c d => bitSign (coeffApply Kp (e A)))
      (fun f : YVec n b × ZVec n c × WVec n d → F => bitSign (coeffApply Kp f))
      (fun A => rfl)
  rw [hsum, signedCoeffSum_formula]
  by_cases hK : K = 0
  · have hKp : Kp = 0 := by
      funext u
      rcases u with ⟨y, z, w⟩
      simp [Kp, e, hK, aFun4Equiv]
    rw [if_pos hKp, if_pos hK, card_vec3]
  · have hKp : Kp ≠ 0 := by
      intro hzero
      exact hK ((aFun4Equiv_eq_zero_iff K).1 (by simpa [Kp, e] using hzero))
    rw [if_neg hKp, if_neg hK]

theorem signedCoeffSumA_add_const {n b c d : ℕ} [NeZero n]
    (K : RootTarget n b c d) (q : F) :
    (∑ A : AFun4 n b c d, bitSign (coeffApplyA K A + q)) =
      if K = 0 then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign q else 0 := by
  calc
    (∑ A : AFun4 n b c d, bitSign (coeffApplyA K A + q))
        = ∑ A : AFun4 n b c d, bitSign (coeffApplyA K A) * bitSign q := by
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [bitSign_add]
    _ = signedCoeffSumA K * bitSign q := by
            unfold signedCoeffSumA
            rw [Finset.sum_mul]
    _ = (if K = 0 then (2 : ℤ) ^ (n ^ (b + c + d)) else 0) * bitSign q := by
            rw [signedCoeffSumA_formula]
    _ = if K = 0 then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign q else 0 := by
            by_cases hK : K = 0 <;> simp [hK]

end Core4loop
