import Core4loop.Basic

/-!
# Singleton local-complement kernel

This owner defines the inverse-square-root-normalized two-by-two complex
kernel and proves its orthogonality, ket, and bra identities over `F`.
These are strictly local finite-bit identities; they make no global
`DeltaNF` or graph-transform claim.
-/

open scoped BigOperators

namespace Core4loop.SquareDiagonal.SingletonLC

noncomputable section

def bitToNat (x : F) : Nat := if x = 0 then 0 else 1

@[simp] private theorem bitToNat_zero : bitToNat (0 : F) = 0 := by
  simp [bitToNat]

@[simp] private theorem bitToNat_one : bitToNat (1 : F) = 1 := by decide

private theorem F_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem sum_F_two (f : F → Complex) :
    (∑ x : F, f x) = f 0 + f 1 := by
  have hu : (Finset.univ : Finset F) = {0, 1} := by rfl
  rw [hu]
  simp

private theorem two_F : (2 : F) = 0 := by rfl
private theorem three_F : (3 : F) = 1 := by rfl
private theorem six_F : (6 : F) = 0 := by rfl

/-- The local kernel, normalized by the inverse of the positive real square root of two. -/
noncomputable def lcKernel (y x : F) : Complex :=
  (Real.sqrt 2 : Complex)⁻¹ *
    (-Complex.I) ^ (bitToNat x + bitToNat y) *
    (-1 : Complex) ^ bitToNat (x * y)

private theorem sqrtTwoC_sq :
    (Real.sqrt 2 : Complex) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow]
  norm_num [Real.sq_sqrt]

private theorem inv_sqrt_two_eq :
    (Real.sqrt 2 : Complex)⁻¹ = (Real.sqrt 2 : Complex) / 2 := by
  symm
  field_simp
  exact sqrtTwoC_sq

theorem lcKernel_orthogonality (x x' : F) :
    (∑ y : F, lcKernel y x * star (lcKernel y x')) =
      if x = x' then 1 else 0 := by
  rw [sum_F_two]
  rcases F_eq_zero_or_one x with rfl | rfl <;>
    rcases F_eq_zero_or_one x' with rfl | rfl <;>
    norm_num [lcKernel, inv_sqrt_two_eq, bitToNat, map_mul,
      Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_div,
      map_div₀, map_ofNat, Complex.I_sq]
  all_goals ring_nf
  all_goals rw [Complex.I_sq, sqrtTwoC_sq]
  all_goals norm_num

private theorem exp_neg_pi_div_four :
    Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) =
      (Real.sqrt 2 : Complex) / 2 -
        ((Real.sqrt 2 : Complex) / 2) * Complex.I := by
  have hexp :
      -((Real.pi : Complex) * Complex.I) / 4 =
        (-((Real.pi : Complex) / 4)) * Complex.I := by ring
  rw [hexp]
  rw [Complex.exp_mul_I]
  norm_num
  have harg : (Real.pi : Complex) / 4 =
      ((Real.pi / 4 : Real) : Complex) := by norm_num
  rw [harg]
  rw [← Complex.ofReal_cos, Real.cos_pi_div_four,
    ← Complex.ofReal_sin, Real.sin_pi_div_four]
  rw [Complex.ofReal_div]
  norm_num
  ring

private theorem exp_pos_pi_div_four :
    Complex.exp (((Real.pi : Complex) * Complex.I) / 4) =
      (Real.sqrt 2 : Complex) / 2 +
        ((Real.sqrt 2 : Complex) / 2) * Complex.I := by
  have hexp :
      ((Real.pi : Complex) * Complex.I) / 4 =
        ((Real.pi : Complex) / 4) * Complex.I := by ring
  rw [hexp]
  rw [Complex.exp_mul_I]
  have harg : (Real.pi : Complex) / 4 =
      ((Real.pi / 4 : Real) : Complex) := by norm_num
  rw [harg]
  rw [← Complex.ofReal_cos, Real.cos_pi_div_four,
    ← Complex.ofReal_sin, Real.sin_pi_div_four]
  rw [Complex.ofReal_div]
  norm_num

theorem lcKernel_ket_identity (b c t y : F) :
    (-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t) *
        (∑ x : F, lcKernel y x *
          (-1 : Complex) ^ bitToNat (x * (b + c + t))) =
      Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
        (-1 : Complex) ^ bitToNat
          (y * (b + c + t) + b * c + b * t + c * t) := by
  rw [sum_F_two, exp_neg_pi_div_four]
  rcases F_eq_zero_or_one b with rfl | rfl <;>
    rcases F_eq_zero_or_one c with rfl | rfl <;>
    rcases F_eq_zero_or_one t with rfl | rfl <;>
    rcases F_eq_zero_or_one y with rfl | rfl <;>
    norm_num [lcKernel, inv_sqrt_two_eq, bitToNat,
      two_F, three_F, six_F,
      Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  all_goals try simp [two_F, three_F, six_F]
  all_goals ring_nf
  all_goals try simp [Complex.I_sq]
  all_goals ring_nf

theorem lcKernel_bra_identity (b c t y : F) :
    Complex.I ^ (bitToNat b + bitToNat c + bitToNat t) *
        (∑ x : F, star (lcKernel y x) *
          (-1 : Complex) ^ bitToNat (x * (b + c + t))) =
      Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
        (-1 : Complex) ^ bitToNat
          (y * (b + c + t) + b * c + b * t + c * t) := by
  rw [sum_F_two, exp_pos_pi_div_four]
  rcases F_eq_zero_or_one b with rfl | rfl <;>
    rcases F_eq_zero_or_one c with rfl | rfl <;>
    rcases F_eq_zero_or_one t with rfl | rfl <;>
    rcases F_eq_zero_or_one y with rfl | rfl <;>
    norm_num [lcKernel, inv_sqrt_two_eq, bitToNat, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_div,
      map_div₀, map_ofNat, two_F, three_F, six_F, Complex.I_sq,
      Complex.I_pow_three, Complex.I_pow_four]
  all_goals try simp [two_F, three_F, six_F]
  all_goals ring_nf
  all_goals try simp [Complex.I_sq]
  all_goals ring_nf

end

end Core4loop.SquareDiagonal.SingletonLC
