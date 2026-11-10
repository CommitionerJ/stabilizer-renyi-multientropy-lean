import Core4loop.Exponents

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

noncomputable section

attribute [local instance] Classical.propDecidable

def k4GenericThetaZ (n : Nat) : Int :=
  mZ n * (2 * (n : Int) - 1)

def k4ThetaCorrectionZ (r s t n : Nat) : Int :=
  k4GenericThetaZ n - ThetaZ r s t n

noncomputable def K4CorrectionZ
    (n a b c d : Nat) : Int :=
  if a = 1 then k4ThetaCorrectionZ b c d n
  else if b = 1 then k4ThetaCorrectionZ a c d n
  else if c = 1 then k4ThetaCorrectionZ a b d n
  else if d = 1 then k4ThetaCorrectionZ a b c n
  else if Odd n then 0
  else -(mZ n * ((n : Int) - 2) * (3 * (n : Int) + 1))

@[simp] theorem K4CorrectionZ_of_a_eq_one
    {n a b c d : Nat} (ha : a = 1) :
    K4CorrectionZ n a b c d = k4ThetaCorrectionZ b c d n := by
  simp only [K4CorrectionZ, ha, if_true]

@[simp] theorem K4CorrectionZ_of_a_ne_one_b_eq_one
    {n a b c d : Nat} (ha : a ≠ 1) (hb : b = 1) :
    K4CorrectionZ n a b c d = k4ThetaCorrectionZ a c d n := by
  simp only [K4CorrectionZ, ha, if_false, hb, if_true]

@[simp] theorem K4CorrectionZ_of_ab_ne_one_c_eq_one
    {n a b c d : Nat}
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c = 1) :
    K4CorrectionZ n a b c d = k4ThetaCorrectionZ a b d n := by
  simp only [K4CorrectionZ, ha, if_false, hb, hc, if_true]

@[simp] theorem K4CorrectionZ_of_abc_ne_one_d_eq_one
    {n a b c d : Nat}
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d = 1) :
    K4CorrectionZ n a b c d = k4ThetaCorrectionZ a b c n := by
  simp only [K4CorrectionZ, ha, if_false, hb, hc, hd, if_true]

@[simp] theorem K4CorrectionZ_of_all_ne_one_odd
    {n a b c d : Nat}
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d ≠ 1)
    (hn : Odd n) :
    K4CorrectionZ n a b c d = 0 := by
  simp only [K4CorrectionZ, ha, if_false, hb, hc, hd, hn, if_true]

@[simp] theorem K4CorrectionZ_of_all_ne_one_even
    {n a b c d : Nat}
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d ≠ 1)
    (hn : Even n) :
    K4CorrectionZ n a b c d =
      -(mZ n * ((n : Int) - 2) * (3 * (n : Int) + 1)) := by
  have hnot : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
  simp only [K4CorrectionZ, ha, if_false, hb, hc, hd, hnot]

end
end Core4loop
