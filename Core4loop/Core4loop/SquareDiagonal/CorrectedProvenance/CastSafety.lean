import Core4loop.Basic

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem cast_n_sub_one
    {n : Nat} (hn1 : 1 ≤ n) :
    ((n - 1 : Nat) : Int) = (n : Int) - 1 := by
  exact Nat.cast_pred (by omega)

theorem pow_pred_ge_one_of_one_le
    {n r : Nat} (hn1 : 1 ≤ n) :
    1 ≤ n ^ (r - 1) := by
  exact Nat.one_le_pow (r - 1) n (by omega)

theorem cast_pow_pred_sub_one
    {n r : Nat} (hn1 : 1 ≤ n) :
    ((n ^ (r - 1) - 1 : Nat) : Int) =
      (n : Int) ^ (r - 1) - 1 := by
  rw [Nat.cast_sub (pow_pred_ge_one_of_one_le hn1)]
  norm_num

theorem pow_pred_ge_two_of_ge_two
    {n r : Nat} (hn2 : 2 ≤ n) (hr2 : 2 ≤ r) :
    2 ≤ n ^ (r - 1) := by
  have hn0 : 0 < n := by omega
  have hexp : 1 ≤ r - 1 := by omega
  have hpow : n ^ 1 ≤ n ^ (r - 1) :=
    Nat.pow_le_pow_right hn0 hexp
  have hpow' : n ≤ n ^ (r - 1) := by
    simpa using hpow
  exact hn2.trans hpow'

theorem cast_pow_pred_sub_two
    {n r : Nat} (hn2 : 2 ≤ n) (hr2 : 2 ≤ r) :
    ((n ^ (r - 1) - 2 : Nat) : Int) =
      (n : Int) ^ (r - 1) - 2 := by
  rw [Nat.cast_sub (pow_pred_ge_two_of_ge_two hn2 hr2)]
  norm_num

end Core4loop
