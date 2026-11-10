import Core4loop.Exponents

namespace Core4loop

theorem X1_d_eq_one_triangle_degenerate
    {a b c n : ℕ} [NeZero n] :
    X1Z a b c 1 n =
      nPowZ n (a + b + c) + XtriangleZ (a + 1) b c n := by
  unfold X1Z XtriangleZ Sigma1Z Sigma2_1Z nPowZ mZ
  ring_nf

end Core4loop
