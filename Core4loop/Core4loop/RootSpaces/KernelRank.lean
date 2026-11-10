import Core4loop.NormalFormDims

namespace Core4loop

theorem finrank_domain_K_yw {n a b c d : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (BFun4 n a c d × WFun4 n a b c) =
      n ^ (a + c + d) + n ^ (a + b + c) := by
  rw [Module.finrank_prod, finrank_BFun4 (n := n) (a := a) (c := c) (d := d) ha,
    finrank_WFun4 (n := n) (a := a) (b := b) (c := c) ha]

theorem finrank_domain_K_yzw {n a b c d : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (BFun4 n a c d × CFun4 n a b d × WFun4 n a b c) =
      n ^ (a + c + d) + n ^ (a + b + d) + n ^ (a + b + c) := by
  rw [Module.finrank_prod, Module.finrank_prod,
    finrank_BFun4 (n := n) (a := a) (c := c) (d := d) ha,
    finrank_CFun4 (n := n) (a := a) (b := b) (d := d) ha,
    finrank_WFun4 (n := n) (a := a) (b := b) (c := c) ha]
  omega

theorem finrank_ker_K_yw_add {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)))
      + ((n - 1) * n ^ (c + d) + (n - 1) * n ^ (b + c)) =
      n ^ (a + c + d) + n ^ (a + b + c) + (n - 1) ^ 2 * n ^ c := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (K_yw (n := n) (a := a) (b := b) (c := c) (d := d))
  have hrange := finrank_range_K_yw_add_inf
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
  rw [finrank_domain_K_yw (n := n) (a := a) (b := b) (c := c) (d := d) ha] at hnull
  omega

set_option synthInstance.maxHeartbeats 200000 in
-- The domain is a nested product of finite function spaces; rank-nullity needs more instance-search budget.
theorem finrank_ker_K_yzw_add {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d)))
      + ((n - 1) * n ^ (c + d)
        + (n - 1) * n ^ (b + d)
        + (n - 1) * n ^ (b + c)
        + (n - 1) ^ 3) =
      n ^ (a + c + d) + n ^ (a + b + d) + n ^ (a + b + c)
        + ((n - 1) ^ 2 * n ^ d + (n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ b) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d))
  have hrange := finrank_range_K_yzw_add_pair_infs
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
  rw [finrank_domain_K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) ha] at hnull
  omega

end Core4loop
