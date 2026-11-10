import Core4loop.SquareDiagonal.SurvivorEval
import Core4loop.RootSpaces.KRange

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

abbrev YZWSource (n a b c d : ℕ) [NeZero n] :=
  BFun4 n a c d × CFun4 n a b d × WFun4 n a b c

theorem sqdiag_survivor_sum_unbundled
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ x : YZWSource n a b c d,
      if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 then
        bitSign (Q3 x.1 x.2.1 x.2.2)
      else 0) := by
  classical
  let p : YZWSource n a b c d → Prop :=
    fun x => K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0
  let f : YZWSource n a b c d → ℤ :=
    fun x => bitSign (Q3 x.1 x.2.1 x.2.2)
  have h := sum_if_mul_eq_mul_subtype p (1 : ℤ) f
  simpa [p, f] using h.symm

theorem sqdiag_survivor_sum_reordered_BWC
    {n a b c d : ℕ} [NeZero n] :
    (∑ x : Surviving_yzw n a b c d,
      bitSign (Q3 x.1.1 x.1.2.1 x.1.2.2)) =
    (∑ B : BFun4 n a c d,
      ∑ W : WFun4 n a b c,
        ∑ C : CFun4 n a b d,
          if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0 then
            bitSign (Q3 B C W)
          else 0) := by
  classical
  rw [sqdiag_survivor_sum_unbundled]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro B _
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem K_yzw_eq_KB_add_KC_add_KW
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)
      = KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W := by
  funext y z w
  change
    (∑ p : PVec n a, (dyB B p y z w + dzC C p y z w + dwW W p y z w))
      =
      (∑ p : PVec n a, dyB B p y z w)
        + (∑ p : PVec n a, dzC C p y z w)
        + (∑ p : PVec n a, dwW W p y z w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem K_yzw_zero_iff_KC_eq_target
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0 ↔
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
        = -(KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
            + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) := by
  constructor
  · intro h
    have h0 :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
          + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
            = 0 := by
      rw [← K_yzw_eq_KB_add_KC_add_KW
        (n := n) (a := a) (b := b) (c := c) (d := d) B C W]
      exact h
    funext y z w
    have hpoint := congrFun (congrFun (congrFun h0 y) z) w
    simp only [Pi.add_apply, Pi.zero_apply] at hpoint
    apply eq_neg_of_add_eq_zero_left
    calc
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C y z w
          + (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B y z w
            + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W y z w)
          =
          KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B y z w
            + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C y z w
            + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W y z w := by
            ac_rfl
      _ = 0 := hpoint
  · intro h
    rw [K_yzw_eq_KB_add_KC_add_KW
      (n := n) (a := a) (b := b) (c := c) (d := d) B C W]
    funext y z w
    have hpoint := congrFun (congrFun (congrFun h y) z) w
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hpoint ⊢
    have hsum := eq_neg_iff_add_eq_zero.mp hpoint
    calc
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B y z w
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C y z w
          + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W y z w
          =
          KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C y z w
            + (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B y z w
              + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W y z w) := by
            ac_rfl
      _ = 0 := hsum

end SquareDiagonal
end Core4loop
