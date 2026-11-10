import Core4loop.RootSpaces.PullYZ
import Core4loop.RootSpaces.PullYZW

namespace Core4loop

theorem finrank_inf_YZ {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F
      (↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 2 * n ^ d := by
  rw [← range_pullYZ_eq_inf_YZ (n := n) (b := b) (c := c) (d := d) hb hc]
  exact finrank_range_pullYZ (n := n) (b := b) (c := c) (d := d) hb hc

theorem finrank_inf_YW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
      (↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 2 * n ^ c := by
  rw [← range_pullYW_eq_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd]
  exact finrank_range_pullYW (n := n) (b := b) (c := c) (d := d) hb hd

theorem finrank_inf_ZW {n b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
      (↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 2 * n ^ b := by
  rw [← range_pullZW_eq_inf_ZW (n := n) (b := b) (c := c) (d := d) hc hd]
  exact finrank_range_pullZW (n := n) (b := b) (c := c) (d := d) hc hd

theorem finrank_inf_YZW {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
      (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 3 := by
  rw [← range_pullYZW_eq_inf_YZW (n := n) (b := b) (c := c) (d := d) hb hc hd]
  exact finrank_range_pullYZW (n := n) (b := b) (c := c) (d := d) hb hc hd

theorem finrank_sup_YZ_add_finrank_inf {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    Module.finrank F
        (↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ d =
      (n - 1) * n ^ (c + d) + (n - 1) * n ^ (b + d) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (YDiffSpace (n := n) (b := b) (c := c) (d := d))
    (ZDiffSpace (n := n) (b := b) (c := c) (d := d))
  rw [finrank_inf_YZ (n := n) (b := b) (c := c) (d := d) hb hc,
    finrank_YDiffSpace (n := n) (b := b) (c := c) (d := d) hb,
    finrank_ZDiffSpace (n := n) (b := b) (c := c) (d := d) hc] at h
  exact h

theorem finrank_sup_YW_add_finrank_inf {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
        (↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ c =
      (n - 1) * n ^ (c + d) + (n - 1) * n ^ (b + c) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (YDiffSpace (n := n) (b := b) (c := c) (d := d))
    (WDiffSpace (n := n) (b := b) (c := c) (d := d))
  rw [finrank_inf_YW (n := n) (b := b) (c := c) (d := d) hb hd,
    finrank_YDiffSpace (n := n) (b := b) (c := c) (d := d) hb,
    finrank_WDiffSpace (n := n) (b := b) (c := c) (d := d) hd] at h
  exact h

theorem finrank_sup_ZW_add_finrank_inf {n b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d)))
      + (n - 1) ^ 2 * n ^ b =
      (n - 1) * n ^ (b + d) + (n - 1) * n ^ (b + c) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (ZDiffSpace (n := n) (b := b) (c := c) (d := d))
    (WDiffSpace (n := n) (b := b) (c := c) (d := d))
  rw [finrank_inf_ZW (n := n) (b := b) (c := c) (d := d) hc hd,
    finrank_ZDiffSpace (n := n) (b := b) (c := c) (d := d) hc,
    finrank_WDiffSpace (n := n) (b := b) (c := c) (d := d) hd] at h
  exact h

end Core4loop
