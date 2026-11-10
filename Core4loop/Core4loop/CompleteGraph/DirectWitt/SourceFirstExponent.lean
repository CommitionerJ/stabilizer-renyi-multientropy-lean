import Core4loop.CompleteGraph.SingletonLC.StarKernel
import Core4loop.CompleteGraph.Odd.Residual
import Core4loop.CompleteGraph.EvenAllLarge.Residual

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

open CompleteGraph.SingletonLC
open CompleteGraph.Odd
open CompleteGraph.EvenP

noncomputable section

attribute [local instance] Classical.propDecidable

noncomputable def k4OddRawExponentNat
    {n a b c d : Nat} [NeZero n] (hn : Odd n) : Nat :=
  n ^ (a + b + d) +
    k4OddResidualExponent
      (a := a) (b := b) (c := c) (d := d) hn

noncomputable def k4EvenAllLargeRawExponentNat
    {n a b c d : Nat} [NeZero n] : Nat :=
  n ^ (a + b + d) +
    k4EvenAllLargeResidualExponent
      (n := n) (a := a) (b := b) (c := c) (d := d)

theorem k4OddRawExponentNat_add_halfRank_eq_scale_add_source
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Odd n)
    (ha2 : 2 <= a) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d) :
    k4OddRawExponentNat
          (a := a) (b := b) (c := c) (d := d) hn +
        k4OddHalfRankNat n a b c d =
      n ^ (a + b + d) + Module.finrank F (K4PreCSource n a b c d) := by
  unfold k4OddRawExponentNat
  rw [Nat.add_assoc,
    k4OddResidualExponent_add_halfRank_eq_source
      hn2 hn ha2 hb2 hc2 hd2]

theorem k4EvenAllLargeRawExponentNat_add_halfRank_eq_scale_add_source
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (hn : Even n)
    (ha2 : 2 <= a) (hb2 : 2 <= b) (hc2 : 2 <= c) (hd2 : 2 <= d)
    (t0 : K4EvenPTailIndex n a) :
    k4EvenAllLargeRawExponentNat
          (n := n) (a := a) (b := b) (c := c) (d := d) +
        k4EvenAllLargeHalfRankNat n a b c d =
      n ^ (a + b + d) + Module.finrank F (K4PreCSource n a b c d) := by
  unfold k4EvenAllLargeRawExponentNat
  rw [Nat.add_assoc,
    k4EvenAllLargeResidualExponent_add_halfRank_eq_source
      hn2 hn ha2 hb2 hc2 hd2 t0]

noncomputable def X4SourceZ
    (a b c d n : Nat) [NeZero n] : Int :=
  if _ha : a = 1 then
    K4StarExpNat n b c d
  else if _hb : b = 1 then
    K4StarExpNat n a c d
  else if _hc : c = 1 then
    K4StarExpNat n a b d
  else if _hd : d = 1 then
    K4StarExpNat n a b c
  else if hn : Odd n then
    k4OddRawExponentNat
      (a := a) (b := b) (c := c) (d := d) hn
  else
    k4EvenAllLargeRawExponentNat
      (n := n) (a := a) (b := b) (c := c) (d := d)

@[simp] theorem X4SourceZ_of_a_eq_one
    {n a b c d : Nat} [NeZero n] (ha : a = 1) :
    X4SourceZ a b c d n = (K4StarExpNat n b c d : Int) := by
  simp only [X4SourceZ, ha, ↓reduceDIte]

@[simp] theorem X4SourceZ_of_a_ne_one_b_eq_one
    {n a b c d : Nat} [NeZero n] (ha : a ≠ 1) (hb : b = 1) :
    X4SourceZ a b c d n = (K4StarExpNat n a c d : Int) := by
  simp only [X4SourceZ, ha, ↓reduceDIte, hb]

@[simp] theorem X4SourceZ_of_ab_ne_one_c_eq_one
    {n a b c d : Nat} [NeZero n]
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c = 1) :
    X4SourceZ a b c d n = (K4StarExpNat n a b d : Int) := by
  simp only [X4SourceZ, ha, ↓reduceDIte, hb, hc]

@[simp] theorem X4SourceZ_of_abc_ne_one_d_eq_one
    {n a b c d : Nat} [NeZero n]
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d = 1) :
    X4SourceZ a b c d n = (K4StarExpNat n a b c : Int) := by
  simp only [X4SourceZ, ha, ↓reduceDIte, hb, hc, hd]

@[simp] theorem X4SourceZ_of_all_ne_one_odd
    {n a b c d : Nat} [NeZero n]
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d ≠ 1)
    (hn : Odd n) :
    X4SourceZ a b c d n =
      (k4OddRawExponentNat
        (a := a) (b := b) (c := c) (d := d) hn : Int) := by
  simp only [X4SourceZ, ha, ↓reduceDIte, hb, hc, hd, hn]

@[simp] theorem X4SourceZ_of_all_ne_one_even
    {n a b c d : Nat} [NeZero n]
    (ha : a ≠ 1) (hb : b ≠ 1) (hc : c ≠ 1) (hd : d ≠ 1)
    (hn : Even n) :
    X4SourceZ a b c d n =
      (k4EvenAllLargeRawExponentNat
        (n := n) (a := a) (b := b) (c := c) (d := d) : Int) := by
  have hnot : ¬ Odd n := Nat.not_odd_iff_even.mpr hn
  simp only [X4SourceZ, ha, ↓reduceDIte, hb, hc, hd, hnot]

end
end Core4loop
