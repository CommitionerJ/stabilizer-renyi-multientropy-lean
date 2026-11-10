import Core4loop.TriangleLeaf.VisibleCard
import Core4loop.TriangleLeaf.ExponentSplit
import Core4loop.TriangleCore.Parity
import Core3loop.OddCase
import Core3loop.EvenCase

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem LeafVisibleUnitZ_eq_genericScalarVisibleExpZ
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d)
    (h : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c)) :
    LeafVisibleUnitZ a b c d n =
      nPowZ n b + nPowZ n c + (mZ n) ^ 2 := by
  unfold LeafVisibleUnitZ
  rw [TriangleCore.ThetaZ_triangleLeaf_eq_of_not_even_or_small
    (a := a) (b := b) (c := c) (d := d) (n := n) ha hd h]
  unfold LeafTailUnitZ nPowZ mZ
  ring

theorem LeafTailUnitZ_add_LeafVisibleUnitZ_eq_evenScalarBlockExpZ
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d)
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n =
      nPowZ n (b + 1) + nPowZ n (c + 1) + nPowZ n b + nPowZ n c
        + nPowZ n 2 - 4 * (n : ℤ) + 3 := by
  unfold LeafVisibleUnitZ
  rw [TriangleCore.ThetaZ_triangleLeaf_eq_of_even_large
    (a := a) (b := b) (c := c) (d := d) (n := n) ha hd hn hb2 hc2]
  unfold LeafTailUnitZ nPowZ mZ
  ring

theorem LeafTailUnitZ_add_LeafVisibleUnitZ_eq_genericEvenScalarBlockExpZ
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d)
    (h : ¬ (Even n ∧ 2 ≤ b ∧ 2 ≤ c)) :
    LeafTailUnitZ b c n + LeafVisibleUnitZ a b c d n =
      nPowZ n (b + 1) + nPowZ n (c + 1) + nPowZ n b + nPowZ n c
        - (n : ℤ) + 1 := by
  unfold LeafVisibleUnitZ
  rw [TriangleCore.ThetaZ_triangleLeaf_eq_of_not_even_or_small
    (a := a) (b := b) (c := c) (d := d) (n := n) ha hd h]
  unfold LeafTailUnitZ nPowZ mZ
  ring

def leafScalarOddVisibleSign {n b c : ℕ} [NeZero n]
    (H : LeafScalarVisibleKernel n b c) : ℤ :=
  Core3loop.oddVisibleSign (b := b) (c := c) (n := n)
    (leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c) H)

theorem sum_leafScalarOddVisibleSign_eq_closed_form_of_odd
    {n b c : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hn : Odd n) :
    ∑ H : LeafScalarVisibleKernel n b c,
      leafScalarOddVisibleSign (n := n) (b := b) (c := c) H
      =
      (2 : ℤ) ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
  let e := leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c)
  calc
    ∑ H : LeafScalarVisibleKernel n b c,
        leafScalarOddVisibleSign (n := n) (b := b) (c := c) H
      =
        ∑ bc : Core3loop.ScalarVisibleCompat b c n,
          Core3loop.oddVisibleSign (b := b) (c := c) (n := n) bc := by
          simpa [e, leafScalarOddVisibleSign] using
            (Equiv.sum_comp e
              (fun bc : Core3loop.ScalarVisibleCompat b c n =>
                Core3loop.oddVisibleSign (b := b) (c := c) (n := n) bc))
    _ = (2 : ℤ) ^ (n ^ b + n ^ c + (n - 1) ^ 2) := by
          exact Core3loop.sum_oddVisible_eq_closed_form_of_odd
            (b := b) (c := c) (n := n) hb hc hn

def leafScalarEvenVisibleKernelSign {n b c : ℕ} [NeZero n]
    (H : LeafScalarVisibleKernel n b c)
    (c₂ : Core3loop.ScalarCCoef b n) (b₂ : Core3loop.ScalarBCoef c n) : ℤ :=
  let bc := leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c) H
  bitSign
    (Core3loop.qScalar (b := b) (c := c) (n := n) bc.bcoef c₂
      + Core3loop.qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)

theorem sum_leafScalarEvenVisible_eq_closed_form_all_ge_two
    {n b c : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    ∑ H : LeafScalarVisibleKernel n b c,
      ∑ c₂ : Core3loop.ScalarCCoef b n, ∑ b₂ : Core3loop.ScalarBCoef c n,
        leafScalarEvenVisibleKernelSign (n := n) (b := b) (c := c) H c₂ b₂
      =
      (2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
  let e := leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c)
  calc
    ∑ H : LeafScalarVisibleKernel n b c,
      ∑ c₂ : Core3loop.ScalarCCoef b n, ∑ b₂ : Core3loop.ScalarBCoef c n,
        leafScalarEvenVisibleKernelSign (n := n) (b := b) (c := c) H c₂ b₂
      =
        ∑ bc : Core3loop.ScalarVisibleCompat b c n,
          ∑ c₂ : Core3loop.ScalarCCoef b n, ∑ b₂ : Core3loop.ScalarBCoef c n,
            bitSign
              (Core3loop.qScalar (b := b) (c := c) (n := n) bc.bcoef c₂
                + Core3loop.qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) := by
          simpa [e, leafScalarEvenVisibleKernelSign] using
            (Equiv.sum_comp e
              (fun bc : Core3loop.ScalarVisibleCompat b c n =>
                ∑ c₂ : Core3loop.ScalarCCoef b n,
                  ∑ b₂ : Core3loop.ScalarBCoef c n,
                    bitSign
                      (Core3loop.qScalar (b := b) (c := c) (n := n) bc.bcoef c₂
                        + Core3loop.qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)))
    _ =
      (2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
          exact Core3loop.sum_evenVisible_eq_kernel_visible_closed_form_all_ge_two
            (b := b) (c := c) (n := n) hn hb2 hc2

theorem sum_leafScalarEvenVisible_eq_closed_form_min_eq_one
    {n b c : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hdeg : b = 1 ∨ c = 1) :
    ∑ H : LeafScalarVisibleKernel n b c,
      ∑ c₂ : Core3loop.ScalarCCoef b n, ∑ b₂ : Core3loop.ScalarBCoef c n,
        leafScalarEvenVisibleKernelSign (n := n) (b := b) (c := c) H c₂ b₂
      =
      (2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) := by
  let e := leafScalarVisibleKernelEquivCore3 (n := n) (b := b) (c := c)
  calc
    ∑ H : LeafScalarVisibleKernel n b c,
      ∑ c₂ : Core3loop.ScalarCCoef b n, ∑ b₂ : Core3loop.ScalarBCoef c n,
        leafScalarEvenVisibleKernelSign (n := n) (b := b) (c := c) H c₂ b₂
      =
        ∑ bc : Core3loop.ScalarVisibleCompat b c n,
          ∑ c₂ : Core3loop.ScalarCCoef b n, ∑ b₂ : Core3loop.ScalarBCoef c n,
            bitSign
              (Core3loop.qScalar (b := b) (c := c) (n := n) bc.bcoef c₂
                + Core3loop.qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) := by
          simpa [e, leafScalarEvenVisibleKernelSign] using
            (Equiv.sum_comp e
              (fun bc : Core3loop.ScalarVisibleCompat b c n =>
                ∑ c₂ : Core3loop.ScalarCCoef b n,
                  ∑ b₂ : Core3loop.ScalarBCoef c n,
                    bitSign
                      (Core3loop.qScalar (b := b) (c := c) (n := n) bc.bcoef c₂
                        + Core3loop.qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)))
    _ =
      (2 : ℤ) ^
        (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) := by
          exact Core3loop.sum_evenVisible_eq_kernel_visible_closed_form_min_eq_one
            (b := b) (c := c) (n := n) hn hb hc hdeg

end

end TriangleLeaf
end Core4loop
