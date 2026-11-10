import Core4loop.TriangleLeaf.CompatibleResidualKCvSum

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

theorem card_LeafCvProfileKernelCoord
    {n a b d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype.card (LeafCvProfileKernelCoord n a b d hd) =
      (2 : ℕ) ^
        (((n ^ (a - 1) - 1) * n) * n ^ b * (n ^ d - (n - 1))) := by
  classical
  unfold LeafCvProfileKernelCoord
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]
  rw [Fintype.card_fun]
  rw [card_LeafScalarProfileKernel (n := n) (a := a)]
  repeat rw [← pow_mul]
  have hI : Fintype.card (I n) = n := by
    simp [I, ZMod.card]
  rw [hI, card_vec, card_PassiveVisibleIndex (n := n) (d := d) hd]
  ring_nf

theorem intCast_card_LeafCvProfileKernelCoord
    {n a b d : ℕ} [NeZero n] (hd : 0 < d) :
    (Fintype.card (LeafCvProfileKernelCoord n a b d hd) : ℤ) =
      (2 : ℤ) ^
        (((n ^ (a - 1) - 1) * n) * n ^ b * (n ^ d - (n - 1))) := by
  exact_mod_cast card_LeafCvProfileKernelCoord (n := n) (a := a) (b := b) (d := d) hd

theorem leafCompatibleResidualSum_eq_after_kCv_totalCoeffCondition_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            if TotalCdCoeffCondition
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd
                  H (kBv, kBd) then
              (2 : ℤ) ^ (n ^ (a + b) * (n - 1)) *
                (if qLeafProfileKernelTotalCvLinearMap
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      H (kBv, kBd) = 0 then
                  (2 : ℤ) ^
                    (((n ^ (a - 1) - 1) * n) * n ^ b * (n ^ d - (n - 1))) *
                    bitSign
                      (qLeafProfileKernelTotalCvConst
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd
                        H (kBv, kBd))
                else 0)
            else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_kCv_totalCoeffCondition
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  by_cases hC :
      TotalCdCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H (kBv, kBd)
  · simp only [hC, if_true]
    by_cases hL :
        qLeafProfileKernelTotalCvLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          H (kBv, kBd) = 0
    · rw [if_pos hL, if_pos hL]
      rw [intCast_card_LeafCvProfileKernelCoord
        (n := n) (a := a) (b := b) (d := d) hd]
    · rw [if_neg hL, if_neg hL]
  · simp [hC]

end

end TriangleLeaf
end Core4loop
