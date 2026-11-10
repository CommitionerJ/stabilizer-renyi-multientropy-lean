import Core4loop.TriangleLeaf.CompatibleResidualKCvCoeffCondition
import Core4loop.TriangleLeaf.TotalQCvCoeffReadZero

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

def TotalBCoeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : Prop :=
  TotalCdCoeffCondition
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
    ∧
  TotalCvCoeffCondition
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB

def kCdCvElimExpNat (n a b d : ℕ) : ℕ :=
  n ^ (a + b) * (n - 1)
    + (((n ^ (a - 1) - 1) * n) * n ^ b * (n ^ d - (n - 1)))

def qLeafProfileKernelTotalBCoeffRead
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (LeafCdFamilyIndex n b × (PVec n a × NonzeroI n) → F)
      ×
    (LeafCvFamilyIndex n b d hd
      × {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F) :=
  (qLeafProfileKernelTotalCdCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB,
    qLeafProfileKernelTotalCvCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)

theorem qLeafProfileKernelTotalBCoeffRead_eq_zero_iff_condition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalBCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      TotalBCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB := by
  constructor
  · intro h
    constructor
    · exact
        (qLeafProfileKernelTotalCdCoeffRead_eq_zero_iff_condition
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB).1
          (congrArg Prod.fst h)
    · exact
        (qLeafProfileKernelTotalCvCoeffRead_eq_zero_iff_condition
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB).1
          (congrArg Prod.snd h)
  · intro h
    apply Prod.ext
    · exact
        (qLeafProfileKernelTotalCdCoeffRead_eq_zero_iff_condition
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB).2 h.1
    · exact
        (qLeafProfileKernelTotalCvCoeffRead_eq_zero_iff_condition
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB).2 h.2

theorem leafCompatibleResidualSum_eq_after_kB_totalCoeffCondition_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kBv : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a,
          ∑ kBd : I n → ZVec n c → LeafDiffProfileCoord n a,
            if TotalBCoeffCondition
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd
                  H (kBv, kBd) then
              (2 : ℤ) ^ kCdCvElimExpNat n a b d *
                bitSign
                  (qLeafProfileKernelTotalCvConst
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    H (kBv, kBd))
            else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_kCv_totalCvCoeffCondition_closedCard
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kBv _
  refine Finset.sum_congr rfl ?_
  intro kBd _
  let eCd := n ^ (a + b) * (n - 1)
  let eCv := (((n ^ (a - 1) - 1) * n) * n ^ b * (n ^ d - (n - 1)))
  let s :=
    bitSign
      (qLeafProfileKernelTotalCvConst
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H (kBv, kBd))
  by_cases hCd :
      TotalCdCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H (kBv, kBd)
  · by_cases hCv :
      TotalCvCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        H (kBv, kBd)
    · simp only [hCd, hCv, if_true, TotalBCoeffCondition, true_and]
      dsimp [eCd, eCv, s, kCdCvElimExpNat]
      rw [pow_add]
      ring
    · simp [hCd, hCv, TotalBCoeffCondition]
  · simp [hCd, TotalBCoeffCondition]

theorem leafCompatibleResidualSum_eq_after_XB_totalCoeffCondition_closedCard
    {n a b c d : ℕ} [NeZero n] (ha : 0 < a) (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          if TotalBCoeffCondition
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB then
            (2 : ℤ) ^ kCdCvElimExpNat n a b d *
              bitSign
                (qLeafProfileKernelTotalCvConst
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
          else 0 := by
  classical
  rw [leafCompatibleResidualSum_eq_after_kB_totalCoeffCondition_closedCard
    (n := n) (a := a) (b := b) (c := c) (d := d) ha hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  rw [Fintype.sum_prod_type]

end

end TriangleLeaf
end Core4loop
