import Core4loop.TriangleLeaf.TotalQCvCoeff
import Core4loop.TriangleLeaf.ProfileKernelIndexDiffVisibleQ

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def qLeafProfileKernelProfileCvCoeffLeft
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  ∑ z : ZVec n c,
    if i.2.2 = vecSum z then
      (XB.1 i.1 (vecSum i.2.1) z).1 p
    else 0

def qLeafProfileKernelProfileCvCoeffRight
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  ∑ z : ZVec n c,
    if i.2.2 = vecSum z + 1 then
      (XB.1 i.1 (vecSum i.2.1 + 1) z).1 p
    else 0

def qLeafProfileKernelProfileCvCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  qLeafProfileKernelProfileCvCoeffLeft
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
  +
  qLeafProfileKernelProfileCvCoeffRight
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p

private theorem qLeafProfileKernelProfileCvCoeffLeft_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelProfileCvCoeffLeft
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          (XB.1 ω (vecSum y) z).1 p *
            (kCv ω y (vecSum z)).1 p := by
  unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
    qLeafProfileKernelProfileCvCoeffLeft
  rw [Fintype.sum_prod_type]
  conv =>
    lhs
    simp only [Finset.mul_sum]
  rw [sum_ω_ysz_p_z_comm
    (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b) (SZ := I n)
    (P := PVec n a) (Z := ZVec n c)
    (f := fun ω y sz p z =>
      (kCv ω y sz).1 p *
        if sz = vecSum z then
          (XB.1 ω (vecSum y) z).1 p
        else 0)]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  refine Finset.sum_congr rfl ?_
  intro p _
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [sum_mul_ite_eq]
  ring

private theorem qLeafProfileKernelProfileCvCoeffRight_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelProfileCvCoeffRight
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          (XB.1 ω (vecSum y + 1) z).1 p *
            (kCv ω y (vecSum z + 1)).1 p := by
  unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
    qLeafProfileKernelProfileCvCoeffRight
  rw [Fintype.sum_prod_type]
  conv =>
    lhs
    simp only [Finset.mul_sum]
  rw [sum_ω_ysz_p_z_comm
    (Ω := PassiveVisibleIndex n d hd) (Y := YVec n b) (SZ := I n)
    (P := PVec n a) (Z := ZVec n c)
    (f := fun ω y sz p z =>
      (kCv ω y sz).1 p *
        if sz = vecSum z + 1 then
          (XB.1 ω (vecSum y + 1) z).1 p
        else 0)]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  refine Finset.sum_congr rfl ?_
  intro p _
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [sum_mul_ite_eq]
  ring

theorem qLeafProfileKernelProfileCvCoeff_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelProfileCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        qProfileABCLeafCvRightLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          XB.1 ω kCv := by
  unfold qLeafProfileKernelProfileCvCoeff
  calc
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (fun i p =>
          qLeafProfileKernelProfileCvCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
          +
          qLeafProfileKernelProfileCvCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p)
        (fun i => kCv i.1 i.2.1 i.2.2)
        =
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelProfileCvCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCv i.1 i.2.1 i.2.2)
        +
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelProfileCvCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCv i.1 i.2.1 i.2.2) := by
          unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
          simp only [Finset.sum_add_distrib, mul_add]
    _ =
        qLeafProfileKernelVisibleIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB.1 kCv := by
          rw [qLeafProfileKernelProfileCvCoeffLeft_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
          rw [qLeafProfileKernelProfileCvCoeffRight_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
          rw [qLeafProfileKernelVisibleIndexDiff_eq_visibleVisibleTerms
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB.1 kCv]
    _ =
        ∑ ω : PassiveVisibleIndex n d hd,
          qProfileABCLeafCvRightLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            XB.1 ω kCv := by
          rfl

end

end TriangleLeaf
end Core4loop
