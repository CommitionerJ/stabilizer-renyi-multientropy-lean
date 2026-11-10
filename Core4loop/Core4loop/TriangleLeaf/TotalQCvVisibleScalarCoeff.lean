import Core4loop.TriangleLeaf.TotalQCvProfileCoeff

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def qLeafProfileKernelVisibleScalarCvCoeffLeft
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  ∑ z : ZVec n c,
    if i.2.2 = vecSum z then
      if p = (zeroVec : PVec n a) then
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) i.1).1.1
          (vecSum i.2.1) z
      else 0
    else 0

def qLeafProfileKernelVisibleScalarCvCoeffRight
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  ∑ z : ZVec n c,
    if i.2.2 = vecSum z + 1 then
      if p = (zeroVec : PVec n a) then
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) i.1).1.1
          (vecSum i.2.1 + 1) z
      else 0
    else 0

def qLeafProfileKernelVisibleScalarCvCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  qLeafProfileKernelVisibleScalarCvCoeffLeft
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H i p
  +
  qLeafProfileKernelVisibleScalarCvCoeffRight
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H i p

private theorem qLeafProfileKernelVisibleScalarCvCoeffLeft_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelVisibleScalarCvCoeffLeft
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          if p = (zeroVec : PVec n a) then
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum y) z *
            (kCv ω y (vecSum z)).1 p
          else 0 := by
  unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
    qLeafProfileKernelVisibleScalarCvCoeffLeft
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
          if p = (zeroVec : PVec n a) then
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum y) z
          else 0
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
  by_cases hp : p = (zeroVec : PVec n a)
  · simp [hp]
    ring
  · simp [hp]

private theorem qLeafProfileKernelVisibleScalarCvCoeffRight_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelVisibleScalarCvCoeffRight
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          if p = (zeroVec : PVec n a) then
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum y + 1) z *
            (kCv ω y (vecSum z + 1)).1 p
          else 0 := by
  unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
    qLeafProfileKernelVisibleScalarCvCoeffRight
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
          if p = (zeroVec : PVec n a) then
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum y + 1) z
          else 0
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
  by_cases hp : p = (zeroVec : PVec n a)
  · simp [hp]
    ring
  · simp [hp]

private theorem sum_y_z_p_ω_if_zero_eq
    {Y Z P Ω : Type*} [Fintype Y] [Fintype Z] [Fintype P]
    [DecidableEq P] [Fintype Ω]
    (p₀ : P) (B : Ω → Y → Z → F) (K : Ω → Y → Z → P → F) :
    (∑ y : Y, ∑ z : Z, ∑ p : P, ∑ ω : Ω,
      if p = p₀ then B ω y z * K ω y z p else 0)
      =
      ∑ ω : Ω, ∑ y : Y, ∑ z : Z, B ω y z * K ω y z p₀ := by
  calc
    (∑ y : Y, ∑ z : Z, ∑ p : P, ∑ ω : Ω,
      if p = p₀ then B ω y z * K ω y z p else 0)
        =
        ∑ y : Y, ∑ z : Z, ∑ ω : Ω, ∑ p : P,
          if p = p₀ then B ω y z * K ω y z p else 0 := by
          refine Finset.sum_congr rfl ?_
          intro y _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [Finset.sum_comm]
    _ =
        ∑ y : Y, ∑ ω : Ω, ∑ z : Z, ∑ p : P,
          if p = p₀ then B ω y z * K ω y z p else 0 := by
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Finset.sum_comm]
    _ =
        ∑ ω : Ω, ∑ y : Y, ∑ z : Z, ∑ p : P,
          if p = p₀ then B ω y z * K ω y z p else 0 := by
          rw [Finset.sum_comm]
    _ =
        ∑ ω : Ω, ∑ y : Y, ∑ z : Z, B ω y z * K ω y z p₀ := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          refine Finset.sum_congr rfl ?_
          intro y _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [Finset.sum_eq_single p₀]
          · simp
          · intro p _ hp
            simp [hp]
          · simp

private theorem core3_sumY_eq_vecSum {n b : ℕ} [NeZero n] (y : YVec n b) :
    Core3loop.sumY (b := b) (n := n) y = vecSum y := by
  rfl

private theorem core3_sumZ_eq_vecSum {n c : ℕ} [NeZero n] (z : ZVec n c) :
    Core3loop.sumZ (c := c) (n := n) z = vecSum z := by
  rfl

theorem qLeafProfileKernelVisibleScalarCvCoeff_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelVisibleScalarCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        (qScalarRightLinearMap
          (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1)
          (leafCVisibleScalarIndexDiffLinearMap
            (n := n) (a := a) (b := b) (d := d) hd ω kCv) := by
  unfold qLeafProfileKernelVisibleScalarCvCoeff
  calc
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (fun i p =>
          qLeafProfileKernelVisibleScalarCvCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H i p
          +
          qLeafProfileKernelVisibleScalarCvCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H i p)
        (fun i => kCv i.1 i.2.1 i.2.2)
        =
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelVisibleScalarCvCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          (fun i => kCv i.1 i.2.1 i.2.2)
        +
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelVisibleScalarCvCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          (fun i => kCv i.1 i.2.1 i.2.2) := by
          unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
          simp only [Finset.sum_add_distrib, mul_add]
    _ =
        (∑ ω : PassiveVisibleIndex n d hd,
          ∑ y : YVec n b, ∑ z : ZVec n c,
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum y) z *
            (kCv ω y (vecSum z)).1 (zeroVec : PVec n a))
        +
        (∑ ω : PassiveVisibleIndex n d hd,
          ∑ y : YVec n b, ∑ z : ZVec n c,
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum y + 1) z *
            (kCv ω y (vecSum z + 1)).1 (zeroVec : PVec n a)) := by
          rw [qLeafProfileKernelVisibleScalarCvCoeffLeft_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCv]
          rw [qLeafProfileKernelVisibleScalarCvCoeffRight_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCv]
          rw [sum_y_z_p_ω_if_zero_eq
            (Y := YVec n b) (Z := ZVec n c) (P := PVec n a)
            (Ω := PassiveVisibleIndex n d hd)
            (p₀ := (zeroVec : PVec n a))
            (B := fun ω y z =>
              ((leafVisibleKernelEquivCoord
                (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
                (vecSum y) z)
            (K := fun ω y z p => (kCv ω y (vecSum z)).1 p)]
          rw [sum_y_z_p_ω_if_zero_eq
            (Y := YVec n b) (Z := ZVec n c) (P := PVec n a)
            (Ω := PassiveVisibleIndex n d hd)
            (p₀ := (zeroVec : PVec n a))
            (B := fun ω y z =>
              ((leafVisibleKernelEquivCoord
                (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
                (vecSum y + 1) z)
            (K := fun ω y z p => (kCv ω y (vecSum z + 1)).1 p)]
    _ =
        ∑ ω : PassiveVisibleIndex n d hd,
          (qScalarRightLinearMap
            (b := b) (c := c) (n := n)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1)
            (leafCVisibleScalarIndexDiffLinearMap
              (n := n) (a := a) (b := b) (d := d) hd ω kCv) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro ω _
          change
            (∑ y : YVec n b, ∑ z : ZVec n c,
                ((leafVisibleKernelEquivCoord
                  (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
                  (vecSum y) z *
                (kCv ω y (vecSum z)).1 (zeroVec : PVec n a))
              +
              (∑ y : YVec n b, ∑ z : ZVec n c,
                ((leafVisibleKernelEquivCoord
                  (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
                  (vecSum y + 1) z *
                (kCv ω y (vecSum z + 1)).1 (zeroVec : PVec n a))
              =
              Core3loop.qScalar (b := b) (c := c) (n := n)
                ((leafVisibleKernelEquivCoord
                  (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
                (fun y sz => (kCv ω y sz).1 (zeroVec : PVec n a))
          rw [Core3loop.qScalar]
          rw [Core3loop.qLeftScalar_eq_sum_yz]
          rw [Core3loop.qRightScalar_eq_sum_yz]
          simp [core3_sumY_eq_vecSum]

end

end TriangleLeaf
end Core4loop
