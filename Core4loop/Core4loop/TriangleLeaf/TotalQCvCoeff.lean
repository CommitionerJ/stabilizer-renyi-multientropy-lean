import Core4loop.TriangleLeaf.CompatibleResidualKCvLinear
import Core4loop.TriangleLeaf.ScalarProfileCoeffZero

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafCvFamilyIndex
    (n b d : ℕ) [NeZero n] (hd : 0 < d) :=
  PassiveVisibleIndex n d hd × (YVec n b × I n)

def qLeafProfileKernelRemainderCvCoeffLeft
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  ∑ z : ZVec n c,
    if i.2.2 = vecSum z then
      (XB.2 (vecSum i.2.1) z p).1 (vecSum i.1.1)
    else 0

def qLeafProfileKernelRemainderCvCoeffRight
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  ∑ z : ZVec n c,
    if i.2.2 = vecSum z + 1 then
      (XB.2 (vecSum i.2.1 + 1) z p).1 (vecSum i.1.1)
    else 0

def qLeafProfileKernelRemainderCvCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  qLeafProfileKernelRemainderCvCoeffLeft
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
  +
  qLeafProfileKernelRemainderCvCoeffRight
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p

theorem sum_ω_ysz_p_z_comm
    {Ω Y SZ P Z : Type*}
    [Fintype Ω] [Fintype Y] [Fintype SZ] [Fintype P] [Fintype Z]
    (f : Ω → Y → SZ → P → Z → F) :
    (∑ ω : Ω, ∑ ysz : Y × SZ, ∑ p : P, ∑ z : Z,
        f ω ysz.1 ysz.2 p z)
      =
      ∑ y : Y, ∑ z : Z, ∑ p : P, ∑ ω : Ω,
        ∑ sz : SZ, f ω y sz p z := by
  calc
    (∑ ω : Ω, ∑ ysz : Y × SZ, ∑ p : P, ∑ z : Z,
        f ω ysz.1 ysz.2 p z)
        =
        ∑ ω : Ω, ∑ y : Y, ∑ sz : SZ, ∑ p : P, ∑ z : Z,
          f ω y sz p z := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          rw [Fintype.sum_prod_type]
    _ =
        ∑ y : Y, ∑ ω : Ω, ∑ sz : SZ, ∑ p : P, ∑ z : Z,
          f ω y sz p z := by
          rw [Finset.sum_comm]
    _ =
        ∑ y : Y, ∑ z : Z, ∑ p : P, ∑ ω : Ω,
          ∑ sz : SZ, f ω y sz p z := by
          refine Finset.sum_congr rfl ?_
          intro y _
          calc
            (∑ ω : Ω, ∑ sz : SZ, ∑ p : P, ∑ z : Z,
                f ω y sz p z)
                =
                ∑ ω : Ω, ∑ sz : SZ, ∑ z : Z, ∑ p : P,
                  f ω y sz p z := by
                  refine Finset.sum_congr rfl ?_
                  intro ω _
                  refine Finset.sum_congr rfl ?_
                  intro sz _
                  rw [Finset.sum_comm]
            _ =
                ∑ ω : Ω, ∑ z : Z, ∑ sz : SZ, ∑ p : P,
                  f ω y sz p z := by
                  refine Finset.sum_congr rfl ?_
                  intro ω _
                  rw [Finset.sum_comm]
            _ =
                ∑ z : Z, ∑ ω : Ω, ∑ sz : SZ, ∑ p : P,
                  f ω y sz p z := by
                  rw [Finset.sum_comm]
            _ =
                ∑ z : Z, ∑ ω : Ω, ∑ p : P, ∑ sz : SZ,
                  f ω y sz p z := by
                  refine Finset.sum_congr rfl ?_
                  intro z _
                  refine Finset.sum_congr rfl ?_
                  intro ω _
                  rw [Finset.sum_comm]
            _ =
                ∑ z : Z, ∑ p : P, ∑ ω : Ω, ∑ sz : SZ,
                  f ω y sz p z := by
                  refine Finset.sum_congr rfl ?_
                  intro z _
                  rw [Finset.sum_comm]

private theorem qLeafProfileKernelRemainderCvCoeffLeft_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelRemainderCvCoeffLeft
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          (XB.2 (vecSum y) z p).1 (vecSum ω.1) *
            (kCv ω y (vecSum z)).1 p := by
  unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
    qLeafProfileKernelRemainderCvCoeffLeft
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
          (XB.2 (vecSum y) z p).1 (vecSum ω.1)
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

private theorem qLeafProfileKernelRemainderCvCoeffRight_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelRemainderCvCoeffRight
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
        ∑ ω : PassiveVisibleIndex n d hd,
          (XB.2 (vecSum y + 1) z p).1 (vecSum ω.1) *
            (kCv ω y (vecSum z + 1)).1 p := by
  unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
    qLeafProfileKernelRemainderCvCoeffRight
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
          (XB.2 (vecSum y + 1) z p).1 (vecSum ω.1)
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

theorem qLeafProfileKernelRemainderCvCoeff_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelRemainderCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      qLeafProfileKernelRemainderCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv := by
  unfold qLeafProfileKernelRemainderCvCoeff
  calc
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (fun i p =>
          qLeafProfileKernelRemainderCvCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
          +
          qLeafProfileKernelRemainderCvCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p)
        (fun i => kCv i.1 i.2.1 i.2.2)
        =
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelRemainderCvCoeffLeft
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCv i.1 i.2.1 i.2.2)
        +
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelRemainderCvCoeffRight
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCv i.1 i.2.1 i.2.2) := by
          unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
          simp only [Finset.sum_add_distrib, mul_add]
    _ =
        (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
          ∑ ω : PassiveVisibleIndex n d hd,
            (XB.2 (vecSum y) z p).1 (vecSum ω.1) *
              (kCv ω y (vecSum z)).1 p)
        +
        (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
          ∑ ω : PassiveVisibleIndex n d hd,
            (XB.2 (vecSum y + 1) z p).1 (vecSum ω.1) *
              (kCv ω y (vecSum z + 1)).1 p) := by
          rw [qLeafProfileKernelRemainderCvCoeffLeft_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
          rw [qLeafProfileKernelRemainderCvCoeffRight_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
    _ =
        qLeafProfileKernelRemainderCvLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv := by
          unfold qLeafProfileKernelRemainderCvLinearMap leafCvEvalLinearMap
          simp

end

end TriangleLeaf
end Core4loop
