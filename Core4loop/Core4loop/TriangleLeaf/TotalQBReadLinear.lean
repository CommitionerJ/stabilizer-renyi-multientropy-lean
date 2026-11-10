import Core4loop.TriangleLeaf.CompatibleResidualBAffine

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private theorem if_add_zero {P : Prop} [Decidable P] (x y : F) :
    (if P then x + y else 0) =
      (if P then x else 0) + (if P then y else 0) := by
  by_cases h : P <;> simp [h]

private theorem sum_if_add_zero
    {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (x y : α → F) :
    (∑ a : α, if P a then x a + y a else 0) =
      (∑ a : α, if P a then x a else 0) +
      (∑ a : α, if P a then y a else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [if_add_zero]

private theorem sum_if_add_add_zero
    {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (x y z w : α → F) :
    (∑ a : α, if P a then (x a + y a) + (z a + w a) else 0) =
      (∑ a : α, if P a then x a + z a else 0) +
      (∑ a : α, if P a then y a + w a else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  by_cases h : P a
  · simp [h]
    abel
  · simp [h]

private theorem if_eq_vecSum_add_one_comm
    {n k : ℕ} [NeZero n] (t : I n) (x : Vec n k) (A : F) :
    (if t = vecSum x + 1 then A else 0) =
      (if t = 1 + vecSum x then A else 0) := by
  rw [add_comm (vecSum x) 1]

theorem qLeafProfileKernelTotalCdCoeff_zeroH_add
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (X + Y)
      =
      qLeafProfileKernelTotalCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) X
        +
      qLeafProfileKernelTotalCdCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) Y := by
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  funext i p s
  unfold qLeafProfileKernelTotalCdCoeff qLeafProfileKernelRemainderCdCoeff
    qLeafScalarCanonicalProfileBlockCdCoeff
  simp [Pi.add_apply, hzero, mul_add, if_add_zero, sum_if_add_zero,
    sum_if_add_add_zero, Finset.sum_add_distrib,
    if_eq_vecSum_add_one_comm]
  repeat rw [Finset.sum_add_distrib]
  abel_nf

theorem qLeafProfileKernelTotalCdCoeff_zeroH_smul
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (X : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (r • X)
      =
      r •
      qLeafProfileKernelTotalCdCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) X := by
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  funext i p s
  unfold qLeafProfileKernelTotalCdCoeff qLeafProfileKernelRemainderCdCoeff
    qLeafScalarCanonicalProfileBlockCdCoeff
  simp [Pi.smul_apply, hzero, Finset.mul_sum, mul_add]
  ring_nf

theorem qLeafProfileKernelTotalCdCoeffRead_zeroH_add
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (X + Y)
      =
      qLeafProfileKernelTotalCdCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) X
        +
      qLeafProfileKernelTotalCdCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) Y := by
  unfold qLeafProfileKernelTotalCdCoeffRead
  rw [qLeafProfileKernelTotalCdCoeff_zeroH_add
    (n := n) (a := a) (b := b) (c := c) (d := d) hd X Y]
  rw [leafDiffFamilyCoeffRead_add]

theorem qLeafProfileKernelTotalCdCoeffRead_zeroH_smul
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (X : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (r • X)
      =
      r •
      qLeafProfileKernelTotalCdCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) X := by
  unfold qLeafProfileKernelTotalCdCoeffRead
  rw [qLeafProfileKernelTotalCdCoeff_zeroH_smul
    (n := n) (a := a) (b := b) (c := c) (d := d) hd r X]
  rw [leafDiffFamilyCoeffRead_smul]

theorem qLeafProfileKernelTotalCvCoeff_zeroH_add
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (X + Y)
      =
      qLeafProfileKernelTotalCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) X
        +
      qLeafProfileKernelTotalCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) Y := by
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  funext i p
  unfold qLeafProfileKernelTotalCvCoeff
    qLeafProfileKernelRemainderCvCoeff qLeafProfileKernelRemainderCvCoeffLeft
    qLeafProfileKernelRemainderCvCoeffRight
    qLeafProfileKernelProfileCvCoeff qLeafProfileKernelProfileCvCoeffLeft
    qLeafProfileKernelProfileCvCoeffRight
    qLeafProfileKernelVisibleScalarCvCoeff
    qLeafProfileKernelVisibleScalarCvCoeffLeft
    qLeafProfileKernelVisibleScalarCvCoeffRight
  simp [Pi.add_apply, hzero, if_add_zero, sum_if_add_zero,
    Finset.sum_add_distrib, if_eq_vecSum_add_one_comm]
  repeat rw [Finset.sum_add_distrib]
  abel_nf

theorem qLeafProfileKernelTotalCvCoeff_zeroH_smul
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (X : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (r • X)
      =
      r •
      qLeafProfileKernelTotalCvCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) X := by
  have hzero :=
    leafVisibleKernelEquivCoord_zero
      (n := n) (b := b) (c := c) (d := d) hd
  funext i p
  unfold qLeafProfileKernelTotalCvCoeff
    qLeafProfileKernelRemainderCvCoeff qLeafProfileKernelRemainderCvCoeffLeft
    qLeafProfileKernelRemainderCvCoeffRight
    qLeafProfileKernelProfileCvCoeff qLeafProfileKernelProfileCvCoeffLeft
    qLeafProfileKernelProfileCvCoeffRight
    qLeafProfileKernelVisibleScalarCvCoeff
    qLeafProfileKernelVisibleScalarCvCoeffLeft
    qLeafProfileKernelVisibleScalarCvCoeffRight
  simp [Pi.smul_apply, hzero, Finset.mul_sum, mul_add]

theorem qLeafProfileKernelTotalCvCoeffRead_zeroH_add
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (X + Y)
      =
      qLeafProfileKernelTotalCvCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) X
        +
      qLeafProfileKernelTotalCvCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) Y := by
  unfold qLeafProfileKernelTotalCvCoeffRead
  rw [qLeafProfileKernelTotalCvCoeff_zeroH_add
    (n := n) (a := a) (b := b) (c := c) (d := d) hd X Y]
  rw [leafScalarFamilyCoeffRead_add]

theorem qLeafProfileKernelTotalCvCoeffRead_zeroH_smul
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (X : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (r • X)
      =
      r •
      qLeafProfileKernelTotalCvCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) X := by
  unfold qLeafProfileKernelTotalCvCoeffRead
  rw [qLeafProfileKernelTotalCvCoeff_zeroH_smul
    (n := n) (a := a) (b := b) (c := c) (d := d) hd r X]
  rw [leafScalarFamilyCoeffRead_smul]

theorem qLeafProfileKernelTotalBCoeffRead_zeroH_add
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalBCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (X + Y)
      =
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) X
        +
      qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafVisibleKernel n b c d) Y := by
  apply Prod.ext
  · exact qLeafProfileKernelTotalCdCoeffRead_zeroH_add
      (n := n) (a := a) (b := b) (c := c) (d := d) hd X Y
  · exact qLeafProfileKernelTotalCvCoeffRead_zeroH_add
      (n := n) (a := a) (b := b) (c := c) (d := d) hd X Y

theorem qLeafProfileKernelTotalBCoeffRead_zeroH_smul
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (X : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalBCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) (r • X)
      =
      r •
      qLeafProfileKernelTotalBCoeffRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafVisibleKernel n b c d) X := by
  apply Prod.ext
  · exact qLeafProfileKernelTotalCdCoeffRead_zeroH_smul
      (n := n) (a := a) (b := b) (c := c) (d := d) hd r X
  · exact qLeafProfileKernelTotalCvCoeffRead_zeroH_smul
      (n := n) (a := a) (b := b) (c := c) (d := d) hd r X

noncomputable def qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
      ((LeafCdFamilyIndex n b × (PVec n a × NonzeroI n) → F)
        ×
       (LeafCvFamilyIndex n b d hd
          × {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F)) where
  toFun X :=
    qLeafProfileKernelTotalBCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      (0 : LeafVisibleKernel n b c d) X
  map_add' X Y :=
    qLeafProfileKernelTotalBCoeffRead_zeroH_add
      (n := n) (a := a) (b := b) (c := c) (d := d) hd X Y
  map_smul' r X :=
    qLeafProfileKernelTotalBCoeffRead_zeroH_smul
      (n := n) (a := a) (b := b) (c := c) (d := d) hd r X

end

end TriangleLeaf
end Core4loop
