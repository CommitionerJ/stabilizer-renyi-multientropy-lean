import Core4loop.TriangleLeaf.LeafDotIndex
import Core4loop.TriangleLeaf.ProfileKernelIndexDiffFun

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafKernelIndexDiffDot
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y :
      (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        × LeafDiffProfileCoord n a) : F :=
  ∑ p : PVec n a,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (X.1 ω).1 p * (Y.1 ω).1 p)
      +
    (∑ ω : PassiveVisibleIndex n d hd,
      (X.1 ω).1 p * (Y.2 p).1 (vecSum ω.1))
      +
    (∑ ω : PassiveVisibleIndex n d hd,
      (X.2 p).1 (vecSum ω.1) * (Y.1 ω).1 p)
      +
    (Fintype.card (Vec n (d - 1)) : F) *
      ∑ s : I n, (X.2 p).1 s * (Y.2 p).1 s)

theorem leafDotProfile_kernel_indexDiff_symm_eq_dot
    {n a d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y :
      (PassiveVisibleIndex n d hd → LeafScalarProfileKernel n a)
        × LeafDiffProfileCoord n a) :
    leafDotProfile
        (((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).symm X).1)
        (((leafProfileKernelEquivIndexDiff
          (n := n) (a := a) (d := d) hd).symm Y).1)
      =
      leafKernelIndexDiffDot (n := n) (a := a) (d := d) hd X Y := by
  rw [leafDotProfile_kernel_indexDiff_symm_apply_index
    (n := n) (a := a) (d := d) hd X Y]
  rfl

def qLeafLeftKernelIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    leafKernelIndexDiffDot (n := n) (a := a) (d := d) hd
      ((fun ω => XB.1 ω (vecSum y) z), XB.2 (vecSum y) z)
      ((fun ω => XC.1 ω y (vecSum z)), XC.2 y (vecSum z))

def qLeafRightKernelIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  ∑ y : YVec n b, ∑ z : ZVec n c,
    leafKernelIndexDiffDot (n := n) (a := a) (d := d) hd
      ((fun ω => XB.1 ω (vecSum y + 1) z), XB.2 (vecSum y + 1) z)
      ((fun ω => XC.1 ω y (vecSum z + 1)), XC.2 y (vecSum z + 1))

def qLeafProfileKernelIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  qLeafLeftKernelIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC
    +
  qLeafRightKernelIndexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC

theorem qLeafProfile_kernel_indexDiff_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    qLeafProfile
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBKernelPart
          (n := n) (a := a) (c := c) (d := d)
          ((leafBProfileKernelCoordEquivIndexDiff
            (n := n) (a := a) (c := c) (d := d) hd).symm XB))
        (leafVisibleCKernelPart
          (n := n) (a := a) (b := b) (d := d)
          ((leafCProfileKernelCoordEquivIndexDiff
            (n := n) (a := a) (b := b) (d := d) hd).symm XC))
      =
      qLeafProfileKernelIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC := by
  unfold qLeafProfile qLeafLeft qLeafRight
    qLeafProfileKernelIndexDiff
    qLeafLeftKernelIndexDiff qLeafRightKernelIndexDiff
  simp_rw [leafBProfile_leafBVisKernelOfCoord,
    leafCProfile_leafCVisKernelOfCoord]
  simp_rw [leafBProfileKernelCoordEquivIndexDiff_symm_apply
    (n := n) (a := a) (c := c) (d := d) hd XB]
  simp_rw [leafCProfileKernelCoordEquivIndexDiff_symm_apply
    (n := n) (a := a) (b := b) (d := d) hd XC]
  simp_rw [leafDotProfile_kernel_indexDiff_symm_eq_dot
    (n := n) (a := a) (d := d) hd]

end

end TriangleLeaf
end Core4loop
