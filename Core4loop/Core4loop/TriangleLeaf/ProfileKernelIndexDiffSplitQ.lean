import Core4loop.TriangleLeaf.ProfileKernelIndexDiffVisibleQ

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def qLeafProfileKernelRemainderIndexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) : F :=
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y) z).1 p *
        (XC.2 y (vecSum z) p).1 (vecSum ω.1))
    +
    (∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y) z p).1 (vecSum ω.1) *
        (XC.1 ω y (vecSum z)).1 p)
    +
    (Fintype.card (Vec n (d - 1)) : F) *
      ∑ s : I n,
        (XB.2 (vecSum y) z p).1 s *
          (XC.2 y (vecSum z) p).1 s))
  +
  (∑ y : YVec n b, ∑ z : ZVec n c, ∑ p : PVec n a,
    ((∑ ω : PassiveVisibleIndex n d hd,
      (XB.1 ω (vecSum y + 1) z).1 p *
        (XC.2 y (vecSum z + 1) p).1 (vecSum ω.1))
    +
    (∑ ω : PassiveVisibleIndex n d hd,
      (XB.2 (vecSum y + 1) z p).1 (vecSum ω.1) *
        (XC.1 ω y (vecSum z + 1)).1 p)
    +
    (Fintype.card (Vec n (d - 1)) : F) *
      ∑ s : I n,
        (XB.2 (vecSum y + 1) z p).1 s *
          (XC.2 y (vecSum z + 1) p).1 s))

theorem qLeafProfileKernelIndexDiff_eq_visible_add_remainder
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    qLeafProfileKernelIndexDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC
      =
      qLeafProfileKernelVisibleIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB.1 XC.1
        +
      qLeafProfileKernelRemainderIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC := by
  rw [qLeafProfileKernelVisibleIndexDiff_eq_visibleVisibleTerms
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB.1 XC.1]
  unfold qLeafProfileKernelIndexDiff qLeafLeftKernelIndexDiff
    qLeafRightKernelIndexDiff leafKernelIndexDiffDot
    qLeafProfileKernelRemainderIndexDiff
  simp only [Finset.sum_add_distrib]
  abel

theorem bitSign_qLeafProfileKernelIndexDiff_eq_visible_mul_remainder
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    bitSign
        (qLeafProfileKernelIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC)
      =
      bitSign
        (qLeafProfileKernelVisibleIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB.1 XC.1)
        *
      bitSign
        (qLeafProfileKernelRemainderIndexDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC) := by
  rw [qLeafProfileKernelIndexDiff_eq_visible_add_remainder
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB XC]
  rw [bitSign_add]

end

end TriangleLeaf
end Core4loop
