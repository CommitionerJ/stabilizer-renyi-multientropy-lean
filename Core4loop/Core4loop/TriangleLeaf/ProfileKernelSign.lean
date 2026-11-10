import Core4loop.TriangleLeaf.ProfileKernelBase

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev leafVisibleBKernelPart {n a c d : ℕ} [NeZero n]
    (kB : I n → ZVec n c → LeafProfileKernel n a d) : BFun4 n a c d :=
  leafBVisKernelOfCoord (n := n) (a := a) (c := c) (d := d) kB

abbrev leafVisibleCKernelPart {n a b d : ℕ} [NeZero n]
    (kC : YVec n b → I n → LeafProfileKernel n a d) : CFun4 n a b d :=
  leafCVisKernelOfCoord (n := n) (a := a) (b := b) (d := d) kC

abbrev leafVisibleBBase {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) : BFun4 n a c d :=
  leafBVisBase (n := n) (a := a) (c := c) (d := d) H.1.1

abbrev leafVisibleCBase {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) : CFun4 n a b d :=
  leafCVisBase (n := n) (a := a) (b := b) (d := d) H.1.2

theorem leafVisibleProfileKernelSign_eq_bitSign_qLeafProfile_expanded
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafVisibleProfileKernelSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC
      =
      bitSign
        (qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
            (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC)
          + qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
            (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
          + qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
            (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC)
          + qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
            (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H)) := by
  unfold leafVisibleProfileKernelSign
  rw [leafBVisFiberCoord_symm_val, leafCVisFiberCoord_symm_val]
  rw [Q1_eq_qLeafProfile]
  rw [qLeafProfile_add_add]

theorem leafVisibleProfileKernelSign_eq_bitSign_product
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafVisibleProfileKernelSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC
      =
      bitSign
        (qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
          (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC))
      * bitSign
        (qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
          (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))
      * bitSign
        (qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
          (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC))
      * bitSign
        (qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
          (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H)) := by
  rw [leafVisibleProfileKernelSign_eq_bitSign_qLeafProfile_expanded
    (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC]
  repeat rw [bitSign_add]

end

end TriangleLeaf
end Core4loop
