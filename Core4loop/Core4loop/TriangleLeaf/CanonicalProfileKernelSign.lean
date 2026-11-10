import Core4loop.TriangleLeaf.CanonicalProfileKernelSum
import Core4loop.TriangleLeaf.ProfileKernelSign

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev leafVisibleBCanonicalBase
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : BFun4 n a c d :=
  leafBVisCanonicalBase (n := n) (a := a) (c := c) (d := d) hd H.1.1

abbrev leafVisibleCCanonicalBase
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : CFun4 n a b d :=
  leafCVisCanonicalBase (n := n) (a := a) (b := b) (d := d) hd H.1.2

theorem leafVisibleCanonicalProfileKernelSign_eq_bitSign_qLeafProfile_expanded
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafVisibleCanonicalProfileKernelSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC
      =
      bitSign
        (qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
            (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC)
          + qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
            (leafVisibleCCanonicalBase
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          + qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBCanonicalBase
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
            (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC)
          + qLeafProfile
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (leafVisibleBCanonicalBase
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
            (leafVisibleCCanonicalBase
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H)) := by
  unfold leafVisibleCanonicalProfileKernelSign
  rw [leafBVisCanonicalFiberCoord_symm_val,
    leafCVisCanonicalFiberCoord_symm_val]
  rw [Q1_eq_qLeafProfile]
  rw [qLeafProfile_add_add]

theorem leafVisibleCanonicalProfileKernelSign_eq_bitSign_product
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafVisibleCanonicalProfileKernelSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC
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
          (leafVisibleCCanonicalBase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H))
      * bitSign
        (qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (leafVisibleBCanonicalBase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC))
      * bitSign
        (qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (leafVisibleBCanonicalBase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          (leafVisibleCCanonicalBase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)) := by
  rw [leafVisibleCanonicalProfileKernelSign_eq_bitSign_qLeafProfile_expanded
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC]
  repeat rw [bitSign_add]

def leafVisibleCanonicalBaseSign
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : ℤ :=
  bitSign
    (qLeafProfile
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      (leafVisibleCCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H))

def leafVisibleCanonicalProfileKernelInteractionSign
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) : ℤ :=
  bitSign
    (qLeafProfile
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
      (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC))
  * bitSign
    (qLeafProfile
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB)
      (leafVisibleCCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H))
  * bitSign
    (qLeafProfile
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC))

theorem leafVisibleCanonicalProfileKernelSign_eq_interaction_mul_base
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafVisibleCanonicalProfileKernelSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC
      =
      leafVisibleCanonicalProfileKernelInteractionSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC
        *
      leafVisibleCanonicalBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  rw [leafVisibleCanonicalProfileKernelSign_eq_bitSign_product]
  rfl

end

end TriangleLeaf
end Core4loop
