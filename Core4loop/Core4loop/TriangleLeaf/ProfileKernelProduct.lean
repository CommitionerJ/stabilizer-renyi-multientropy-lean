import Core4loop.TriangleLeaf.ProfileKernelSign

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafVisibleProfileKernelProductSign
    {n a b c d : ℕ} [NeZero n]
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
      (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))

theorem leafVisibleProfileKernelSign_eq_productSign
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafVisibleProfileKernelSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC
      =
      leafVisibleProfileKernelProductSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC := by
  rw [leafVisibleProfileKernelSign_eq_bitSign_product]
  rfl

theorem leafCompatibleResidualSum_eq_profileKernelProductSignSum
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
          ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
            leafVisibleProfileKernelProductSign
              (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC := by
  rw [leafCompatibleResidualSum_eq_profileKernelCoordSum]
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro kB _
  refine Finset.sum_congr rfl ?_
  intro kC _
  rw [leafVisibleProfileKernelSign_eq_productSign]

end

end TriangleLeaf
end Core4loop
