import Core4loop.TriangleLeaf.ProfileKernelProduct

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafVisibleBaseSign
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) : ℤ :=
  bitSign
    (qLeafProfile
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
      (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))

def leafVisibleProfileKernelInteractionSign
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

theorem leafVisibleProfileKernelProductSign_eq_interaction_mul_base
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafVisibleProfileKernelProductSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC
      =
      leafVisibleProfileKernelInteractionSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC
        *
      leafVisibleBaseSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H := by
  rfl

def leafVisibleProfileKernelInteractionSum
    (n a b c d : ℕ) [NeZero n]
    (H : LeafVisibleKernel n b c d) : ℤ :=
  ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
    ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
      leafVisibleProfileKernelInteractionSign
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC

theorem leafCompatibleResidualSum_eq_baseWeightedInteractionSum
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        leafVisibleProfileKernelInteractionSum n a b c d H *
          leafVisibleBaseSign
            (n := n) (a := a) (b := b) (c := c) (d := d) H := by
  rw [leafCompatibleResidualSum_eq_profileKernelProductSignSum]
  refine Finset.sum_congr rfl ?_
  intro H _
  calc
    (∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
      ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
        leafVisibleProfileKernelProductSign
          (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC)
      =
      ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
        ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
          leafVisibleProfileKernelInteractionSign
            (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC
            * leafVisibleBaseSign
              (n := n) (a := a) (b := b) (c := c) (d := d) H := by
        refine Finset.sum_congr rfl ?_
        intro kB _
        refine Finset.sum_congr rfl ?_
        intro kC _
        rw [leafVisibleProfileKernelProductSign_eq_interaction_mul_base]
    _ =
      leafVisibleProfileKernelInteractionSum n a b c d H *
        leafVisibleBaseSign
          (n := n) (a := a) (b := b) (c := c) (d := d) H := by
        simp_rw [← Finset.sum_mul]
        rfl

end

end TriangleLeaf
end Core4loop
