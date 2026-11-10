import Core4loop.TriangleLeaf.CanonicalProfileKernelSign

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafVisibleCanonicalProfileKernelInteractionSum
    (n a b c d : ℕ) [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : ℤ :=
  ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
    ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
      leafVisibleCanonicalProfileKernelInteractionSign
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC

theorem leafCompatibleResidualSum_eq_canonicalBaseWeightedInteractionSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        leafVisibleCanonicalProfileKernelInteractionSum n a b c d hd H *
          leafVisibleCanonicalBaseSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  rw [leafCompatibleResidualSum_eq_canonicalProfileKernelCoordSum
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  refine Finset.sum_congr rfl ?_
  intro H _
  calc
    (∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
      ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
        leafVisibleCanonicalProfileKernelSign
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC)
      =
      ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
        ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
          leafVisibleCanonicalProfileKernelInteractionSign
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC
            * leafVisibleCanonicalBaseSign
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
        refine Finset.sum_congr rfl ?_
        intro kB _
        refine Finset.sum_congr rfl ?_
        intro kC _
        rw [leafVisibleCanonicalProfileKernelSign_eq_interaction_mul_base]
    _ =
      leafVisibleCanonicalProfileKernelInteractionSum n a b c d hd H *
        leafVisibleCanonicalBaseSign
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
        simp_rw [← Finset.sum_mul]
        rfl

end

end TriangleLeaf
end Core4loop
