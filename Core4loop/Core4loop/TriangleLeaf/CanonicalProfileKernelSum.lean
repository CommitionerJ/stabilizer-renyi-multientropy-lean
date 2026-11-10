import Core4loop.TriangleLeaf.CanonicalProfileKernelBase

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafVisibleCanonicalProfileKernelSign
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) : ℤ :=
  bitSign
    (Q1
      ((leafBVisCanonicalFiberEquivProfileKernelCoord
        (n := n) (a := a) (c := c) (d := d) hd H.1.1).symm kB).1
      ((leafCVisCanonicalFiberEquivProfileKernelCoord
        (n := n) (a := a) (b := b) (d := d) hd H.1.2).symm kC).1)

theorem leafVisibleSigmaSignSum_eq_canonicalProfileKernelCoordSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafVisibleSigmaSignSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
          ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
            leafVisibleCanonicalProfileKernelSign
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC := by
  classical
  unfold leafVisibleSigmaSignSum
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro H _
  unfold LeafVisibleFiberPair leafVisibleCanonicalProfileKernelSign
  rw [Fintype.sum_prod_type]
  let eB :=
    leafBVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d) hd H.1.1
  let eC :=
    leafCVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d) hd H.1.2
  calc
    (∑ x : LeafBVisFiber (n := n) (a := a) (c := c) (d := d) H.1.1,
        ∑ x_1 : LeafCVisFiber (n := n) (a := a) (b := b) (d := d) H.1.2,
          bitSign (Q1 x.1 x_1.1))
      =
        ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
          ∑ x_1 : LeafCVisFiber (n := n) (a := a) (b := b) (d := d) H.1.2,
            bitSign (Q1 ((eB.symm kB).1) x_1.1) := by
          simpa [eB] using
            (Equiv.sum_comp eB
              (fun kB : I n → ZVec n c → LeafProfileKernel n a d =>
                ∑ x_1 :
                    LeafCVisFiber (n := n) (a := a) (b := b) (d := d) H.1.2,
                  bitSign (Q1 ((eB.symm kB).1) x_1.1)))
    _ =
        ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
          ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
            bitSign (Q1 ((eB.symm kB).1) ((eC.symm kC).1)) := by
          refine Finset.sum_congr rfl ?_
          intro kB _
          simpa [eC] using
            (Equiv.sum_comp eC
              (fun kC : YVec n b → I n → LeafProfileKernel n a d =>
                bitSign (Q1 ((eB.symm kB).1) ((eC.symm kC).1))))

theorem leafCompatibleResidualSum_eq_canonicalProfileKernelCoordSum
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
          ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
            leafVisibleCanonicalProfileKernelSign
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H kB kC := by
  rw [leafCompatibleResidualSum_eq_visibleSigmaSignSum,
    leafVisibleSigmaSignSum_eq_canonicalProfileKernelCoordSum
      (n := n) (a := a) (b := b) (c := c) (d := d) hd]

end

end TriangleLeaf
end Core4loop
