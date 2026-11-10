import Core4loop.TriangleLeaf.ProfileBilinear

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafVisibleProfileKernelSign
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) : ℤ :=
  bitSign
    (Q1
      ((leafBVisFiberEquivProfileKernelCoord
        (n := n) (a := a) (c := c) (d := d) H.1.1).symm kB).1
      ((leafCVisFiberEquivProfileKernelCoord
        (n := n) (a := a) (b := b) (d := d) H.1.2).symm kC).1)

theorem leafVisibleSigmaSignSum_eq_profileKernelCoordSum
    {n a b c d : ℕ} [NeZero n] :
    leafVisibleSigmaSignSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
          ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
            leafVisibleProfileKernelSign
              (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC := by
  classical
  unfold leafVisibleSigmaSignSum
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro H _
  unfold LeafVisibleFiberPair leafVisibleProfileKernelSign
  rw [Fintype.sum_prod_type]
  let eB :=
    leafBVisFiberEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d) H.1.1
  let eC :=
    leafCVisFiberEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d) H.1.2
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

theorem leafCompatibleResidualSum_eq_profileKernelCoordSum
    {n a b c d : ℕ} [NeZero n] :
    leafCompatibleResidualSum n a b c d =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ kB : I n → ZVec n c → LeafProfileKernel n a d,
          ∑ kC : YVec n b → I n → LeafProfileKernel n a d,
            leafVisibleProfileKernelSign
              (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC := by
  rw [leafCompatibleResidualSum_eq_visibleSigmaSignSum,
    leafVisibleSigmaSignSum_eq_profileKernelCoordSum]

end

end TriangleLeaf
end Core4loop
