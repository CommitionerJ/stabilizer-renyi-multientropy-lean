import Core4loop.TriangleLeaf.BReadVisiblePhase
import Core4loop.TriangleLeaf.BReadOddClosed

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafBReadTraceData
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    PassiveVisibleIndex n d hd → LeafScalarEvenBlockData n b c :=
  fun ω =>
    leafBReadEvenBlockDataOfTraces
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB ω

theorem leafBReadFiber_scaled_fourier_expansion_with_k_tail_raw
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) *
      (∑ H : LeafVisibleKernel n b c d,
        (2 : ℤ) ^ kCdCvElimExpNat n a b d *
          leafBReadFiberSignValue
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
  =
    (2 : ℤ) ^ kCdCvElimExpNat n a b d *
      (∑ H : LeafVisibleKernel n b c d,
        ∑ U : LeafBReadTarget n a b c d hd,
          ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
            bitSign
              (leafBReadFourierTailPhase
                (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB)
              *
            leafEvenRawBlockProductSign
              (n := n) (b := b) (c := c) (d := d) hd
              (leafBReadTraceData
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB)) := by
  rw [leafBReadFiber_scaled_fourier_expansion_with_k
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro H _
  refine Finset.sum_congr rfl ?_
  intro U _
  refine Finset.sum_congr rfl ?_
  intro XB _
  simpa [leafBReadTraceData] using
    bRead_fourier_phase_eq_tail_mul_rawEvenBlockProductSign
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB

end

end TriangleLeaf
end Core4loop
