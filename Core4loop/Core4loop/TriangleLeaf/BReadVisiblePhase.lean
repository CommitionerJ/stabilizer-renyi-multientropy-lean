import Core4loop.TriangleLeaf.BReadDualReduction
import Core4loop.TriangleLeaf.EvenRawBlock

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private lemma prod_bitSign_eq_bitSign_sum {α : Type*} (s : Finset α)
    (f : α → F) :
    s.prod (fun a => bitSign (f a)) = bitSign (s.sum f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bitSign_zero]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, bitSign_add, ih]

private lemma sum_three_right_swap {α : Type*} [Fintype α]
    (f g h : α → F) :
    Finset.univ.sum f + Finset.univ.sum g + Finset.univ.sum h
      =
    Finset.univ.sum (fun x : α => (f x) + (h x) + (g x)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ac_rfl

theorem bRead_visible_phase_eq_rawEvenBlockProductSign
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    bitSign
      (qLeafProfileKernelTotalCvVisibleConst
          (n := n) (b := b) (c := c) (d := d) hd H
        + qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
        + leafBReadTargetDot hd U
          (qLeafProfileKernelTotalBCoeffRead
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H
            (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)))
      =
    leafEvenRawBlockProductSign
      (n := n) (b := b) (c := c) (d := d) hd
      (fun ω =>
        leafBReadEvenBlockDataOfTraces
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB ω) := by
  rw [qLeafProfileKernelTotalCvConstLinearMap_eq_scalarBTrace_visibleC
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB]
  rw [leafBReadTargetDot_target_eq_scalarCTrace_visibleB
    (n := n) (a := a) (b := b) (c := c) (d := d) hd U H]
  unfold qLeafProfileKernelTotalCvVisibleConst
    leafEvenRawBlockProductSign
    leafScalarEvenRawBlockSign
    leafScalarEvenRawVisibleKernelSign
    leafBReadEvenBlockDataOfTraces
  rw [prod_bitSign_eq_bitSign_sum]
  congr 1
  exact sum_three_right_swap
    (α := PassiveVisibleIndex n d hd)
    (fun ω =>
      Core3loop.qScalar (b := b) (c := c) (n := n)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)
    (fun ω =>
      Core3loop.qScalar (b := b) (c := c) (n := n)
        (leafBReadKernelScalarBTrace
          (n := n) (a := a) (c := c) (d := d) hd XB ω)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2)
    (fun ω =>
      Core3loop.qScalar (b := b) (c := c) (n := n)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
        (leafBReadDualScalarCTrace
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω))

def leafBReadFourierTailPhase
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : F :=
  leafBReadTargetDot hd U
    (qLeafProfileKernelTotalBCoeffRead
      (n := n) (a := a) (b := b) (c := c) (d := d) hd
      (0 : LeafVisibleKernel n b c d) XB)

theorem bRead_fourier_phase_eq_tail_mul_rawEvenBlockProductSign
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    bitSign
      (qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
        + qLeafProfileKernelTotalCvVisibleConst
          (n := n) (b := b) (c := c) (d := d) hd H
        + leafBReadTargetDot hd U
          (qLeafProfileKernelTotalBCoeffRead
              (n := n) (a := a) (b := b) (c := c) (d := d) hd
              (0 : LeafVisibleKernel n b c d) XB
            + qLeafProfileKernelTotalBCoeffRead
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0))
      =
    bitSign
      (leafBReadFourierTailPhase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB)
      *
    leafEvenRawBlockProductSign
      (n := n) (b := b) (c := c) (d := d) hd
      (fun ω =>
        leafBReadEvenBlockDataOfTraces
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB ω) := by
  rw [leafBReadTargetDot_add_right
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  unfold leafBReadFourierTailPhase
  rw [show
      qLeafProfileKernelTotalCvConstLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
        + qLeafProfileKernelTotalCvVisibleConst
          (n := n) (b := b) (c := c) (d := d) hd H
        +
          (leafBReadTargetDot hd U
              (qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                (0 : LeafVisibleKernel n b c d) XB)
            +
            leafBReadTargetDot hd U
              (qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)))
        =
          leafBReadTargetDot hd U
              (qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                (0 : LeafVisibleKernel n b c d) XB)
        +
          (qLeafProfileKernelTotalCvVisibleConst
              (n := n) (b := b) (c := c) (d := d) hd H
            + qLeafProfileKernelTotalCvConstLinearMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
            + leafBReadTargetDot hd U
              (qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H
                (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))) by
      ac_rfl]
  rw [bitSign_add]
  rw [bRead_visible_phase_eq_rawEvenBlockProductSign
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB]

end

end TriangleLeaf
end Core4loop
