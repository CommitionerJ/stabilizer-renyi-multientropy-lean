import Core4loop.TriangleLeaf.BReadTarget

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem sum_leafBReadTarget_bitSign_phase_add_dot_eq_card_if_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (q : F) (X Y : LeafBReadTarget n a b c d hd) :
    (∑ U : LeafBReadTarget n a b c d hd,
        bitSign (q + leafBReadTargetDot hd U (X + Y))) =
      (if X = Y then (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) else 0)
        * bitSign q := by
  classical
  calc
    (∑ U : LeafBReadTarget n a b c d hd,
        bitSign (q + leafBReadTargetDot hd U (X + Y)))
        =
      ∑ U : LeafBReadTarget n a b c d hd,
        bitSign q * bitSign (leafBReadTargetDot hd U (X + Y)) := by
          refine Finset.sum_congr rfl ?_
          intro U _
          rw [bitSign_add]
    _ =
      bitSign q *
        (∑ U : LeafBReadTarget n a b c d hd,
          bitSign (leafBReadTargetDot hd U (X + Y))) := by
          rw [Finset.mul_sum]
    _ =
      bitSign q *
        (if X = Y then
          (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        else 0) := by
          rw [sum_leafBReadTargetDot_eq_card_if_eq hd X Y]
    _ =
      (if X = Y then
          (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
        else 0) * bitSign q := by
          ring

private theorem leafBReadFiber_scaled_fourier_expansion_one
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) *
      leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    =
      ∑ U : LeafBReadTarget n a b c d hd,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          bitSign
            (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H
              +
              leafBReadTargetDot hd U
                (qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    (0 : LeafVisibleKernel n b c d) XB
                  +
                  qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)) := by
  classical
  let C : ℤ := (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
  calc
    C *
      leafBReadFiberSignValue
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        =
      C *
        (∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          if qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                (0 : LeafVisibleKernel n b c d) XB
              =
              qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
            bitSign
              (qLeafProfileKernelTotalCvConstLinearMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                +
                qLeafProfileKernelTotalCvVisibleConst
                  (n := n) (b := b) (c := c) (d := d) hd H)
          else 0) := by
          rw [← leafCompatibleResidualXBInnerSum_eq_fiberSignValue
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
          rfl
    _ =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        C *
          (if qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd
                (0 : LeafVisibleKernel n b c d) XB
              =
              qLeafProfileKernelTotalBCoeffRead
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0 then
            bitSign
              (qLeafProfileKernelTotalCvConstLinearMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                +
                qLeafProfileKernelTotalCvVisibleConst
                  (n := n) (b := b) (c := c) (d := d) hd H)
          else 0) := by
          congr 1
          rw [← Finset.mul_sum]
    _ =
      ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
        ∑ U : LeafBReadTarget n a b c d hd,
          bitSign
            (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H
              +
              leafBReadTargetDot hd U
                (qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    (0 : LeafVisibleKernel n b c d) XB
                  +
                  qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)) := by
          refine Finset.sum_congr rfl ?_
          intro XB _
          let q : F :=
            qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H
          let X : LeafBReadTarget n a b c d hd :=
            qLeafProfileKernelTotalBCoeffRead
              (n := n) (a := a) (b := b) (c := c) (d := d) hd
              (0 : LeafVisibleKernel n b c d) XB
          let Y : LeafBReadTarget n a b c d hd :=
            qLeafProfileKernelTotalBCoeffRead
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0
          have hsum :=
            sum_leafBReadTarget_bitSign_phase_add_dot_eq_card_if_eq
              (n := n) (a := a) (b := b) (c := c) (d := d) hd q X Y
          change
            C * (if X = Y then bitSign q else 0)
              =
            ∑ U : LeafBReadTarget n a b c d hd,
              bitSign (q + leafBReadTargetDot hd U (X + Y))
          rw [hsum]
          by_cases hXY : X = Y
          · simp [C, hXY]
          · simp [C, hXY]
    _ =
      ∑ U : LeafBReadTarget n a b c d hd,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          bitSign
            (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H
              +
              leafBReadTargetDot hd U
                (qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    (0 : LeafVisibleKernel n b c d) XB
                  +
                  qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)) := by
          rw [Finset.sum_comm]

theorem leafBReadFiber_scaled_fourier_expansion
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) *
      (∑ H : LeafVisibleKernel n b c d,
        leafBReadFiberSignValue
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
  =
    ∑ H : LeafVisibleKernel n b c d,
      ∑ U : LeafBReadTarget n a b c d hd,
        ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
          bitSign
            (qLeafProfileKernelTotalCvConstLinearMap
                (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
              +
              qLeafProfileKernelTotalCvVisibleConst
                (n := n) (b := b) (c := c) (d := d) hd H
              +
              leafBReadTargetDot hd U
                (qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd
                    (0 : LeafVisibleKernel n b c d) XB
                  +
                  qLeafProfileKernelTotalBCoeffRead
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)) := by
  classical
  let C : ℤ := (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
  calc
    C *
      (∑ H : LeafVisibleKernel n b c d,
        leafBReadFiberSignValue
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        =
      ∑ H : LeafVisibleKernel n b c d,
        C *
          leafBReadFiberSignValue
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
          rw [← Finset.mul_sum]
    _ =
      ∑ H : LeafVisibleKernel n b c d,
        ∑ U : LeafBReadTarget n a b c d hd,
          ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
            bitSign
              (qLeafProfileKernelTotalCvConstLinearMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                +
                qLeafProfileKernelTotalCvVisibleConst
                  (n := n) (b := b) (c := c) (d := d) hd H
                +
                leafBReadTargetDot hd U
                  (qLeafProfileKernelTotalBCoeffRead
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      (0 : LeafVisibleKernel n b c d) XB
                    +
                    qLeafProfileKernelTotalBCoeffRead
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0)) := by
          refine Finset.sum_congr rfl ?_
          intro H _
          exact leafBReadFiber_scaled_fourier_expansion_one
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H

theorem leafBReadFiber_scaled_fourier_expansion_with_k
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
              (qLeafProfileKernelTotalCvConstLinearMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                +
                qLeafProfileKernelTotalCvVisibleConst
                  (n := n) (b := b) (c := c) (d := d) hd H
                +
                leafBReadTargetDot hd U
                  (qLeafProfileKernelTotalBCoeffRead
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd
                      (0 : LeafVisibleKernel n b c d) XB
                    +
                    qLeafProfileKernelTotalBCoeffRead
                      (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0))) := by
  classical
  let C : ℤ := (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ)
  let K : ℤ := (2 : ℤ) ^ kCdCvElimExpNat n a b d
  calc
    C *
      (∑ H : LeafVisibleKernel n b c d,
        K *
          leafBReadFiberSignValue
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        =
      C *
        (K *
          (∑ H : LeafVisibleKernel n b c d,
            leafBReadFiberSignValue
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H)) := by
          exact congrArg (fun z : ℤ => C * z)
            ((Finset.mul_sum
              (s := (Finset.univ : Finset (LeafVisibleKernel n b c d)))
              (f := fun H : LeafVisibleKernel n b c d =>
                leafBReadFiberSignValue
                  (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
              K).symm)
    _ =
      K *
        (C *
          (∑ H : LeafVisibleKernel n b c d,
            leafBReadFiberSignValue
              (n := n) (a := a) (b := b) (c := c) (d := d) hd H)) := by
          ring
    _ =
      K *
        (∑ H : LeafVisibleKernel n b c d,
          ∑ U : LeafBReadTarget n a b c d hd,
            ∑ XB : LeafBProfileKernelIndexDiffCoord n a c d hd,
              bitSign
                (qLeafProfileKernelTotalCvConstLinearMap
                    (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
                  +
                  qLeafProfileKernelTotalCvVisibleConst
                    (n := n) (b := b) (c := c) (d := d) hd H
                  +
                  leafBReadTargetDot hd U
                    (qLeafProfileKernelTotalBCoeffRead
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd
                        (0 : LeafVisibleKernel n b c d) XB
                      +
                      qLeafProfileKernelTotalBCoeffRead
                        (n := n) (a := a) (b := b) (c := c) (d := d) hd H 0))) := by
          rw [leafBReadFiber_scaled_fourier_expansion
            (n := n) (a := a) (b := b) (c := c) (d := d) hd]

end

end TriangleLeaf
end Core4loop
