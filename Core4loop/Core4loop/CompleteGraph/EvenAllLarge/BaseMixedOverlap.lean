import Core4loop.CompleteGraph.EvenAllLarge.AggregateRadicalCoordinates

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

noncomputable abbrev K4BaseMixedOverlapSource
    (n b c d : Nat) [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :=
  K4AggregateKernel n b c d hn hb2 hc2 hd2 ×
    K4AggregatePolarCoordinateTarget n c

noncomputable def k4GPolarKernelMixedOverlapEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4GPolarKernel n b c d ≃ₗ[F]
      K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 :=
  (k4GPolarKernelAggregateSplit hn hb2 hc2 hd2).trans
    ((LinearEquiv.refl F
        (K4AggregateKernel n b c d hn hb2 hc2 hd2)).prodCongr
      (k4AggregatePolarKernelCoordinateEquiv hn2 hn hc2))

noncomputable def k4GPolarKernelMixedOverlapRead
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4GPolarKernel n b c d →ₗ[F]
      K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 :=
  (k4GPolarKernelMixedOverlapEquiv hn2 hn hb2 hc2 hd2).toLinearMap

noncomputable def k4GPolarKernelMixedOverlapBuild
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 →ₗ[F]
      K4GPolarKernel n b c d :=
  (k4GPolarKernelMixedOverlapEquiv hn2 hn hb2 hc2 hd2).symm.toLinearMap

@[simp] theorem k4GPolarKernelMixedOverlapRead_build
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2) :
    k4GPolarKernelMixedOverlapRead hn2 hn hb2 hc2 hd2
        (k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2 z) = z :=
  (k4GPolarKernelMixedOverlapEquiv
    hn2 hn hb2 hc2 hd2).apply_symm_apply z

@[simp] theorem k4GPolarKernelMixedOverlapBuild_read
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4GPolarKernel n b c d) :
    k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2
        (k4GPolarKernelMixedOverlapRead hn2 hn hb2 hc2 hd2 sigma) =
      sigma :=
  (k4GPolarKernelMixedOverlapEquiv
    hn2 hn hb2 hc2 hd2).symm_apply_apply sigma

noncomputable def k4BaseDescendedMixedOverlapCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (k4BaseDescendedCross (n := n) (b := b) (c := c) (d := d)).comp
    (k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2)

noncomputable def k4BaseDescendedAggregateKernelCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregateKernel n b c d hn hb2 hc2 hd2 →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2).comp
    (LinearMap.inl F
      (K4AggregateKernel n b c d hn hb2 hc2 hd2)
      (K4AggregatePolarCoordinateTarget n c))

noncomputable def k4BaseDescendedAggregatePolarCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4AggregatePolarCoordinateTarget n c →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2).comp
    (LinearMap.inr F
      (K4AggregateKernel n b c d hn hb2 hc2 hd2)
      (K4AggregatePolarCoordinateTarget n c))

theorem k4GPolarKernelMixedOverlapBuild_val
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2) :
    (k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2 z).1 =
      z.1.1 +
        k4AggregateLift (by omega) (by omega) (by omega)
          (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2).1 := by
  rfl

theorem k4BaseDescendedMixedOverlapCross_projection
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2)
    (r : K4EvenPBaseRight n b c d) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2 z
        (k4BaseRightToDiamondReachable r) =
      k4EvenPBaseCross
        (k4GPolarKernelMixedOverlapBuild
          hn2 hn hb2 hc2 hd2 z).1 r := by
  exact k4BaseDescendedCross_projection
    (k4GPolarKernelMixedOverlapBuild hn2 hn hb2 hc2 hd2 z) r

theorem k4BaseDescendedMixedOverlapCross_literal
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (z : K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2)
    (r : K4EvenPBaseRight n b c d) :
    let sigma : K4EvenPLeft n b c d :=
      z.1.1 +
        k4AggregateLift (by omega) (by omega) (by omega)
          (k4AggregatePolarKernelCoordinateBuild hn2 hn hc2 z.2).1
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2 z
        (k4BaseRightToDiamondReachable r) =
      coeffApplyA
          (KBMap sigma.1.1 + KWMap sigma.1.2) r.1.1 +
        k4EvenPSlicePolar sigma.1 r.1.2 := by
  rw [k4BaseDescendedMixedOverlapCross_projection]
  rfl

set_option synthInstance.maxHeartbeats 2000000 in
-- Unfolding the nested aggregate-kernel subtype during the two product
-- injections exceeds the default instance-search budget deterministically.
theorem k4BaseDescendedMixedOverlapCross_add
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (k : K4AggregateKernel n b c d hn hb2 hc2 hd2)
    (x : K4AggregatePolarCoordinateTarget n c) :
    k4BaseDescendedMixedOverlapCross hn2 hn hb2 hc2 hd2 (k, x) =
      k4BaseDescendedAggregateKernelCross
          hn2 hn hb2 hc2 hd2 k +
        k4BaseDescendedAggregatePolarCross
          hn2 hn hb2 hc2 hd2 x := by
  have h :=
    (k4BaseDescendedMixedOverlapCross
      hn2 hn hb2 hc2 hd2).map_add (k, 0) (0, x)
  simpa [k4BaseDescendedAggregateKernelCross,
    k4BaseDescendedAggregatePolarCross] using h

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
