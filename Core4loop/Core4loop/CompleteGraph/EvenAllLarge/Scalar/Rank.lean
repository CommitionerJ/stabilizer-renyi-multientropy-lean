import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Rank.SourceRank

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

theorem finrank_K4ScalarLeftKernel_add
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (K4ScalarLeftKernel hn2 hn hb2 hc2 hd2) + 5 * n =
      2 * n ^ 3 + 5 * n ^ 2 + 6 := by
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (scalarMultiplierProjection hn2 hn hb2 hc2 hd2)
  rw [range_scalarMultiplierProjection_eq_leftKernel,
    ker_scalarMultiplierProjection_eq_gauge,
    finrank_K4ScalarMultiplierGauge] at hnull
  have hsol := finrank_K4ScalarMultiplierSolution_add
    hn2 hn hb2 hc2 hd2
  ring_nf at hnull hsol ⊢
  omega

theorem finrank_K4ScalarLeftKernel
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (K4ScalarLeftKernel hn2 hn hb2 hc2 hd2) =
      2 * n ^ 3 + 5 * n ^ 2 - 5 * n + 6 := by
  have hadd := finrank_K4ScalarLeftKernel_add
    hn2 hn hb2 hc2 hd2
  have hbound : 5 * n ≤ 2 * n ^ 3 + 5 * n ^ 2 := by
    nlinarith
  omega

theorem rank_localScalarCross_addition_safe
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
          (LinearMap.range
            (localScalarCross hn2 hn hb2 hc2 hd2)) +
        4 * n * (n - 1) =
      (n - 1) * (3 * n ^ 2 + 6) := by
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (localScalarCross hn2 hn hb2 hc2 hd2)
  change
    Module.finrank F
          (LinearMap.range
            (localScalarCross hn2 hn hb2 hc2 hd2)) +
        Module.finrank F
          (K4ScalarLeftKernel hn2 hn hb2 hc2 hd2) =
      Module.finrank F (K4BaseMixedScalarSector n) at hnull
  have hsource := finrank_K4BaseMixedScalarSector_add (n := n)
  have hleft := finrank_K4ScalarLeftKernel_add
    hn2 hn hb2 hc2 hd2
  have hpoly :
      (5 * n ^ 3 + 5 * n) + 4 * n * (n - 1) + 5 * n =
        (2 * n ^ 3 + 5 * n ^ 2 + 6) +
          (n - 1) * (3 * n ^ 2 + 6) + 2 * n ^ 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  omega

theorem rank_localScalarCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (localScalarCross hn2 hn hb2 hc2 hd2)) =
      (n - 1) * (3 * n ^ 2 - 4 * n + 6) := by
  have hadd := rank_localScalarCross_addition_safe
    hn2 hn hb2 hc2 hd2
  have hbound : 4 * n ≤ 3 * n ^ 2 := by
    nlinarith
  have hinner :
      (3 * n ^ 2 - 4 * n + 6) + 4 * n =
        3 * n ^ 2 + 6 := by
    omega
  have hpoly :
      (n - 1) * (3 * n ^ 2 - 4 * n + 6) +
          4 * n * (n - 1) =
        (n - 1) * (3 * n ^ 2 + 6) := by
    calc
      _ = (n - 1) *
          ((3 * n ^ 2 - 4 * n + 6) + 4 * n) := by ring
      _ = (n - 1) * (3 * n ^ 2 + 6) := by rw [hinner]
  omega

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
