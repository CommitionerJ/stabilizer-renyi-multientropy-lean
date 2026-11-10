import Core4loop.CompleteGraph.EvenAllLarge.BaseRadicalDescent

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.CompleteGraph.EvenP

noncomputable section

private theorem module_add_self
    {V : Type*} [AddCommGroup V] [Module F V] (x : V) :
    x + x = 0 := by
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + 1) • x := (add_smul (1 : F) 1 x).symm
    _ = 0 := by rw [F_add_self, zero_smul]

set_option maxHeartbeats 2000000 in
-- Elaborating the formula-defined aggregate map unfolds the four finite source
-- blocks while synthesizing their module instance; the default budget expires
-- before that deterministic instance search finishes.
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 512 in
noncomputable abbrev K4AggregateKernel
    (n b c d : Nat) [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :=
  LinearMap.ker (k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2)

noncomputable abbrev K4AggregatePolarKernel
    (n c : Nat) [NeZero n] :=
  LinearMap.ker (k4AggregateHyperbolicPolar (n := n) (c := c))

set_option maxHeartbeats 2000000 in
-- The residual map contains the same unfolded four-block aggregate and lift;
-- its linearity fields need the corresponding deterministic instance budget.
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 512 in
noncomputable def k4AggregateResidual
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4EvenPLeft n b c d →ₗ[F]
      K4AggregateKernel n b c d hn hb2 hc2 hd2 where
  toFun sigma :=
    ⟨sigma +
        k4AggregateLift (by omega) (by omega) (by omega)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma), by
      apply LinearMap.mem_ker.mpr
      rw [map_add, k4EvenPAggregate_lift]
      exact module_add_self _⟩
  map_add' sigma tau := by
    apply Subtype.ext
    change
      (sigma + tau) +
          k4AggregateLift (by omega) (by omega) (by omega)
            (k4EvenPAggregate hn hb2 (by omega) hd2 (sigma + tau)) =
        (sigma +
            k4AggregateLift (by omega) (by omega) (by omega)
              (k4EvenPAggregate hn hb2 (by omega) hd2 sigma)) +
          (tau +
            k4AggregateLift (by omega) (by omega) (by omega)
              (k4EvenPAggregate hn hb2 (by omega) hd2 tau))
    rw [map_add, map_add]
    abel
  map_smul' r sigma := by
    apply Subtype.ext
    change
      r • sigma +
          k4AggregateLift (by omega) (by omega) (by omega)
            (k4EvenPAggregate hn hb2 (by omega) hd2 (r • sigma)) =
        r • (sigma +
          k4AggregateLift (by omega) (by omega) (by omega)
            (k4EvenPAggregate hn hb2 (by omega) hd2 sigma))
    rw [map_smul, map_smul, smul_add]

set_option maxHeartbeats 2000000 in
-- Constructing the explicit product equivalence repeatedly normalizes the
-- aggregate module structures, which exceeds Lean's default local budgets.
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 512 in
noncomputable def k4AggregateSplit
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4EvenPLeft n b c d ≃ₗ[F]
      (K4AggregateKernel n b c d hn hb2 hc2 hd2 ×
        (K4BAggregateLeft n c × K4WAggregateLeft n c)) where
  toFun sigma :=
    (k4AggregateResidual hn hb2 hc2 hd2 sigma,
      k4EvenPAggregate hn hb2 (by omega) hd2 sigma)
  invFun z :=
    z.1.1 + k4AggregateLift (by omega) (by omega) (by omega) z.2
  left_inv sigma := by
    change
      (sigma + k4AggregateLift (by omega) (by omega) (by omega)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma)) +
        k4AggregateLift (by omega) (by omega) (by omega)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma) = sigma
    rw [add_assoc, module_add_self, add_zero]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change
        z.1.1 + k4AggregateLift (by omega) (by omega) (by omega) z.2 +
            k4AggregateLift (by omega) (by omega) (by omega)
              (k4EvenPAggregate hn hb2 (by omega) hd2
                (z.1.1 +
                  k4AggregateLift (by omega) (by omega) (by omega) z.2)) =
          z.1.1
      rw [map_add, LinearMap.mem_ker.mp z.1.2,
        k4EvenPAggregate_lift, zero_add]
      rw [add_assoc, module_add_self, add_zero]
    · change
        k4EvenPAggregate hn hb2 (by omega) hd2
            (z.1.1 + k4AggregateLift (by omega) (by omega) (by omega) z.2) =
          z.2
      rw [map_add, LinearMap.mem_ker.mp z.1.2,
        k4EvenPAggregate_lift, zero_add]
  map_add' sigma tau := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add]
      abel
    · exact map_add _ sigma tau
  map_smul' r sigma := by
    apply Prod.ext
    · exact (k4AggregateResidual hn hb2 hc2 hd2).map_smul r sigma
    · exact map_smul _ r sigma

theorem mem_k4GPolarKernel_iff_aggregate_mem
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (sigma : K4EvenPLeft n b c d) :
    sigma ∈ K4GPolarKernel n b c d ↔
      k4EvenPAggregate hn hb2 (by omega) hd2 sigma ∈
        K4AggregatePolarKernel n c := by
  let A := k4EvenPAggregate hn hb2 (by omega : 0 < c) hd2
  let H := k4AggregateHyperbolicPolar (n := n) (c := c)
  have hA : Function.Surjective A :=
    k4EvenPAggregate_surjective hn hb2 (by omega) hd2
  have hdual : Function.Injective A.dualMap :=
    LinearMap.dualMap_injective_of_surjective hA
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  rw [k4EvenPGPolar_factor_through_aggregate hn hb2 (by omega) hd2]
  change A.dualMap (H (A sigma)) = 0 ↔ H (A sigma) = 0
  constructor
  · intro h
    apply hdual
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

set_option maxHeartbeats 2000000 in
-- The final restricted equivalence combines both kernel subtypes and the
-- aggregate product; its inverse-law elaboration needs the same local budget.
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 512 in
noncomputable def k4GPolarKernelAggregateSplit
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4GPolarKernel n b c d ≃ₗ[F]
      (K4AggregateKernel n b c d hn hb2 hc2 hd2 ×
        K4AggregatePolarKernel n c) where
  toFun sigma :=
    (k4AggregateResidual hn hb2 hc2 hd2 sigma.1,
      ⟨k4EvenPAggregate hn hb2 (by omega) hd2 sigma.1,
        (mem_k4GPolarKernel_iff_aggregate_mem
          hn hb2 hc2 hd2 sigma.1).mp sigma.2⟩)
  invFun z := by
    let sigma : K4EvenPLeft n b c d :=
      z.1.1 + k4AggregateLift (by omega) (by omega) (by omega) z.2.1
    have hAggregate :
        k4EvenPAggregate hn hb2 (by omega) hd2 sigma = z.2.1 := by
      change
        k4EvenPAggregate hn hb2 (by omega) hd2
            (z.1.1 +
              k4AggregateLift (by omega) (by omega) (by omega) z.2.1) =
          z.2.1
      rw [map_add, LinearMap.mem_ker.mp z.1.2,
        k4EvenPAggregate_lift, zero_add]
    exact
      ⟨sigma,
        (mem_k4GPolarKernel_iff_aggregate_mem
          hn hb2 hc2 hd2 sigma).mpr (hAggregate.symm ▸ z.2.2)⟩
  left_inv sigma := by
    apply Subtype.ext
    change
      (sigma.1 + k4AggregateLift (by omega) (by omega) (by omega)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma.1)) +
        k4AggregateLift (by omega) (by omega) (by omega)
          (k4EvenPAggregate hn hb2 (by omega) hd2 sigma.1) = sigma.1
    rw [add_assoc, module_add_self, add_zero]
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      change
        z.1.1 + k4AggregateLift (by omega) (by omega) (by omega) z.2.1 +
            k4AggregateLift (by omega) (by omega) (by omega)
              (k4EvenPAggregate hn hb2 (by omega) hd2
                (z.1.1 +
                  k4AggregateLift (by omega) (by omega) (by omega) z.2.1)) =
          z.1.1
      rw [map_add, LinearMap.mem_ker.mp z.1.2,
        k4EvenPAggregate_lift, zero_add]
      rw [add_assoc, module_add_self, add_zero]
    · apply Subtype.ext
      change
        k4EvenPAggregate hn hb2 (by omega) hd2
            (z.1.1 +
              k4AggregateLift (by omega) (by omega) (by omega) z.2.1) =
          z.2.1
      rw [map_add, LinearMap.mem_ker.mp z.1.2,
        k4EvenPAggregate_lift, zero_add]
  map_add' sigma tau := by
    apply Prod.ext
    · change
        k4AggregateResidual hn hb2 hc2 hd2 (sigma.1 + tau.1) =
          k4AggregateResidual hn hb2 hc2 hd2 sigma.1 +
            k4AggregateResidual hn hb2 hc2 hd2 tau.1
      exact (k4AggregateResidual hn hb2 hc2 hd2).map_add sigma.1 tau.1
    · apply Subtype.ext
      exact map_add _ sigma.1 tau.1
  map_smul' r sigma := by
    apply Prod.ext
    · change
        k4AggregateResidual hn hb2 hc2 hd2 (r • sigma.1) =
          r • k4AggregateResidual hn hb2 hc2 hd2 sigma.1
      exact (k4AggregateResidual hn hb2 hc2 hd2).map_smul r sigma.1
    · apply Subtype.ext
      exact map_smul _ r sigma.1

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
