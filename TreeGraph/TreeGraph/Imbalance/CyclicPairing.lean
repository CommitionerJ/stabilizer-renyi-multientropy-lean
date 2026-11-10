import TreeGraph.Imbalance.CyclicDifference

namespace TreeGraph
namespace Imbalance

theorem cyclic_pairing_sum_eq_forwardCoeff_shifted
    (n : Nat) [NeZero n] (h μ : Rep n → F2) :
    (∑ s : Rep n,
      ((h s) * (μ s) + (h s) * (μ (s + (1 : Rep n))))) =
      ∑ s : Rep n,
        (h s + h (s + (1 : Rep n))) * μ (s + (1 : Rep n)) := by
  classical
  have hshift :
      (∑ s : Rep n,
        (h (s + (1 : Rep n)) * μ (s + (1 : Rep n)))) =
        ∑ s : Rep n, (h s * μ s) := by
    simpa using
      (Equiv.sum_comp (Equiv.addRight (1 : Rep n))
        (fun s : Rep n => h s * μ s))
  calc
    (∑ s : Rep n, (h s * μ s + h s * μ (s + (1 : Rep n)))) =
        (∑ s : Rep n, (h s * μ s)) +
          ∑ s : Rep n, (h s * μ (s + (1 : Rep n))) := by
          rw [Finset.sum_add_distrib]
    _ =
        (∑ s : Rep n, (h (s + (1 : Rep n)) * μ (s + (1 : Rep n)))) +
          ∑ s : Rep n, (h s * μ (s + (1 : Rep n))) := by
          rw [hshift]
    _ =
        ∑ s : Rep n,
          (h (s + (1 : Rep n)) * μ (s + (1 : Rep n)) +
            h s * μ (s + (1 : Rep n))) := by
          rw [← Finset.sum_add_distrib]
    _ =
        ∑ s : Rep n,
          (h s + h (s + (1 : Rep n))) * μ (s + (1 : Rep n)) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [add_mul]
          rw [add_comm]

theorem cyclic_dual_pairing_sum_eq_forwardCoeff_shifted
    (n : Nat) [NeZero n]
    (M : Type) [AddCommGroup M] [Module F2 M]
    (h : Rep n → Module.Dual F2 M) (μ : Rep n → M) :
    (∑ s : Rep n, (h s (μ s) + h s (μ (s + (1 : Rep n))))) =
      ∑ s : Rep n,
        (h s + h (s + (1 : Rep n))) (μ (s + (1 : Rep n))) := by
  classical
  have hshift :
      (∑ s : Rep n, (h (s + (1 : Rep n)) (μ (s + (1 : Rep n))))) =
        ∑ s : Rep n, (h s (μ s)) := by
    simpa using
      (Equiv.sum_comp (Equiv.addRight (1 : Rep n))
        (fun s : Rep n => h s (μ s)))
  calc
    (∑ s : Rep n, (h s (μ s) + h s (μ (s + (1 : Rep n))))) =
        (∑ s : Rep n, (h s (μ s))) +
          ∑ s : Rep n, (h s (μ (s + (1 : Rep n)))) := by
          rw [Finset.sum_add_distrib]
    _ =
        (∑ s : Rep n, (h (s + (1 : Rep n)) (μ (s + (1 : Rep n))))) +
          ∑ s : Rep n, (h s (μ (s + (1 : Rep n)))) := by
          rw [hshift]
    _ =
        ∑ s : Rep n,
          (h (s + (1 : Rep n)) (μ (s + (1 : Rep n))) +
            h s (μ (s + (1 : Rep n)))) := by
          rw [← Finset.sum_add_distrib]
    _ =
        ∑ s : Rep n,
          (h s + h (s + (1 : Rep n))) (μ (s + (1 : Rep n))) := by
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [LinearMap.add_apply]
          rw [add_comm]

end Imbalance
end TreeGraph
