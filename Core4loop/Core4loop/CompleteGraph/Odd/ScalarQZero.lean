import Core4loop.CompleteGraph.ScalarCycle.RelationBridge

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.ScalarCycle

noncomputable section

theorem k4ScalarQ_zero
    {n : Nat} [NeZero n] (hn : 2 <= n)
    (x : K4PreCSource n 1 1 1 1) :
    k4PreCQ x = 0 := by
  rw [k4ScalarQ_eq_singletonDefect x]
  exact k4Singleton_defect_zero hn
    (k4ScalarR x) (k4ScalarB x) (k4ScalarC x)
    (k4ScalarW x) (k4ScalarZ x)
    (k4Scalar_source_root x)
    (k4Scalar_source_dualB x)
    (k4Scalar_source_dualZ x)

end

end Core4loop.CompleteGraph.ScalarCycle
