import Core4loop.CompleteGraph.CorrectedFacade
import Core4loop.CompleteGraph.CorrectedProvenance.Definitions

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem DeltaNF_complete_eq_pow_X4CorrectedZ
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .complete a b c d n =
      (2 : Int) ^ Int.toNat (X4CorrectedZ a b c d n) := by
  simpa only [X4CorrectedZ] using
    DeltaNF_complete_eq_pow_X4SourceZ
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn2 ha hb hc hd

end Core4loop
