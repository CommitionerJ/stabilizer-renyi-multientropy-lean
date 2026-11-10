import Core4loop.TriangleLeaf.Transfer
import Core4loop.TriangleLeaf.ProfileFibers

open scoped BigOperators

namespace Core4loop

noncomputable section

theorem DeltaNF_triangleLeaf_after_WDiff {n a b c d : ℕ} [NeZero n] :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ((2 : ℤ) ^ Module.finrank F
          (LinearMap.ker
            (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) *
          TriangleLeaf.leafCompatibleResidualSum n a b c d) := by
  classical
  rw [DeltaNF_triangleLeaf_after_W (n := n) (a := a) (b := b) (c := c) (d := d)]
  let kerScale : ℤ :=
    (2 : ℤ) ^ Module.finrank F
      (LinearMap.ker
        (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
  have hpredicate :
      (∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
        if
          ∃ W : WFun4 n a b c,
            KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
              KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
        then kerScale * bitSign (Q1 B C)
        else 0)
        =
        ∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
          if
            KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
              + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
                ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
          then kerScale * bitSign (Q1 B C)
          else 0 := by
    refine Finset.sum_congr rfl ?_
    intro B _
    refine Finset.sum_congr rfl ?_
    intro C _
    have hiff :=
      triangleLeaf_W_compatible_iff_mem_WDiffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d) B C
    by_cases h :
        ∃ W : WFun4 n a b c,
          KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
            KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
              + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
    · simp [h, hiff.mp h]
    · have hnot :
          ¬ KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
              + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
                ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
        intro hw
        exact h (hiff.mpr hw)
      simp [h, hnot]
  have hfactor :
      (∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
        if
          KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
            + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
              ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
        then kerScale * bitSign (Q1 B C)
        else 0)
        =
        kerScale * TriangleLeaf.leafCompatibleResidualSum n a b c d := by
    unfold TriangleLeaf.leafCompatibleResidualSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro B _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro C _
    by_cases h :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
            ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
    · simp [h]
    · simp [h]
  rw [hpredicate, hfactor]

end

end Core4loop
