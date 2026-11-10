import Core4loop.Square.Kernel
import Core4loop.Square.Rank.Diagonal
import Core4loop.Square.Rank.PairMapsCore

open scoped BigOperators

namespace Core4loop

lemma SquareCombined_eq_B_add_W {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) =
      SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d) W := by
  apply Prod.ext
  · funext y z w
    change
      (∑ p : PVec n a, (dyB B p y z w + dwW W p y z w)) =
        (∑ p : PVec n a, dyB B p y z w)
          + ∑ p : PVec n a, dwW W p y z w
    rw [Finset.sum_add_distrib]
  · funext p y sz w
    change
      squareCompatFun B W p y sz w =
        squareCompatFun B 0 p y sz w + squareCompatFun 0 W p y sz w
    unfold squareCompatFun betaB gammaB xiW zetaW
    calc
      ((∑ z : ZVec n c,
          if vecSum z = sz then B p (vecSum y) z w + W p y z (vecSum w) else 0)
        + ∑ z : ZVec n c,
          if vecSum z + 1 = sz then
            B p (vecSum y + 1) z w + W p y z (vecSum w + 1)
          else 0)
          =
          ((∑ z : ZVec n c, if vecSum z = sz then B p (vecSum y) z w else 0)
            + ∑ z : ZVec n c, if vecSum z = sz then W p y z (vecSum w) else 0)
          + ((∑ z : ZVec n c,
              if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0)
            + ∑ z : ZVec n c,
              if vecSum z + 1 = sz then W p y z (vecSum w + 1) else 0) := by
            congr 1
            · rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro z _
              by_cases h : vecSum z = sz
              · simp [h]
              · simp [h]
            · rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro z _
              by_cases h : vecSum z + 1 = sz
              · simp [h]
              · simp [h]
      _ =
          ((∑ z : ZVec n c, if vecSum z = sz then B p (vecSum y) z w else 0)
            + ∑ z : ZVec n c,
              if vecSum z + 1 = sz then B p (vecSum y + 1) z w else 0)
          + ((∑ z : ZVec n c, if vecSum z = sz then W p y z (vecSum w) else 0)
            + ∑ z : ZVec n c,
              if vecSum z + 1 = sz then W p y z (vecSum w + 1) else 0) := by
            ring
      _ = squareCompatFun B 0 p y sz w + squareCompatFun 0 W p y sz w := by
            unfold squareCompatFun betaB gammaB xiW zetaW
            simp

theorem range_SquareCombined_eq_sup_range_B_W {n a b c d : ℕ} [NeZero n] :
    LinearMap.range (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))
        ⊔ LinearMap.range (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨x, rfl⟩
    refine Submodule.mem_sup.mpr ⟨
      SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1, ?_,
      SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2, ?_, ?_⟩
    · exact ⟨x.1, rfl⟩
    · exact ⟨x.2, rfl⟩
    · exact (SquareCombined_eq_B_add_W (n := n) (a := a) (b := b) (c := c) (d := d)
        x.1 x.2).symm
  · intro f hf
    rcases Submodule.mem_sup.mp hf with ⟨fB, hfB, fW, hfW, rfl⟩
    rcases hfB with ⟨B, rfl⟩
    rcases hfW with ⟨W, rfl⟩
    refine ⟨(B, W), ?_⟩
    exact SquareCombined_eq_B_add_W (n := n) (a := a) (b := b) (c := c) (d := d) B W

end Core4loop
