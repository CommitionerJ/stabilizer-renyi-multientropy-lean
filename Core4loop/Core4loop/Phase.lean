import Core4loop.NormalForm

open scoped BigOperators

namespace Core4loop

def alphaOf {n a b c d : ℕ} (nf : NF4 n a b c d)
    (_p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  nf.A y z w

noncomputable def betaOf {n a b c d : ℕ} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  nf.B p (vecSum y) z w

noncomputable def gammaOf {n a b c d : ℕ} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  nf.B p (vecSum y + 1) z w

noncomputable def deltaOf {n a b c d : ℕ} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  nf.C p y (vecSum z) w

noncomputable def etaOf {n a b c d : ℕ} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  nf.C p y (vecSum z + 1) w

noncomputable def xiOf {n a b c d : ℕ} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  nf.W p y z (vecSum w)

noncomputable def zetaOf {n a b c d : ℕ} [NeZero n] (nf : NF4 n a b c d)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  nf.W p y z (vecSum w + 1)

noncomputable def localPhase {n a b c d : ℕ} [NeZero n] (G : CoreGraph)
    (nf : NF4 n a b c d) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  disc G (alphaOf nf p y z w) (betaOf nf p y z w)
    (deltaOf nf p y z w) (xiOf nf p y z w)
  + disc G (alphaOf nf p y z w) (gammaOf nf p y z w)
    (etaOf nf p y z w) (zetaOf nf p y z w)

noncomputable def phaseExponentNF {a b c d n : ℕ} [NeZero n]
    (G : CoreGraph) (nf : NF4 n a b c d) : F :=
  ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    localPhase G nf p y z w

noncomputable def DeltaNF (G : CoreGraph) (a b c d n : ℕ) [NeZero n] : ℤ :=
  ∑ nf : NF4 n a b c d, bitSign (phaseExponentNF G nf)

lemma disc_triangleLeaf_pair_expanded (α β γ δ η ξ ζ : F) :
    disc .triangleLeaf α β δ ξ + disc .triangleLeaf α γ η ζ =
      α * (β + γ + δ + η + ξ + ζ) + β * δ + γ * η := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    fin_cases δ <;> fin_cases η <;> fin_cases ξ <;> fin_cases ζ <;> decide

lemma disc_square_pair_expanded (α β γ δ η ξ ζ : F) :
    disc .square α β δ ξ + disc .square α γ η ζ =
      α * (β + γ + ξ + ζ) + β * δ + γ * η + δ * ξ + η * ζ := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    fin_cases δ <;> fin_cases η <;> fin_cases ξ <;> fin_cases ζ <;> decide

lemma disc_squareDiagonal_pair_expanded (α β γ δ η ξ ζ : F) :
    disc .squareDiagonal α β δ ξ + disc .squareDiagonal α γ η ζ =
      α * (β + γ + δ + η + ξ + ζ) + β * δ + γ * η + δ * ξ + η * ζ := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    fin_cases δ <;> fin_cases η <;> fin_cases ξ <;> fin_cases ζ <;> decide

lemma disc_completeGraph_pair_expanded (α β γ δ η ξ ζ : F) :
    disc .complete α β δ ξ + disc .complete α γ η ζ =
      α * (β + γ + δ + η + ξ + ζ)
        + β * δ + γ * η + β * ξ + γ * ζ + δ * ξ + η * ζ := by
  fin_cases α <;> fin_cases β <;> fin_cases γ <;>
    fin_cases δ <;> fin_cases η <;> fin_cases ξ <;> fin_cases ζ <;> decide

theorem localPhase_triangleLeaf_expanded {n a b c d : ℕ} [NeZero n]
    (nf : NF4 n a b c d) (p : PVec n a) (y : YVec n b)
    (z : ZVec n c) (w : WVec n d) :
    localPhase .triangleLeaf nf p y z w =
      alphaOf nf p y z w *
        (betaOf nf p y z w + gammaOf nf p y z w +
         deltaOf nf p y z w + etaOf nf p y z w +
         xiOf nf p y z w + zetaOf nf p y z w)
      + betaOf nf p y z w * deltaOf nf p y z w
      + gammaOf nf p y z w * etaOf nf p y z w := by
  simpa [localPhase] using
    disc_triangleLeaf_pair_expanded
      (alphaOf nf p y z w) (betaOf nf p y z w) (gammaOf nf p y z w)
      (deltaOf nf p y z w) (etaOf nf p y z w)
      (xiOf nf p y z w) (zetaOf nf p y z w)

theorem localPhase_square_expanded {n a b c d : ℕ} [NeZero n]
    (nf : NF4 n a b c d) (p : PVec n a) (y : YVec n b)
    (z : ZVec n c) (w : WVec n d) :
    localPhase .square nf p y z w =
      alphaOf nf p y z w *
        (betaOf nf p y z w + gammaOf nf p y z w +
         xiOf nf p y z w + zetaOf nf p y z w)
      + betaOf nf p y z w * deltaOf nf p y z w
      + gammaOf nf p y z w * etaOf nf p y z w
      + deltaOf nf p y z w * xiOf nf p y z w
      + etaOf nf p y z w * zetaOf nf p y z w := by
  simpa [localPhase] using
    disc_square_pair_expanded
      (alphaOf nf p y z w) (betaOf nf p y z w) (gammaOf nf p y z w)
      (deltaOf nf p y z w) (etaOf nf p y z w)
      (xiOf nf p y z w) (zetaOf nf p y z w)

theorem localPhase_squareDiagonal_expanded {n a b c d : ℕ} [NeZero n]
    (nf : NF4 n a b c d) (p : PVec n a) (y : YVec n b)
    (z : ZVec n c) (w : WVec n d) :
    localPhase .squareDiagonal nf p y z w =
      alphaOf nf p y z w *
        (betaOf nf p y z w + gammaOf nf p y z w +
         deltaOf nf p y z w + etaOf nf p y z w +
         xiOf nf p y z w + zetaOf nf p y z w)
      + betaOf nf p y z w * deltaOf nf p y z w
      + gammaOf nf p y z w * etaOf nf p y z w
      + deltaOf nf p y z w * xiOf nf p y z w
      + etaOf nf p y z w * zetaOf nf p y z w := by
  simpa [localPhase] using
    disc_squareDiagonal_pair_expanded
      (alphaOf nf p y z w) (betaOf nf p y z w) (gammaOf nf p y z w)
      (deltaOf nf p y z w) (etaOf nf p y z w)
      (xiOf nf p y z w) (zetaOf nf p y z w)

theorem localPhase_complete_expanded {n a b c d : ℕ} [NeZero n]
    (nf : NF4 n a b c d) (p : PVec n a) (y : YVec n b)
    (z : ZVec n c) (w : WVec n d) :
    localPhase .complete nf p y z w =
      alphaOf nf p y z w *
        (betaOf nf p y z w + gammaOf nf p y z w +
         deltaOf nf p y z w + etaOf nf p y z w +
         xiOf nf p y z w + zetaOf nf p y z w)
      + betaOf nf p y z w * deltaOf nf p y z w
      + gammaOf nf p y z w * etaOf nf p y z w
      + betaOf nf p y z w * xiOf nf p y z w
      + gammaOf nf p y z w * zetaOf nf p y z w
      + deltaOf nf p y z w * xiOf nf p y z w
      + etaOf nf p y z w * zetaOf nf p y z w := by
  simpa [localPhase] using
    disc_completeGraph_pair_expanded
      (alphaOf nf p y z w) (betaOf nf p y z w) (gammaOf nf p y z w)
      (deltaOf nf p y z w) (etaOf nf p y z w)
      (xiOf nf p y z w) (zetaOf nf p y z w)

end Core4loop
