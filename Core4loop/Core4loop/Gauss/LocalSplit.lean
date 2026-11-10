import Core4loop.Gauss.AElimination

namespace Core4loop

theorem localPhase_triangleLeaf_afterA {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    localPhase .triangleLeaf ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w =
      A y z w * (dyB B p y z w + dzC C p y z w + dwW W p y z w)
      + betaB B p y z w * deltaC C p y z w
      + gammaB B p y z w * etaC C p y z w := by
  rw [localPhase_triangleLeaf_expanded]
  simp only [alphaOf, betaOf, gammaOf, deltaOf, etaOf, xiOf, zetaOf,
    betaB, gammaB, deltaC, etaC, xiW, zetaW, dyB, dzC, dwW]
  ring_nf

theorem localPhase_square_afterA {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    localPhase .square ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w =
      A y z w * (dyB B p y z w + dwW W p y z w)
      + betaB B p y z w * deltaC C p y z w
      + gammaB B p y z w * etaC C p y z w
      + deltaC C p y z w * xiW W p y z w
      + etaC C p y z w * zetaW W p y z w := by
  rw [localPhase_square_expanded]
  simp only [alphaOf, betaOf, gammaOf, deltaOf, etaOf, xiOf, zetaOf,
    betaB, gammaB, deltaC, etaC, xiW, zetaW, dyB, dwW]
  ring_nf

theorem localPhase_squareDiagonal_afterA {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    localPhase .squareDiagonal ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w =
      A y z w * (dyB B p y z w + dzC C p y z w + dwW W p y z w)
      + betaB B p y z w * deltaC C p y z w
      + gammaB B p y z w * etaC C p y z w
      + deltaC C p y z w * xiW W p y z w
      + etaC C p y z w * zetaW W p y z w := by
  rw [localPhase_squareDiagonal_expanded]
  simp only [alphaOf, betaOf, gammaOf, deltaOf, etaOf, xiOf, zetaOf,
    betaB, gammaB, deltaC, etaC, xiW, zetaW, dyB, dzC, dwW]
  ring_nf

theorem localPhase_complete_afterA {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c)
    (p : PVec n a) (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    localPhase .complete ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w =
      A y z w * (dyB B p y z w + dzC C p y z w + dwW W p y z w)
      + betaB B p y z w * deltaC C p y z w
      + gammaB B p y z w * etaC C p y z w
      + betaB B p y z w * xiW W p y z w
      + gammaB B p y z w * zetaW W p y z w
      + deltaC C p y z w * xiW W p y z w
      + etaC C p y z w * zetaW W p y z w := by
  rw [localPhase_complete_expanded]
  simp only [alphaOf, betaOf, gammaOf, deltaOf, etaOf, xiOf, zetaOf,
    betaB, gammaB, deltaC, etaC, xiW, zetaW, dyB, dzC, dwW]
  ring_nf

end Core4loop
