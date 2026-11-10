import Core4loop.Gauss.LocalSplit

open scoped BigOperators

namespace Core4loop

lemma sum_index_A_mul {ι : Type*} [Fintype ι] {n b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (L : ι → RootTarget n b c d) :
    (∑ i : ι, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        A y z w * L i y z w) =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        A y z w * ∑ i : ι, L i y z w := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro w _
  rw [Finset.mul_sum]

theorem phaseExponent_triangleLeaf_split {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c) :
    phaseExponentNF .triangleLeaf
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) =
      coeffApplyA (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
      + Q1 B C := by
  let L : PVec n a → RootTarget n b c d := fun p y z w =>
    dyB B p y z w + dzC C p y z w + dwW W p y z w
  let R : PVec n a → RootTarget n b c d := fun p y z w =>
    betaB B p y z w * deltaC C p y z w +
      gammaB B p y z w * etaC C p y z w
  calc
    phaseExponentNF .triangleLeaf
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)
        = ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            (A y z w * L p y z w + R p y z w) := by
            unfold phaseExponentNF
            refine Finset.sum_congr rfl ?_
            intro p _
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            calc
              localPhase .triangleLeaf
                  ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w
                  = A y z w * (dyB B p y z w + dzC C p y z w + dwW W p y z w)
                    + betaB B p y z w * deltaC C p y z w
                    + gammaB B p y z w * etaC C p y z w :=
                      localPhase_triangleLeaf_afterA A B C W p y z w
              _ = A y z w * L p y z w + R p y z w := by
                      simp [L, R]
                      ring
    _ = (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * L p y z w)
        + (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            R p y z w) := by
            simp only [Finset.sum_add_distrib]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * ∑ p : PVec n a, L p y z w)
        + Q1 B C := by
            rw [sum_index_A_mul]
            rfl
    _ = coeffApplyA (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
        + Q1 B C := by
            rw [coeffApplyA_eq_sum]
            rfl

theorem phaseExponent_square_split {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c) :
    phaseExponentNF .square
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) =
      coeffApplyA (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) A
      + Q2 B C W := by
  let L : PVec n a → RootTarget n b c d := fun p y z w =>
    dyB B p y z w + dwW W p y z w
  let R : PVec n a → RootTarget n b c d := fun p y z w =>
    betaB B p y z w * deltaC C p y z w +
      gammaB B p y z w * etaC C p y z w +
      deltaC C p y z w * xiW W p y z w +
      etaC C p y z w * zetaW W p y z w
  calc
    phaseExponentNF .square
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)
        = ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            (A y z w * L p y z w + R p y z w) := by
            unfold phaseExponentNF
            refine Finset.sum_congr rfl ?_
            intro p _
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            calc
              localPhase .square
                  ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w
                  = A y z w * (dyB B p y z w + dwW W p y z w)
                    + betaB B p y z w * deltaC C p y z w
                    + gammaB B p y z w * etaC C p y z w
                    + deltaC C p y z w * xiW W p y z w
                    + etaC C p y z w * zetaW W p y z w :=
                      localPhase_square_afterA A B C W p y z w
              _ = A y z w * L p y z w + R p y z w := by
                      simp [L, R]
                      ring
    _ = (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * L p y z w)
        + (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            R p y z w) := by
            simp only [Finset.sum_add_distrib]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * ∑ p : PVec n a, L p y z w)
        + Q2 B C W := by
            rw [sum_index_A_mul]
            rfl
    _ = coeffApplyA (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) A
        + Q2 B C W := by
            rw [coeffApplyA_eq_sum]
            rfl

theorem phaseExponent_squareDiagonal_split {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c) :
    phaseExponentNF .squareDiagonal
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) =
      coeffApplyA (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
      + Q3 B C W := by
  let L : PVec n a → RootTarget n b c d := fun p y z w =>
    dyB B p y z w + dzC C p y z w + dwW W p y z w
  let R : PVec n a → RootTarget n b c d := fun p y z w =>
    betaB B p y z w * deltaC C p y z w +
      gammaB B p y z w * etaC C p y z w +
      deltaC C p y z w * xiW W p y z w +
      etaC C p y z w * zetaW W p y z w
  calc
    phaseExponentNF .squareDiagonal
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)
        = ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            (A y z w * L p y z w + R p y z w) := by
            unfold phaseExponentNF
            refine Finset.sum_congr rfl ?_
            intro p _
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            calc
              localPhase .squareDiagonal
                  ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w
                  = A y z w * (dyB B p y z w + dzC C p y z w + dwW W p y z w)
                    + betaB B p y z w * deltaC C p y z w
                    + gammaB B p y z w * etaC C p y z w
                    + deltaC C p y z w * xiW W p y z w
                    + etaC C p y z w * zetaW W p y z w :=
                      localPhase_squareDiagonal_afterA A B C W p y z w
              _ = A y z w * L p y z w + R p y z w := by
                      simp [L, R]
                      ring
    _ = (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * L p y z w)
        + (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            R p y z w) := by
            simp only [Finset.sum_add_distrib]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * ∑ p : PVec n a, L p y z w)
        + Q3 B C W := by
            rw [sum_index_A_mul]
            rfl
    _ = coeffApplyA (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
        + Q3 B C W := by
            rw [coeffApplyA_eq_sum]
            rfl

theorem phaseExponent_complete_split {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c) :
    phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) =
      coeffApplyA (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
      + Q4 B C W := by
  let L : PVec n a → RootTarget n b c d := fun p y z w =>
    dyB B p y z w + dzC C p y z w + dwW W p y z w
  let R : PVec n a → RootTarget n b c d := fun p y z w =>
    betaB B p y z w * deltaC C p y z w +
      gammaB B p y z w * etaC C p y z w +
      betaB B p y z w * xiW W p y z w +
      gammaB B p y z w * zetaW W p y z w +
      deltaC C p y z w * xiW W p y z w +
      etaC C p y z w * zetaW W p y z w
  calc
    phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)
        = ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            (A y z w * L p y z w + R p y z w) := by
            unfold phaseExponentNF
            refine Finset.sum_congr rfl ?_
            intro p _
            refine Finset.sum_congr rfl ?_
            intro y _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            calc
              localPhase .complete
                  ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) p y z w
                  = A y z w * (dyB B p y z w + dzC C p y z w + dwW W p y z w)
                    + betaB B p y z w * deltaC C p y z w
                    + gammaB B p y z w * etaC C p y z w
                    + betaB B p y z w * xiW W p y z w
                    + gammaB B p y z w * zetaW W p y z w
                    + deltaC C p y z w * xiW W p y z w
                    + etaC C p y z w * zetaW W p y z w :=
                      localPhase_complete_afterA A B C W p y z w
              _ = A y z w * L p y z w + R p y z w := by
                      simp [L, R]
                      ring
    _ = (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * L p y z w)
        + (∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            R p y z w) := by
            simp only [Finset.sum_add_distrib]
    _ = (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            A y z w * ∑ p : PVec n a, L p y z w)
        + Q4 B C W := by
            rw [sum_index_A_mul]
            rfl
    _ = coeffApplyA (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
        + Q4 B C W := by
            rw [coeffApplyA_eq_sum]
            rfl

theorem sum_A_triangleLeaf_afterA {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .triangleLeaf
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d))) =
      if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
      then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q1 B C)
      else 0 := by
  calc
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .triangleLeaf
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)))
        = ∑ A : AFun4 n b c d,
            bitSign
              (coeffApplyA
                (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
                + Q1 B C) := by
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [phaseExponent_triangleLeaf_split]
    _ = _ := signedCoeffSumA_add_const
      (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) (Q1 B C)

theorem sum_A_square_afterA {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .square
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d))) =
      if K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) = 0
      then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q2 B C W)
      else 0 := by
  calc
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .square
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)))
        = ∑ A : AFun4 n b c d,
            bitSign
              (coeffApplyA
                (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) A
                + Q2 B C W) := by
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [phaseExponent_square_split]
    _ = _ := signedCoeffSumA_add_const
      (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) (Q2 B C W)

theorem sum_A_squareDiagonal_afterA {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .squareDiagonal
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d))) =
      if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
      then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q3 B C W)
      else 0 := by
  calc
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .squareDiagonal
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)))
        = ∑ A : AFun4 n b c d,
            bitSign
              (coeffApplyA
                (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
                + Q3 B C W) := by
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [phaseExponent_squareDiagonal_split]
    _ = _ := signedCoeffSumA_add_const
      (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) (Q3 B C W)

theorem sum_A_complete_afterA {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d))) =
      if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
      then (2 : ℤ) ^ (n ^ (b + c + d)) * bitSign (Q4 B C W)
      else 0 := by
  calc
    (∑ A : AFun4 n b c d,
      bitSign (phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d)))
        = ∑ A : AFun4 n b c d,
            bitSign
              (coeffApplyA
                (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) A
                + Q4 B C W) := by
            refine Finset.sum_congr rfl ?_
            intro A _
            rw [phaseExponent_complete_split]
    _ = _ := signedCoeffSumA_add_const
      (K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)) (Q4 B C W)

end Core4loop
