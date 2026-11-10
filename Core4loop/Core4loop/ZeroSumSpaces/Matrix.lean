import Core4loop.ZeroSumSpaces.Profile

open scoped BigOperators

namespace Core4loop

abbrev MatrixProfile (n : ℕ) := I n → I n → F

noncomputable def rowSum2Map {n : ℕ} [NeZero n] :
    MatrixProfile n →ₗ[F] Profile n where
  toFun M := fun x => ∑ y : I n, M x y
  map_add' M N := by
    funext x
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r M := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

noncomputable def colSum2Map {n : ℕ} [NeZero n] :
    MatrixProfile n →ₗ[F] Profile n where
  toFun M := fun y => ∑ x : I n, M x y
  map_add' M N := by
    funext y
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r M := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

noncomputable def MatrixZeroSum (n : ℕ) [NeZero n] :
    Submodule F (MatrixProfile n) :=
  LinearMap.ker (rowSum2Map (n := n)) ⊓ LinearMap.ker (colSum2Map (n := n))

noncomputable def pullMatrixVal {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → F) : MatrixProfile n :=
  fun x y => pullProfileVal (fun x0 : NonzeroI n => pullProfileVal (g x0) y) x

lemma pullMatrixVal_col_zero_sum {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → F) (y : I n) :
    (∑ x : I n, pullMatrixVal g x y) = 0 := by
  exact pullProfileVal_zero_sum (fun x0 : NonzeroI n => pullProfileVal (g x0) y)

lemma pullMatrixVal_row_zero_sum {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → F) (x : I n) :
    (∑ y : I n, pullMatrixVal g x y) = 0 := by
  classical
  by_cases hx : x = 0
  · subst hx
    calc
      (∑ y : I n, pullMatrixVal g 0 y)
          = ∑ y : I n, ∑ x0 : NonzeroI n, pullProfileVal (g x0) y := by
              refine Finset.sum_congr rfl ?_
              intro y _
              simp [pullMatrixVal, pullProfileVal]
      _ = ∑ x0 : NonzeroI n, ∑ y : I n, pullProfileVal (g x0) y := by
              rw [Finset.sum_comm]
      _ = 0 := by
              simp [pullProfileVal_zero_sum]
  · calc
      (∑ y : I n, pullMatrixVal g x y)
          = ∑ y : I n, pullProfileVal (g ⟨x, hx⟩) y := by
              refine Finset.sum_congr rfl ?_
              intro y _
              simp [pullMatrixVal, pullProfileVal, hx]
      _ = 0 := pullProfileVal_zero_sum (g ⟨x, hx⟩)

noncomputable def pullMatrix {n : ℕ} [NeZero n] :
    (NonzeroI n → NonzeroI n → F) →ₗ[F] MatrixZeroSum n where
  toFun g :=
    ⟨pullMatrixVal g, by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext x
        exact pullMatrixVal_row_zero_sum g x
      · apply LinearMap.mem_ker.mpr
        funext y
        exact pullMatrixVal_col_zero_sum g y⟩
  map_add' g h := by
    apply Subtype.ext
    funext x y
    unfold pullMatrixVal pullProfileVal
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · simp [hx, hy, Finset.sum_add_distrib]
    · simp [hx, hy, Finset.sum_add_distrib]
    · simp [hx, hy, Finset.sum_add_distrib]
    · simp [hx, hy]
  map_smul' r g := by
    apply Subtype.ext
    funext x y
    unfold pullMatrixVal pullProfileVal
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · simp [hx, hy, Finset.mul_sum]
    · simp [hx, hy, Finset.mul_sum]
    · simp [hx, hy, Finset.mul_sum]
    · simp [hx, hy]

noncomputable def readMatrix {n : ℕ} [NeZero n] :
    MatrixZeroSum n →ₗ[F] (NonzeroI n → NonzeroI n → F) where
  toFun M := fun x y => M.1 x.1 y.1
  map_add' M N := by
    funext x y
    rfl
  map_smul' r M := by
    funext x y
    rfl

lemma readMatrix_pullMatrix {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → F) :
    readMatrix (pullMatrix (n := n) g) = g := by
  funext x y
  simp [readMatrix, pullMatrix, pullMatrixVal, pullProfileVal, x.2, y.2]

lemma matrix_row_zero {n : ℕ} [NeZero n] (M : MatrixZeroSum n) (x : I n) :
    (∑ y : I n, M.1 x y) = 0 := by
  have hrow : rowSum2Map (n := n) M.1 = 0 := LinearMap.mem_ker.mp M.2.1
  exact congrFun hrow x

lemma matrix_col_zero {n : ℕ} [NeZero n] (M : MatrixZeroSum n) (y : I n) :
    (∑ x : I n, M.1 x y) = 0 := by
  have hcol : colSum2Map (n := n) M.1 = 0 := LinearMap.mem_ker.mp M.2.2
  exact congrFun hcol y

lemma pullMatrix_readMatrix {n : ℕ} [NeZero n]
    (M : MatrixZeroSum n) :
    pullMatrix (n := n) (readMatrix M) = M := by
  apply Subtype.ext
  funext x y
  by_cases hx : x = 0
  · subst hx
    by_cases hy : y = 0
    · subst hy
      have hcol0 :
          M.1 0 0 = ∑ x0 : NonzeroI n, M.1 x0.1 0 :=
        value_zero_eq_sum_nonzero_of_sum_zero (matrix_col_zero M 0)
      have hrow0 :
          ∀ x0 : NonzeroI n,
            M.1 x0.1 0 = ∑ y0 : NonzeroI n, M.1 x0.1 y0.1 := by
        intro x0
        exact value_zero_eq_sum_nonzero_of_sum_zero (matrix_row_zero M x0.1)
      calc
        (pullMatrix (n := n) (readMatrix M)).1 0 0
            = ∑ x0 : NonzeroI n, ∑ y0 : NonzeroI n, M.1 x0.1 y0.1 := by
                simp [pullMatrix, pullMatrixVal, pullProfileVal, readMatrix]
        _ = ∑ x0 : NonzeroI n, M.1 x0.1 0 := by
                refine Finset.sum_congr rfl ?_
                intro x0 _
                exact (hrow0 x0).symm
        _ = M.1 0 0 := hcol0.symm
    · have hcol :
          M.1 0 y = ∑ x0 : NonzeroI n, M.1 x0.1 y :=
        value_zero_eq_sum_nonzero_of_sum_zero (matrix_col_zero M y)
      calc
        (pullMatrix (n := n) (readMatrix M)).1 0 y
            = ∑ x0 : NonzeroI n, M.1 x0.1 y := by
                simp [pullMatrix, pullMatrixVal, pullProfileVal, readMatrix, hy]
        _ = M.1 0 y := hcol.symm
  · by_cases hy : y = 0
    · subst hy
      have hrow :
          M.1 x 0 = ∑ y0 : NonzeroI n, M.1 x y0.1 :=
        value_zero_eq_sum_nonzero_of_sum_zero (matrix_row_zero M x)
      calc
        (pullMatrix (n := n) (readMatrix M)).1 x 0
            = ∑ y0 : NonzeroI n, M.1 x y0.1 := by
                simp [pullMatrix, pullMatrixVal, pullProfileVal, readMatrix, hx]
        _ = M.1 x 0 := hrow.symm
    · simp [pullMatrix, pullMatrixVal, pullProfileVal, readMatrix, hx, hy]

noncomputable def matrixZeroSumEquivNonzero2 {n : ℕ} [NeZero n] :
    MatrixZeroSum n ≃ₗ[F] (NonzeroI n → NonzeroI n → F) where
  toFun := readMatrix
  invFun := pullMatrix
  left_inv := pullMatrix_readMatrix
  right_inv := readMatrix_pullMatrix
  map_add' := by
    intro M N
    rfl
  map_smul' := by
    intro r M
    rfl

lemma finrank_MatrixZeroSum {n : ℕ} [NeZero n] :
    Module.finrank F (MatrixZeroSum n) = (n - 1) ^ 2 := by
  have hnonzero : Module.finrank F (NonzeroI n → F) = n - 1 := by
    calc
      Module.finrank F (NonzeroI n → F)
          = ∑ _ : NonzeroI n, Module.finrank F F := by
              simp [Module.finrank_pi_fintype
                (R := F) (M := fun _ : NonzeroI n => F)]
      _ = Fintype.card (NonzeroI n) := by
              simp
      _ = n - 1 := card_NonzeroI
  calc
    Module.finrank F (MatrixZeroSum n)
        = Module.finrank F (NonzeroI n → NonzeroI n → F) := by
            exact LinearEquiv.finrank_eq (matrixZeroSumEquivNonzero2 (n := n))
    _ = ∑ _ : NonzeroI n, Module.finrank F (NonzeroI n → F) := by
            simp [Module.finrank_pi_fintype
              (R := F) (M := fun _ : NonzeroI n => NonzeroI n → F)]
    _ = ∑ _ : NonzeroI n, (n - 1) := by
            simp [hnonzero]
    _ = Fintype.card (NonzeroI n) * (n - 1) := by
            simp
    _ = (n - 1) ^ 2 := by
            rw [card_NonzeroI, pow_two]

end Core4loop
