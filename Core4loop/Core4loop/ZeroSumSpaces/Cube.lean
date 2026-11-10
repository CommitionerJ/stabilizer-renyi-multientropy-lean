import Core4loop.ZeroSumSpaces.Matrix

open scoped BigOperators

namespace Core4loop

abbrev CubeProfile (n : ℕ) := I n → I n → I n → F

noncomputable def sumX3Map {n : ℕ} [NeZero n] :
    CubeProfile n →ₗ[F] MatrixProfile n where
  toFun T := fun y z => ∑ x : I n, T x y z
  map_add' T U := by
    funext y z
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r T := by
    funext y z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

noncomputable def sumY3Map {n : ℕ} [NeZero n] :
    CubeProfile n →ₗ[F] MatrixProfile n where
  toFun T := fun x z => ∑ y : I n, T x y z
  map_add' T U := by
    funext x z
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r T := by
    funext x z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

noncomputable def sumZ3Map {n : ℕ} [NeZero n] :
    CubeProfile n →ₗ[F] MatrixProfile n where
  toFun T := fun x y => ∑ z : I n, T x y z
  map_add' T U := by
    funext x y
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r T := by
    funext x y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

noncomputable def CubeZeroSum (n : ℕ) [NeZero n] :
    Submodule F (CubeProfile n) :=
  (LinearMap.ker (sumX3Map (n := n)) ⊓ LinearMap.ker (sumY3Map (n := n)))
    ⊓ LinearMap.ker (sumZ3Map (n := n))

noncomputable def pullCubeVal {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → NonzeroI n → F) : CubeProfile n :=
  fun x y z => pullProfileVal (fun x0 : NonzeroI n => pullMatrixVal (g x0) y z) x

lemma pullCubeVal_sumX_zero {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → NonzeroI n → F) (y z : I n) :
    (∑ x : I n, pullCubeVal g x y z) = 0 :=
  pullProfileVal_zero_sum (fun x0 : NonzeroI n => pullMatrixVal (g x0) y z)

lemma pullCubeVal_sumY_zero {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → NonzeroI n → F) (x z : I n) :
    (∑ y : I n, pullCubeVal g x y z) = 0 := by
  classical
  by_cases hx : x = 0
  · subst hx
    calc
      (∑ y : I n, pullCubeVal g 0 y z)
          = ∑ y : I n, ∑ x0 : NonzeroI n, pullMatrixVal (g x0) y z := by
              refine Finset.sum_congr rfl ?_
              intro y _
              simp [pullCubeVal, pullProfileVal]
      _ = ∑ x0 : NonzeroI n, ∑ y : I n, pullMatrixVal (g x0) y z := by
              rw [Finset.sum_comm]
      _ = 0 := by
              simp [pullMatrixVal_col_zero_sum]
  · calc
      (∑ y : I n, pullCubeVal g x y z)
          = ∑ y : I n, pullMatrixVal (g ⟨x, hx⟩) y z := by
              refine Finset.sum_congr rfl ?_
              intro y _
              simp [pullCubeVal, pullProfileVal, hx]
      _ = 0 := pullMatrixVal_col_zero_sum (g ⟨x, hx⟩) z

lemma pullCubeVal_sumZ_zero {n : ℕ} [NeZero n]
    (g : NonzeroI n → NonzeroI n → NonzeroI n → F) (x y : I n) :
    (∑ z : I n, pullCubeVal g x y z) = 0 := by
  classical
  by_cases hx : x = 0
  · subst hx
    calc
      (∑ z : I n, pullCubeVal g 0 y z)
          = ∑ z : I n, ∑ x0 : NonzeroI n, pullMatrixVal (g x0) y z := by
              refine Finset.sum_congr rfl ?_
              intro z _
              simp [pullCubeVal, pullProfileVal]
      _ = ∑ x0 : NonzeroI n, ∑ z : I n, pullMatrixVal (g x0) y z := by
              rw [Finset.sum_comm]
      _ = 0 := by
              simp [pullMatrixVal_row_zero_sum]
  · calc
      (∑ z : I n, pullCubeVal g x y z)
          = ∑ z : I n, pullMatrixVal (g ⟨x, hx⟩) y z := by
              refine Finset.sum_congr rfl ?_
              intro z _
              simp [pullCubeVal, pullProfileVal, hx]
      _ = 0 := pullMatrixVal_row_zero_sum (g ⟨x, hx⟩) y

lemma cube_sumX_zero {n : ℕ} [NeZero n] (T : CubeZeroSum n) (y z : I n) :
    (∑ x : I n, T.1 x y z) = 0 := by
  have h : sumX3Map (n := n) T.1 = 0 := LinearMap.mem_ker.mp T.2.1.1
  exact congrFun (congrFun h y) z

lemma cube_sumY_zero {n : ℕ} [NeZero n] (T : CubeZeroSum n) (x z : I n) :
    (∑ y : I n, T.1 x y z) = 0 := by
  have h : sumY3Map (n := n) T.1 = 0 := LinearMap.mem_ker.mp T.2.1.2
  exact congrFun (congrFun h x) z

lemma cube_sumZ_zero {n : ℕ} [NeZero n] (T : CubeZeroSum n) (x y : I n) :
    (∑ z : I n, T.1 x y z) = 0 := by
  have h : sumZ3Map (n := n) T.1 = 0 := LinearMap.mem_ker.mp T.2.2
  exact congrFun (congrFun h x) y

noncomputable def cubeSliceYZ {n : ℕ} [NeZero n]
    (T : CubeZeroSum n) (x : I n) : MatrixZeroSum n :=
  ⟨fun y z => T.1 x y z, by
    constructor
    · apply LinearMap.mem_ker.mpr
      funext y
      exact cube_sumZ_zero T x y
    · apply LinearMap.mem_ker.mpr
      funext z
      exact cube_sumY_zero T x z⟩

noncomputable def cubeSlicesX {n : ℕ} [NeZero n] :
    CubeZeroSum n →ₗ[F] ZeroSumProfileM n (MatrixZeroSum n) where
  toFun T :=
    ⟨fun x => cubeSliceYZ T x, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      funext y z
      simp [sigmaMapM, cubeSliceYZ, cube_sumX_zero T y z]⟩
  map_add' T U := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    funext y z
    rfl
  map_smul' r T := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    funext y z
    rfl

noncomputable def cubeFromSlicesX {n : ℕ} [NeZero n] :
    ZeroSumProfileM n (MatrixZeroSum n) →ₗ[F] CubeZeroSum n where
  toFun S :=
    ⟨fun x y z => (S.1 x).1 y z, by
      constructor
      · constructor
        · apply LinearMap.mem_ker.mpr
          funext y z
          have hS : (∑ x : I n, S.1 x) = 0 := LinearMap.mem_ker.mp S.2
          have h := congrArg (fun M : MatrixZeroSum n => M.1 y z) hS
          simpa using h
        · apply LinearMap.mem_ker.mpr
          funext x z
          exact matrix_col_zero (S.1 x) z
      · apply LinearMap.mem_ker.mpr
        funext x y
        exact matrix_row_zero (S.1 x) y⟩
  map_add' S T := by
    apply Subtype.ext
    funext x y z
    rfl
  map_smul' r S := by
    apply Subtype.ext
    funext x y z
    rfl

lemma cubeFromSlicesX_cubeSlicesX {n : ℕ} [NeZero n]
    (T : CubeZeroSum n) :
    cubeFromSlicesX (n := n) (cubeSlicesX (n := n) T) = T := by
  apply Subtype.ext
  funext x y z
  rfl

lemma cubeSlicesX_cubeFromSlicesX {n : ℕ} [NeZero n]
    (S : ZeroSumProfileM n (MatrixZeroSum n)) :
    cubeSlicesX (n := n) (cubeFromSlicesX (n := n) S) = S := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  funext y z
  rfl

noncomputable def cubeZeroSumEquivSlicesX {n : ℕ} [NeZero n] :
    CubeZeroSum n ≃ₗ[F] ZeroSumProfileM n (MatrixZeroSum n) where
  toFun := cubeSlicesX (n := n)
  invFun := cubeFromSlicesX (n := n)
  left_inv := cubeFromSlicesX_cubeSlicesX
  right_inv := cubeSlicesX_cubeFromSlicesX
  map_add' := by
    intro T U
    rfl
  map_smul' := by
    intro r T
    rfl

lemma finrank_CubeZeroSum {n : ℕ} [NeZero n] :
    Module.finrank F (CubeZeroSum n) = (n - 1) ^ 3 := by
  calc
    Module.finrank F (CubeZeroSum n)
        = Module.finrank F (ZeroSumProfileM n (MatrixZeroSum n)) := by
            exact LinearEquiv.finrank_eq (cubeZeroSumEquivSlicesX (n := n))
    _ = (n - 1) * Module.finrank F (MatrixZeroSum n) := by
            exact finrank_ZeroSumProfileM (n := n) (M := MatrixZeroSum n)
    _ = (n - 1) ^ 3 := by
            rw [finrank_MatrixZeroSum]
            ring

end Core4loop
