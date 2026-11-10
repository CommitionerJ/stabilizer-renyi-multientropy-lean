import Core4loop.TriangleLeaf.E5OneSidedQZero
import Core4loop.QuadraticSignSum
import Core4loop.ZeroSumSpaces.ExplicitCyclicPrefix
import Core4loop.TriangleLeaf.ExponentSplit
import Core4loop.TriangleCore.Parity

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def triangleLeafE5BaseEmbed
    {n a d : ℕ} [NeZero n] :
    TriangleLeafE5BaseC n d →ₗ[F] CFun4 n a 1 d where
  toFun C₀ := fun _p y r w => C₀ (vecSum y) r w
  map_add' C₀ D₀ := by
    funext p y r w
    rfl
  map_smul' x C₀ := by
    funext p y r w
    rfl

@[simp] theorem triangleLeafE5BaseEmbed_apply
    {n a d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseC n d)
    (p : PVec n a) (y : YVec n 1) (r : I n) (w : WVec n d) :
    triangleLeafE5BaseEmbed C₀ p y r w =
      C₀ (vecSum y) r w := rfl

noncomputable def triangleLeafE5PointedEmbed
    {n a d : ℕ} [NeZero n] :
    TriangleLeafE5PointedPart n a d →ₗ[F] CFun4 n a 1 d where
  toFun g := fun p y r w =>
    if hp : p = zeroVec then 0
    else g ⟨p, hp⟩ (vecSum y + r) w
  map_add' g h := by
    funext p y r w
    by_cases hp : p = zeroVec
    · simp [hp]
    · simp [hp]
  map_smul' x g := by
    funext p y r w
    by_cases hp : p = zeroVec
    · simp [hp]
    · simp [hp]

@[simp] theorem triangleLeafE5PointedEmbed_apply
    {n a d : ℕ} [NeZero n]
    (g : TriangleLeafE5PointedPart n a d)
    (p : PVec n a) (y : YVec n 1) (r : I n) (w : WVec n d) :
    triangleLeafE5PointedEmbed g p y r w =
      if hp : p = zeroVec then 0
      else g ⟨p, hp⟩ (vecSum y + r) w := rfl

theorem triangleLeafE5BCoeff_pointedEmbed_eq_zero
    {n a c d : ℕ} [NeZero n]
    (g : TriangleLeafE5PointedPart n a d)
    (p : PVec n a) (t : I n) (z : ZVec n c) (w : WVec n d) :
    triangleLeafE5BCoeff
        (triangleLeafE5PointedEmbed g) p t z w = 0 := by
  by_cases hp : p = zeroVec
  · simp [triangleLeafE5BCoeff, triangleLeafE5PointedEmbed, hp]
  · unfold triangleLeafE5BCoeff
    simp only [triangleLeafE5PointedEmbed_apply, hp, ↓reduceDIte,
      vecSum_scalarYEquiv]
    rw [show
      (t - 1) + (vecSum z + 1) = t + vecSum z by abel]
    exact F_add_self _

theorem triangleLeafE5PointedEmbed_mem_Cadm
    {n a c d : ℕ} [NeZero n]
    (g : TriangleLeafE5PointedPart n a d) :
    triangleLeafE5PointedEmbed g ∈
      TriangleLeafE5Cadm n a c d := by
  apply LinearMap.mem_ker.mpr
  ext Y
  change Q1 Y.1.1.1 (triangleLeafE5PointedEmbed g) = 0
  rw [Q1_eq_sum_B_mul_triangleLeafE5BCoeff]
  simp only [triangleLeafE5BCoeff_pointedEmbed_eq_zero,
    mul_zero, Finset.sum_const_zero]

abbrev TriangleLeafE5SemanticBaseCadm
    (n a c d : ℕ) [NeZero n] :=
  (TriangleLeafE5Cadm n a c d).comap
    (triangleLeafE5BaseEmbed (n := n) (a := a) (d := d))

noncomputable def triangleLeafE5PointedRead
    {n a d : ℕ} [NeZero n] :
    CFun4 n a 1 d →ₗ[F] TriangleLeafE5PointedPart n a d where
  toFun C := fun p u w =>
    C p.1 (triangleLeafE5YOf u) 0 w +
      C zeroVec (triangleLeafE5YOf u) 0 w
  map_add' C D := by
    funext p u w
    change
      (C p.1 (triangleLeafE5YOf u) 0 w +
          D p.1 (triangleLeafE5YOf u) 0 w) +
        (C zeroVec (triangleLeafE5YOf u) 0 w +
          D zeroVec (triangleLeafE5YOf u) 0 w) =
      (C p.1 (triangleLeafE5YOf u) 0 w +
          C zeroVec (triangleLeafE5YOf u) 0 w) +
        (D p.1 (triangleLeafE5YOf u) 0 w +
          D zeroVec (triangleLeafE5YOf u) 0 w)
    abel
  map_smul' x C := by
    funext p u w
    change
      x * C p.1 (triangleLeafE5YOf u) 0 w +
          x * C zeroVec (triangleLeafE5YOf u) 0 w =
        x * (C p.1 (triangleLeafE5YOf u) 0 w +
          C zeroVec (triangleLeafE5YOf u) 0 w)
    ring

@[simp] theorem triangleLeafE5PointedRead_apply
    {n a d : ℕ} [NeZero n]
    (C : CFun4 n a 1 d) (p : TriangleLeafE5NonzeroPVec n a)
    (u : I n) (w : WVec n d) :
    triangleLeafE5PointedRead C p u w =
      C p.1 (triangleLeafE5YOf u) 0 w +
        C zeroVec (triangleLeafE5YOf u) 0 w := rfl

noncomputable def triangleLeafE5BaseRead
    {n a d : ℕ} [NeZero n] :
    CFun4 n a 1 d →ₗ[F] TriangleLeafE5BaseC n d where
  toFun C := fun t r w =>
    C zeroVec (triangleLeafE5YOf t) r w
  map_add' C D := by
    funext t r w
    rfl
  map_smul' x C := by
    funext t r w
    rfl

@[simp] theorem triangleLeafE5BaseRead_apply
    {n a d : ℕ} [NeZero n]
    (C : CFun4 n a 1 d) (t r : I n) (w : WVec n d) :
    triangleLeafE5BaseRead C t r w =
      C zeroVec (triangleLeafE5YOf t) r w := rfl

theorem triangleLeafE5PointedRead_pointedEmbed
    {n a d : ℕ} [NeZero n]
    (g : TriangleLeafE5PointedPart n a d) :
    triangleLeafE5PointedRead
        (triangleLeafE5PointedEmbed g) = g := by
  funext p u w
  simp [triangleLeafE5PointedRead, triangleLeafE5PointedEmbed,
    p.2]

theorem triangleLeafE5BaseRead_baseEmbed
    {n a d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseC n d) :
    triangleLeafE5BaseRead
        (triangleLeafE5BaseEmbed (a := a) C₀) = C₀ := by
  funext t r w
  simp [triangleLeafE5BaseRead, triangleLeafE5BaseEmbed]

theorem triangleLeafE5BaseRead_pointedEmbed
    {n a d : ℕ} [NeZero n]
    (g : TriangleLeafE5PointedPart n a d) :
    triangleLeafE5BaseRead
        (triangleLeafE5PointedEmbed g) = 0 := by
  funext t r w
  simp [triangleLeafE5BaseRead, triangleLeafE5PointedEmbed]

theorem triangleLeafE5PointedRead_baseEmbed
    {n a d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseC n d) :
    triangleLeafE5PointedRead
        (triangleLeafE5BaseEmbed (a := a) C₀) = 0 := by
  funext p u w
  simp [triangleLeafE5PointedRead, triangleLeafE5BaseEmbed,
    F_add_self]

theorem triangleLeafE5Cadm_pointed_orbit
    {n a c d : ℕ} [NeZero n] (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d)
    (p : PVec n a) (t r : I n) (w : WVec n d) :
    C.1 p (triangleLeafE5YOf t) r w +
        C.1 zeroVec (triangleLeafE5YOf t) r w =
      C.1 p (triangleLeafE5YOf (t + r)) 0 w +
        C.1 zeroVec (triangleLeafE5YOf (t + r)) 0 w := by
  let G : I n → I n → F := fun u s =>
    C.1 p (triangleLeafE5YOf u) s w +
      C.1 zeroVec (triangleLeafE5YOf u) s w
  let h : Profile n := fun s => G (t + r - s) s
  have hzero : cycDiff (n := n) F h = 0 := by
    funext s
    let z : ZVec n c := vecSingle hc s
    have hz : vecSum z = s := vecSum_vecSingle hc s
    have hcoeff :=
      triangleLeafE5Cadm_BCoeff_eq_zeroVec
        C p (t + r - s) z w
    change
      (C.1 p (triangleLeafE5YOf (t + r - s)) (vecSum z) w +
          C.1 p
            (triangleLeafE5YOf ((t + r - s) - 1))
            (vecSum z + 1) w)
        =
      C.1 zeroVec
            (triangleLeafE5YOf (t + r - s)) (vecSum z) w +
          C.1 zeroVec
            (triangleLeafE5YOf ((t + r - s) - 1))
            (vecSum z + 1) w at hcoeff
    rw [hz] at hcoeff
    change h s + h (s + 1) = 0
    change
      G (t + r - s) s +
        G (t + r - (s + 1)) (s + 1) = 0
    rw [show t + r - (s + 1) = (t + r - s) - 1 by abel]
    change
      (C.1 p (triangleLeafE5YOf (t + r - s)) s w +
          C.1 zeroVec (triangleLeafE5YOf (t + r - s)) s w) +
        (C.1 p
            (triangleLeafE5YOf ((t + r - s) - 1)) (s + 1) w +
          C.1 zeroVec
            (triangleLeafE5YOf ((t + r - s) - 1)) (s + 1) w) = 0
    calc
      (C.1 p (triangleLeafE5YOf (t + r - s)) s w +
          C.1 zeroVec (triangleLeafE5YOf (t + r - s)) s w) +
        (C.1 p
            (triangleLeafE5YOf ((t + r - s) - 1)) (s + 1) w +
          C.1 zeroVec
            (triangleLeafE5YOf ((t + r - s) - 1)) (s + 1) w)
          =
        (C.1 p (triangleLeafE5YOf (t + r - s)) s w +
          C.1 p
            (triangleLeafE5YOf ((t + r - s) - 1)) (s + 1) w) +
        (C.1 zeroVec (triangleLeafE5YOf (t + r - s)) s w +
          C.1 zeroVec
            (triangleLeafE5YOf ((t + r - s) - 1)) (s + 1) w) := by
              abel
      _ = 0 := by rw [hcoeff]; exact F_add_self _
  have hconst :=
    (cycDiff_eq_zero_iff_constant_apply F h).mp hzero r
  simpa [h, G] using hconst

theorem triangleLeafE5Cadm_decompose
    {n a c d : ℕ} [NeZero n] (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d) :
    triangleLeafE5PointedEmbed
          (triangleLeafE5PointedRead C.1) +
        triangleLeafE5BaseEmbed
          (triangleLeafE5BaseRead C.1) =
      C.1 := by
  funext p y r w
  let t : I n := vecSum y
  have hy : triangleLeafE5YOf t = y := by
    have h := (scalarYEquiv (n := n)).apply_symm_apply y
    change triangleLeafE5YOf (y 0) = y at h
    have hsum : vecSum y = y 0 := by simp [vecSum]
    dsimp [t]
    rw [hsum]
    exact h
  by_cases hp : p = zeroVec
  · subst p
    simp [triangleLeafE5PointedEmbed_apply,
      triangleLeafE5BaseEmbed_apply, triangleLeafE5BaseRead_apply]
    have hy' : triangleLeafE5YOf (vecSum y) = y := by
      simpa [t] using hy
    rw [hy']
  · have horbit :=
      triangleLeafE5Cadm_pointed_orbit hc C p t r w
    simp only [Pi.add_apply, triangleLeafE5PointedEmbed_apply,
      dif_neg hp, triangleLeafE5BaseEmbed_apply,
      triangleLeafE5PointedRead_apply,
      triangleLeafE5BaseRead_apply]
    change
      (C.1 p
            (triangleLeafE5YOf (vecSum y + r)) 0 w +
          C.1 zeroVec
            (triangleLeafE5YOf (vecSum y + r)) 0 w) +
        C.1 zeroVec
            (triangleLeafE5YOf (vecSum y)) r w =
      C.1 p y r w
    rw [← hy]
    simp only [vecSum_scalarYEquiv]
    rw [← horbit]
    calc
      (C.1 p (triangleLeafE5YOf t) r w +
          C.1 zeroVec (triangleLeafE5YOf t) r w) +
        C.1 zeroVec (triangleLeafE5YOf t) r w
          =
        C.1 p (triangleLeafE5YOf t) r w +
          (C.1 zeroVec (triangleLeafE5YOf t) r w +
            C.1 zeroVec (triangleLeafE5YOf t) r w) := by
              abel
      _ = C.1 p (triangleLeafE5YOf t) r w := by
        rw [F_add_self, add_zero]

theorem triangleLeafE5BaseRead_mem_SemanticBaseCadm
    {n a c d : ℕ} [NeZero n] (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d) :
    triangleLeafE5BaseRead C.1 ∈
      TriangleLeafE5SemanticBaseCadm n a c d := by
  have hpoint :
      triangleLeafE5PointedEmbed
          (triangleLeafE5PointedRead C.1) ∈
        TriangleLeafE5Cadm n a c d :=
    triangleLeafE5PointedEmbed_mem_Cadm
      (triangleLeafE5PointedRead C.1)
  have hdecompose := triangleLeafE5Cadm_decompose hc C
  have hself :
      triangleLeafE5PointedEmbed
            (triangleLeafE5PointedRead C.1) +
          triangleLeafE5PointedEmbed
            (triangleLeafE5PointedRead C.1) = 0 := by
    funext p y r w
    exact F_add_self _
  have hbase :
      triangleLeafE5BaseEmbed
          (triangleLeafE5BaseRead C.1) =
        C.1 +
          triangleLeafE5PointedEmbed
            (triangleLeafE5PointedRead C.1) := by
    calc
      triangleLeafE5BaseEmbed
          (triangleLeafE5BaseRead C.1)
          =
        triangleLeafE5BaseEmbed
            (triangleLeafE5BaseRead C.1) +
          (triangleLeafE5PointedEmbed
              (triangleLeafE5PointedRead C.1) +
            triangleLeafE5PointedEmbed
              (triangleLeafE5PointedRead C.1)) := by
                rw [hself, add_zero]
      _ =
        (triangleLeafE5PointedEmbed
              (triangleLeafE5PointedRead C.1) +
            triangleLeafE5BaseEmbed
              (triangleLeafE5BaseRead C.1)) +
          triangleLeafE5PointedEmbed
            (triangleLeafE5PointedRead C.1) := by
              abel
      _ = C.1 +
          triangleLeafE5PointedEmbed
            (triangleLeafE5PointedRead C.1) := by
              rw [hdecompose]
  change
    triangleLeafE5BaseEmbed
        (triangleLeafE5BaseRead C.1) ∈
      TriangleLeafE5Cadm n a c d
  rw [hbase]
  exact
    (TriangleLeafE5Cadm n a c d).add_mem C.2 hpoint

noncomputable def triangleLeafE5CadmCoordinateRead
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) :
    TriangleLeafE5Cadm n a c d →ₗ[F]
      TriangleLeafE5PointedPart n a d ×
        TriangleLeafE5SemanticBaseCadm n a c d where
  toFun C :=
    (triangleLeafE5PointedRead C.1,
      ⟨triangleLeafE5BaseRead C.1,
        triangleLeafE5BaseRead_mem_SemanticBaseCadm hc C⟩)
  map_add' C D := by
    apply Prod.ext
    · exact (triangleLeafE5PointedRead (n := n) (a := a) (d := d)).map_add
        C.1 D.1
    · apply Subtype.ext
      exact (triangleLeafE5BaseRead (n := n) (a := a) (d := d)).map_add
        C.1 D.1
  map_smul' x C := by
    apply Prod.ext
    · exact (triangleLeafE5PointedRead (n := n) (a := a) (d := d)).map_smul
        x C.1
    · apply Subtype.ext
      exact (triangleLeafE5BaseRead (n := n) (a := a) (d := d)).map_smul
        x C.1

noncomputable def triangleLeafE5CadmCoordinateBuild
    {n a c d : ℕ} [NeZero n] :
    (TriangleLeafE5PointedPart n a d ×
        TriangleLeafE5SemanticBaseCadm n a c d) →ₗ[F]
      TriangleLeafE5Cadm n a c d where
  toFun X :=
    ⟨triangleLeafE5PointedEmbed X.1 +
        triangleLeafE5BaseEmbed X.2.1,
      (TriangleLeafE5Cadm n a c d).add_mem
        (triangleLeafE5PointedEmbed_mem_Cadm X.1) X.2.2⟩
  map_add' X Y := by
    apply Subtype.ext
    change
      triangleLeafE5PointedEmbed (X.1 + Y.1) +
          triangleLeafE5BaseEmbed (X.2.1 + Y.2.1) =
        (triangleLeafE5PointedEmbed X.1 +
            triangleLeafE5BaseEmbed X.2.1) +
          (triangleLeafE5PointedEmbed Y.1 +
            triangleLeafE5BaseEmbed Y.2.1)
    rw [(triangleLeafE5PointedEmbed
      (n := n) (a := a) (d := d)).map_add,
      (triangleLeafE5BaseEmbed
        (n := n) (a := a) (d := d)).map_add]
    abel
  map_smul' x X := by
    apply Subtype.ext
    change
      triangleLeafE5PointedEmbed (x • X.1) +
          triangleLeafE5BaseEmbed (x • X.2.1) =
        x • (triangleLeafE5PointedEmbed X.1 +
          triangleLeafE5BaseEmbed X.2.1)
    rw [(triangleLeafE5PointedEmbed
      (n := n) (a := a) (d := d)).map_smul,
      (triangleLeafE5BaseEmbed
        (n := n) (a := a) (d := d)).map_smul,
      smul_add]

theorem triangleLeafE5CadmCoordinateBuild_read
    {n a c d : ℕ} [NeZero n] (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d) :
    triangleLeafE5CadmCoordinateBuild
        (triangleLeafE5CadmCoordinateRead hc C) = C := by
  apply Subtype.ext
  exact triangleLeafE5Cadm_decompose hc C

theorem triangleLeafE5CadmCoordinateRead_build
    {n a c d : ℕ} [NeZero n] (hc : 0 < c)
    (X : TriangleLeafE5PointedPart n a d ×
      TriangleLeafE5SemanticBaseCadm n a c d) :
    triangleLeafE5CadmCoordinateRead hc
        (triangleLeafE5CadmCoordinateBuild X) = X := by
  apply Prod.ext
  · change
      triangleLeafE5PointedRead
          (triangleLeafE5PointedEmbed X.1 +
            triangleLeafE5BaseEmbed X.2.1) = X.1
    rw [(triangleLeafE5PointedRead
        (n := n) (a := a) (d := d)).map_add,
      triangleLeafE5PointedRead_pointedEmbed,
      triangleLeafE5PointedRead_baseEmbed,
      add_zero]
  · apply Subtype.ext
    change
      triangleLeafE5BaseRead
          (triangleLeafE5PointedEmbed X.1 +
            triangleLeafE5BaseEmbed X.2.1) = X.2.1
    rw [(triangleLeafE5BaseRead
        (n := n) (a := a) (d := d)).map_add,
      triangleLeafE5BaseRead_pointedEmbed,
      triangleLeafE5BaseRead_baseEmbed,
      zero_add]

noncomputable def triangleLeafE5CadmEquivCoordinates
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) :
    TriangleLeafE5Cadm n a c d ≃ₗ[F]
      TriangleLeafE5PointedPart n a d ×
        TriangleLeafE5SemanticBaseCadm n a c d where
  toFun := triangleLeafE5CadmCoordinateRead hc
  invFun := triangleLeafE5CadmCoordinateBuild
  left_inv := triangleLeafE5CadmCoordinateBuild_read hc
  right_inv := triangleLeafE5CadmCoordinateRead_build hc
  map_add' C D :=
    (triangleLeafE5CadmCoordinateRead hc).map_add C D
  map_smul' x C :=
    (triangleLeafE5CadmCoordinateRead hc).map_smul x C

/-! Step 17: the base-table B1 cyclic row constraint and a concrete right inverse. -/

abbrev TriangleLeafE5B1Target (n d : ℕ) [NeZero n] :=
  WVec n d → ZeroSumProfile n

noncomputable def triangleLeafE5B1Map
    {n d : ℕ} [NeZero n] :
    TriangleLeafE5BaseC n d →ₗ[F] TriangleLeafE5B1Target n d where
  toFun C := fun w =>
    ⟨cycDiff (n := n) F (fun r => ∑ t : I n, C t r w),
      cycDiff_mem_ZeroSumProfile (fun r => ∑ t : I n, C t r w)⟩
  map_add' C C' := by
    funext w
    apply Subtype.ext
    funext r
    change
      (∑ t : I n, (C t r w + C' t r w)) +
          (∑ t : I n, (C t (r + 1) w + C' t (r + 1) w)) =
        ((∑ t : I n, C t r w) + ∑ t : I n, C t (r + 1) w) +
          ((∑ t : I n, C' t r w) + ∑ t : I n, C' t (r + 1) w)
    simp_rw [Finset.sum_add_distrib]
    abel
  map_smul' x C := by
    funext w
    apply Subtype.ext
    funext r
    change
      (∑ t : I n, x * C t r w) +
          (∑ t : I n, x * C t (r + 1) w) =
        x * ((∑ t : I n, C t r w) + ∑ t : I n, C t (r + 1) w)
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]

noncomputable def triangleLeafE5B1RightInverse
    {n d : ℕ} [NeZero n] :
    TriangleLeafE5B1Target n d →ₗ[F] TriangleLeafE5BaseC n d where
  toFun U := fun t r w =>
    if t = 0 then explicitCyclicPrimitive n (U w) r else 0
  map_add' U V := by
    funext t r w
    by_cases ht : t = 0
    · simp [ht]
    · simp [ht]
  map_smul' x U := by
    funext t r w
    by_cases ht : t = 0
    · simp [ht]
    · simp [ht]

theorem triangleLeafE5B1Map_rightInverse
    {n d : ℕ} [NeZero n]
    (U : TriangleLeafE5B1Target n d) :
    triangleLeafE5B1Map
        (triangleLeafE5B1RightInverse U) = U := by
  classical
  funext w
  apply Subtype.ext
  funext r
  have hrows :
      (fun r : I n =>
        ∑ t : I n, triangleLeafE5B1RightInverse U t r w) =
        explicitCyclicPrimitive n (U w) := by
    funext s
    simp [triangleLeafE5B1RightInverse]
  change
    cycDiff (n := n) F
        (fun s : I n =>
          ∑ t : I n, triangleLeafE5B1RightInverse U t s w) r =
      (U w).1 r
  rw [hrows]
  exact congrFun (cycDiff_explicitCyclicPrimitive (U w)) r

theorem triangleLeafE5B1Map_surjective
    {n d : ℕ} [NeZero n] :
    Function.Surjective
      (triangleLeafE5B1Map :
        TriangleLeafE5BaseC n d → TriangleLeafE5B1Target n d) := by
  intro U
  exact ⟨triangleLeafE5B1RightInverse U,
    triangleLeafE5B1Map_rightInverse U⟩

theorem range_triangleLeafE5B1Map_eq_top
    {n d : ℕ} [NeZero n] :
    LinearMap.range
      (triangleLeafE5B1Map :
        TriangleLeafE5BaseC n d →ₗ[F] TriangleLeafE5B1Target n d) = ⊤ :=
  LinearMap.range_eq_top.mpr triangleLeafE5B1Map_surjective

theorem finrank_triangleLeafE5B1Target
    {n d : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5B1Target n d) =
      n ^ d * (n - 1) := by
  calc
    Module.finrank F (TriangleLeafE5B1Target n d)
        =
      ∑ _w : WVec n d, Module.finrank F (ZeroSumProfile n) := by
        rw [Module.finrank_pi_fintype]
    _ = ∑ _w : WVec n d, (n - 1) := by
          simp only [finrank_ZeroSumProfile]
    _ = Fintype.card (WVec n d) * (n - 1) := by
          simp
    _ = n ^ d * (n - 1) := by
          rw [card_vec]

theorem finrank_range_triangleLeafE5B1Map
    {n d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (triangleLeafE5B1Map :
            TriangleLeafE5BaseC n d →ₗ[F] TriangleLeafE5B1Target n d))
      =
    (n - 1) * n ^ d := by
  rw [range_triangleLeafE5B1Map_eq_top, finrank_top,
    finrank_triangleLeafE5B1Target]
  exact Nat.mul_comm _ _

/-! Step 18: the row-admissible `Ktr` space. -/

abbrev TriangleLeafE5KtrAmbient (n : ℕ) :=
  I n → I n → F

noncomputable def triangleLeafE5KtrRowMap
    {n : ℕ} [NeZero n] :
    TriangleLeafE5KtrAmbient n →ₗ[F] ZeroSumProfile n where
  toFun f :=
    ⟨cycDiff (n := n) F (fun r => ∑ t : I n, f t r),
      cycDiff_mem_ZeroSumProfile (fun r => ∑ t : I n, f t r)⟩
  map_add' f g := by
    apply Subtype.ext
    funext r
    change
      (∑ t : I n, (f t r + g t r)) +
          (∑ t : I n, (f t (r + 1) + g t (r + 1))) =
        ((∑ t : I n, f t r) + ∑ t : I n, f t (r + 1)) +
          ((∑ t : I n, g t r) + ∑ t : I n, g t (r + 1))
    simp_rw [Finset.sum_add_distrib]
    abel
  map_smul' x f := by
    apply Subtype.ext
    funext r
    change
      (∑ t : I n, x * f t r) +
          (∑ t : I n, x * f t (r + 1)) =
        x * ((∑ t : I n, f t r) + ∑ t : I n, f t (r + 1))
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]

noncomputable def triangleLeafE5KtrRowRightInverse
    {n : ℕ} [NeZero n] :
    ZeroSumProfile n →ₗ[F] TriangleLeafE5KtrAmbient n where
  toFun U := fun t r =>
    if t = 0 then explicitCyclicPrimitive n U r else 0
  map_add' U V := by
    funext t r
    by_cases ht : t = 0
    · simp [ht]
    · simp [ht]
  map_smul' x U := by
    funext t r
    by_cases ht : t = 0
    · simp [ht]
    · simp [ht]

theorem triangleLeafE5KtrRowMap_rightInverse
    {n : ℕ} [NeZero n] (U : ZeroSumProfile n) :
    triangleLeafE5KtrRowMap
        (triangleLeafE5KtrRowRightInverse U) = U := by
  classical
  apply Subtype.ext
  funext r
  have hrows :
      (fun r : I n =>
        ∑ t : I n, triangleLeafE5KtrRowRightInverse U t r) =
        explicitCyclicPrimitive n U := by
    funext s
    simp [triangleLeafE5KtrRowRightInverse]
  change
    cycDiff (n := n) F
        (fun s : I n =>
          ∑ t : I n, triangleLeafE5KtrRowRightInverse U t s) r =
      U.1 r
  rw [hrows]
  exact congrFun (cycDiff_explicitCyclicPrimitive U) r

theorem triangleLeafE5KtrRowMap_surjective
    {n : ℕ} [NeZero n] :
    Function.Surjective
      (triangleLeafE5KtrRowMap :
        TriangleLeafE5KtrAmbient n → ZeroSumProfile n) := by
  intro U
  exact ⟨triangleLeafE5KtrRowRightInverse U,
    triangleLeafE5KtrRowMap_rightInverse U⟩

abbrev TriangleLeafE5Ktr (n : ℕ) [NeZero n] :=
  LinearMap.ker
    (triangleLeafE5KtrRowMap :
      TriangleLeafE5KtrAmbient n →ₗ[F] ZeroSumProfile n)

theorem finrank_triangleLeafE5KtrAmbient
    {n : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5KtrAmbient n) = n ^ 2 := by
  calc
    Module.finrank F (TriangleLeafE5KtrAmbient n)
        = ∑ _t : I n, Module.finrank F (Profile n) := by
            rw [Module.finrank_pi_fintype]
    _ = ∑ _t : I n, n := by
          simp only [finrank_profile]
    _ = n * n := by
          simp [I, ZMod.card]
    _ = n ^ 2 := by ring

theorem finrank_triangleLeafE5Ktr
    {n : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5Ktr n) =
      n ^ 2 - (n - 1) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE5KtrRowMap :
        TriangleLeafE5KtrAmbient n →ₗ[F] ZeroSumProfile n)
  have hrange :
      LinearMap.range
          (triangleLeafE5KtrRowMap :
            TriangleLeafE5KtrAmbient n →ₗ[F] ZeroSumProfile n) = ⊤ :=
    LinearMap.range_eq_top.mpr triangleLeafE5KtrRowMap_surjective
  rw [hrange, finrank_top, finrank_ZeroSumProfile,
    finrank_triangleLeafE5KtrAmbient] at hnull
  apply Nat.eq_sub_of_add_eq
  simpa [Nat.add_comm] using hnull

noncomputable def triangleLeafE5KtrDiagDiff
    {n : ℕ} [NeZero n] :
    TriangleLeafE5Ktr n →ₗ[F] TriangleLeafE5KtrAmbient n where
  toFun f := fun t r => f.1 t r + f.1 (t - 1) (r + 1)
  map_add' f g := by
    funext t r
    change
      (f.1 t r + g.1 t r) +
          (f.1 (t - 1) (r + 1) + g.1 (t - 1) (r + 1)) =
        (f.1 t r + f.1 (t - 1) (r + 1)) +
          (g.1 t r + g.1 (t - 1) (r + 1))
    abel
  map_smul' x f := by
    funext t r
    change
      x * f.1 t r + x * f.1 (t - 1) (r + 1) =
        x * (f.1 t r + f.1 (t - 1) (r + 1))
    ring

noncomputable def triangleLeafE5KtrBuild
    {n : ℕ} [NeZero n] :
    Profile n →ₗ[F] TriangleLeafE5Ktr n where
  toFun g :=
    ⟨fun t r => g (t + r), by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      funext r
      change
        (∑ t : I n, g (t + r)) +
            (∑ t : I n, g (t + (r + 1))) = 0
      rw [sum_zmod_add_right (n := n) r g,
        sum_zmod_add_right (n := n) (r + 1) g]
      exact F_add_self _⟩
  map_add' g h := by
    apply Subtype.ext
    funext t r
    rfl
  map_smul' x g := by
    apply Subtype.ext
    funext t r
    rfl

theorem triangleLeafE5KtrDiagDiff_build
    {n : ℕ} [NeZero n] (g : Profile n) :
    triangleLeafE5KtrDiagDiff (triangleLeafE5KtrBuild g) = 0 := by
  funext t r
  change g (t + r) + g ((t - 1) + (r + 1)) = 0
  rw [show (t - 1) + (r + 1) = t + r by abel]
  exact F_add_self _

noncomputable def triangleLeafE5KtrDiagKernelBuild
    {n : ℕ} [NeZero n] :
    Profile n →ₗ[F]
      LinearMap.ker (triangleLeafE5KtrDiagDiff (n := n)) where
  toFun g :=
    ⟨triangleLeafE5KtrBuild g,
      LinearMap.mem_ker.mpr (triangleLeafE5KtrDiagDiff_build g)⟩
  map_add' g h := by
    apply Subtype.ext
    apply Subtype.ext
    funext t r
    rfl
  map_smul' x g := by
    apply Subtype.ext
    apply Subtype.ext
    funext t r
    rfl

noncomputable def triangleLeafE5KtrDiagKernelRead
    {n : ℕ} [NeZero n] :
    LinearMap.ker (triangleLeafE5KtrDiagDiff (n := n)) →ₗ[F] Profile n where
  toFun f := fun u => f.1.1 u 0
  map_add' f g := by
    funext u
    rfl
  map_smul' x f := by
    funext u
    rfl

theorem triangleLeafE5KtrDiagKernelRead_build
    {n : ℕ} [NeZero n] (g : Profile n) :
    triangleLeafE5KtrDiagKernelRead
        (triangleLeafE5KtrDiagKernelBuild g) = g := by
  funext u
  simp [triangleLeafE5KtrDiagKernelRead,
    triangleLeafE5KtrDiagKernelBuild, triangleLeafE5KtrBuild]

theorem triangleLeafE5KtrDiagKernel_eq_build_read
    {n : ℕ} [NeZero n]
    (f : LinearMap.ker (triangleLeafE5KtrDiagDiff (n := n))) :
    triangleLeafE5KtrDiagKernelBuild
        (triangleLeafE5KtrDiagKernelRead f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext t r
  let h : Profile n := fun s => f.1.1 (t + r - s) s
  have hzero : cycDiff (n := n) F h = 0 := by
    funext s
    have hf :=
      congrFun
        (LinearMap.mem_ker.mp f.2)
        (t + r - s)
    have hfs := congrFun hf s
    change
      f.1.1 (t + r - s) s +
        f.1.1 ((t + r - s) - 1) (s + 1) = 0 at hfs
    change
      f.1.1 (t + r - s) s +
        f.1.1 (t + r - (s + 1)) (s + 1) = 0
    rw [show t + r - (s + 1) = (t + r - s) - 1 by abel]
    exact hfs
  have hconst :=
    (cycDiff_eq_zero_iff_constant_apply F h).mp hzero r
  simpa [h] using hconst.symm

noncomputable def triangleLeafE5KtrDiagKernelEquivProfile
    {n : ℕ} [NeZero n] :
    LinearMap.ker (triangleLeafE5KtrDiagDiff (n := n)) ≃ₗ[F]
      Profile n where
  toFun := triangleLeafE5KtrDiagKernelRead
  invFun := triangleLeafE5KtrDiagKernelBuild
  left_inv := triangleLeafE5KtrDiagKernel_eq_build_read
  right_inv := triangleLeafE5KtrDiagKernelRead_build
  map_add' f g :=
    (triangleLeafE5KtrDiagKernelRead (n := n)).map_add f g
  map_smul' x f :=
    (triangleLeafE5KtrDiagKernelRead (n := n)).map_smul x f

theorem finrank_ker_triangleLeafE5KtrDiagDiff
    {n : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.ker (triangleLeafE5KtrDiagDiff (n := n))) = n := by
  calc
    Module.finrank F
        (LinearMap.ker (triangleLeafE5KtrDiagDiff (n := n)))
        =
      Module.finrank F (Profile n) :=
        LinearEquiv.finrank_eq triangleLeafE5KtrDiagKernelEquivProfile
    _ = n := finrank_profile

theorem finrank_range_triangleLeafE5KtrDiagDiff
    {n : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range (triangleLeafE5KtrDiagDiff (n := n))) =
      (n - 1) ^ 2 := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE5KtrDiagDiff (n := n))
  rw [finrank_ker_triangleLeafE5KtrDiagDiff,
    finrank_triangleLeafE5Ktr] at h
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hsq : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, hsq] at h ⊢
  omega

/-! Step 19: the nonzero-`w`-fiber B2 aggregate. -/

abbrev TriangleLeafE5BaseB1 (n d : ℕ) [NeZero n] :=
  LinearMap.ker
    (triangleLeafE5B1Map :
      TriangleLeafE5BaseC n d →ₗ[F] TriangleLeafE5B1Target n d)

abbrev TriangleLeafE5B2AggregateTarget (n : ℕ) [NeZero n] :=
  NonzeroI n → TriangleLeafE5Ktr n

noncomputable def triangleLeafE5WFiberSum
    {n d : ℕ} [NeZero n]
    (C : TriangleLeafE5BaseC n d)
    (t r s : I n) : F :=
  ∑ w : WVec n d, if vecSum w = s then C t r w else 0

private theorem triangleLeafE5WFiberSum_rowDiff
    {n d : ℕ} [NeZero n]
    (C : TriangleLeafE5BaseC n d)
    (r s : I n) :
    (∑ t : I n, triangleLeafE5WFiberSum C t r s) +
        (∑ t : I n, triangleLeafE5WFiberSum C t (r + 1) s)
      =
    ∑ w : WVec n d,
      if vecSum w = s then
        ((∑ t : I n, C t r w) + ∑ t : I n, C t (r + 1) w)
      else 0 := by
  classical
  unfold triangleLeafE5WFiberSum
  calc
    (∑ t : I n, ∑ w : WVec n d,
        if vecSum w = s then C t r w else 0) +
      (∑ t : I n, ∑ w : WVec n d,
        if vecSum w = s then C t (r + 1) w else 0)
        =
      (∑ w : WVec n d, ∑ t : I n,
        if vecSum w = s then C t r w else 0) +
      (∑ w : WVec n d, ∑ t : I n,
        if vecSum w = s then C t (r + 1) w else 0) := by
          rw [Finset.sum_comm]
          congr 1
          rw [Finset.sum_comm]
    _ =
      ∑ w : WVec n d,
        ((∑ t : I n, if vecSum w = s then C t r w else 0) +
          ∑ t : I n,
            if vecSum w = s then C t (r + 1) w else 0) := by
              rw [Finset.sum_add_distrib]
    _ = _ := by
      refine Finset.sum_congr rfl ?_
      intro w _
      by_cases hw : vecSum w = s
      · simp [hw]
      · simp [hw]

noncomputable def triangleLeafE5B2AggregateMap
    {n d : ℕ} [NeZero n] :
    TriangleLeafE5BaseB1 n d →ₗ[F]
      TriangleLeafE5B2AggregateTarget n where
  toFun C := fun s =>
    ⟨fun t r =>
        triangleLeafE5WFiberSum C.1 t r s.1 +
          triangleLeafE5WFiberSum C.1 t r 0,
      by
        apply LinearMap.mem_ker.mpr
        apply Subtype.ext
        funext r
        have hB1 :
            triangleLeafE5B1Map C.1 = 0 :=
          LinearMap.mem_ker.mp C.2
        have hrow (w : WVec n d) :
            (∑ t : I n, C.1 t r w) +
                (∑ t : I n, C.1 t (r + 1) w) = 0 := by
          have hw := congrFun hB1 w
          have hr := congrFun (congrArg Subtype.val hw) r
          change
            (∑ t : I n, C.1 t r w) +
                (∑ t : I n, C.1 t (r + 1) w) = 0 at hr
          exact hr
        change
          (∑ t : I n,
              (triangleLeafE5WFiberSum C.1 t r s.1 +
                triangleLeafE5WFiberSum C.1 t r 0)) +
            (∑ t : I n,
              (triangleLeafE5WFiberSum C.1 t (r + 1) s.1 +
                triangleLeafE5WFiberSum C.1 t (r + 1) 0)) = 0
        simp_rw [Finset.sum_add_distrib]
        have hsZero :
            (∑ t : I n, triangleLeafE5WFiberSum C.1 t r s.1) +
                (∑ t : I n,
                  triangleLeafE5WFiberSum C.1 t (r + 1) s.1) = 0 := by
          rw [triangleLeafE5WFiberSum_rowDiff]
          simp [hrow]
        have hbaseZero :
            (∑ t : I n, triangleLeafE5WFiberSum C.1 t r 0) +
                (∑ t : I n,
                  triangleLeafE5WFiberSum C.1 t (r + 1) 0) = 0 := by
          rw [triangleLeafE5WFiberSum_rowDiff]
          simp [hrow]
        calc
          (∑ t : I n, triangleLeafE5WFiberSum C.1 t r s.1) +
                (∑ t : I n, triangleLeafE5WFiberSum C.1 t r 0) +
              ((∑ t : I n,
                  triangleLeafE5WFiberSum C.1 t (r + 1) s.1) +
                ∑ t : I n,
                  triangleLeafE5WFiberSum C.1 t (r + 1) 0)
              =
            ((∑ t : I n, triangleLeafE5WFiberSum C.1 t r s.1) +
              ∑ t : I n,
                triangleLeafE5WFiberSum C.1 t (r + 1) s.1) +
            ((∑ t : I n, triangleLeafE5WFiberSum C.1 t r 0) +
              ∑ t : I n,
                triangleLeafE5WFiberSum C.1 t (r + 1) 0) := by
                  abel
          _ = 0 := by rw [hsZero, hbaseZero, add_zero]⟩
  map_add' C D := by
    funext s
    apply Subtype.ext
    funext t r
    change
      triangleLeafE5WFiberSum (C + D).1 t r s.1 +
            triangleLeafE5WFiberSum (C + D).1 t r 0 =
        (triangleLeafE5WFiberSum C.1 t r s.1 +
            triangleLeafE5WFiberSum C.1 t r 0) +
          (triangleLeafE5WFiberSum D.1 t r s.1 +
            triangleLeafE5WFiberSum D.1 t r 0)
    have hfiber (q : I n) :
        triangleLeafE5WFiberSum (C + D).1 t r q =
          triangleLeafE5WFiberSum C.1 t r q +
            triangleLeafE5WFiberSum D.1 t r q := by
      classical
      unfold triangleLeafE5WFiberSum
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro w _
      by_cases hw : vecSum w = q
      · simp [hw]
      · simp [hw]
    rw [hfiber, hfiber]
    abel
  map_smul' x C := by
    funext s
    apply Subtype.ext
    funext t r
    change
      triangleLeafE5WFiberSum (x • C).1 t r s.1 +
            triangleLeafE5WFiberSum (x • C).1 t r 0 =
        x * (triangleLeafE5WFiberSum C.1 t r s.1 +
          triangleLeafE5WFiberSum C.1 t r 0)
    have hfiber (q : I n) :
        triangleLeafE5WFiberSum (x • C).1 t r q =
          x * triangleLeafE5WFiberSum C.1 t r q := by
      classical
      unfold triangleLeafE5WFiberSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro w _
      by_cases hw : vecSum w = q
      · simp [hw]
      · simp [hw]
    rw [hfiber, hfiber]
    ring

noncomputable def triangleLeafE5B2AggregateRightInverseRawValue
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (U : TriangleLeafE5B2AggregateTarget n)
    (t r : I n) (w : WVec n d) : F :=
  if hzero : vecSum w = 0 then 0
  else if w = vecSingle hd (vecSum w) then
    (U ⟨vecSum w, hzero⟩).1 t r
  else 0

noncomputable def triangleLeafE5B2AggregateRightInverseRaw
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    TriangleLeafE5B2AggregateTarget n →ₗ[F]
      TriangleLeafE5BaseC n d where
  toFun U := triangleLeafE5B2AggregateRightInverseRawValue hd U
  map_add' U V := by
    funext t r w
    change
      triangleLeafE5B2AggregateRightInverseRawValue hd (U + V) t r w =
        triangleLeafE5B2AggregateRightInverseRawValue hd U t r w +
          triangleLeafE5B2AggregateRightInverseRawValue hd V t r w
    by_cases hzero : vecSum w = 0
    · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
      rw [dif_pos hzero, dif_pos hzero, dif_pos hzero, zero_add]
    · by_cases hrep : w = vecSingle hd (vecSum w)
      · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
        rw [dif_neg hzero, if_pos hrep, dif_neg hzero, if_pos hrep,
          dif_neg hzero, if_pos hrep]
        rfl
      · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
        rw [dif_neg hzero, if_neg hrep, dif_neg hzero, if_neg hrep,
          dif_neg hzero, if_neg hrep, zero_add]
  map_smul' x U := by
    funext t r w
    change
      triangleLeafE5B2AggregateRightInverseRawValue hd (x • U) t r w =
        x • triangleLeafE5B2AggregateRightInverseRawValue hd U t r w
    by_cases hzero : vecSum w = 0
    · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
      rw [dif_pos hzero, dif_pos hzero, smul_zero]
    · by_cases hrep : w = vecSingle hd (vecSum w)
      · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
        rw [dif_neg hzero, if_pos hrep, dif_neg hzero, if_pos hrep]
        rfl
      · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
        rw [dif_neg hzero, if_neg hrep, dif_neg hzero, if_neg hrep,
          smul_zero]

theorem triangleLeafE5B2AggregateRightInverseRaw_mem
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (U : TriangleLeafE5B2AggregateTarget n) :
    triangleLeafE5B2AggregateRightInverseRaw hd U ∈
      TriangleLeafE5BaseB1 n d := by
  apply LinearMap.mem_ker.mpr
  funext w
  apply Subtype.ext
  funext r
  change
    (∑ t : I n,
        triangleLeafE5B2AggregateRightInverseRawValue hd U t r w) +
      (∑ t : I n,
        triangleLeafE5B2AggregateRightInverseRawValue hd U t (r + 1) w) = 0
  by_cases hzero : vecSum w = 0
  · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
    simp_rw [dif_pos hzero]
    simp
  · by_cases hrep : w = vecSingle hd (vecSum w)
    · have hKtr :
          triangleLeafE5KtrRowMap
              (U ⟨vecSum w, hzero⟩).1 = 0 :=
        LinearMap.mem_ker.mp (U ⟨vecSum w, hzero⟩).2
      have hpoint :=
        congrFun (congrArg Subtype.val hKtr) r
      change
        (∑ t : I n, (U ⟨vecSum w, hzero⟩).1 t r) +
          (∑ t : I n,
            (U ⟨vecSum w, hzero⟩).1 t (r + 1)) = 0 at hpoint
      simp only [triangleLeafE5B2AggregateRightInverseRawValue]
      simp_rw [dif_neg hzero, if_pos hrep]
      exact hpoint
    · simp only [triangleLeafE5B2AggregateRightInverseRawValue]
      simp_rw [dif_neg hzero, if_neg hrep]
      simp

noncomputable def triangleLeafE5B2AggregateRightInverse
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    TriangleLeafE5B2AggregateTarget n →ₗ[F]
      TriangleLeafE5BaseB1 n d where
  toFun U :=
    ⟨triangleLeafE5B2AggregateRightInverseRaw hd U,
      triangleLeafE5B2AggregateRightInverseRaw_mem hd U⟩
  map_add' U V := by
    apply Subtype.ext
    exact (triangleLeafE5B2AggregateRightInverseRaw hd).map_add U V
  map_smul' x U := by
    apply Subtype.ext
    exact (triangleLeafE5B2AggregateRightInverseRaw hd).map_smul x U

theorem triangleLeafE5WFiberSum_B2AggregateRightInverse_nonzero
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (U : TriangleLeafE5B2AggregateTarget n) (s : NonzeroI n)
    (t r : I n) :
    triangleLeafE5WFiberSum
        (triangleLeafE5B2AggregateRightInverse hd U).1 t r s.1 =
      (U s).1 t r := by
  classical
  unfold triangleLeafE5WFiberSum
  rw [Finset.sum_eq_single (vecSingle hd s.1)]
  · rw [if_pos (vecSum_vecSingle hd s.1)]
    change
      triangleLeafE5B2AggregateRightInverseRawValue hd U t r
          (vecSingle hd s.1) =
        (U s).1 t r
    simp only [triangleLeafE5B2AggregateRightInverseRawValue,
      vecSum_vecSingle hd s.1, s.2, if_pos]
    rfl
  · intro w _ hw
    by_cases hsum : vecSum w = s.1
    · have hzero : vecSum w ≠ 0 := by
        simpa [hsum] using s.2
      have hrep : w ≠ vecSingle hd (vecSum w) := by
        intro h
        apply hw
        simpa [hsum] using h
      simp only [hsum, if_pos]
      change
        triangleLeafE5B2AggregateRightInverseRawValue hd U t r w = 0
      simp only [triangleLeafE5B2AggregateRightInverseRawValue]
      rw [dif_neg hzero, if_neg hrep]
    · simp [hsum]
  · simp

theorem triangleLeafE5WFiberSum_B2AggregateRightInverse_zero
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (U : TriangleLeafE5B2AggregateTarget n) (t r : I n) :
    triangleLeafE5WFiberSum
        (triangleLeafE5B2AggregateRightInverse hd U).1 t r 0 = 0 := by
  classical
  unfold triangleLeafE5WFiberSum
  refine Finset.sum_eq_zero ?_
  intro w _
  by_cases hzero : vecSum w = 0
  · simp only [hzero, if_pos]
    change
      triangleLeafE5B2AggregateRightInverseRawValue hd U t r w = 0
    simp only [triangleLeafE5B2AggregateRightInverseRawValue,
      dif_pos hzero]
  · simp [hzero]

theorem triangleLeafE5B2AggregateMap_rightInverse
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (U : TriangleLeafE5B2AggregateTarget n) :
    triangleLeafE5B2AggregateMap
        (triangleLeafE5B2AggregateRightInverse hd U) = U := by
  funext s
  apply Subtype.ext
  funext t r
  change
    triangleLeafE5WFiberSum
          (triangleLeafE5B2AggregateRightInverse hd U).1 t r s.1 +
        triangleLeafE5WFiberSum
          (triangleLeafE5B2AggregateRightInverse hd U).1 t r 0 =
      (U s).1 t r
  rw [triangleLeafE5WFiberSum_B2AggregateRightInverse_nonzero hd U s,
    triangleLeafE5WFiberSum_B2AggregateRightInverse_zero hd U,
    add_zero]

theorem triangleLeafE5B2AggregateMap_surjective
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Surjective
      (triangleLeafE5B2AggregateMap (n := n) (d := d)) := by
  intro U
  exact
    ⟨triangleLeafE5B2AggregateRightInverse hd U,
      triangleLeafE5B2AggregateMap_rightInverse hd U⟩

theorem range_triangleLeafE5B2AggregateMap_eq_top
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    LinearMap.range
        (triangleLeafE5B2AggregateMap (n := n) (d := d)) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (triangleLeafE5B2AggregateMap_surjective hd)

abbrev TriangleLeafE5KtrDiagRange (n : ℕ) [NeZero n] :=
  LinearMap.range (triangleLeafE5KtrDiagDiff (n := n))

noncomputable def triangleLeafE5KtrDiagRangeMap
    {n : ℕ} [NeZero n] :
    TriangleLeafE5Ktr n →ₗ[F] TriangleLeafE5KtrDiagRange n :=
  (triangleLeafE5KtrDiagDiff (n := n)).rangeRestrict

theorem triangleLeafE5KtrDiagRangeMap_surjective
    {n : ℕ} [NeZero n] :
    Function.Surjective
      (triangleLeafE5KtrDiagRangeMap (n := n)) := by
  intro y
  rcases y.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

abbrev TriangleLeafE5B2Target (n : ℕ) [NeZero n] :=
  NonzeroI n → TriangleLeafE5KtrDiagRange n

noncomputable def triangleLeafE5B2Map
    {n d : ℕ} [NeZero n] :
    TriangleLeafE5BaseB1 n d →ₗ[F] TriangleLeafE5B2Target n where
  toFun C := fun s =>
    triangleLeafE5KtrDiagRangeMap
      (triangleLeafE5B2AggregateMap C s)
  map_add' C D := by
    funext s
    change
      triangleLeafE5KtrDiagRangeMap
          (triangleLeafE5B2AggregateMap (C + D) s) =
        triangleLeafE5KtrDiagRangeMap
            (triangleLeafE5B2AggregateMap C s) +
          triangleLeafE5KtrDiagRangeMap
            (triangleLeafE5B2AggregateMap D s)
    rw [(triangleLeafE5B2AggregateMap (n := n) (d := d)).map_add]
    exact
      (triangleLeafE5KtrDiagRangeMap (n := n)).map_add
        (triangleLeafE5B2AggregateMap C s)
        (triangleLeafE5B2AggregateMap D s)
  map_smul' x C := by
    funext s
    change
      triangleLeafE5KtrDiagRangeMap
          (triangleLeafE5B2AggregateMap (x • C) s) =
        x • triangleLeafE5KtrDiagRangeMap
          (triangleLeafE5B2AggregateMap C s)
    rw [(triangleLeafE5B2AggregateMap (n := n) (d := d)).map_smul]
    exact
      (triangleLeafE5KtrDiagRangeMap (n := n)).map_smul x
        (triangleLeafE5B2AggregateMap C s)

theorem triangleLeafE5B2Map_surjective
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Surjective
      (triangleLeafE5B2Map (n := n) (d := d)) := by
  intro Y
  classical
  have hex :
      ∀ s : NonzeroI n,
        ∃ x : TriangleLeafE5Ktr n,
          triangleLeafE5KtrDiagRangeMap x = Y s := by
    intro s
    exact triangleLeafE5KtrDiagRangeMap_surjective (Y s)
  choose U hU using hex
  rcases triangleLeafE5B2AggregateMap_surjective
      (n := n) (d := d) hd U with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  funext s
  change
    triangleLeafE5KtrDiagRangeMap
        (triangleLeafE5B2AggregateMap C s) = Y s
  rw [congrFun hC s, hU s]

theorem range_triangleLeafE5B2Map_eq_top
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    LinearMap.range
        (triangleLeafE5B2Map (n := n) (d := d)) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (triangleLeafE5B2Map_surjective hd)

theorem finrank_triangleLeafE5KtrDiagRange
    {n : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5KtrDiagRange n) =
      (n - 1) ^ 2 :=
  finrank_range_triangleLeafE5KtrDiagDiff

theorem finrank_triangleLeafE5B2Target
    {n : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5B2Target n) =
      (n - 1) ^ 3 := by
  calc
    Module.finrank F (TriangleLeafE5B2Target n) =
        ∑ _s : NonzeroI n,
          Module.finrank F (TriangleLeafE5KtrDiagRange n) := by
            simp only [TriangleLeafE5B2Target,
              Module.finrank_pi_fintype (R := F)
                (M := fun _s : NonzeroI n =>
                  TriangleLeafE5KtrDiagRange n)]
    _ = ∑ _s : NonzeroI n, (n - 1) ^ 2 := by
          simp only [finrank_triangleLeafE5KtrDiagRange]
    _ = Fintype.card (NonzeroI n) * (n - 1) ^ 2 := by
          simp
    _ = (n - 1) * (n - 1) ^ 2 := by rw [card_NonzeroI]
    _ = (n - 1) ^ 3 := by ring

theorem finrank_range_triangleLeafE5B2Map
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafE5B2Map (n := n) (d := d))) =
      (n - 1) ^ 3 := by
  rw [range_triangleLeafE5B2Map_eq_top hd, finrank_top,
    finrank_triangleLeafE5B2Target]

/-! Step 20: semantic base admissibility equals the B1/B2 kernel. -/

abbrev TriangleLeafE5BaseCadm
    (n d : ℕ) [NeZero n] :=
  LinearMap.ker
    (triangleLeafE5B2Map (n := n) (d := d))

private noncomputable def triangleLeafE5BAggregateTest
    {n a c d : ℕ} [NeZero n]
    (U : I n → ZVec n c → WVec n d → F) :
    BFun4 n a c d :=
  fun p t z w =>
    if p = (zeroVec : PVec n a) then U t z w else 0

private theorem sum_p_triangleLeafE5BAggregateTest
    {n a c d : ℕ} [NeZero n]
    (U : I n → ZVec n c → WVec n d → F)
    (t : I n) (z : ZVec n c) (w : WVec n d) :
    (∑ p : PVec n a,
        triangleLeafE5BAggregateTest U p t z w) =
      U t z w := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · simp [triangleLeafE5BAggregateTest]
  · intro p _ hp
    simp [triangleLeafE5BAggregateTest, hp]
  · simp

private theorem KBMap_triangleLeafE5BAggregateTest
    {n a c d : ℕ} [NeZero n]
    (U : I n → ZVec n c → WVec n d → F)
    (y : YVec n 1) (z : ZVec n c) (w : WVec n d) :
    KBMap (n := n) (a := a) (b := 1) (c := c) (d := d)
        (triangleLeafE5BAggregateTest U) y z w =
      U (vecSum y) z w + U (vecSum y + 1) z w := by
  unfold KBMap dyB betaB gammaB
  change
    (∑ p : PVec n a,
      (triangleLeafE5BAggregateTest U p (vecSum y) z w +
        triangleLeafE5BAggregateTest U p (vecSum y + 1) z w)) =
      U (vecSum y) z w + U (vecSum y + 1) z w
  rw [Finset.sum_add_distrib,
    sum_p_triangleLeafE5BAggregateTest,
    sum_p_triangleLeafE5BAggregateTest]

private theorem Q1_triangleLeafE5BAggregateTest
    {n a c d : ℕ} [NeZero n]
    (U : I n → ZVec n c → WVec n d → F)
    (C : CFun4 n a 1 d) :
    Q1 (triangleLeafE5BAggregateTest U) C =
      ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        U t z w *
          triangleLeafE5BCoeff C zeroVec t z w := by
  rw [Q1_eq_sum_B_mul_triangleLeafE5BCoeff]
  rw [Finset.sum_eq_single (zeroVec : PVec n a)]
  · simp [triangleLeafE5BAggregateTest]
  · intro p _ hp
    simp [triangleLeafE5BAggregateTest, hp]
  · simp

theorem triangleLeafE5SemanticBaseCadm_mem_B1
    {n a c d : ℕ} [NeZero n] (hc : 0 < c)
    (C₀ : TriangleLeafE5SemanticBaseCadm n a c d) :
    triangleLeafE5B1Map C₀.1 = 0 := by
  let C : TriangleLeafE5Cadm n a c d :=
    ⟨triangleLeafE5BaseEmbed C₀.1, C₀.2⟩
  funext w
  apply Subtype.ext
  funext r
  let z₀ : ZVec n c := vecSingle hc r
  let U : I n → ZVec n c → WVec n d → F :=
    fun _t z w' => if z = z₀ ∧ w' = w then 1 else 0
  have hKB :
      KBMap (n := n) (a := a) (b := 1) (c := c) (d := d)
          (triangleLeafE5BAggregateTest U) = 0 := by
    funext y z w'
    rw [KBMap_triangleLeafE5BAggregateTest]
    change
      (if z = z₀ ∧ w' = w then 1 else 0) +
        (if z = z₀ ∧ w' = w then 1 else 0) = 0
    exact F_add_self _
  let YV : triangleLeafCompatibleSubmodule n a 1 c d :=
    ⟨(triangleLeafE5BAggregateTest U, 0), by
      apply (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := 1) (c := c) (d := d)
        (triangleLeafE5BAggregateTest U, 0)).mpr
      rw [hKB, LinearMap.map_zero, zero_add]
      exact (WDiffSpace
        (n := n) (b := 1) (c := c) (d := d)).zero_mem⟩
  let Y : triangleLeafBOnly n a 1 c d :=
    ⟨YV, by rfl⟩
  have hCadm :
      triangleLeafE5CadmMap C.1 = 0 :=
    LinearMap.mem_ker.mp C.2
  have hQ := DFunLike.congr_fun hCadm Y
  change
    Q1 (triangleLeafE5BAggregateTest U)
      (triangleLeafE5BaseEmbed C₀.1) = 0 at hQ
  rw [Q1_triangleLeafE5BAggregateTest] at hQ
  have hz₀ : vecSum z₀ = r := vecSum_vecSingle hc r
  have hpoint :
      (∑ t : I n,
          triangleLeafE5BCoeff
            (triangleLeafE5BaseEmbed (a := a) C₀.1)
            (zeroVec : PVec n a) t z₀ w) = 0 := by
    classical
    simp only [U, ite_mul, one_mul, zero_mul] at hQ
    calc
      (∑ t : I n,
          triangleLeafE5BCoeff
            (triangleLeafE5BaseEmbed (a := a) C₀.1)
            (zeroVec : PVec n a) t z₀ w)
          =
        ∑ t : I n, ∑ z : ZVec n c, ∑ w' : WVec n d,
          if z = z₀ ∧ w' = w then
            triangleLeafE5BCoeff
              (triangleLeafE5BaseEmbed (a := a) C₀.1)
              (zeroVec : PVec n a) t z w'
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro t _
            rw [Finset.sum_eq_single z₀]
            · rw [Finset.sum_eq_single w]
              · simp
              · intro w' _ hw'
                simp [hw']
              · simp
            · intro z _ hz
              simp [hz]
            · simp
      _ = 0 := hQ
  have hexpand :
      (∑ t : I n,
          triangleLeafE5BCoeff
            (triangleLeafE5BaseEmbed (a := a) C₀.1)
            (zeroVec : PVec n a) t z₀ w)
        =
      (∑ t : I n, C₀.1 t r w) +
        ∑ t : I n, C₀.1 (t - 1) (r + 1) w := by
    simp only [triangleLeafE5BCoeff,
      triangleLeafE5BaseEmbed_apply, vecSum_scalarYEquiv,
      hz₀, Finset.sum_add_distrib]
  have hshift :
      (∑ t : I n, C₀.1 (t - 1) (r + 1) w) =
        ∑ t : I n, C₀.1 t (r + 1) w := by
    simpa only [cyclicInvShift_apply] using
      sum_cyclicInvShift
        (n := n) (fun t : I n => C₀.1 t (r + 1) w)
  change
    (∑ t : I n, C₀.1 t r w) +
        (∑ t : I n, C₀.1 t (r + 1) w) = 0
  rw [hexpand, hshift] at hpoint
  exact hpoint

private noncomputable def triangleLeafE5TwoFiberProfile
    {n : ℕ} [NeZero n] (s : NonzeroI n) :
    ZeroSumProfile n :=
  ⟨fun u =>
      (if u = s.1 then 1 else 0) +
        (if u = 0 then 1 else 0),
    by
      apply LinearMap.mem_ker.mpr
      change
        (∑ u : I n,
          ((if u = s.1 then 1 else 0) +
            if u = 0 then 1 else 0)) = 0
      rw [Finset.sum_add_distrib]
      have hs :
          (∑ u : I n, if u = s.1 then (1 : F) else 0) = 1 := by
        rw [Finset.sum_eq_single s.1]
        · simp
        · intro u _ hu
          simp [hu]
        · simp
      have hzero :
          (∑ u : I n, if u = 0 then (1 : F) else 0) = 1 := by
        rw [Finset.sum_eq_single (0 : I n)]
        · simp
        · intro u _ hu
          simp [hu]
        · simp
      rw [hs, hzero]
      exact F_add_self _⟩

@[simp] private theorem triangleLeafE5TwoFiberProfile_apply
    {n : ℕ} [NeZero n] (s : NonzeroI n) (u : I n) :
    (triangleLeafE5TwoFiberProfile s).1 u =
      (if u = s.1 then 1 else 0) +
        (if u = 0 then 1 else 0) := rfl

theorem triangleLeafE5SemanticBaseCadm_mem_B2
    {n a c d : ℕ} [NeZero n] (hc : 0 < c)
    (C₀ : TriangleLeafE5SemanticBaseCadm n a c d) :
    let C₁ : TriangleLeafE5BaseB1 n d :=
      ⟨C₀.1, triangleLeafE5SemanticBaseCadm_mem_B1 hc C₀⟩
    triangleLeafE5B2Map C₁ = 0 := by
  let C : TriangleLeafE5Cadm n a c d :=
    ⟨triangleLeafE5BaseEmbed C₀.1, C₀.2⟩
  let C₁ : TriangleLeafE5BaseB1 n d :=
    ⟨C₀.1, triangleLeafE5SemanticBaseCadm_mem_B1 hc C₀⟩
  dsimp only
  funext s
  apply Subtype.ext
  funext t₀ r
  let z₀ : ZVec n c := vecSingle hc r
  let R : ZeroSumProfile n := triangleLeafE5TwoFiberProfile s
  let U : I n → ZVec n c → WVec n d → F :=
    fun t z w =>
      if t = t₀ ∧ z = z₀ then R.1 (vecSum w) else 0
  let RW : WCoeff n 1 c := fun y z =>
    ((if vecSum y = t₀ ∧ z = z₀ then (1 : F) else 0) +
      (if vecSum y + 1 = t₀ ∧ z = z₀ then (1 : F) else 0)) • R
  have hKBmem :
      KBMap (n := n) (a := a) (b := 1) (c := c) (d := d)
          (triangleLeafE5BAggregateTest U) ∈
        WDiffSpace (n := n) (b := 1) (c := c) (d := d) := by
    apply LinearMap.mem_range.mpr
    refine ⟨RW, ?_⟩
    funext y z w
    rw [KBMap_triangleLeafE5BAggregateTest]
    change
      (((if vecSum y = t₀ ∧ z = z₀ then (1 : F) else 0) +
            (if vecSum y + 1 = t₀ ∧ z = z₀ then (1 : F) else 0)) • R).1
          (vecSum w) =
        (if vecSum y = t₀ ∧ z = z₀ then R.1 (vecSum w) else 0) +
          (if vecSum y + 1 = t₀ ∧ z = z₀ then
            R.1 (vecSum w) else 0)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    have h₁ :
        (if vecSum y = t₀ ∧ z = z₀ then R.1 (vecSum w) else 0) =
          (if vecSum y = t₀ ∧ z = z₀ then (1 : F) else 0) *
            R.1 (vecSum w) := by
      by_cases h : vecSum y = t₀ ∧ z = z₀ <;> simp [h]
    have h₂ :
        (if vecSum y + 1 = t₀ ∧ z = z₀ then
            R.1 (vecSum w) else 0) =
          (if vecSum y + 1 = t₀ ∧ z = z₀ then (1 : F) else 0) *
            R.1 (vecSum w) := by
      by_cases h : vecSum y + 1 = t₀ ∧ z = z₀ <;> simp [h]
    rw [h₁, h₂]
    ring
  let YV : triangleLeafCompatibleSubmodule n a 1 c d :=
    ⟨(triangleLeafE5BAggregateTest U, 0), by
      apply (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := 1) (c := c) (d := d)
        (triangleLeafE5BAggregateTest U, 0)).mpr
      rw [LinearMap.map_zero, add_zero]
      exact hKBmem⟩
  let Y : triangleLeafBOnly n a 1 c d :=
    ⟨YV, by rfl⟩
  have hCadm :
      triangleLeafE5CadmMap C.1 = 0 :=
    LinearMap.mem_ker.mp C.2
  have hQ := DFunLike.congr_fun hCadm Y
  change
    Q1 (triangleLeafE5BAggregateTest U)
      (triangleLeafE5BaseEmbed C₀.1) = 0 at hQ
  rw [Q1_triangleLeafE5BAggregateTest] at hQ
  have hz₀ : vecSum z₀ = r := vecSum_vecSingle hc r
  have hweighted :
      (∑ w : WVec n d,
        R.1 (vecSum w) *
          triangleLeafE5BCoeff
            (triangleLeafE5BaseEmbed (a := a) C₀.1)
            (zeroVec : PVec n a) t₀ z₀ w) = 0 := by
    classical
    simp only [U, ite_mul, zero_mul] at hQ
    calc
      (∑ w : WVec n d,
        R.1 (vecSum w) *
          triangleLeafE5BCoeff
            (triangleLeafE5BaseEmbed (a := a) C₀.1)
            (zeroVec : PVec n a) t₀ z₀ w)
          =
        ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
          if t = t₀ ∧ z = z₀ then
            R.1 (vecSum w) *
              triangleLeafE5BCoeff
                (triangleLeafE5BaseEmbed (a := a) C₀.1)
                (zeroVec : PVec n a) t z w
          else 0 := by
            rw [Finset.sum_eq_single t₀]
            · rw [Finset.sum_eq_single z₀]
              · simp
              · intro z _ hz
                simp [hz]
              · simp
            · intro t _ ht
              simp [ht]
            · simp
      _ = 0 := hQ
  change
    triangleLeafE5KtrDiagDiff
        (triangleLeafE5B2AggregateMap C₁ s) t₀ r = 0
  change
    (triangleLeafE5WFiberSum C₀.1 t₀ r s.1 +
        triangleLeafE5WFiberSum C₀.1 t₀ r 0) +
      (triangleLeafE5WFiberSum C₀.1 (t₀ - 1) (r + 1) s.1 +
        triangleLeafE5WFiberSum C₀.1 (t₀ - 1) (r + 1) 0) = 0
  have hweightedD :
      (∑ w : WVec n d,
        R.1 (vecSum w) *
          (C₀.1 t₀ r w +
            C₀.1 (t₀ - 1) (r + 1) w)) = 0 := by
    simpa only [triangleLeafE5BCoeff,
      triangleLeafE5BaseEmbed_apply, vecSum_scalarYEquiv,
      hz₀] using hweighted
  classical
  unfold triangleLeafE5WFiberSum
  calc
    ((∑ w : WVec n d,
          if vecSum w = s.1 then C₀.1 t₀ r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then C₀.1 t₀ r w else 0)) +
      ((∑ w : WVec n d,
          if vecSum w = s.1 then
            C₀.1 (t₀ - 1) (r + 1) w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            C₀.1 (t₀ - 1) (r + 1) w else 0))
        =
      ((∑ w : WVec n d,
          if vecSum w = s.1 then C₀.1 t₀ r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = s.1 then
            C₀.1 (t₀ - 1) (r + 1) w else 0)) +
      ((∑ w : WVec n d,
          if vecSum w = 0 then C₀.1 t₀ r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            C₀.1 (t₀ - 1) (r + 1) w else 0)) := by
              abel
    _ =
      (∑ w : WVec n d,
        if vecSum w = s.1 then
          C₀.1 t₀ r w + C₀.1 (t₀ - 1) (r + 1) w
        else 0) +
      (∑ w : WVec n d,
        if vecSum w = 0 then
          C₀.1 t₀ r w + C₀.1 (t₀ - 1) (r + 1) w
        else 0) := by
          rw [← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib]
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro w _
            by_cases hw : vecSum w = s.1 <;> simp [hw]
          · refine Finset.sum_congr rfl ?_
            intro w _
            by_cases hw : vecSum w = 0 <;> simp [hw]
    _ =
      ∑ w : WVec n d,
        R.1 (vecSum w) *
          (C₀.1 t₀ r w +
            C₀.1 (t₀ - 1) (r + 1) w) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro w _
          simp only [R, triangleLeafE5TwoFiberProfile_apply]
          let D :=
            C₀.1 t₀ r w + C₀.1 (t₀ - 1) (r + 1) w
          have hsMul :
              (if vecSum w = s.1 then D else 0) =
                (if vecSum w = s.1 then (1 : F) else 0) * D := by
            by_cases hs : vecSum w = s.1 <;> simp [hs]
          have hzeroMul :
              (if vecSum w = 0 then D else 0) =
                (if vecSum w = 0 then (1 : F) else 0) * D := by
            by_cases hzero : vecSum w = 0 <;> simp [hzero]
          change
            (if vecSum w = s.1 then D else 0) +
                (if vecSum w = 0 then D else 0) =
              ((if vecSum w = s.1 then (1 : F) else 0) +
                (if vecSum w = 0 then (1 : F) else 0)) * D
          rw [hsMul, hzeroMul]
          ring
    _ = 0 := hweightedD

noncomputable def triangleLeafE5SemanticBaseToBaseCadm
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) :
    TriangleLeafE5SemanticBaseCadm n a c d →ₗ[F]
      TriangleLeafE5BaseCadm n d where
  toFun C₀ :=
    ⟨⟨C₀.1, triangleLeafE5SemanticBaseCadm_mem_B1 hc C₀⟩,
      by
        simpa only using
          triangleLeafE5SemanticBaseCadm_mem_B2 hc C₀⟩
  map_add' C₀ D₀ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' x C₀ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def triangleLeafE5BaseD0
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseC n d)
    (t r : I n) (w : WVec n d) : F :=
  C₀ t r w + C₀ (t - 1) (r + 1) w

theorem triangleLeafE5BCoeff_baseEmbed
    {n a c d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseC n d)
    (p : PVec n a) (t : I n) (z : ZVec n c) (w : WVec n d) :
    triangleLeafE5BCoeff
        (triangleLeafE5BaseEmbed (a := a) C₀) p t z w =
      triangleLeafE5BaseD0 C₀ t (vecSum z) w := by
  simp [triangleLeafE5BCoeff, triangleLeafE5BaseD0]

theorem triangleLeafE5BaseD0_sum_eq_zero
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseB1 n d)
    (r : I n) (w : WVec n d) :
    (∑ t : I n, triangleLeafE5BaseD0 C₀.1 t r w) = 0 := by
  have hB1 :
      triangleLeafE5B1Map C₀.1 = 0 :=
    LinearMap.mem_ker.mp C₀.2
  have hpoint :=
    congrFun (congrArg Subtype.val (congrFun hB1 w)) r
  change
    (∑ t : I n, C₀.1 t r w) +
      (∑ t : I n, C₀.1 t (r + 1) w) = 0 at hpoint
  have hshift :
      (∑ t : I n, C₀.1 (t - 1) (r + 1) w) =
        ∑ t : I n, C₀.1 t (r + 1) w := by
    simpa only [cyclicInvShift_apply] using
      sum_cyclicInvShift
        (n := n) (fun t : I n => C₀.1 t (r + 1) w)
  unfold triangleLeafE5BaseD0
  rw [Finset.sum_add_distrib, hshift]
  exact hpoint

noncomputable def triangleLeafE5BaseDProfile
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseB1 n d)
    (r : I n) (w : WVec n d) :
    ZeroSumProfile n :=
  ⟨fun t => triangleLeafE5BaseD0 C₀.1 t r w,
    LinearMap.mem_ker.mpr
      (triangleLeafE5BaseD0_sum_eq_zero C₀ r w)⟩

noncomputable def triangleLeafE5BaseH0
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseB1 n d) :
    TriangleLeafE5BaseC n d :=
  fun t r w =>
    explicitCyclicPrimitive n
      (triangleLeafE5BaseDProfile C₀ r w) (t + 1)

theorem triangleLeafE5BaseH0_backwardDiff
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseB1 n d)
    (t r : I n) (w : WVec n d) :
    triangleLeafE5BaseH0 C₀ t r w +
        triangleLeafE5BaseH0 C₀ (t - 1) r w =
      triangleLeafE5BaseD0 C₀.1 t r w := by
  have hprimitive :=
    congrFun
      (cycDiff_explicitCyclicPrimitive
        (triangleLeafE5BaseDProfile C₀ r w)) t
  change
    explicitCyclicPrimitive n
          (triangleLeafE5BaseDProfile C₀ r w) (t + 1) +
        explicitCyclicPrimitive n
          (triangleLeafE5BaseDProfile C₀ r w) ((t - 1) + 1) =
      triangleLeafE5BaseD0 C₀.1 t r w
  simpa [add_comm] using hprimitive

theorem triangleLeafE5BaseCadm_B2_raw
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseCadm n d)
    (s : NonzeroI n) (t r : I n) :
    triangleLeafE5WFiberSum
          (triangleLeafE5BaseD0 C₀.1.1) t r s.1 +
        triangleLeafE5WFiberSum
          (triangleLeafE5BaseD0 C₀.1.1) t r 0 = 0 := by
  have hB2 :
      triangleLeafE5B2Map C₀.1 = 0 :=
    LinearMap.mem_ker.mp C₀.2
  have hs := congrFun hB2 s
  have hsval := congrArg Subtype.val hs
  have hpoint := congrFun (congrFun hsval t) r
  change
    (triangleLeafE5WFiberSum C₀.1.1 t r s.1 +
        triangleLeafE5WFiberSum C₀.1.1 t r 0) +
      (triangleLeafE5WFiberSum C₀.1.1 (t - 1) (r + 1) s.1 +
        triangleLeafE5WFiberSum C₀.1.1 (t - 1) (r + 1) 0) = 0 at hpoint
  unfold triangleLeafE5WFiberSum triangleLeafE5BaseD0
  calc
    (∑ w : WVec n d,
        if vecSum w = s.1 then
          C₀.1.1 t r w + C₀.1.1 (t - 1) (r + 1) w
        else 0) +
      (∑ w : WVec n d,
        if vecSum w = 0 then
          C₀.1.1 t r w + C₀.1.1 (t - 1) (r + 1) w
        else 0)
        =
      ((∑ w : WVec n d,
          if vecSum w = s.1 then C₀.1.1 t r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = s.1 then
            C₀.1.1 (t - 1) (r + 1) w else 0)) +
      ((∑ w : WVec n d,
          if vecSum w = 0 then C₀.1.1 t r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            C₀.1.1 (t - 1) (r + 1) w else 0)) := by
          congr 1 <;>
            rw [← Finset.sum_add_distrib] <;>
            apply Finset.sum_congr rfl <;>
            intro w _ <;>
            split <;> simp_all
    _ =
      ((∑ w : WVec n d,
          if vecSum w = s.1 then C₀.1.1 t r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then C₀.1.1 t r w else 0)) +
      ((∑ w : WVec n d,
          if vecSum w = s.1 then
            C₀.1.1 (t - 1) (r + 1) w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            C₀.1.1 (t - 1) (r + 1) w else 0)) := by
          abel
    _ = 0 := hpoint

noncomputable def triangleLeafE5BaseH0Discrepancy
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseCadm n d)
    (s : NonzeroI n) (t r : I n) : F :=
  triangleLeafE5WFiberSum
      (triangleLeafE5BaseH0 C₀.1) t r s.1 +
    triangleLeafE5WFiberSum
      (triangleLeafE5BaseH0 C₀.1) t r 0

theorem triangleLeafE5BaseH0Discrepancy_backwardDiff
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseCadm n d)
    (s : NonzeroI n) (t r : I n) :
    triangleLeafE5BaseH0Discrepancy C₀ s t r +
        triangleLeafE5BaseH0Discrepancy C₀ s (t - 1) r = 0 := by
  rw [show
    triangleLeafE5BaseH0Discrepancy C₀ s t r +
          triangleLeafE5BaseH0Discrepancy C₀ s (t - 1) r
        =
      (triangleLeafE5WFiberSum
          (triangleLeafE5BaseD0 C₀.1.1) t r s.1 +
        triangleLeafE5WFiberSum
          (triangleLeafE5BaseD0 C₀.1.1) t r 0) by
    unfold triangleLeafE5BaseH0Discrepancy
    unfold triangleLeafE5WFiberSum
    calc
      ((∑ w : WVec n d,
          if vecSum w = s.1 then
            triangleLeafE5BaseH0 C₀.1 t r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            triangleLeafE5BaseH0 C₀.1 t r w else 0)) +
      ((∑ w : WVec n d,
          if vecSum w = s.1 then
            triangleLeafE5BaseH0 C₀.1 (t - 1) r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            triangleLeafE5BaseH0 C₀.1 (t - 1) r w else 0))
          =
        (∑ w : WVec n d,
          if vecSum w = s.1 then
            (triangleLeafE5BaseH0 C₀.1 t r w +
              triangleLeafE5BaseH0 C₀.1 (t - 1) r w)
          else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            (triangleLeafE5BaseH0 C₀.1 t r w +
              triangleLeafE5BaseH0 C₀.1 (t - 1) r w)
          else 0) := by
            calc
              ((∑ w : WVec n d,
                  if vecSum w = s.1 then
                    triangleLeafE5BaseH0 C₀.1 t r w else 0) +
                (∑ w : WVec n d,
                  if vecSum w = 0 then
                    triangleLeafE5BaseH0 C₀.1 t r w else 0)) +
              ((∑ w : WVec n d,
                  if vecSum w = s.1 then
                    triangleLeafE5BaseH0 C₀.1 (t - 1) r w else 0) +
                (∑ w : WVec n d,
                  if vecSum w = 0 then
                    triangleLeafE5BaseH0 C₀.1 (t - 1) r w else 0))
                  =
                ((∑ w : WVec n d,
                    if vecSum w = s.1 then
                      triangleLeafE5BaseH0 C₀.1 t r w else 0) +
                  (∑ w : WVec n d,
                    if vecSum w = s.1 then
                      triangleLeafE5BaseH0 C₀.1 (t - 1) r w else 0)) +
                ((∑ w : WVec n d,
                    if vecSum w = 0 then
                      triangleLeafE5BaseH0 C₀.1 t r w else 0) +
                  (∑ w : WVec n d,
                    if vecSum w = 0 then
                      triangleLeafE5BaseH0 C₀.1 (t - 1) r w else 0)) := by
                        abel
              _ = _ := by
                congr 1
                · rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro w _
                  by_cases hw : vecSum w = s.1 <;> simp [hw]
                · rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro w _
                  by_cases hw : vecSum w = 0 <;> simp [hw]
      _ =
        (∑ w : WVec n d,
          if vecSum w = s.1 then
            triangleLeafE5BaseD0 C₀.1.1 t r w else 0) +
        (∑ w : WVec n d,
          if vecSum w = 0 then
            triangleLeafE5BaseD0 C₀.1.1 t r w else 0) := by
              congr 1 <;>
                apply Finset.sum_congr rfl <;>
                intro w _ <;>
                split <;> simp_all only
                  [triangleLeafE5BaseH0_backwardDiff]
      _ = _ := rfl]
  exact triangleLeafE5BaseCadm_B2_raw C₀ s t r

theorem triangleLeafE5BaseH0Discrepancy_constant
    {n d : ℕ} [NeZero n]
    (C₀ : TriangleLeafE5BaseCadm n d)
    (s : NonzeroI n) (t r : I n) :
    triangleLeafE5BaseH0Discrepancy C₀ s t r =
      triangleLeafE5BaseH0Discrepancy C₀ s 0 r := by
  let K : Profile n :=
    fun u => triangleLeafE5BaseH0Discrepancy C₀ s u r
  have hzero : cycDiff (n := n) F K = 0 := by
    funext u
    have hback :=
      triangleLeafE5BaseH0Discrepancy_backwardDiff
        C₀ s (u + 1) r
    change
      K (u + 1) + K ((u + 1) - 1) = 0 at hback
    change K u + K (u + 1) = 0
    simpa [add_comm] using hback
  exact (cycDiff_eq_zero_iff_constant_apply F K).mp hzero t

noncomputable def triangleLeafE5BaseHCorr
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d) :
    TriangleLeafE5BaseC n d :=
  fun _t r w =>
    if hzero : vecSum w = 0 then 0
    else if w = vecSingle hd (vecSum w) then
      triangleLeafE5BaseH0Discrepancy
        C₀ ⟨vecSum w, hzero⟩ 0 r
    else 0

theorem triangleLeafE5BaseHCorr_backwardDiff
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d)
    (t r : I n) (w : WVec n d) :
    triangleLeafE5BaseHCorr hd C₀ t r w +
        triangleLeafE5BaseHCorr hd C₀ (t - 1) r w = 0 := by
  unfold triangleLeafE5BaseHCorr
  by_cases hzero : vecSum w = 0
  · simp [hzero]
  · by_cases hrep : w = vecSingle hd (vecSum w)
    · simp only [dif_neg hzero, if_pos hrep]
      exact F_add_self _
    · simp [hzero, hrep]

noncomputable def triangleLeafE5BaseH
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d) :
    TriangleLeafE5BaseC n d :=
  triangleLeafE5BaseH0 C₀.1 +
    triangleLeafE5BaseHCorr hd C₀

theorem triangleLeafE5BaseH_backwardDiff
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d)
    (t r : I n) (w : WVec n d) :
    triangleLeafE5BaseH hd C₀ t r w +
        triangleLeafE5BaseH hd C₀ (t - 1) r w =
      triangleLeafE5BaseD0 C₀.1.1 t r w := by
  change
    (triangleLeafE5BaseH0 C₀.1 t r w +
        triangleLeafE5BaseHCorr hd C₀ t r w) +
      (triangleLeafE5BaseH0 C₀.1 (t - 1) r w +
        triangleLeafE5BaseHCorr hd C₀ (t - 1) r w) =
    triangleLeafE5BaseD0 C₀.1.1 t r w
  calc
    (triangleLeafE5BaseH0 C₀.1 t r w +
        triangleLeafE5BaseHCorr hd C₀ t r w) +
      (triangleLeafE5BaseH0 C₀.1 (t - 1) r w +
        triangleLeafE5BaseHCorr hd C₀ (t - 1) r w)
        =
      (triangleLeafE5BaseH0 C₀.1 t r w +
        triangleLeafE5BaseH0 C₀.1 (t - 1) r w) +
      (triangleLeafE5BaseHCorr hd C₀ t r w +
        triangleLeafE5BaseHCorr hd C₀ (t - 1) r w) := by
          abel
    _ = triangleLeafE5BaseD0 C₀.1.1 t r w := by
      rw [triangleLeafE5BaseH0_backwardDiff,
        triangleLeafE5BaseHCorr_backwardDiff, add_zero]

theorem triangleLeafE5WFiberSum_BaseHCorr_nonzero
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d)
    (s : NonzeroI n) (t r : I n) :
    triangleLeafE5WFiberSum
        (triangleLeafE5BaseHCorr hd C₀) t r s.1 =
      triangleLeafE5BaseH0Discrepancy C₀ s 0 r := by
  classical
  unfold triangleLeafE5WFiberSum
  rw [Finset.sum_eq_single (vecSingle hd s.1)]
  · rw [if_pos (vecSum_vecSingle hd s.1)]
    simp only [triangleLeafE5BaseHCorr,
      vecSum_vecSingle hd s.1, s.2, if_pos]
    rfl
  · intro w _ hw
    by_cases hsum : vecSum w = s.1
    · have hzero : vecSum w ≠ 0 := by
        simpa [hsum] using s.2
      have hrep : w ≠ vecSingle hd (vecSum w) := by
        intro h
        apply hw
        simpa [hsum] using h
      simp only [hsum, if_pos]
      simp [triangleLeafE5BaseHCorr, hzero, hrep]
    · simp [hsum]
  · simp

theorem triangleLeafE5WFiberSum_BaseHCorr_zero
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d)
    (t r : I n) :
    triangleLeafE5WFiberSum
        (triangleLeafE5BaseHCorr hd C₀) t r 0 = 0 := by
  classical
  unfold triangleLeafE5WFiberSum
  refine Finset.sum_eq_zero ?_
  intro w _
  by_cases hzero : vecSum w = 0
  · simp [hzero, triangleLeafE5BaseHCorr]
  · simp [hzero]

theorem triangleLeafE5WFiberSum_add
    {n d : ℕ} [NeZero n]
    (C D : TriangleLeafE5BaseC n d)
    (t r s : I n) :
    triangleLeafE5WFiberSum (C + D) t r s =
      triangleLeafE5WFiberSum C t r s +
        triangleLeafE5WFiberSum D t r s := by
  classical
  unfold triangleLeafE5WFiberSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro w _
  by_cases hw : vecSum w = s <;> simp [hw]

theorem triangleLeafE5BaseH_fiber_eq_zeroFiber
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d)
    (s t r : I n) :
    triangleLeafE5WFiberSum
        (triangleLeafE5BaseH hd C₀) t r s =
      triangleLeafE5WFiberSum
        (triangleLeafE5BaseH hd C₀) t r 0 := by
  by_cases hzero : s = 0
  · rw [hzero]
  · let s₀ : NonzeroI n := ⟨s, hzero⟩
    rw [show
      triangleLeafE5BaseH hd C₀ =
        triangleLeafE5BaseH0 C₀.1 +
          triangleLeafE5BaseHCorr hd C₀ by rfl]
    rw [triangleLeafE5WFiberSum_add,
      triangleLeafE5WFiberSum_add,
      triangleLeafE5WFiberSum_BaseHCorr_nonzero
        hd C₀ s₀ t r,
      triangleLeafE5WFiberSum_BaseHCorr_zero]
    have hconst :=
      triangleLeafE5BaseH0Discrepancy_constant
        C₀ s₀ t r
    change
      triangleLeafE5WFiberSum
            (triangleLeafE5BaseH0 C₀.1) t r s +
          triangleLeafE5BaseH0Discrepancy C₀ s₀ 0 r =
      triangleLeafE5WFiberSum
            (triangleLeafE5BaseH0 C₀.1) t r 0 + 0
    rw [← hconst]
    unfold triangleLeafE5BaseH0Discrepancy
    change
      triangleLeafE5WFiberSum
            (triangleLeafE5BaseH0 C₀.1) t r s +
          (triangleLeafE5WFiberSum
              (triangleLeafE5BaseH0 C₀.1) t r s +
            triangleLeafE5WFiberSum
              (triangleLeafE5BaseH0 C₀.1) t r 0) =
        triangleLeafE5WFiberSum
            (triangleLeafE5BaseH0 C₀.1) t r 0 + 0
    rw [← add_assoc, F_add_self, zero_add, add_zero]

theorem triangleLeafE5BaseH_WOrth
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d)
    (R : ZeroSumProfile n) (t r : I n) :
    (∑ w : WVec n d,
        R.1 (vecSum w) * triangleLeafE5BaseH hd C₀ t r w) = 0 := by
  classical
  calc
    (∑ w : WVec n d,
        R.1 (vecSum w) * triangleLeafE5BaseH hd C₀ t r w)
        =
      ∑ w : WVec n d, ∑ s : I n,
        if vecSum w = s then
          R.1 s * triangleLeafE5BaseH hd C₀ t r w
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro w _
          rw [Finset.sum_eq_single (vecSum w)]
          · simp
          · intro s _ hs
            simp [Ne.symm hs]
          · simp
    _ =
      ∑ s : I n, ∑ w : WVec n d,
        if vecSum w = s then
          R.1 s * triangleLeafE5BaseH hd C₀ t r w
        else 0 := by
          rw [Finset.sum_comm]
    _ =
      ∑ s : I n,
        R.1 s *
          triangleLeafE5WFiberSum
            (triangleLeafE5BaseH hd C₀) t r s := by
          refine Finset.sum_congr rfl ?_
          intro s _
          unfold triangleLeafE5WFiberSum
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro w _
          by_cases hw : vecSum w = s <;> simp [hw]
    _ =
      ∑ s : I n,
        R.1 s *
          triangleLeafE5WFiberSum
            (triangleLeafE5BaseH hd C₀) t r 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [triangleLeafE5BaseH_fiber_eq_zeroFiber hd C₀ s t r]
    _ =
      (∑ s : I n, R.1 s) *
        triangleLeafE5WFiberSum
          (triangleLeafE5BaseH hd C₀) t r 0 := by
            rw [Finset.sum_mul]
    _ = 0 := by
      have hsum :
          (∑ s : I n, R.1 s) = 0 :=
        LinearMap.mem_ker.mp R.2
      rw [hsum, zero_mul]

theorem triangleLeafE5BaseCadm_baseEmbed_mem_Cadm
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseCadm n d) :
    triangleLeafE5BaseEmbed (a := a) C₀.1.1 ∈
      TriangleLeafE5Cadm n a c d := by
  apply LinearMap.mem_ker.mpr
  ext Y
  let B : BFun4 n a c d := Y.1.1.1
  let U : I n → ZVec n c → WVec n d → F :=
    fun t z w => ∑ p : PVec n a, B p t z w
  have hC : Y.1.1.2 = 0 := by
    have h := LinearMap.mem_ker.mp Y.2
    change Y.1.1.2 = 0 at h
    exact h
  have hKB :
      KBMap (n := n) (a := a) (b := 1) (c := c) (d := d) B ∈
        WDiffSpace (n := n) (b := 1) (c := c) (d := d) := by
    have hcompat :=
      (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := 1) (c := c) (d := d)
        Y.1.1).mp Y.1.2
    change
      KBMap (n := n) (a := a) (b := 1) (c := c) (d := d) B +
          KCMap (n := n) (a := a) (b := 1) (c := c) (d := d)
            Y.1.1.2
        ∈ WDiffSpace (n := n) (b := 1) (c := c) (d := d) at hcompat
    rw [hC, LinearMap.map_zero, add_zero] at hcompat
    exact hcompat
  rcases hKB with ⟨R, hR⟩
  have hForward (t : I n) (z : ZVec n c) (w : WVec n d) :
      U t z w + U (t + 1) z w =
        (R (triangleLeafE5YOf t) z).1 (vecSum w) := by
    have hpoint :=
      congrFun
        (congrFun
          (congrFun hR (triangleLeafE5YOf t)) z) w
    change
      (R (triangleLeafE5YOf t) z).1 (vecSum w) =
        ∑ p : PVec n a,
          dyB B p (triangleLeafE5YOf t) z w at hpoint
    simp only [dyB, betaB, gammaB, vecSum_scalarYEquiv] at hpoint
    change
      (R (triangleLeafE5YOf t) z).1 (vecSum w) =
        ∑ p : PVec n a,
          (B p t z w + B p (t + 1) z w) at hpoint
    rw [Finset.sum_add_distrib] at hpoint
    exact hpoint.symm
  have hParts (z : ZVec n c) (w : WVec n d) :
      (∑ t : I n,
          U t z w *
            triangleLeafE5BaseD0 C₀.1.1 t (vecSum z) w)
        =
      ∑ t : I n,
        (U t z w + U (t + 1) z w) *
          triangleLeafE5BaseH hd C₀ t (vecSum z) w := by
    have hp :=
      cycDiff_pairing_adjoint
        (fun t : I n => U t z w)
        (fun t : I n =>
          triangleLeafE5BaseH hd C₀ t (vecSum z) w)
    simpa only [cycDiff_apply, cyclicBackwardDiff_apply,
      triangleLeafE5BaseH_backwardDiff] using hp.symm
  change Q1 B (triangleLeafE5BaseEmbed (a := a) C₀.1.1) = 0
  rw [Q1_eq_sum_B_mul_triangleLeafE5BCoeff]
  simp_rw [triangleLeafE5BCoeff_baseEmbed]
  calc
    (∑ p : PVec n a, ∑ t : I n, ∑ z : ZVec n c,
        ∑ w : WVec n d,
          B p t z w *
            triangleLeafE5BaseD0 C₀.1.1 t (vecSum z) w)
        =
      ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        U t z w *
          triangleLeafE5BaseD0 C₀.1.1 t (vecSum z) w := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro t _
            calc
              (∑ p : PVec n a, ∑ z : ZVec n c,
                  ∑ w : WVec n d,
                    B p t z w *
                      triangleLeafE5BaseD0
                        C₀.1.1 t (vecSum z) w)
                  =
                ∑ z : ZVec n c, ∑ p : PVec n a,
                  ∑ w : WVec n d,
                    B p t z w *
                      triangleLeafE5BaseD0
                        C₀.1.1 t (vecSum z) w := by
                          rw [Finset.sum_comm]
              _ =
                ∑ z : ZVec n c, ∑ w : WVec n d,
                  ∑ p : PVec n a,
                    B p t z w *
                      triangleLeafE5BaseD0
                        C₀.1.1 t (vecSum z) w := by
                          refine Finset.sum_congr rfl ?_
                          intro z _
                          rw [Finset.sum_comm]
              _ =
                ∑ z : ZVec n c, ∑ w : WVec n d,
                  U t z w *
                    triangleLeafE5BaseD0
                      C₀.1.1 t (vecSum z) w := by
                        refine Finset.sum_congr rfl ?_
                        intro z _
                        refine Finset.sum_congr rfl ?_
                        intro w _
                        unfold U
                        rw [Finset.sum_mul]
    _ =
      ∑ z : ZVec n c, ∑ w : WVec n d, ∑ t : I n,
        U t z w *
          triangleLeafE5BaseD0 C₀.1.1 t (vecSum z) w := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [Finset.sum_comm]
    _ =
      ∑ z : ZVec n c, ∑ w : WVec n d, ∑ t : I n,
        (U t z w + U (t + 1) z w) *
          triangleLeafE5BaseH hd C₀ t (vecSum z) w := by
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            exact hParts z w
    _ =
      ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        (U t z w + U (t + 1) z w) *
          triangleLeafE5BaseH hd C₀ t (vecSum z) w := by
            calc
              (∑ z : ZVec n c, ∑ w : WVec n d, ∑ t : I n,
                  (U t z w + U (t + 1) z w) *
                    triangleLeafE5BaseH hd C₀ t (vecSum z) w)
                  =
                ∑ z : ZVec n c, ∑ t : I n, ∑ w : WVec n d,
                  (U t z w + U (t + 1) z w) *
                    triangleLeafE5BaseH hd C₀ t (vecSum z) w := by
                          refine Finset.sum_congr rfl ?_
                          intro z _
                          rw [Finset.sum_comm]
              _ = _ := by rw [Finset.sum_comm]
    _ =
      ∑ t : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        (R (triangleLeafE5YOf t) z).1 (vecSum w) *
          triangleLeafE5BaseH hd C₀ t (vecSum z) w := by
            refine Finset.sum_congr rfl ?_
            intro t _
            refine Finset.sum_congr rfl ?_
            intro z _
            refine Finset.sum_congr rfl ?_
            intro w _
            rw [hForward]
    _ = 0 := by
      refine Finset.sum_eq_zero ?_
      intro t _
      refine Finset.sum_eq_zero ?_
      intro z _
      exact
        triangleLeafE5BaseH_WOrth hd C₀
          (R (triangleLeafE5YOf t) z) t (vecSum z)

noncomputable def triangleLeafE5BaseCadmToSemanticBase
    {n a c d : ℕ} [NeZero n] (hd : 0 < d) :
    TriangleLeafE5BaseCadm n d →ₗ[F]
      TriangleLeafE5SemanticBaseCadm n a c d where
  toFun C₀ :=
    ⟨C₀.1.1, triangleLeafE5BaseCadm_baseEmbed_mem_Cadm hd C₀⟩
  map_add' C₀ D₀ := by
    apply Subtype.ext
    rfl
  map_smul' x C₀ := by
    apply Subtype.ext
    rfl

theorem mem_triangleLeafE5SemanticBaseCadm_iff_B1_B2
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (C₀ : TriangleLeafE5BaseC n d) :
    C₀ ∈ TriangleLeafE5SemanticBaseCadm n a c d ↔
      ∃ hB1 : triangleLeafE5B1Map C₀ = 0,
        triangleLeafE5B2Map
          (⟨C₀, hB1⟩ : TriangleLeafE5BaseB1 n d) = 0 := by
  constructor
  · intro hSemantic
    let Csem : TriangleLeafE5SemanticBaseCadm n a c d :=
      ⟨C₀, hSemantic⟩
    refine
      ⟨triangleLeafE5SemanticBaseCadm_mem_B1 hc Csem, ?_⟩
    simpa only using triangleLeafE5SemanticBaseCadm_mem_B2 hc Csem
  · rintro ⟨hB1, hB2⟩
    let Cbase : TriangleLeafE5BaseCadm n d :=
      ⟨⟨C₀, hB1⟩, hB2⟩
    exact triangleLeafE5BaseCadm_baseEmbed_mem_Cadm hd Cbase

noncomputable def triangleLeafE5SemanticBaseEquivBaseCadm
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    TriangleLeafE5SemanticBaseCadm n a c d ≃ₗ[F]
      TriangleLeafE5BaseCadm n d where
  toFun := triangleLeafE5SemanticBaseToBaseCadm hc
  invFun := triangleLeafE5BaseCadmToSemanticBase hd
  left_inv C₀ := by
    apply Subtype.ext
    rfl
  right_inv C₀ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' C₀ D₀ :=
    (triangleLeafE5SemanticBaseToBaseCadm hc).map_add C₀ D₀
  map_smul' x C₀ :=
    (triangleLeafE5SemanticBaseToBaseCadm hc).map_smul x C₀

theorem finrank_triangleLeafE5BaseC
    {n d : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5BaseC n d) =
      n ^ (d + 2) := by
  calc
    Module.finrank F (TriangleLeafE5BaseC n d)
        =
      ∑ _t : I n,
        Module.finrank F (I n → WVec n d → F) := by
          rw [Module.finrank_pi_fintype]
    _ =
      ∑ _t : I n, ∑ _r : I n,
        Module.finrank F (WVec n d → F) := by
          simp only [Module.finrank_pi_fintype]
    _ =
      ∑ _t : I n, ∑ _r : I n,
        Fintype.card (WVec n d) := by
          simp only [Module.finrank_fintype_fun_eq_card]
    _ = n * (n * n ^ d) := by
      simp [I, ZMod.card]
    _ = n ^ (d + 2) := by
      rw [pow_add]
      ring

theorem finrank_triangleLeafE5BaseB1
    {n d : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5BaseB1 n d) =
      n ^ (d + 2) - (n - 1) * n ^ d := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE5B1Map :
        TriangleLeafE5BaseC n d →ₗ[F] TriangleLeafE5B1Target n d)
  rw [finrank_range_triangleLeafE5B1Map,
    finrank_triangleLeafE5BaseC] at h
  apply Nat.eq_sub_of_add_eq
  simpa [Nat.add_comm] using h

theorem finrank_triangleLeafE5BaseCadm
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (TriangleLeafE5BaseCadm n d) =
      n ^ (d + 2) - (n - 1) * n ^ d - (n - 1) ^ 3 := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE5B2Map :
        TriangleLeafE5BaseB1 n d →ₗ[F] TriangleLeafE5B2Target n)
  rw [finrank_range_triangleLeafE5B2Map hd,
    finrank_triangleLeafE5BaseB1] at h
  apply Nat.eq_sub_of_add_eq
  simpa [Nat.add_comm] using h

theorem finrank_triangleLeafE5PointedFiber
    {n d : ℕ} [NeZero n] :
    Module.finrank F (I n → WVec n d → F) =
      n ^ (d + 1) := by
  calc
    Module.finrank F (I n → WVec n d → F)
        =
      ∑ _t : I n, Module.finrank F (WVec n d → F) := by
          rw [Module.finrank_pi_fintype]
    _ = ∑ _t : I n, Fintype.card (WVec n d) := by
          simp only [Module.finrank_fintype_fun_eq_card]
    _ = n * n ^ d := by
          simp [I, ZMod.card]
    _ = n ^ (d + 1) := by
          rw [pow_add]
          ring

theorem finrank_triangleLeafE5PointedPart
    {n a d : ℕ} [NeZero n] :
    Module.finrank F (TriangleLeafE5PointedPart n a d) =
      (n ^ (a - 1) - 1) * n ^ (d + 1) := by
  calc
    Module.finrank F (TriangleLeafE5PointedPart n a d)
        =
      ∑ _p : TriangleLeafE5NonzeroPVec n a,
        Module.finrank F (I n → WVec n d → F) := by
          rw [Module.finrank_pi_fintype]
    _ =
      ∑ _p : TriangleLeafE5NonzeroPVec n a,
        n ^ (d + 1) := by
          simp only [finrank_triangleLeafE5PointedFiber]
    _ =
      Fintype.card (TriangleLeafE5NonzeroPVec n a) *
        n ^ (d + 1) := by
          simp
    _ = (n ^ (a - 1) - 1) * n ^ (d + 1) := by
      congr 1
      classical
      calc
        Fintype.card (TriangleLeafE5NonzeroPVec n a)
            =
          Fintype.card (PVec n a) -
            Fintype.card
              {p : PVec n a // p = (zeroVec : PVec n a)} := by
                simp [Fintype.card_subtype_compl
                  (fun p : PVec n a => p = zeroVec)]
        _ = n ^ (a - 1) - 1 := by
          rw [Fintype.card_subtype_eq
            (zeroVec : PVec n a), card_vec]

theorem finrank_triangleLeafE5Cadm_expanded
    {n a c d : ℕ} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (TriangleLeafE5Cadm n a c d) =
      (n ^ (a - 1) - 1) * n ^ (d + 1) +
        (n ^ (d + 2) - (n - 1) * n ^ d - (n - 1) ^ 3) := by
  calc
    Module.finrank F (TriangleLeafE5Cadm n a c d)
        =
      Module.finrank F
        (TriangleLeafE5PointedPart n a d ×
          TriangleLeafE5SemanticBaseCadm n a c d) :=
            LinearEquiv.finrank_eq
              (triangleLeafE5CadmEquivCoordinates hc)
    _ =
      Module.finrank F (TriangleLeafE5PointedPart n a d) +
        Module.finrank F
          (TriangleLeafE5SemanticBaseCadm n a c d) := by
            rw [Module.finrank_prod]
    _ =
      (n ^ (a - 1) - 1) * n ^ (d + 1) +
        Module.finrank F (TriangleLeafE5BaseCadm n d) := by
          rw [finrank_triangleLeafE5PointedPart]
          congr 1
          exact
            LinearEquiv.finrank_eq
              (triangleLeafE5SemanticBaseEquivBaseCadm hc hd)
    _ = _ := by rw [finrank_triangleLeafE5BaseCadm hd]

theorem triangleLeafE5Cadm_rank_arithmetic
    {n a d : ℕ} [NeZero n]
    (ha2 : 2 ≤ a) (hd : 0 < d) :
    (n ^ (a - 1) - 1) * n ^ (d + 1) +
        (n ^ (d + 2) - (n - 1) * n ^ d - (n - 1) ^ 3) =
      n ^ (a + d) +
        (n - 1) ^ 2 * (n ^ d - (n - 1)) := by
  have hnpos : 0 < n :=
    Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : 1 ≤ n := by omega
  have hmnPow : n - 1 ≤ n ^ d := by
    have hpow : n ^ 1 ≤ n ^ d :=
      Nat.pow_le_pow_right hn1 hd
    exact (Nat.sub_le n 1).trans (by simpa using hpow)
  have hcube :
      (n - 1) ^ 3 ≤ (n - 1) ^ 2 * n ^ d := by
    have hmul :=
      Nat.mul_le_mul_left ((n - 1) ^ 2) hmnPow
    simpa [pow_succ] using hmul
  have hcancel :
      (n - 1) ^ 3 +
          ((n - 1) ^ 2 * n ^ d - (n - 1) ^ 3) =
        (n - 1) ^ 2 * n ^ d :=
    Nat.add_sub_of_le hcube
  have hX :
      (n - 1) ^ 3 +
          (n - 1) ^ 2 * (n ^ d - (n - 1)) =
        (n - 1) ^ 2 * n ^ d := by
    rw [Nat.mul_sub_left_distrib]
    have hpow3 :
        (n - 1) ^ 2 * (n - 1) = (n - 1) ^ 3 := by
      ring
    rw [hpow3]
    exact hcancel
  have hbasePoly :
      n ^ (d + 2) =
        n ^ (d + 1) + (n - 1) * n ^ d +
          (n - 1) ^ 2 * n ^ d := by
    rw [show n ^ (d + 2) = n ^ d * n ^ 2 by rw [pow_add]]
    rw [show n ^ (d + 1) = n ^ d * n by
      rw [pow_add]
      simp]
    let m : ℕ := n - 1
    have hnSplit : n = m + 1 := by
      dsimp [m]
      omega
    change
      n ^ d * n ^ 2 =
        n ^ d * n + m * n ^ d + m ^ 2 * n ^ d
    rw [hnSplit]
    ring
  let X : ℕ :=
    (n - 1) ^ 2 * (n ^ d - (n - 1))
  have hbasePartition :
      n ^ (d + 2) =
        n ^ (d + 1) + (n - 1) * n ^ d +
          (n - 1) ^ 3 + X := by
    dsimp [X]
    calc
      n ^ (d + 2) =
          n ^ (d + 1) + (n - 1) * n ^ d +
            (n - 1) ^ 2 * n ^ d := hbasePoly
      _ =
          n ^ (d + 1) + (n - 1) * n ^ d +
            ((n - 1) ^ 3 +
              (n - 1) ^ 2 * (n ^ d - (n - 1))) := by
                rw [hX]
      _ = _ := by ring
  have hbaseSub :
      n ^ (d + 2) - (n - 1) * n ^ d - (n - 1) ^ 3 =
        n ^ (d + 1) + X := by
    omega
  have hexp :
      (a - 1) + (d + 1) = a + d := by
    omega
  have hpointed :
      (n ^ (a - 1) - 1) * n ^ (d + 1) =
        n ^ (a + d) - n ^ (d + 1) := by
    rw [Nat.sub_mul, one_mul, ← pow_add, hexp]
  have hpowBound :
      n ^ (d + 1) ≤ n ^ (a + d) :=
    Nat.pow_le_pow_right hn1 (by omega)
  rw [hpointed, hbaseSub]
  dsimp [X]
  omega

theorem finrank_triangleLeafE5Cadm
    {n a c d : ℕ} [NeZero n]
    (ha2 : 2 ≤ a) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (TriangleLeafE5Cadm n a c d) =
      n ^ (a + d) +
        (n - 1) ^ 2 * (n ^ d - (n - 1)) := by
  rw [finrank_triangleLeafE5Cadm_expanded hc hd]
  exact triangleLeafE5Cadm_rank_arithmetic ha2 hd

noncomputable def bOnlyQuotientMap
    {n a b c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F]
      RootTarget n b c d ⧸
        WDiffSpace (n := n) (b := b) (c := c) (d := d) :=
  (Submodule.mkQ
      (WDiffSpace (n := n) (b := b) (c := c) (d := d))).comp
    (KBMap (n := n) (a := a) (b := b) (c := c) (d := d))

abbrev DirectB0 (n a b c d : ℕ) [NeZero n] :=
  LinearMap.ker
    (bOnlyQuotientMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def triangleLeafBOnlyEquivDirectB0
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafBOnly n a b c d ≃ₗ[F]
      DirectB0 n a b c d where
  toFun X :=
    ⟨X.1.1.1, by
      apply LinearMap.mem_ker.mpr
      rw [bOnlyQuotientMap, LinearMap.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hcompat :=
        (triangleLeafCompatibleSubmodule_carrier_iff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          X.1.1).mp X.1.2
      have hC : X.1.1.2 = 0 := by
        have hCmap := LinearMap.mem_ker.mp X.2
        change X.1.1.2 = 0 at hCmap
        exact hCmap
      rw [hC, LinearMap.map_zero, add_zero] at hcompat
      exact hcompat⟩
  invFun B :=
    ⟨⟨(B.1, 0), by
        apply (triangleLeafCompatibleSubmodule_carrier_iff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (B.1, 0)).mpr
        have hq :
            bOnlyQuotientMap
              (n := n) (a := a) (b := b) (c := c) (d := d) B.1 = 0 :=
          LinearMap.mem_ker.mp B.2
        rw [bOnlyQuotientMap, LinearMap.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
        simpa only [LinearMap.map_zero, add_zero] using hq⟩,
      by rfl⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hC := LinearMap.mem_ker.mp X.2
      change X.1.1.2 = 0 at hC
      exact hC.symm
  right_inv B := by
    apply Subtype.ext
    rfl
  map_add' X Y := by
    apply Subtype.ext
    rfl
  map_smul' x X := by
    apply Subtype.ext
    rfl

theorem finrank_triangleLeafBOnly_eq_directB0
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (triangleLeafBOnly n a b c d) =
      Module.finrank F (DirectB0 n a b c d) :=
  LinearEquiv.finrank_eq triangleLeafBOnlyEquivDirectB0

theorem range_bOnlyQuotientMap
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (bOnlyQuotientMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      Submodule.map
        (WDiffSpace
          (n := n) (b := b) (c := c) (d := d)).mkQ
        (YDiffSpace
          (n := n) (b := b) (c := c) (d := d)) := by
  rw [bOnlyQuotientMap, LinearMap.range_comp,
    range_KBMap_eq_YDiffSpace]

noncomputable def yToWQuotientMap
    {n b c d : ℕ} [NeZero n] :
    YDiffSpace (n := n) (b := b) (c := c) (d := d) →ₗ[F]
      RootTarget n b c d ⧸
        WDiffSpace (n := n) (b := b) (c := c) (d := d) :=
  (Submodule.mkQ
      (WDiffSpace (n := n) (b := b) (c := c) (d := d))).comp
    (YDiffSpace (n := n) (b := b) (c := c) (d := d)).subtype

theorem range_yToWQuotientMap
    {n b c d : ℕ} [NeZero n] :
    LinearMap.range
        (yToWQuotientMap
          (n := n) (b := b) (c := c) (d := d)) =
      Submodule.map
        (WDiffSpace
          (n := n) (b := b) (c := c) (d := d)).mkQ
        (YDiffSpace
          (n := n) (b := b) (c := c) (d := d)) := by
  rw [yToWQuotientMap, LinearMap.range_comp,
    Submodule.range_subtype]

noncomputable def kerYToWQuotientEquivInf
    {n b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (yToWQuotientMap
          (n := n) (b := b) (c := c) (d := d)) ≃ₗ[F]
      ↥(YDiffSpace
          (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace
          (n := n) (b := b) (c := c) (d := d)) where
  toFun X :=
    ⟨X.1.1, ⟨X.1.2, by
      have hq :
          (WDiffSpace
            (n := n) (b := b) (c := c) (d := d)).mkQ X.1.1 = 0 := by
        have hq0 := LinearMap.mem_ker.mp X.2
        change
          (WDiffSpace
            (n := n) (b := b) (c := c) (d := d)).mkQ X.1.1 = 0 at hq0
        exact hq0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      exact hq⟩⟩
  invFun X :=
    ⟨⟨X.1, X.2.1⟩, by
      apply LinearMap.mem_ker.mpr
      change
        (WDiffSpace
          (n := n) (b := b) (c := c) (d := d)).mkQ X.1 = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact X.2.2⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv X := by
    apply Subtype.ext
    rfl
  map_add' X Y := by
    apply Subtype.ext
    rfl
  map_smul' x X := by
    apply Subtype.ext
    rfl

theorem finrank_ker_yToWQuotientMap
    {n b c d : ℕ} [NeZero n] (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker
          (yToWQuotientMap
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) ^ 2 * n ^ c := by
  calc
    Module.finrank F
        (LinearMap.ker
          (yToWQuotientMap
            (n := n) (b := b) (c := c) (d := d))) =
      Module.finrank F
        ↥(YDiffSpace
            (n := n) (b := b) (c := c) (d := d) ⊓
          WDiffSpace
            (n := n) (b := b) (c := c) (d := d)) :=
        LinearEquiv.finrank_eq kerYToWQuotientEquivInf
    _ = (n - 1) ^ 2 * n ^ c :=
      finrank_inf_YW
        (n := n) (b := b) (c := c) (d := d) hb hd

theorem finrank_range_yToWQuotientMap
    {n b c d : ℕ} [NeZero n] (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (yToWQuotientMap
            (n := n) (b := b) (c := c) (d := d))) =
      (n - 1) * n ^ c * (n ^ d - (n - 1)) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (yToWQuotientMap
        (n := n) (b := b) (c := c) (d := d))
  rw [finrank_ker_yToWQuotientMap
      (n := n) (b := b) (c := c) (d := d) hb hd,
    finrank_YDiffSpace
      (n := n) (b := b) (c := c) (d := d) hb] at hnull
  have hsub :
      Module.finrank F
          (LinearMap.range
            (yToWQuotientMap
              (n := n) (b := b) (c := c) (d := d))) =
        (n - 1) * n ^ (c + d) - (n - 1) ^ 2 * n ^ c := by
    apply Nat.eq_sub_of_add_eq
    simpa [Nat.add_comm] using hnull
  rw [hsub, pow_add]
  calc
    (n - 1) * (n ^ c * n ^ d) - (n - 1) ^ 2 * n ^ c =
        ((n - 1) * n ^ c) * n ^ d -
          ((n - 1) * n ^ c) * (n - 1) := by
            rw [pow_two]
            congr 1 <;> ac_rfl
    _ = ((n - 1) * n ^ c) * (n ^ d - (n - 1)) := by
          exact
            (Nat.mul_sub_left_distrib
              ((n - 1) * n ^ c) (n ^ d) (n - 1)).symm
    _ = (n - 1) * n ^ c * (n ^ d - (n - 1)) := rfl

theorem finrank_range_bOnlyQuotientMap
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (bOnlyQuotientMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      (n - 1) * n ^ c * (n ^ d - (n - 1)) := by
  rw [range_bOnlyQuotientMap, ← range_yToWQuotientMap]
  exact finrank_range_yToWQuotientMap hb hd

theorem finrank_DirectB0
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F (DirectB0 n a b c d) =
      n ^ (a + c + d) -
        (n - 1) * n ^ c * (n ^ d - (n - 1)) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (bOnlyQuotientMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [finrank_range_bOnlyQuotientMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd,
    finrank_BFun4
      (n := n) (a := a) (c := c) (d := d) ha] at hnull
  apply Nat.eq_sub_of_add_eq
  simpa [Nat.add_comm] using hnull

theorem finrank_triangleLeafBOnly
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    Module.finrank F (triangleLeafBOnly n a b c d) =
      n ^ (a + c + d) -
        (n - 1) * n ^ c * (n ^ d - (n - 1)) := by
  rw [finrank_triangleLeafBOnly_eq_directB0,
    finrank_DirectB0 ha hb hd]

noncomputable def triangleLeafE5LBProjC
    {n a c d : ℕ} [NeZero n] :
    triangleLeafE5LB n a 1 c d →ₗ[F] CFun4 n a 1 d :=
  (triangleLeafCompatibleCProj
    (n := n) (a := a) (b := 1) (c := c) (d := d)).comp
      (triangleLeafE5LB n a 1 c d).subtype

@[simp] theorem triangleLeafE5LBProjC_apply
    {n a c d : ℕ} [NeZero n]
    (X : triangleLeafE5LB n a 1 c d) :
    triangleLeafE5LBProjC X = X.1.1.2 :=
  rfl

private theorem Q1_zero_right
    {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) :
    Q1 B (0 : CFun4 n a 1 d) = 0 := by
  unfold Q1 deltaC etaC
  simp

set_option synthInstance.maxHeartbeats 100000 in
-- Nested kernels require additional typeclass normalization.
noncomputable def triangleLeafE5LBProjC_ker_equiv_BOnly
    {n a c d : ℕ} [NeZero n] :
    LinearMap.ker
        (triangleLeafE5LBProjC
          (n := n) (a := a) (c := c) (d := d)) ≃ₗ[F]
      triangleLeafBOnly n a 1 c d where
  toFun X :=
    ⟨X.1.1, by
      change X.1.1.1.2 = 0
      exact X.2⟩
  invFun Y :=
    ⟨⟨Y.1, by
        apply LinearMap.mem_ker.mpr
        ext Z
        change
          Q1 Y.1.1.1 Z.1.1.2 +
              Q1 Z.1.1.1 Y.1.1.2 = 0
        have hY : Y.1.1.2 = 0 := Y.2
        have hZ : Z.1.1.2 = 0 := Z.2
        rw [hY, hZ, Q1_zero_right, Q1_zero_right, zero_add]⟩,
      by
        change Y.1.1.2 = 0
        exact Y.2⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv Y := by
    apply Subtype.ext
    rfl
  map_add' X Y := by
    rfl
  map_smul' x X := by
    rfl

theorem range_triangleLeafE5LBProjC_le_Cadm
    {n a c d : ℕ} [NeZero n] :
    LinearMap.range
        (triangleLeafE5LBProjC
          (n := n) (a := a) (c := c) (d := d)) ≤
      TriangleLeafE5Cadm n a c d := by
  intro C hC
  rcases hC with ⟨X, rfl⟩
  apply LinearMap.mem_ker.mpr
  ext Y
  have hpolar :
      triangleLeafBOnlyPolarMap
          (n := n) (a := a) (b := 1) (c := c) (d := d) X.1 = 0 :=
    LinearMap.mem_ker.mp X.2
  have hpoint := DFunLike.congr_fun hpolar Y
  change
    Q1 X.1.1.1 Y.1.1.2 + Q1 Y.1.1.1 X.1.1.2 = 0 at hpoint
  have hY : Y.1.1.2 = 0 := Y.2
  rw [hY, Q1_zero_right, zero_add] at hpoint
  exact hpoint

theorem triangleLeafE5Cadm_Cbar_diagonal
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d)
    (t r : I n) (w : WVec n d) :
    triangleLeafE5Cbar C.1 t r w =
      triangleLeafE5Cbar C.1 (t - 1) (r + 1) w := by
  let z : ZVec n c := vecSingle hc r
  have hz : vecSum z = r := vecSum_vecSingle hc r
  have hsum :
      (∑ p : PVec n a,
          triangleLeafE5BCoeff C.1 p t z w) =
        ∑ _p : PVec n a,
          triangleLeafE5BCoeff C.1 zeroVec t z w := by
    refine Finset.sum_congr rfl ?_
    intro p _
    exact triangleLeafE5Cadm_BCoeff_eq_zeroVec C p t z w
  have hcard :
      (Fintype.card (PVec n a) : F) = 0 := by
    exact natCast_card_vec_eq_zero_of_even_pos hn (by omega)
  have hrhs :
      (∑ _p : PVec n a,
          triangleLeafE5BCoeff C.1 zeroVec t z w) = 0 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change
      (Fintype.card (PVec n a) : F) *
          triangleLeafE5BCoeff C.1 zeroVec t z w = 0
    rw [hcard, zero_mul]
  rw [hrhs] at hsum
  change
    (∑ p : PVec n a,
        (C.1 p (triangleLeafE5YOf t) (vecSum z) w +
          C.1 p (triangleLeafE5YOf (t - 1))
            (vecSum z + 1) w)) = 0 at hsum
  rw [Finset.sum_add_distrib] at hsum
  change
    triangleLeafE5Cbar C.1 t (vecSum z) w +
      triangleLeafE5Cbar C.1 (t - 1) (vecSum z + 1) w = 0 at hsum
  rw [hz] at hsum
  exact (add_eq_zero_iff_eq_of_F_module _ _).mp hsum

theorem KBMap_triangleLeafE5BCLift_eq_KCMap_of_Cadm
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d) :
    KBMap (n := n) (a := a) (b := 1) (c := c) (d := d)
        (triangleLeafE5BCLift (c := c) C.1)
      =
    KCMap (n := n) (a := a) (b := 1) (c := c) (d := d)
        C.1 := by
  classical
  have hsum (t : I n) (z : ZVec n c) (w : WVec n d) :
      (∑ p : PVec n a,
          triangleLeafE5BCLift (c := c) C.1 p t z w) =
        triangleLeafE5Cbar C.1 t (vecSum z) w := by
    rw [Finset.sum_eq_single (zeroVec : PVec n a)]
    · simp [triangleLeafE5BCLift]
    · intro p _ hp
      simp [triangleLeafE5BCLift, hp]
    · simp
  funext y z w
  let t : I n := vecSum y
  let r : I n := vecSum z
  have hy : triangleLeafE5YOf t = y := by
    have h := (scalarYEquiv (n := n)).apply_symm_apply y
    change triangleLeafE5YOf (y 0) = y at h
    have hsumY : vecSum y = y 0 := by simp [vecSum]
    dsimp [t]
    rw [hsumY]
    exact h
  have hstep :
      triangleLeafE5Cbar C.1 (t + 1) r w =
        triangleLeafE5Cbar C.1 t (r + 1) w := by
    have h :=
      triangleLeafE5Cadm_Cbar_diagonal hn ha2 hc C (t + 1) r w
    simpa [sub_eq_add_neg, add_assoc] using h
  change
    (∑ p : PVec n a,
      (triangleLeafE5BCLift (c := c) C.1 p t z w +
        triangleLeafE5BCLift (c := c) C.1 p (t + 1) z w))
      =
    ∑ p : PVec n a,
      (C.1 p y r w + C.1 p y (r + 1) w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsum, hsum]
  change
    triangleLeafE5Cbar C.1 t r w +
        triangleLeafE5Cbar C.1 (t + 1) r w =
      (∑ p : PVec n a, C.1 p y r w) +
        ∑ p : PVec n a, C.1 p y (r + 1) w
  rw [hstep]
  simp only [triangleLeafE5Cbar, hy]

noncomputable def triangleLeafE5CadmCompatibleLift
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d) :
    triangleLeafCompatibleSubmodule n a 1 c d :=
  ⟨(triangleLeafE5BCLift (c := c) C.1, C.1), by
    apply (triangleLeafCompatibleSubmodule_carrier_iff
      (n := n) (a := a) (b := 1) (c := c) (d := d)
      (triangleLeafE5BCLift (c := c) C.1, C.1)).mpr
    rw [KBMap_triangleLeafE5BCLift_eq_KCMap_of_Cadm hn ha2 hc C]
    rw [(add_eq_zero_iff_eq_of_F_module _ _).mpr rfl]
    exact
      (WDiffSpace
        (n := n) (b := 1) (c := c) (d := d)).zero_mem⟩

noncomputable def triangleLeafE5CadmLBLift
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d) :
    triangleLeafE5LB n a 1 c d :=
  ⟨triangleLeafE5CadmCompatibleLift hn ha2 hc C, by
    apply LinearMap.mem_ker.mpr
    ext Y
    change
      Q1 (triangleLeafE5BCLift (c := c) C.1) Y.1.1.2 +
          Q1 Y.1.1.1 C.1 = 0
    have hY : Y.1.1.2 = 0 := Y.2
    have hCadm :
        triangleLeafE5CadmMap
            (n := n) (a := a) (c := c) (d := d) C.1 = 0 :=
      LinearMap.mem_ker.mp C.2
    have hpoint := DFunLike.congr_fun hCadm Y
    change Q1 Y.1.1.1 C.1 = 0 at hpoint
    rw [hY, Q1_zero_right, hpoint, zero_add]⟩

@[simp] theorem triangleLeafE5LBProjC_CadmLBLift
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c)
    (C : TriangleLeafE5Cadm n a c d) :
    triangleLeafE5LBProjC (triangleLeafE5CadmLBLift hn ha2 hc C) = C.1 :=
  rfl

theorem range_triangleLeafE5LBProjC_eq_Cadm
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) :
    LinearMap.range
        (triangleLeafE5LBProjC
          (n := n) (a := a) (c := c) (d := d)) =
      TriangleLeafE5Cadm n a c d :=
  by
    apply le_antisymm range_triangleLeafE5LBProjC_le_Cadm
    intro C hC
    let CadmC : TriangleLeafE5Cadm n a c d := ⟨C, hC⟩
    refine ⟨triangleLeafE5CadmLBLift hn ha2 hc CadmC, ?_⟩
    rfl

set_option synthInstance.maxHeartbeats 100000 in
-- The finrank instance follows the same nested-kernel normalization path.
theorem finrank_ker_triangleLeafE5LBProjC
    {n a c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.ker
          (triangleLeafE5LBProjC
            (n := n) (a := a) (c := c) (d := d))) =
      Module.finrank F (triangleLeafBOnly n a 1 c d) :=
  LinearEquiv.finrank_eq
    (triangleLeafE5LBProjC_ker_equiv_BOnly
      (n := n) (a := a) (c := c) (d := d))

theorem finrank_triangleLeafE5LB_eq_BOnly_add_Cadm
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) :
    Module.finrank F (triangleLeafE5LB n a 1 c d) =
      Module.finrank F (triangleLeafBOnly n a 1 c d) +
        Module.finrank F (TriangleLeafE5Cadm n a c d) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE5LBProjC
        (n := n) (a := a) (c := c) (d := d))
  calc
    Module.finrank F (triangleLeafE5LB n a 1 c d) =
        Module.finrank F
            (LinearMap.range
              (triangleLeafE5LBProjC
                (n := n) (a := a) (c := c) (d := d))) +
          Module.finrank F
            (LinearMap.ker
              (triangleLeafE5LBProjC
                (n := n) (a := a) (c := c) (d := d))) :=
      hnull.symm
    _ =
        Module.finrank F (TriangleLeafE5Cadm n a c d) +
          Module.finrank F (triangleLeafBOnly n a 1 c d) := by
      rw [range_triangleLeafE5LBProjC_eq_Cadm hn ha2 hc,
        finrank_ker_triangleLeafE5LBProjC]
    _ = _ := Nat.add_comm _ _

private theorem triangleLeafE5BOnly_subtrahend_le
    {n a c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    (n - 1) * n ^ c * (n ^ d - (n - 1)) ≤
      n ^ (a + c + d) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (bOnlyQuotientMap
        (n := n) (a := a) (b := 1) (c := c) (d := d))
  rw [finrank_range_bOnlyQuotientMap
      (n := n) (a := a) (b := 1) (c := c) (d := d)
      (by omega) hd,
    finrank_BFun4
      (n := n) (a := a) (c := c) (d := d) ha] at hnull
  omega

private theorem triangleLeafE5BOnly_subtrahend_factor
    {n c d : ℕ} [NeZero n]
    (hc : 0 < c) :
    (n - 1) * n ^ c * (n ^ d - (n - 1)) =
      (n - 1) * (n ^ d - (n - 1)) * (n ^ c - (n - 1)) +
        (n - 1) ^ 2 * (n ^ d - (n - 1)) := by
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  have hxc : n - 1 ≤ n ^ c := by
    have hpow : n ≤ n ^ c := Nat.le_pow hc
    omega
  rw [pow_two]
  calc
    (n - 1) * n ^ c * (n ^ d - (n - 1)) =
        ((n - 1) * (n ^ d - (n - 1))) * n ^ c := by ring
    _ =
        ((n - 1) * (n ^ d - (n - 1))) *
          ((n ^ c - (n - 1)) + (n - 1)) := by
            rw [Nat.sub_add_cancel hxc]
    _ =
        (n - 1) * (n ^ d - (n - 1)) * (n ^ c - (n - 1)) +
          (n - 1) * (n - 1) * (n ^ d - (n - 1)) := by ring

theorem triangleLeafE5LB_rank_arithmetic
    {n a c d : ℕ} [NeZero n]
    (ha2 : 2 ≤ a) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (triangleLeafBOnly n a 1 c d) +
        Module.finrank F (TriangleLeafE5Cadm n a c d) =
      n ^ (a + c + d) + n ^ (a + d) -
        (n - 1) * (n ^ d - (n - 1)) * (n ^ c - (n - 1)) := by
  have ha : 0 < a := by omega
  rw [finrank_triangleLeafBOnly
      (n := n) (a := a) (b := 1) (c := c) (d := d)
      ha (by omega) hd,
    finrank_triangleLeafE5Cadm
      (n := n) (a := a) (c := c) (d := d) ha2 hc hd]
  have hA :
      (n - 1) * n ^ c * (n ^ d - (n - 1)) ≤
        n ^ (a + c + d) :=
    triangleLeafE5BOnly_subtrahend_le ha hd
  have hfactor :=
    triangleLeafE5BOnly_subtrahend_factor
      (n := n) (c := c) (d := d) hc
  omega

theorem finrank_triangleLeafE5LB
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (triangleLeafE5LB n a 1 c d) =
      n ^ (a + c + d) + n ^ (a + d) -
        (n - 1) * (n ^ d - (n - 1)) * (n ^ c - (n - 1)) := by
  rw [finrank_triangleLeafE5LB_eq_BOnly_add_Cadm hn ha2 hc]
  exact triangleLeafE5LB_rank_arithmetic ha2 hc hd

theorem triangleLeafE5LB_rank_int_bridge
    {n a c d : ℕ} [NeZero n]
    (ha2 : 2 ≤ a) (hc : 0 < c) (hd : 0 < d) :
    ((n ^ (a + c + d) + n ^ (a + d) -
          (n - 1) * (n ^ d - (n - 1)) *
            (n ^ c - (n - 1)) : ℕ) : ℤ) =
      CompatibleResidualSplitZ a 1 c d n := by
  have ha : 0 < a := by omega
  have hn1 : 1 ≤ n := one_le_of_neZero (n := n)
  have hnc : n - 1 ≤ n ^ c := by
    have hpow : n ≤ n ^ c := Nat.le_pow hc
    omega
  have hnd : n - 1 ≤ n ^ d := by
    have hpow : n ≤ n ^ d := Nat.le_pow hd
    omega
  have hA :
      (n - 1) * n ^ c * (n ^ d - (n - 1)) ≤
        n ^ (a + c + d) :=
    triangleLeafE5BOnly_subtrahend_le ha hd
  have hfactor :=
    triangleLeafE5BOnly_subtrahend_factor
      (n := n) (c := c) (d := d) hc
  have hres :
      (n - 1) * (n ^ d - (n - 1)) * (n ^ c - (n - 1)) ≤
        n ^ (a + c + d) + n ^ (a + d) := by
    omega
  have htheta :
      ThetaZ (a + d) 1 c n =
        mZ n * (2 * (n : ℤ) - 1) := by
    apply
      TriangleCore.ThetaZ_triangleLeaf_eq_of_not_even_or_small ha hd
    omega
  have hcastResidual :
      (((n - 1) * (n ^ d - (n - 1)) *
          (n ^ c - (n - 1)) : ℕ) : ℤ) =
        ((n : ℤ) - 1) *
          ((n : ℤ) ^ d - ((n : ℤ) - 1)) *
          ((n : ℤ) ^ c - ((n : ℤ) - 1)) := by
    rw [Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub hnd, Nat.cast_sub hnc,
      Nat.cast_sub hn1, Nat.cast_pow, Nat.cast_pow]
    norm_num
  rw [CompatibleResidualSplitZ_eq_CompatibleResidualExpZ ha hd]
  unfold CompatibleResidualExpZ
  rw [htheta]
  rw [Nat.cast_sub hres, Nat.cast_add, hcastResidual]
  simp only [nPowZ, mZ, Nat.cast_pow]
  ring

theorem finrank_triangleLeafE5LB_eq_CompatibleResidualSplitZ
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) (hd : 0 < d) :
    (Module.finrank F (triangleLeafE5LB n a 1 c d) : ℤ) =
      CompatibleResidualSplitZ a 1 c d n := by
  rw [finrank_triangleLeafE5LB hn ha2 hc hd]
  exact
    triangleLeafE5LB_rank_int_bridge
      (n := n) (a := a) (c := c) (d := d) ha2 hc hd

set_option synthInstance.maxHeartbeats 100000 in
-- The terminal evaluator needs instances for the nested LB submodule.
theorem leafCompatibleResidualSum_b_eq_one_eq_pow_finrank
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n a 1 c d =
      (2 : ℤ) ^
        Module.finrank F (triangleLeafE5LB n a 1 c d) := by
  letI : Fintype (triangleLeafE5LB n a 1 c d) :=
    Fintype.ofFinite _
  rw [leafCompatibleResidualSum_eq_compatibleSubmoduleSignSum]
  exact
    sum_bitSign_eq_pow_finrank_of_selfDual_isotropic
      (q := triangleLeafCompatibleQ)
      (polar := triangleLeafCompatiblePolar)
      (hq_add := fun X Y => triangleLeafCompatibleQ_add X Y)
      (L := triangleLeafE5LB n a 1 c d)
      (hq_zero :=
        triangleLeafE5LB_q_zero_b_eq_one hn ha2 hc hd2)
      (hself :=
        triangleLeafE5LB_selfDual_b_eq_one hn ha2 hc hd2)

set_option synthInstance.maxHeartbeats 100000 in
-- The cast rewrite normalizes the same nested LB finrank instances.
theorem toNat_CompatibleResidualSplitZ_eq_finrank_triangleLeafE5LB
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) (hd : 0 < d) :
    Int.toNat (CompatibleResidualSplitZ a 1 c d n) =
      Module.finrank F (triangleLeafE5LB n a 1 c d) := by
  rw [← finrank_triangleLeafE5LB_eq_CompatibleResidualSplitZ
    hn ha2 hc hd]
  simp

set_option synthInstance.maxHeartbeats 100000 in
-- Both frozen residual endpoints expose the nested LB finrank.
theorem leafCompatibleResidualSum_b_eq_one
    {n a c d : ℕ} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) (hc : 0 < c) (hd2 : 2 ≤ d) :
    leafCompatibleResidualSum n a 1 c d =
      (2 : ℤ) ^
        Int.toNat (CompatibleResidualSplitZ a 1 c d n) := by
  rw [leafCompatibleResidualSum_b_eq_one_eq_pow_finrank
      hn ha2 hc hd2,
    toNat_CompatibleResidualSplitZ_eq_finrank_triangleLeafE5LB
      hn ha2 hc (by omega)]


end

end TriangleLeaf
end Core4loop
