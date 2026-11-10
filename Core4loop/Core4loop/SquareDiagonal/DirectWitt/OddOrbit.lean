import Core4loop.SquareDiagonal.DirectWitt.CyclicOdd
import Core4loop.ZeroSumSpaces.Cube
open scoped BigOperators
namespace Core4loop.SquareDiagonal.DirectWitt
noncomputable section
noncomputable def oddDiagonalReindex
    {n : Nat} [NeZero n] : CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j s => f i j (s - i)
  invFun g := fun i j k => g i j (i + k)
  map_add' f g := rfl
  map_smul' r f := rfl
  left_inv f := by funext i j k; abel
  right_inv g := by funext i j s; abel
@[simp] theorem oddDiagonalReindex_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j s : I n) :
    oddDiagonalReindex f i j s = f i j (s - i) := rfl
@[simp] theorem oddDiagonalReindex_symm_apply
    {n : Nat} [NeZero n] (g : CyclicCube n) (i j k : I n) :
    oddDiagonalReindex.symm g i j k = g i j (i + k) := rfl
noncomputable def oddOrbitSumPi
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] MatrixProfile n where
  toFun f := fun j s => ∑ i : I n, f i j (s - i)
  map_add' f g := by
    funext j s
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r f := by
    funext j s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
@[simp] theorem oddOrbitSumPi_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (j s : I n) :
    oddOrbitSumPi f j s = ∑ i : I n, f i j (s - i) := rfl
noncomputable def oddIKStarMap
    {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n where
  toFun f := cyclicDiffX f + cyclicDiffZ f
  map_add' f g := by
    funext i j k
    simp only [Pi.add_apply, cyclicDiffX, cyclicDiffZ]
    abel
  map_smul' r f := by
    funext i j k
    change
      (r * f i j k + r * f (i + 1) j k) +
          (r * f i j k + r * f i j (k + 1)) =
        r * ((f i j k + f (i + 1) j k) +
          (f i j k + f i j (k + 1)))
    ring
@[simp] theorem oddIKStarMap_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    oddIKStarMap f i j k =
      cyclicDiffX f i j k + cyclicDiffZ f i j k := rfl
theorem oddDiagonalReindex_oddIKStarMap_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j s : I n) :
    oddDiagonalReindex (oddIKStarMap f) i j s =
      oddDiagonalReindex f (i + 1) j (s + 1) +
        oddDiagonalReindex f i j (s + 1) := by
  change
    (f i j (s - i) + f (i + 1) j (s - i)) +
        (f i j (s - i) + f i j (s - i + 1)) =
      f (i + 1) j (s + 1 - (i + 1)) + f i j (s + 1 - i)
  have h1 : s + 1 - (i + 1) = s - i := by abel
  have h2 : s + 1 - i = s - i + 1 := by abel
  rw [h1, h2]
  calc
    (f i j (s - i) + f (i + 1) j (s - i)) +
          (f i j (s - i) + f i j (s - i + 1)) =
        (f i j (s - i) + f i j (s - i)) +
          (f (i + 1) j (s - i) + f i j (s - i + 1)) := by abel
    _ = f (i + 1) j (s - i) + f i j (s - i + 1) := by
      rw [F_add_self, zero_add]
private theorem oddOrbitSumPi_zero_sum_profile
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (oddOrbitSumPi (n := n))) (j s : I n) :
    (∑ i : I n, X.1 i j (s - i)) = 0 :=
  congrFun (congrFun (LinearMap.mem_ker.mp X.2) j) s
noncomputable def oddIKStarPrimitive
    {n : Nat} [NeZero n] :
    LinearMap.ker (oddOrbitSumPi (n := n)) →ₗ[F] CyclicCube n where
  toFun X := fun i j k =>
    explicitCyclicPrimitive n
      ⟨fun u => X.1 u j ((i + k - 1) - u),
        oddOrbitSumPi_zero_sum_profile X j (i + k - 1)⟩ i
  map_add' X Y := by
    funext i j k
    simpa only [Submodule.coe_add, Pi.add_apply] using
      congrArg (fun p : Profile n => p i)
        ((explicitCyclicPrimitive n).map_add
          ⟨fun u => X.1 u j ((i + k - 1) - u),
            oddOrbitSumPi_zero_sum_profile X j (i + k - 1)⟩
          ⟨fun u => Y.1 u j ((i + k - 1) - u),
            oddOrbitSumPi_zero_sum_profile Y j (i + k - 1)⟩)
  map_smul' r X := by
    funext i j k
    simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] using
      congrArg (fun p : Profile n => p i)
        ((explicitCyclicPrimitive n).map_smul r
          ⟨fun u => X.1 u j ((i + k - 1) - u),
            oddOrbitSumPi_zero_sum_profile X j (i + k - 1)⟩)
@[simp] theorem oddIKStarMap_oddIKStarPrimitive
    {n : Nat} [NeZero n]
    (X : LinearMap.ker (oddOrbitSumPi (n := n))) :
    oddIKStarMap (oddIKStarPrimitive X) = X.1 := by
  funext i j k
  simp only [oddIKStarMap, oddIKStarPrimitive, LinearMap.coe_mk,
    AddHom.coe_mk, cyclicDiffX, cyclicDiffZ, Pi.add_apply]
  ring_nf
  rw [show (2 : F) = 0 by decide, mul_zero, zero_add]
  let U : ZeroSumProfile n :=
    ⟨fun u => X.1 u j ((i + k) - u),
      oddOrbitSumPi_zero_sum_profile X j (i + k)⟩
  have h := congrFun (cycDiff_explicitCyclicPrimitive U) i
  change explicitCyclicPrimitive n U (1 + i) +
      explicitCyclicPrimitive n U i = X.1 i j k
  calc
    explicitCyclicPrimitive n U (1 + i) +
        explicitCyclicPrimitive n U i = U.1 i := by
      simpa only [add_comm] using h
    _ = X.1 i j k := by
      change X.1 i j ((i + k) - i) = X.1 i j k
      rw [show (i + k) - i = k by abel]

theorem range_oddIKStarMap_eq_ker_oddOrbitSumPi
    {n : Nat} [NeZero n] :
    LinearMap.range (oddIKStarMap (n := n)) =
      LinearMap.ker (oddOrbitSumPi (n := n)) := by
  apply le_antisymm
  · rintro X ⟨f, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext j s
    change
      (∑ i : I n,
        (oddDiagonalReindex (oddIKStarMap f)) i j s) = 0
    simp_rw [oddDiagonalReindex_oddIKStarMap_apply]
    rw [Finset.sum_add_distrib]
    have h := sum_shift (n := n) (1 : I n)
      (fun i => oddDiagonalReindex f i j (s + 1))
    rw [h, F_add_self]
  · intro X hX
    exact ⟨oddIKStarPrimitive ⟨X, hX⟩,
      oddIKStarMap_oddIKStarPrimitive ⟨X, hX⟩⟩

noncomputable def DiamondOddJZero
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (sumY3Map (n := n))

abbrev DiamondOddOrbitProfile
    (n : Nat) [NeZero n] := ZeroSumProfileM n (Profile n)

noncomputable def oddOrbitColumn
    {n : Nat} [NeZero n]
    (x : DiamondOddOrbitProfile n) (s : I n) : ZeroSumProfile n :=
  ⟨fun j => x.1 j s, by
    simpa only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_apply, Pi.zero_apply] using
      congrFun (LinearMap.mem_ker.mp x.2) s⟩

private theorem oddOrbitSumPi_mem
    {n : Nat} [NeZero n] (X : DiamondOddJZero n) :
    oddOrbitSumPi X.1 ∈ DiamondOddOrbitProfile n := by
  apply LinearMap.mem_ker.mpr
  funext s
  simp only [sigmaMapM, oddOrbitSumPi, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  exact congrFun (congrFun (LinearMap.mem_ker.mp X.2) i) (s - i)

noncomputable def oddOrbitSumPiRestrict
    {n : Nat} [NeZero n] :
    DiamondOddJZero n →ₗ[F] DiamondOddOrbitProfile n :=
  LinearMap.codRestrict (DiamondOddOrbitProfile n)
    ((oddOrbitSumPi (n := n)).comp (DiamondOddJZero n).subtype)
    oddOrbitSumPi_mem

noncomputable def oddOrbitLift
    {n : Nat} [NeZero n] :
    DiamondOddOrbitProfile n →ₗ[F] DiamondOddJZero n where
  toFun x :=
    ⟨fun i j k => x.1 j (i + k), by
      apply LinearMap.mem_ker.mpr
      funext i k
      change (∑ j : I n, x.1 j (i + k)) = 0
      simpa only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.zero_apply] using
        congrFun (LinearMap.mem_ker.mp x.2) (i + k)⟩
  map_add' x y := rfl
  map_smul' r x := rfl

@[simp] theorem oddOrbitLift_apply
    {n : Nat} [NeZero n]
    (x : DiamondOddOrbitProfile n) (i j k : I n) :
    (oddOrbitLift x).1 i j k = x.1 j (i + k) := rfl

@[simp] theorem oddOrbitSumPiRestrict_oddOrbitLift
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddOrbitProfile n) :
    oddOrbitSumPiRestrict (oddOrbitLift x) = x := by
  apply Subtype.ext
  funext j s
  change (∑ i : I n, x.1 j (i + (s - i))) = x.1 j s
  have hidx : ∀ i : I n, i + (s - i) = s := by intro i; abel
  simp_rw [hidx, Finset.sum_const, Finset.card_univ]
  rw [show Fintype.card (I n) = n by simp [I, ZMod.card]]
  rw [nsmul_eq_mul, natCast_odd_eq_one_F hn, one_mul]

theorem range_oddOrbitSumPiRestrict_eq_top
    {n : Nat} [NeZero n] (hn : Odd n) :
    LinearMap.range (oddOrbitSumPiRestrict (n := n)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact ⟨oddOrbitLift x, oddOrbitSumPiRestrict_oddOrbitLift hn x⟩

noncomputable def DiamondOddHighFreq
    (n : Nat) [NeZero n] : Submodule F (DiamondOddJZero n) :=
  LinearMap.ker (oddOrbitSumPiRestrict (n := n))

noncomputable def diamondOddHighFreqEquivSlices
    {n : Nat} [NeZero n] :
    DiamondOddHighFreq n ≃ₗ[F] (I n → MatrixZeroSum n) where
  toFun X := fun s =>
    ⟨fun i j => X.1.1 i j (s - i), by
      constructor
      · apply LinearMap.mem_ker.mpr
        funext i
        exact congrFun (congrFun (LinearMap.mem_ker.mp X.1.2) i) (s - i)
      · apply LinearMap.mem_ker.mpr
        funext j
        exact congrFun
          (congrFun (congrArg Subtype.val (LinearMap.mem_ker.mp X.2)) j) s⟩
  invFun H :=
    ⟨⟨fun i j k => (H (i + k)).1 i j, by
        apply LinearMap.mem_ker.mpr
        funext i k
        exact matrix_row_zero (H (i + k)) i⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      funext j s
      change (∑ i : I n, (H (i + (s - i))).1 i j) = 0
      have hidx : ∀ i : I n, i + (s - i) = s := by intro i; abel
      simp_rw [hidx]
      exact matrix_col_zero (H s) j⟩
  map_add' X Y := rfl
  map_smul' r X := rfl
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    funext i j k
    change X.1.1 i j ((i + k) - i) = X.1.1 i j k
    abel
  right_inv H := by
    funext s
    apply Subtype.ext
    funext i j
    change (H (i + (s - i))).1 i j = (H s).1 i j
    abel

@[simp] theorem diamondOddHighFreqEquivSlices_apply
    {n : Nat} [NeZero n]
    (X : DiamondOddHighFreq n) (s i j : I n) :
    ((diamondOddHighFreqEquivSlices X) s).1 i j =
      X.1.1 i j (s - i) := rfl

@[simp] theorem diamondOddHighFreqEquivSlices_symm_apply
    {n : Nat} [NeZero n]
    (H : I n → MatrixZeroSum n) (i j k : I n) :
    ((diamondOddHighFreqEquivSlices (n := n)).symm H).1.1 i j k =
      (H (i + k)).1 i j := rfl

theorem finrank_DiamondOddHighFreq
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondOddHighFreq n) = n * (n - 1) ^ 2 := by
  rw [LinearEquiv.finrank_eq diamondOddHighFreqEquivSlices]
  rw [Module.finrank_pi_fintype]
  simp [finrank_MatrixZeroSum, I, ZMod.card]

noncomputable def oddMatrixDiffS
    {n : Nat} [NeZero n] : MatrixProfile n →ₗ[F] MatrixProfile n where
  toFun y := fun j s => y j s + y j (s + 1)
  map_add' x y := by funext j s; simp only [Pi.add_apply]; abel
  map_smul' r y := by
    funext j s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem oddMatrixDiffS_apply
    {n : Nat} [NeZero n] (y : MatrixProfile n) (j s : I n) :
    oddMatrixDiffS y j s = y j s + y j (s + 1) := rfl

noncomputable def oddOrbitProfileInverseJ
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddOrbitProfile n →ₗ[F] DiamondOddOrbitProfile n where
  toFun x :=
    ⟨fun j s => (oddCyclicInverse hn (oddOrbitColumn x s)).1 j, by
      apply LinearMap.mem_ker.mpr
      funext s
      simp only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.zero_apply]
      exact LinearMap.mem_ker.mp (oddCyclicInverse hn (oddOrbitColumn x s)).2⟩
  map_add' x y := by
    apply Subtype.ext
    funext j s
    simpa only [Submodule.coe_add, Pi.add_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 j)
        ((oddCyclicInverse hn).map_add (oddOrbitColumn x s)
          (oddOrbitColumn y s))
  map_smul' r x := by
    apply Subtype.ext
    funext j s
    simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 j)
        ((oddCyclicInverse hn).map_smul r (oddOrbitColumn x s))

@[simp] theorem oddOrbitProfileInverseJ_apply
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddOrbitProfile n) (j s : I n) :
    (oddOrbitProfileInverseJ hn x).1 j s =
      (oddCyclicInverse hn (oddOrbitColumn x s)).1 j := rfl

private noncomputable def oddMatrixInverseJRaw
    {n : Nat} [NeZero n] (hn : Odd n) :
    MatrixZeroSum n →ₗ[F] MatrixProfile n where
  toFun x := fun j s =>
    (oddCyclicInverse hn
      ⟨fun t => x.1 t s, matrix_col_zero x s⟩).1 j
  map_add' x y := by
    funext j s
    simpa only [Submodule.coe_add, Pi.add_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 j)
        ((oddCyclicInverse hn).map_add
          ⟨fun t => x.1 t s, matrix_col_zero x s⟩
          ⟨fun t => y.1 t s, matrix_col_zero y s⟩)
  map_smul' r x := by
    funext j s
    simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 j)
        ((oddCyclicInverse hn).map_smul r
          ⟨fun t => x.1 t s, matrix_col_zero x s⟩)

private theorem oddMatrixInverseJRaw_mem
    {n : Nat} [NeZero n] (hn : Odd n) (x : MatrixZeroSum n) :
    oddMatrixInverseJRaw hn x ∈ MatrixZeroSum n := by
  constructor
  · apply LinearMap.mem_ker.mpr
    funext j
    let c : I n → ZeroSumProfile n :=
      fun s => ⟨fun t => x.1 t s, matrix_col_zero x s⟩
    have hc : (∑ s : I n, c s) = 0 := by
      apply Subtype.ext
      funext t
      simpa only [c, Submodule.coe_sum, Finset.sum_apply, Pi.zero_apply]
        using matrix_row_zero x t
    change (∑ s : I n, (oddCyclicInverse hn (c s)).1 j) = 0
    calc
      _ = ((∑ s : I n, oddCyclicInverse hn (c s))).1 j := by
        simp only [Submodule.coe_sum, Finset.sum_apply]
      _ = (oddCyclicInverse hn (∑ s : I n, c s)).1 j := by rw [map_sum]
      _ = 0 := by rw [hc, map_zero]; rfl
  · apply LinearMap.mem_ker.mpr
    funext s
    exact LinearMap.mem_ker.mp
      (oddCyclicInverse hn
        ⟨fun t => x.1 t s, matrix_col_zero x s⟩).2

noncomputable def oddMatrixInverseJ
    {n : Nat} [NeZero n] (hn : Odd n) :
    MatrixZeroSum n →ₗ[F] MatrixZeroSum n :=
  LinearMap.codRestrict (MatrixZeroSum n)
    (oddMatrixInverseJRaw hn) (oddMatrixInverseJRaw_mem hn)

@[simp] theorem oddMatrixInverseJ_apply
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : MatrixZeroSum n) (j s : I n) :
    (oddMatrixInverseJ hn x).1 j s =
      (oddCyclicInverse hn
        ⟨fun t => x.1 t s, matrix_col_zero x s⟩).1 j := rfl

private noncomputable def oddMatrixInverseSRaw
    {n : Nat} [NeZero n] (hn : Odd n) :
    MatrixZeroSum n →ₗ[F] MatrixProfile n where
  toFun x := fun j s =>
    (oddCyclicInverse hn
      ⟨fun t => x.1 j t, matrix_row_zero x j⟩).1 s
  map_add' x y := by
    funext j s
    simpa only [Submodule.coe_add, Pi.add_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 s)
        ((oddCyclicInverse hn).map_add
          ⟨fun t => x.1 j t, matrix_row_zero x j⟩
          ⟨fun t => y.1 j t, matrix_row_zero y j⟩)
  map_smul' r x := by
    funext j s
    simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 s)
        ((oddCyclicInverse hn).map_smul r
          ⟨fun t => x.1 j t, matrix_row_zero x j⟩)

private theorem oddMatrixInverseSRaw_mem
    {n : Nat} [NeZero n] (hn : Odd n) (x : MatrixZeroSum n) :
    oddMatrixInverseSRaw hn x ∈ MatrixZeroSum n := by
  constructor
  · apply LinearMap.mem_ker.mpr
    funext j
    exact LinearMap.mem_ker.mp
      (oddCyclicInverse hn
        ⟨fun t => x.1 j t, matrix_row_zero x j⟩).2
  · apply LinearMap.mem_ker.mpr
    funext s
    let r : I n → ZeroSumProfile n :=
      fun j => ⟨fun t => x.1 j t, matrix_row_zero x j⟩
    have hr : (∑ j : I n, r j) = 0 := by
      apply Subtype.ext
      funext t
      simpa only [r, Submodule.coe_sum, Finset.sum_apply, Pi.zero_apply]
        using matrix_col_zero x t
    change (∑ j : I n, (oddCyclicInverse hn (r j)).1 s) = 0
    calc
      _ = ((∑ j : I n, oddCyclicInverse hn (r j))).1 s := by
        simp only [Submodule.coe_sum, Finset.sum_apply]
      _ = (oddCyclicInverse hn (∑ j : I n, r j)).1 s := by rw [map_sum]
      _ = 0 := by rw [hr, map_zero]; rfl

noncomputable def oddMatrixInverseS
    {n : Nat} [NeZero n] (hn : Odd n) :
    MatrixZeroSum n →ₗ[F] MatrixZeroSum n :=
  LinearMap.codRestrict (MatrixZeroSum n)
    (oddMatrixInverseSRaw hn) (oddMatrixInverseSRaw_mem hn)

@[simp] theorem oddMatrixInverseS_apply
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : MatrixZeroSum n) (j s : I n) :
    (oddMatrixInverseS hn x).1 j s =
      (oddCyclicInverse hn
        ⟨fun t => x.1 j t, matrix_row_zero x j⟩).1 s := rfl

noncomputable def oddMatrixDot
    {n : Nat} [NeZero n] (x y : MatrixProfile n) : F :=
  ∑ j : I n, ∑ s : I n, x j s * y j s

theorem oddMatrixInverseJ_pairing
    {n : Nat} [NeZero n] (hn : Odd n)
    (x y : MatrixZeroSum n) :
    oddMatrixDot (oddMatrixInverseJ hn x).1 y.1 +
        oddMatrixDot x.1 (oddMatrixInverseJ hn y).1 =
      oddMatrixDot x.1 y.1 := by
  simp only [oddMatrixDot, oddMatrixInverseJ_apply]
  calc
    (∑ j, ∑ s,
        (oddCyclicInverse hn
          ⟨fun t => x.1 t s, matrix_col_zero x s⟩).1 j * y.1 j s) +
        (∑ j, ∑ s, x.1 j s *
          (oddCyclicInverse hn
            ⟨fun t => y.1 t s, matrix_col_zero y s⟩).1 j) =
      (∑ s, ∑ j,
        (oddCyclicInverse hn
          ⟨fun t => x.1 t s, matrix_col_zero x s⟩).1 j * y.1 j s) +
        (∑ s, ∑ j, x.1 j s *
          (oddCyclicInverse hn
            ⟨fun t => y.1 t s, matrix_col_zero y s⟩).1 j) := by
        rw [Finset.sum_comm, Finset.sum_comm
          (f := fun j s => x.1 j s *
            (oddCyclicInverse hn
              ⟨fun t => y.1 t s, matrix_col_zero y s⟩).1 j)]
    _ = ∑ s, ((∑ j,
        (oddCyclicInverse hn
          ⟨fun t => x.1 t s, matrix_col_zero x s⟩).1 j * y.1 j s) +
        (∑ j, x.1 j s *
          (oddCyclicInverse hn
            ⟨fun t => y.1 t s, matrix_col_zero y s⟩).1 j)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ s, ∑ j, x.1 j s * y.1 j s := by
      apply Finset.sum_congr rfl
      intro s _
      exact oddCyclicInverse_pairing_add_pairing hn
        ⟨fun t => x.1 t s, matrix_col_zero x s⟩
        ⟨fun t => y.1 t s, matrix_col_zero y s⟩
    _ = ∑ j, ∑ s, x.1 j s * y.1 j s := Finset.sum_comm

theorem oddMatrixInverseS_pairing
    {n : Nat} [NeZero n] (hn : Odd n)
    (x y : MatrixZeroSum n) :
    oddMatrixDot (oddMatrixInverseS hn x).1 y.1 +
        oddMatrixDot x.1 (oddMatrixInverseS hn y).1 =
      oddMatrixDot x.1 y.1 := by
  simp only [oddMatrixDot, oddMatrixInverseS_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact oddCyclicInverse_pairing_add_pairing hn
    ⟨fun t => x.1 j t, matrix_row_zero x j⟩
    ⟨fun t => y.1 j t, matrix_row_zero y j⟩

noncomputable def oddOrbitRelationMap
    {n : Nat} [NeZero n] (hn : Odd n) :
    (DiamondOddOrbitProfile n × MatrixProfile n) →ₗ[F] MatrixProfile n where
  toFun z :=
    z.1.1 + oddMatrixDiffS
      (z.2 + (oddOrbitProfileInverseJ hn z.1).1)
  map_add' z w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]
    abel
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd,
      Submodule.coe_smul_of_tower, map_smul, RingHom.id_apply]
    rw [← smul_add, map_smul, smul_add]

@[simp] theorem oddOrbitRelationMap_apply
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddOrbitProfile n × MatrixProfile n) :
    oddOrbitRelationMap hn z =
      z.1.1 + oddMatrixDiffS
        (z.2 + (oddOrbitProfileInverseJ hn z.1).1) := rfl

abbrev DiamondOddOrbitRelation
    (n : Nat) [NeZero n] (hn : Odd n) :=
  LinearMap.ker (oddOrbitRelationMap (n := n) hn)

private theorem oddMatrixDiffS_sum_zero
    {n : Nat} [NeZero n] (y : MatrixProfile n) (j : I n) :
    (∑ s : I n, oddMatrixDiffS y j s) = 0 := by
  change (∑ s : I n, (y j s + y j (s + 1))) = 0
  rw [Finset.sum_add_distrib]
  rw [sum_shift (n := n) (1 : I n) (y j), F_add_self]

theorem oddOrbitRelation_sumS_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddOrbitRelation n hn) (j : I n) :
    (∑ s : I n, z.1.1.1 j s) = 0 := by
  have hrel := LinearMap.mem_ker.mp z.2
  have hsum :=
    congrArg (fun M : MatrixProfile n => ∑ s : I n, M j s) hrel
  simp only [oddOrbitRelationMap, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply, Finset.sum_const_zero] at hsum
  change
    (∑ s : I n,
      (z.1.1.1 j s +
        oddMatrixDiffS
          (z.1.2 + (oddOrbitProfileInverseJ hn z.1.1).1) j s)) = 0 at hsum
  rw [Finset.sum_add_distrib, oddMatrixDiffS_sum_zero] at hsum
  simpa using hsum

noncomputable def oddOrbitRelationX
    {n : Nat} [NeZero n] {hn : Odd n}
    (z : DiamondOddOrbitRelation n hn) : MatrixZeroSum n :=
  ⟨z.1.1.1, by
    constructor
    · apply LinearMap.mem_ker.mpr
      funext j
      exact oddOrbitRelation_sumS_zero hn z j
    · apply LinearMap.mem_ker.mpr
      funext s
      simpa only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.zero_apply] using
        congrFun (LinearMap.mem_ker.mp z.1.1.2) s⟩

@[simp] theorem oddOrbitRelationX_apply
    {n : Nat} [NeZero n] {hn : Odd n}
    (z : DiamondOddOrbitRelation n hn) (j s : I n) :
    (oddOrbitRelationX z).1 j s = z.1.1.1 j s := rfl

private theorem oddOrbitProfileInverseJ_compat
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddOrbitRelation n hn) (j s : I n) :
    (oddOrbitProfileInverseJ hn z.1.1).1 j s =
      (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s := rfl

private theorem oddOrbitProfileInverseJ_eq_relationX
    {n : Nat} [NeZero n] {hn : Odd n}
    (z : DiamondOddOrbitRelation n hn) :
    (oddOrbitProfileInverseJ hn z.1.1).1 =
      (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 := rfl

private theorem oddMatrixDiffS_inverseS
    {n : Nat} [NeZero n] (hn : Odd n) (x : MatrixZeroSum n) :
    oddMatrixDiffS (oddMatrixInverseS hn x).1 = x.1 := by
  funext j s
  exact congrArg (fun u : ZeroSumProfile n => u.1 s)
    (oddCyclicDiffRestrict_oddCyclicInverse hn
      ⟨fun t => x.1 j t, matrix_row_zero x j⟩)

noncomputable def oddOrbitRelationH
    {n : Nat} [NeZero n] {hn : Odd n}
    (z : DiamondOddOrbitRelation n hn) : Profile n :=
  fun j =>
    z.1.2 j 0 +
      (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j 0 +
      (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j 0

theorem oddOrbitRelation_normal_form
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddOrbitRelation n hn) :
    z.1.2 =
      (oddMatrixInverseS hn (oddOrbitRelationX z)).1 +
      (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 +
      fun j _ => oddOrbitRelationH z j := by
  have hrel := LinearMap.mem_ker.mp z.2
  change z.1.1.1 + oddMatrixDiffS
      (z.1.2 + (oddOrbitProfileInverseJ hn z.1.1).1) = 0 at hrel
  rw [oddOrbitProfileInverseJ_eq_relationX z] at hrel
  have hdiff : oddMatrixDiffS
      (z.1.2 + (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 +
        (oddMatrixInverseS hn (oddOrbitRelationX z)).1) = 0 := by
    rw [show z.1.2 + (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 +
        (oddMatrixInverseS hn (oddOrbitRelationX z)).1 =
      (z.1.2 + (oddMatrixInverseJ hn (oddOrbitRelationX z)).1) +
        (oddMatrixInverseS hn (oddOrbitRelationX z)).1 by rfl]
    rw [map_add, oddMatrixDiffS_inverseS]
    calc
      oddMatrixDiffS
          (z.1.2 + (oddMatrixInverseJ hn (oddOrbitRelationX z)).1) +
          (oddOrbitRelationX z).1 =
        z.1.1.1 + oddMatrixDiffS
          (z.1.2 + (oddMatrixInverseJ hn (oddOrbitRelationX z)).1) := by
            abel
      _ = 0 := hrel
  funext j s
  let K : Profile n := fun t =>
    z.1.2 j t +
      (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j t +
      (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j t
  have hK : cycDiff (n := n) F K = 0 := by
    funext t
    exact congrFun (congrFun hdiff j) t
  have hc := (cycDiff_eq_zero_iff_constant_apply F K).mp hK s
  have hj : (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
      (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s = 0 :=
    F_add_self _
  have hs : (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s +
      (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s = 0 :=
    F_add_self _
  dsimp only [K, oddOrbitRelationH] at hc ⊢
  calc
    z.1.2 j s =
        (z.1.2 j s +
          (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
          (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s) +
        (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
        (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s := by
          rw [show
            (z.1.2 j s +
              (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
              (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s) +
              (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
              (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s =
            z.1.2 j s +
              ((oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
                (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s) +
              ((oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s +
                (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s) by abel,
            hj, hs, add_zero, add_zero]
    _ = (z.1.2 j 0 +
          (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j 0 +
          (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j 0) +
        (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
        (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s := by rw [hc]
    _ = (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j s +
        (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j s +
        (z.1.2 j 0 +
          (oddMatrixInverseS hn (oddOrbitRelationX z)).1 j 0 +
          (oddMatrixInverseJ hn (oddOrbitRelationX z)).1 j 0) := by abel

theorem oddOrbitRelation_of_normal_form
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : MatrixZeroSum n) (h : Profile n) :
    let xo : DiamondOddOrbitProfile n :=
      ⟨x.1, by
        apply LinearMap.mem_ker.mpr
        funext s
        simpa only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk,
          Finset.sum_apply, Pi.zero_apply] using matrix_col_zero x s⟩
    let y : MatrixProfile n :=
      (oddMatrixInverseS hn x).1 +
        (oddMatrixInverseJ hn x).1 + fun j _ => h j
    (xo, y) ∈ DiamondOddOrbitRelation n hn := by
  dsimp only
  apply LinearMap.mem_ker.mpr
  change x.1 + oddMatrixDiffS
    (((oddMatrixInverseS hn x).1 + (oddMatrixInverseJ hn x).1 +
      fun j _ => h j) + (oddMatrixInverseJ hn x).1) = 0
  have hi :
      ((oddMatrixInverseS hn x).1 + (oddMatrixInverseJ hn x).1 +
        fun j _ => h j) + (oddMatrixInverseJ hn x).1 =
      (oddMatrixInverseS hn x).1 + fun j _ => h j := by
    funext j s
    simp only [Pi.add_apply]
    rw [show
      (oddMatrixInverseS hn x).1 j s +
          (oddMatrixInverseJ hn x).1 j s + h j +
          (oddMatrixInverseJ hn x).1 j s =
        (oddMatrixInverseS hn x).1 j s +
          ((oddMatrixInverseJ hn x).1 j s +
            (oddMatrixInverseJ hn x).1 j s) + h j by abel,
      F_add_self, add_zero]
  rw [hi, map_add, oddMatrixDiffS_inverseS]
  have hc : oddMatrixDiffS (fun j (_ : I n) => h j) = 0 := by
    funext j s
    exact F_add_self _
  rw [hc, add_zero]
  funext j s
  exact F_add_self _

noncomputable def oddOrbitQuadratic
    {n : Nat} [NeZero n] (hn : Odd n) (x : MatrixZeroSum n) : F :=
  oddMatrixDot x.1 (oddMatrixInverseS hn x).1 +
    oddMatrixDot x.1 (oddMatrixInverseJ hn x).1

private theorem oddMatrixDot_comm
    {n : Nat} [NeZero n] (x y : MatrixProfile n) :
    oddMatrixDot x y = oddMatrixDot y x := by
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

private theorem oddMatrixDot_add_left
    {n : Nat} [NeZero n] (x y z : MatrixProfile n) :
    oddMatrixDot (x + y) z = oddMatrixDot x z + oddMatrixDot y z := by
  simp only [oddMatrixDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem oddMatrixDot_add_right
    {n : Nat} [NeZero n] (x y z : MatrixProfile n) :
    oddMatrixDot x (y + z) = oddMatrixDot x y + oddMatrixDot x z := by
  simp only [oddMatrixDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem oddOrbitQuadratic_add
    {n : Nat} [NeZero n] (hn : Odd n)
    (x y : MatrixZeroSum n) :
    oddOrbitQuadratic hn (x + y) =
      oddOrbitQuadratic hn x + oddOrbitQuadratic hn y := by
  have hs := oddMatrixInverseS_pairing hn x y
  have hj := oddMatrixInverseJ_pairing hn x y
  rw [oddMatrixDot_comm (oddMatrixInverseS hn x).1 y.1] at hs
  rw [oddMatrixDot_comm (oddMatrixInverseJ hn x).1 y.1] at hj
  have hc :
      (oddMatrixDot x.1 (oddMatrixInverseS hn y).1 +
        oddMatrixDot y.1 (oddMatrixInverseS hn x).1) +
      (oddMatrixDot x.1 (oddMatrixInverseJ hn y).1 +
        oddMatrixDot y.1 (oddMatrixInverseJ hn x).1) = 0 := by
    calc
      _ = (oddMatrixDot y.1 (oddMatrixInverseS hn x).1 +
          oddMatrixDot x.1 (oddMatrixInverseS hn y).1) +
        (oddMatrixDot y.1 (oddMatrixInverseJ hn x).1 +
          oddMatrixDot x.1 (oddMatrixInverseJ hn y).1) := by abel
      _ = oddMatrixDot x.1 y.1 + oddMatrixDot x.1 y.1 := by rw [hs, hj]
      _ = 0 := F_add_self _
  simp only [oddOrbitQuadratic, map_add, Submodule.coe_add,
    oddMatrixDot_add_left, oddMatrixDot_add_right]
  calc
    _ = oddOrbitQuadratic hn x + oddOrbitQuadratic hn y +
        ((oddMatrixDot x.1 (oddMatrixInverseS hn y).1 +
          oddMatrixDot y.1 (oddMatrixInverseS hn x).1) +
        (oddMatrixDot x.1 (oddMatrixInverseJ hn y).1 +
          oddMatrixDot y.1 (oddMatrixInverseJ hn x).1)) := by
            unfold oddOrbitQuadratic
            abel
    _ = oddOrbitQuadratic hn x + oddOrbitQuadratic hn y := by rw [hc, add_zero]

private theorem profileSelfDot_zero {n : Nat} [NeZero n]
    (a : ZeroSumProfile n) : (∑ j : I n, a.1 j * a.1 j) = 0 := by
  calc
    _ = ∑ j : I n, a.1 j := by
      apply Finset.sum_congr rfl
      intro j _
      exact (show ∀ c : F, c * c = c by decide) _
    _ = 0 := LinearMap.mem_ker.mp a.2
private noncomputable def oddOrbitQuadraticLinear {n : Nat} [NeZero n]
    (hn : Odd n) : MatrixZeroSum n →ₗ[F] F where
  toFun := oddOrbitQuadratic hn
  map_add' := oddOrbitQuadratic_add hn
  map_smul' c x := by
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · left; change (0 : F) = 0; rfl
      · right; change (1 : F) = 1; rfl
    rcases hc with rfl | rfl
    · simp [oddOrbitQuadratic, oddMatrixDot]
    · simp
private noncomputable def oddMatrixCoordEquiv {n : Nat} [NeZero n] :
    MatrixZeroSum n ≃ₗ[F]
      ((p : Sigma (fun _ : NonzeroI n => NonzeroI n)) → F) :=
  (matrixZeroSumEquivNonzero2 (n := n)).trans
    (LinearEquiv.piCurry F
      (fun _ : NonzeroI n => fun _ : NonzeroI n => F)).symm
private theorem oddMatrixCoordSingle_apply {n : Nat} [NeZero n]
    (p : Sigma (fun _ : NonzeroI n => NonzeroI n)) (j s : I n) :
    ((oddMatrixCoordEquiv (n := n)).symm (Pi.single p (1 : F))).1 j s =
      (pullProfile (n := n) (Pi.single p.1 (1 : F))).1 j *
      (pullProfile (n := n) (Pi.single p.2 (1 : F))).1 s := by
  classical
  rcases p with ⟨r, t⟩
  change pullMatrixVal
      (fun r' t' => (Pi.single (Sigma.mk r t) (1 : F) :
        ((p : Sigma (fun _ : NonzeroI n => NonzeroI n)) → F))
        (Sigma.mk r' t')) j s =
    pullProfileVal (Pi.single r (1 : F)) j *
      pullProfileVal (Pi.single t (1 : F)) s
  unfold pullMatrixVal pullProfileVal
  by_cases hj : j = 0 <;> by_cases hs : s = 0
  · subst j; subst s; simp only [Pi.single_apply]
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single t] <;> simp
    · intro r' _ hr'; simp [hr']
    · simp
  · subst j
    let s' : NonzeroI n := ⟨s, hs⟩
    by_cases h : s' = t <;> simp [hs, Pi.single_apply, s', h]
  · subst s
    let j' : NonzeroI n := ⟨j, hj⟩
    by_cases h : j' = r <;> simp [hj, Pi.single_apply, j', h]
  · let j' : NonzeroI n := ⟨j, hj⟩
    let s' : NonzeroI n := ⟨s, hs⟩
    by_cases hr : j' = r <;> by_cases ht : s' = t <;>
      simp [hj, hs, Pi.single_apply, j', s', hr, ht]
private theorem oddOrbitQuadratic_coordSingle {n : Nat} [NeZero n]
    (hn : Odd n) (p : Sigma (fun _ : NonzeroI n => NonzeroI n)) :
    oddOrbitQuadratic hn
      ((oddMatrixCoordEquiv (n := n)).symm (Pi.single p (1 : F))) = 0 := by
  classical
  let x := (oddMatrixCoordEquiv (n := n)).symm (Pi.single p (1 : F))
  let a : ZeroSumProfile n := pullProfile (n := n) (Pi.single p.1 (1 : F))
  let b : ZeroSumProfile n := pullProfile (n := n) (Pi.single p.2 (1 : F))
  have hx (j s : I n) : x.1 j s = a.1 j * b.1 s :=
    oddMatrixCoordSingle_apply p j s
  have hS (j s : I n) : (oddMatrixInverseS hn x).1 j s =
      a.1 j * (oddCyclicInverse hn b).1 s := by
    have hr : (⟨fun t => x.1 j t, matrix_row_zero x j⟩ :
        ZeroSumProfile n) = a.1 j • b := by
      apply Subtype.ext; funext t
      simp only [hx, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
    rw [oddMatrixInverseS_apply, hr]
    exact congrArg (fun u : ZeroSumProfile n => u.1 s)
      ((oddCyclicInverse hn).map_smul (a.1 j) b)
  have hJ (j s : I n) : (oddMatrixInverseJ hn x).1 j s =
      (oddCyclicInverse hn a).1 j * b.1 s := by
    have hc : (⟨fun t => x.1 t s, matrix_col_zero x s⟩ :
        ZeroSumProfile n) = b.1 s • a := by
      apply Subtype.ext; funext t
      simp only [hx, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
    rw [oddMatrixInverseJ_apply, hc]
    simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      mul_comm] using congrArg (fun u : ZeroSumProfile n => u.1 j)
        ((oddCyclicInverse hn).map_smul (b.1 s) a)
  change oddOrbitQuadratic hn x = 0
  simp only [oddOrbitQuadratic, oddMatrixDot, hx, hS, hJ]
  have h1 : (∑ j, ∑ s, (a.1 j * b.1 s) *
      (a.1 j * (oddCyclicInverse hn b).1 s)) =
      (∑ j, a.1 j * a.1 j) *
        (∑ s, b.1 s * (oddCyclicInverse hn b).1 s) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
  have h2 : (∑ j, ∑ s, (a.1 j * b.1 s) *
      ((oddCyclicInverse hn a).1 j * b.1 s)) =
      (∑ j, a.1 j * (oddCyclicInverse hn a).1 j) *
        (∑ s, b.1 s * b.1 s) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
  rw [h1, h2, profileSelfDot_zero a, profileSelfDot_zero b]
  ring
theorem oddOrbitQuadratic_eq_zero
    {n : Nat} [NeZero n] (hn : Odd n) (x : MatrixZeroSum n) :
    oddOrbitQuadratic hn x = 0 := by
  let L := (oddOrbitQuadraticLinear hn).comp
    (oddMatrixCoordEquiv (n := n)).symm.toLinearMap
  have hL : L = 0 := by
    apply (Pi.basisFun F
      (Sigma (fun _ : NonzeroI n => NonzeroI n))).ext
    intro p
    rw [Pi.basisFun_apply]
    exact oddOrbitQuadratic_coordSingle hn p
  have h := congrArg (fun M => M (oddMatrixCoordEquiv x)) hL
  change oddOrbitQuadratic hn
    ((oddMatrixCoordEquiv).symm (oddMatrixCoordEquiv x)) = 0 at h
  rwa [LinearEquiv.symm_apply_apply] at h
theorem diamondOddOrbitRelation_q_eq_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddOrbitRelation n hn) :
    oddMatrixDot z.1.1.1 z.1.2 = 0 := by
  rw [oddOrbitRelation_normal_form hn z, oddMatrixDot_add_right,
    oddMatrixDot_add_right]
  change oddOrbitQuadratic hn (oddOrbitRelationX z) +
    oddMatrixDot (oddOrbitRelationX z).1
      (fun j _ => oddOrbitRelationH z j) = 0
  rw [oddOrbitQuadratic_eq_zero, zero_add]
  unfold oddMatrixDot
  apply Finset.sum_eq_zero
  intro j _
  change (∑ s : I n,
    (oddOrbitRelationX z).1 j s * oddOrbitRelationH z j) = 0
  rw [← Finset.sum_mul, matrix_row_zero, zero_mul]

end

end Core4loop.SquareDiagonal.DirectWitt
