import Core4loop.ZeroSumSpaces.ExplicitCyclicPrefix
import Core4loop.ZeroSumSpaces.Matrix
open scoped BigOperators
namespace Core4loop.SquareDiagonal.EvenP
open Core4loop
noncomputable section
abbrev CubeOrbitConst (n : Nat) := MatrixProfile n
abbrev CubeMatrixConstSumParam (n : Nat) [NeZero n] :=
  ZeroSumProfileM n (Profile n) × F
noncomputable def cubeDiffI {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n :=
  cycDiff (n := n) (MatrixProfile n)
private noncomputable def cubeStepDiff {n : Nat} [NeZero n] (di dj dk : I n) : CyclicCube n →ₗ[F] CyclicCube n where
  toFun f := fun i j k => f i j k + f (i + di) (j + dj) (k + dk)
  map_add' f g := by funext i j k; simp only [Pi.add_apply]; abel
  map_smul' r f := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
noncomputable def cubeDiffK {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n := cubeStepDiff 0 0 1
noncomputable def cubeDiffJInv {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n := cubeStepDiff 0 (-1) 0
noncomputable def cubeDiffP {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n := cubeStepDiff 1 (-1) 0
noncomputable def cubeDiffR {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n := cubeStepDiff 0 (-1) 1
noncomputable def cubeDiffJStar {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n := cubeStepDiff 0 1 0
noncomputable def cubeDiffPStar {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n := cubeStepDiff (-1) 1 0
noncomputable def cubeDiffRStar {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CyclicCube n := cubeStepDiff 0 1 (-1)
@[simp] private theorem cubeDiffI_apply {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffI f i j k = f i j k + f (i + 1) j k := rfl
@[simp] private theorem cubeDiffK_apply {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  simp [cubeDiffK, cubeStepDiff]
@[simp] private theorem cubeDiffP_apply {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffP f i j k = f i j k + f (i + 1) (j - 1) k := by
  simp [cubeDiffP, cubeStepDiff, sub_eq_add_neg]
@[simp] private theorem cubeDiffR_apply {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffR f i j k = f i j k + f i (j - 1) (k + 1) := by
  simp [cubeDiffR, cubeStepDiff, sub_eq_add_neg]
@[simp] private theorem cubeDiffJStar_apply {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffJStar f i j k = f i j k + f i (j + 1) k := by
  simp [cubeDiffJStar, cubeStepDiff]
@[simp] private theorem cubeDiffRStar_apply {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffRStar f i j k = f i j k + f i (j + 1) (k - 1) := by
  simp [cubeDiffRStar, cubeStepDiff, sub_eq_add_neg]
noncomputable def CubeOrbitZero (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  ZeroSumProfileM n (MatrixProfile n)
noncomputable def cubeDiffToOrbitZero {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] CubeOrbitZero n :=
  LinearMap.codRestrict (CubeOrbitZero n) cubeDiffI
    (fun f => cycDiff_mem_ZeroSumProfileM f)
private theorem cubeOrbitZero_sum {n : Nat} [NeZero n] (X : CubeOrbitZero n) (j k : I n) : (∑ i : I n, X.1 i j k) = 0 := by
  have h := LinearMap.mem_ker.mp X.2
  change (∑ i : I n, X.1 i) = 0 at h
  simpa only [Finset.sum_apply, Pi.zero_apply] using
    congrFun (congrFun h j) k
noncomputable def cubeDiffPrefix {n : Nat} [NeZero n] : CubeOrbitZero n →ₗ[F] CyclicCube n where
  toFun X := fun i j k =>
    explicitCyclicPrimitive n
      ⟨fun t => X.1 t j k, cubeOrbitZero_sum X j k⟩ i
  map_add' X Y := by
    funext i j k
    simpa only [Submodule.coe_add, Pi.add_apply] using
      congrArg (fun p : Profile n => p i)
        ((explicitCyclicPrimitive n).map_add ⟨fun t => X.1 t j k, cubeOrbitZero_sum X j k⟩
          ⟨fun t => Y.1 t j k, cubeOrbitZero_sum Y j k⟩)
  map_smul' r X := by
    funext i j k
    simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using
      congrArg (fun p : Profile n => p i)
        ((explicitCyclicPrimitive n).map_smul r ⟨fun t => X.1 t j k, cubeOrbitZero_sum X j k⟩)
theorem cubeDiff_prefix_rightInverse {n : Nat} [NeZero n] (X : CubeOrbitZero n) : cubeDiffToOrbitZero (cubeDiffPrefix X) = X := by
  apply Subtype.ext
  funext i j k
  exact congrFun
    (cycDiff_explicitCyclicPrimitive ⟨fun t => X.1 t j k, cubeOrbitZero_sum X j k⟩) i
theorem cubeDiff_range_eq_orbitZero {n : Nat} [NeZero n] : LinearMap.range (cubeDiffI (n := n)) = CubeOrbitZero n := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact (cubeDiffToOrbitZero f).2
  · intro x hx
    let X : CubeOrbitZero n := ⟨x, hx⟩
    exact ⟨cubeDiffPrefix X,
      congrArg Subtype.val (cubeDiff_prefix_rightInverse X)⟩
noncomputable def cubeDiff_ker_equiv_orbitConst {n : Nat} [NeZero n] : LinearMap.ker (cubeDiffI (n := n)) ≃ₗ[F] CubeOrbitConst n :=
  cycDiffKerEquiv (MatrixProfile n)
private noncomputable def cubePlaneSumIK {n : Nat} [NeZero n] : CyclicCube n →ₗ[F] Profile n where
  toFun f := fun j => ∑ i : I n, ∑ k : I n, f i j k
  map_add' f g := by
    funext j
    simp only [Pi.add_apply]
    simp_rw [Finset.sum_add_distrib]
  map_smul' r f := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← Finset.mul_sum]
noncomputable def CubePlaneZero (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (cubePlaneSumIK (n := n))
noncomputable def cubeStarIK {n : Nat} [NeZero n] : (CyclicCube n × CyclicCube n) →ₗ[F] CyclicCube n :=
  LinearMap.coprod cubeDiffI cubeDiffK
private theorem cubeStarIK_mem_planeZero {n : Nat} [NeZero n] (q : CyclicCube n × CyclicCube n) : cubeStarIK q ∈ CubePlaneZero n := by
  apply LinearMap.mem_ker.mpr
  funext j
  simp only [cubePlaneSumIK, cubeStarIK, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.zero_apply, LinearMap.coprod_apply, Pi.add_apply,
    cubeDiffI_apply, cubeDiffK_apply]
  change
    (∑ i : I n, ∑ k : I n, ((q.1 i j k + q.1 (i + 1) j k) + (q.2 i j k + q.2 i j (k + 1)))) = 0
  have hi :
      (∑ i : I n, ∑ k : I n, q.1 (i + 1) j k) =
        ∑ i : I n, ∑ k : I n, q.1 i j k := by
    simpa using sum_shift (n := n) (1 : I n)
      (fun i => ∑ k : I n, q.1 i j k)
  have hk :
      (∑ i : I n, ∑ k : I n, q.2 i j (k + 1)) =
        ∑ i : I n, ∑ k : I n, q.2 i j k := by
    apply Finset.sum_congr rfl
    intro i _
    simpa using sum_shift (n := n) (1 : I n) (fun k => q.2 i j k)
  simp_rw [Finset.sum_add_distrib]
  rw [hi, hk, F_add_self, F_add_self, zero_add]
private noncomputable def cubePlaneKColumn {n : Nat} [NeZero n] (j : I n) : CubePlaneZero n →ₗ[F] ZeroSumProfile n where
  toFun u := ⟨fun k => ∑ i : I n, u.1 i j k, by
    apply LinearMap.mem_ker.mpr
    change (∑ k : I n, ∑ i : I n, u.1 i j k) = 0
    rw [Finset.sum_comm]
    exact congrFun (LinearMap.mem_ker.mp u.2) j⟩
  map_add' u v := by
    apply Subtype.ext
    funext k
    exact Finset.sum_add_distrib
  map_smul' r u := by
    apply Subtype.ext
    funext k
    change (∑ i : I n, r * u.1 i j k) = r * ∑ i : I n, u.1 i j k
    rw [← Finset.mul_sum]
private noncomputable def cubeStarV {n : Nat} [NeZero n] : CubePlaneZero n →ₗ[F] CyclicCube n where
  toFun u i j k :=
    if i = 0 then explicitCyclicPrimitive n (cubePlaneKColumn j u) k else 0
  map_add' u v := by
    funext i j k
    by_cases hi : i = 0
    · simp only [hi, if_pos, Pi.add_apply]
      rw [map_add, map_add]
      rfl
    · simp [hi]
  map_smul' r u := by
    funext i j k
    by_cases hi : i = 0
    · simp only [hi, if_pos, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [map_smul, map_smul]
      rfl
    · simp [hi]
private theorem sum_cubeStarV {n : Nat} [NeZero n] (u : CubePlaneZero n) (j k : I n) :
    (∑ i : I n, cubeStarV u i j k) = explicitCyclicPrimitive n (cubePlaneKColumn j u) k := by
  classical
  rw [Finset.sum_eq_single (0 : I n)]
  · simp [cubeStarV]
  · intro i _ hi
    simp [cubeStarV, hi]
  · simp
private noncomputable def cubeStarResidualColumn {n : Nat} [NeZero n] (j k : I n) : CubePlaneZero n →ₗ[F] ZeroSumProfile n where
  toFun u := ⟨fun i =>
      u.1 i j k + (cubeStarV u i j k + cubeStarV u i j (k + 1)), by
    apply LinearMap.mem_ker.mpr
    change
      (∑ i : I n, (u.1 i j k + (cubeStarV u i j k + cubeStarV u i j (k + 1)))) = 0
    simp_rw [Finset.sum_add_distrib]
    rw [sum_cubeStarV, sum_cubeStarV]
    have hp := congrFun
      (cycDiff_explicitCyclicPrimitive (cubePlaneKColumn j u)) k
    change
      explicitCyclicPrimitive n (cubePlaneKColumn j u) k +
          explicitCyclicPrimitive n (cubePlaneKColumn j u) (k + 1) =
        (∑ i : I n, u.1 i j k) at hp
    rw [hp]
    exact F_add_self _⟩
  map_add' u v := by
    apply Subtype.ext
    funext i
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    abel
  map_smul' r u := by
    apply Subtype.ext
    funext i
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_smul]
    ring
private noncomputable def cubeStarU {n : Nat} [NeZero n] : CubePlaneZero n →ₗ[F] CyclicCube n where
  toFun u i j k :=
    explicitCyclicPrimitive n (cubeStarResidualColumn j k u) i
  map_add' u v := by
    funext i j k
    rw [map_add, map_add]
    rfl
  map_smul' r u := by
    funext i j k
    rw [map_smul, map_smul]
    rfl
private noncomputable def cubeStarPrimitive {n : Nat} [NeZero n] : CubePlaneZero n →ₗ[F] (CyclicCube n × CyclicCube n) :=
  LinearMap.prod cubeStarU cubeStarV
private theorem cubeStarIK_cubeStarPrimitive {n : Nat} [NeZero n] (u : CubePlaneZero n) : cubeStarIK (cubeStarPrimitive u) = u.1 := by
  funext i j k
  have hp := congrFun
    (cycDiff_explicitCyclicPrimitive (cubeStarResidualColumn j k u)) i
  simp only [cubeStarIK, LinearMap.coprod_apply, Pi.add_apply, cubeDiffI_apply, cubeDiffK_apply]
  change
    (cubeStarU u i j k + cubeStarU u (i + 1) j k) +
        (cubeStarV u i j k + cubeStarV u i j (k + 1)) =
      u.1 i j k
  rw [show cubeStarU u i j k + cubeStarU u (i + 1) j k = (cubeStarResidualColumn j k u).1 i by exact hp]
  change
    (u.1 i j k + (cubeStarV u i j k + cubeStarV u i j (k + 1))) +
        (cubeStarV u i j k + cubeStarV u i j (k + 1)) =
      u.1 i j k
  rw [add_assoc, F_add_self, add_zero]
theorem cubeStarIK_range_eq_planeZero {n : Nat} [NeZero n] : LinearMap.range (cubeStarIK (n := n)) = CubePlaneZero n := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    exact cubeStarIK_mem_planeZero q
  · intro u hu
    exact ⟨cubeStarPrimitive ⟨u, hu⟩,
      cubeStarIK_cubeStarPrimitive ⟨u, hu⟩⟩
private noncomputable def cubePlaneSumLift (n : Nat) [NeZero n] : Profile n →ₗ[F] CyclicCube n where
  toFun h := fun i j k => if i = 0 ∧ k = 0 then h j else 0
  map_add' h q := by
    funext i j k
    by_cases hi : i = 0 <;> by_cases hk : k = 0 <;> simp [hi, hk]
  map_smul' r h := by
    funext i j k
    by_cases hi : i = 0 <;> by_cases hk : k = 0 <;> simp [hi, hk]
private theorem cubePlaneSum_cubePlaneSumLift {n : Nat} [NeZero n] (h : Profile n) : cubePlaneSumIK (cubePlaneSumLift n h) = h := by
  funext j
  classical
  change
    (∑ i : I n, ∑ k : I n, if i = 0 ∧ k = 0 then h j else 0) = h j
  rw [Finset.sum_eq_single (0 : I n)]
  · simp
  · intro i _ hi
    simp [hi]
  · simp
private theorem finrank_cubeField {n : Nat} [NeZero n] : Module.finrank F (CyclicCube n) = n ^ 3 := by
  simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card, pow_succ, mul_assoc]
private theorem finrank_cubePlaneZero {n : Nat} [NeZero n] : Module.finrank F (CubePlaneZero n) = n ^ 3 - n := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker (cubePlaneSumIK (n := n))
  have hrange :
      Module.finrank F (LinearMap.range (cubePlaneSumIK (n := n))) = n := by
    rw [LinearMap.range_eq_top.mpr]
    · rw [finrank_top]
      exact finrank_profile (n := n)
    · intro h
      exact ⟨cubePlaneSumLift n h, cubePlaneSum_cubePlaneSumLift h⟩
  have hsum :
      n + Module.finrank F (CubePlaneZero n) = n ^ 3 := by
    simpa [hrange, finrank_cubeField] using hnull
  omega
theorem finrank_ker_cubeStarIK {n : Nat} [NeZero n] : Module.finrank F (LinearMap.ker (cubeStarIK (n := n))) =
      n ^ 3 + n := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker (cubeStarIK (n := n))
  have hrange :
      Module.finrank F (LinearMap.range (cubeStarIK (n := n))) =
        n ^ 3 - n := by
    rw [cubeStarIK_range_eq_planeZero]
    exact finrank_cubePlaneZero
  have hdom :
      Module.finrank F (CyclicCube n × CyclicCube n) = 2 * n ^ 3 := by
    simp [finrank_cubeField]
    omega
  have hsum :
      (n ^ 3 - n) +
          Module.finrank F (LinearMap.ker (cubeStarIK (n := n))) =
        2 * n ^ 3 := by
    simpa [hrange, hdom] using hnull
  have hnle : n ≤ n ^ 3 := Nat.le_pow (by decide)
  omega
noncomputable def cubePairPRDIMap {n : Nat} [NeZero n] : (CyclicCube n × CyclicCube n) →ₗ[F] (CyclicCube n × CyclicCube n) :=
  LinearMap.prod
    (LinearMap.coprod cubeDiffP cubeDiffR)
    (LinearMap.coprod cubeDiffI cubeDiffK)
noncomputable def CubePairPRDISolution (n : Nat) [NeZero n] : Submodule F (CyclicCube n × CyclicCube n) :=
  LinearMap.ker (cubePairPRDIMap (n := n))
private noncomputable def matrixConstBuild {n : Nat} [NeZero n] : CubeMatrixConstSumParam n →ₗ[F] MatrixProfile n where
  toFun p := fun i s => p.1.1 i s + if i = 0 then p.2 else 0
  map_add' p q := by
    funext i s
    by_cases hi : i = 0
    · subst i
      simp
      abel
    · simp [hi]
  map_smul' r p := by
    funext i s
    by_cases hi : i = 0
    · subst i
      simp
      ring
    · simp [hi]
private theorem sum_matrixConstBuild {n : Nat} [NeZero n] (p : CubeMatrixConstSumParam n) (s : I n) :
    (∑ i : I n, matrixConstBuild p i s) = p.2 := by
  classical
  change
    (∑ i : I n, (p.1.1 i s + if i = 0 then p.2 else 0)) = p.2
  rw [Finset.sum_add_distrib]
  have hK := LinearMap.mem_ker.mp p.1.2
  change (∑ i : I n, p.1.1 i) = 0 at hK
  have hKs := congrFun hK s
  simp only [Finset.sum_apply, Pi.zero_apply] at hKs
  rw [hKs, zero_add]
  simp
private noncomputable def pairOrbitR {n : Nat} [NeZero n] : (CubeMatrixConstSumParam n × MatrixProfile n) →ₗ[F] CubeOrbitZero n where
  toFun p :=
    ⟨fun i _ t =>
        matrixConstBuild p.1 i (t - 1) + matrixConstBuild p.1 i t,
      by
        apply LinearMap.mem_ker.mpr
        funext j t
        simp only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.zero_apply]
        change
          (∑ i : I n, (matrixConstBuild p.1 i (t - 1) + matrixConstBuild p.1 i t)) = 0
        rw [Finset.sum_add_distrib, sum_matrixConstBuild, sum_matrixConstBuild, F_add_self]⟩
  map_add' p q := by
    apply Subtype.ext
    funext i j t
    change
      matrixConstBuild (p.1 + q.1) i (t - 1) +
          matrixConstBuild (p.1 + q.1) i t =
        (matrixConstBuild p.1 i (t - 1) + matrixConstBuild p.1 i t) +
          (matrixConstBuild q.1 i (t - 1) + matrixConstBuild q.1 i t)
    rw [map_add]
    simp only [Pi.add_apply]
    abel
  map_smul' r p := by
    apply Subtype.ext
    funext i j t
    change
      matrixConstBuild (r • p.1) i (t - 1) +
          matrixConstBuild (r • p.1) i t =
        r * (matrixConstBuild p.1 i (t - 1) + matrixConstBuild p.1 i t)
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
private noncomputable def pairC {n : Nat} [NeZero n] : (CubeMatrixConstSumParam n × MatrixProfile n) →ₗ[F] CyclicCube n where
  toFun p := fun i _ k => matrixConstBuild p.1 i (i + k)
  map_add' p q := by
    funext i j k
    change
      matrixConstBuild (p.1 + q.1) i (i + k) =
        matrixConstBuild p.1 i (i + k) +
          matrixConstBuild q.1 i (i + k)
    exact congrFun (congrFun (map_add matrixConstBuild p.1 q.1) i) (i + k)
  map_smul' r p := by
    funext i j k
    change
      matrixConstBuild (r • p.1) i (i + k) =
        r * matrixConstBuild p.1 i (i + k)
    exact congrFun (congrFun (map_smul matrixConstBuild r p.1) i) (i + k)
private noncomputable def pairB {n : Nat} [NeZero n] : (CubeMatrixConstSumParam n × MatrixProfile n) →ₗ[F] CyclicCube n where
  toFun p := fun i j k =>
    cubeDiffPrefix (pairOrbitR p) i j (i + k) + p.2 j (i + k)
  map_add' p q := by
    funext i j k
    rw [map_add, map_add]
    simp only [Pi.add_apply, Prod.snd_add]
    abel
  map_smul' r p := by
    funext i j k
    rw [map_smul, map_smul]
    simp only [Pi.smul_apply, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring
private theorem pairB_cross {n : Nat} [NeZero n] (p : CubeMatrixConstSumParam n × MatrixProfile n)
    (i j k : I n) : pairB p (i + 1) j k + pairB p i j (k + 1) = pairC p i j k + pairC p i j (k + 1) := by
  have hp := congrArg Subtype.val
    (cubeDiff_prefix_rightInverse (pairOrbitR p))
  have h := congrFun (congrFun (congrFun hp i) j) (i + k + 1)
  change
    (cubeDiffPrefix (pairOrbitR p) i j (i + k + 1) + cubeDiffPrefix (pairOrbitR p) (i + 1) j (i + k + 1)) =
      matrixConstBuild p.1 i (i + k + 1 - 1) +
        matrixConstBuild p.1 i (i + k + 1) at h
  change
    (cubeDiffPrefix (pairOrbitR p) (i + 1) j (i + 1 + k) + p.2 j (i + 1 + k)) +
      (cubeDiffPrefix (pairOrbitR p) i j (i + (k + 1)) + p.2 j (i + (k + 1))) =
      matrixConstBuild p.1 i (i + k) +
        matrixConstBuild p.1 i (i + (k + 1))
  rw [show i + 1 + k = i + k + 1 by abel, show i + (k + 1) = i + k + 1 by abel]
  rw [show i + k + 1 - 1 = i + k by abel] at h
  calc
    (cubeDiffPrefix (pairOrbitR p) (i + 1) j (i + k + 1) + p.2 j (i + k + 1)) +
        (cubeDiffPrefix (pairOrbitR p) i j (i + k + 1) + p.2 j (i + k + 1)) =
      (cubeDiffPrefix (pairOrbitR p) i j (i + k + 1) + cubeDiffPrefix (pairOrbitR p) (i + 1) j (i + k + 1)) +
          (p.2 j (i + k + 1) + p.2 j (i + k + 1)) := by abel
    _ = matrixConstBuild p.1 i (i + k) +
        matrixConstBuild p.1 i (i + k + 1) := by
      rw [F_add_self, add_zero, h]
private noncomputable def pairBuild {n : Nat} [NeZero n] : (CubeMatrixConstSumParam n × MatrixProfile n) →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  LinearMap.prod pairB (pairB + pairC)
private theorem pairBuild_mem {n : Nat} [NeZero n] (p : CubeMatrixConstSumParam n × MatrixProfile n) :
    pairBuild p ∈ CubePairPRDISolution n := by
  apply LinearMap.mem_ker.mpr
  apply Prod.ext <;> funext i j k
  · simp only [cubePairPRDIMap, pairBuild, LinearMap.prod_apply, Pi.prod, LinearMap.coprod_apply, LinearMap.add_apply,
      Prod.fst_zero, Pi.zero_apply, Pi.add_apply,
      cubeDiffP_apply, cubeDiffR_apply]
    change
      (pairB p i j k + pairB p (i + 1) (j - 1) k) +
        ((pairB p i j k + pairC p i j k) + (pairB p i (j - 1) (k + 1) + pairC p i (j - 1) (k + 1))) = 0
    have h := pairB_cross p i (j - 1) k
    change
      pairB p (i + 1) (j - 1) k +
          pairB p i (j - 1) (k + 1) =
        pairC p i (j - 1) k + pairC p i (j - 1) (k + 1) at h
    calc
      (pairB p i j k + pairB p (i + 1) (j - 1) k) +
          ((pairB p i j k + pairC p i j k) + (pairB p i (j - 1) (k + 1) + pairC p i (j - 1) (k + 1))) =
        (pairB p i j k + pairB p i j k) +
          (pairB p (i + 1) (j - 1) k + pairB p i (j - 1) (k + 1)) +
          (pairC p i j k + pairC p i (j - 1) (k + 1)) := by abel
      _ = 0 := by
        rw [F_add_self, zero_add, h]
        change
          (pairC p i j k + pairC p i (j - 1) (k + 1)) +
            (pairC p i j k + pairC p i (j - 1) (k + 1)) = 0
        exact F_add_self _
  · simp only [cubePairPRDIMap, pairBuild, LinearMap.prod_apply, Pi.prod, LinearMap.coprod_apply, LinearMap.add_apply,
      Prod.snd_zero, Pi.zero_apply, Pi.add_apply,
      cubeDiffI_apply, cubeDiffK_apply]
    change
      (pairB p i j k + pairB p (i + 1) j k) +
        ((pairB p i j k + pairC p i j k) + (pairB p i j (k + 1) + pairC p i j (k + 1))) = 0
    have h := pairB_cross p i j k
    calc
      (pairB p i j k + pairB p (i + 1) j k) +
          ((pairB p i j k + pairC p i j k) + (pairB p i j (k + 1) + pairC p i j (k + 1))) =
        (pairB p i j k + pairB p i j k) +
          (pairB p (i + 1) j k + pairB p i j (k + 1)) +
          (pairC p i j k + pairC p i j (k + 1)) := by abel
      _ = 0 := by
        rw [F_add_self, zero_add, h, F_add_self]
private noncomputable def pairBuildSolution {n : Nat} [NeZero n] :
    (CubeMatrixConstSumParam n × MatrixProfile n) →ₗ[F] CubePairPRDISolution n :=
  LinearMap.codRestrict (CubePairPRDISolution n) pairBuild pairBuild_mem
private theorem F_eq_of_add_eq_zero (x y : F) (h : x + y = 0) : x = y := by
  calc
    x = x + 0 := by simp
    _ = x + (y + y) := by rw [F_add_self]
    _ = (x + y) + y := by abel
    _ = y := by rw [h]; simp
private noncomputable def pairReadC {n : Nat} [NeZero n] (z : CubePairPRDISolution n) : CyclicCube n :=
  z.1.1 + z.1.2
private theorem pairReadC_constant {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (i j k : I n) :
    pairReadC z i j k = pairReadC z i 0 k := by
  have hz := LinearMap.mem_ker.mp z.2
  have hpr := congrArg Prod.fst hz
  have hik := congrArg Prod.snd hz
  have hback : ∀ t : I n,
      pairReadC z i t k = pairReadC z i (t - 1) k := by
    intro t
    have h1 := congrFun (congrFun (congrFun hpr i) t) k
    have h2 := congrFun (congrFun (congrFun hik i) (t - 1)) k
    simp only [cubePairPRDIMap, LinearMap.prod_apply, Pi.prod,
      LinearMap.coprod_apply, Prod.fst_zero, Pi.zero_apply, Pi.add_apply,
      cubeDiffP_apply, cubeDiffR_apply] at h1
    simp only [cubePairPRDIMap, LinearMap.prod_apply, Pi.prod,
      LinearMap.coprod_apply, Prod.snd_zero, Pi.zero_apply, Pi.add_apply,
      cubeDiffI_apply, cubeDiffK_apply] at h2
    change
      (z.1.1 i t k + z.1.1 (i + 1) (t - 1) k) +
        (z.1.2 i t k + z.1.2 i (t - 1) (k + 1)) = 0 at h1
    change
      (z.1.1 i (t - 1) k + z.1.1 (i + 1) (t - 1) k) +
        (z.1.2 i (t - 1) k + z.1.2 i (t - 1) (k + 1)) = 0 at h2
    have hp :
        pairReadC z i t k +
          (z.1.1 (i + 1) (t - 1) k + z.1.2 i (t - 1) (k + 1)) = 0 := by
      calc
        _ = (z.1.1 i t k + z.1.1 (i + 1) (t - 1) k) +
            (z.1.2 i t k + z.1.2 i (t - 1) (k + 1)) := by
          simp only [pairReadC, Pi.add_apply]
          abel
        _ = 0 := h1
    have hq :
        pairReadC z i (t - 1) k +
          (z.1.1 (i + 1) (t - 1) k + z.1.2 i (t - 1) (k + 1)) = 0 := by
      calc
        _ = (z.1.1 i (t - 1) k + z.1.1 (i + 1) (t - 1) k) +
            (z.1.2 i (t - 1) k + z.1.2 i (t - 1) (k + 1)) := by
          simp only [pairReadC, Pi.add_apply]
          abel
        _ = 0 := h2
    exact (F_eq_of_add_eq_zero _ _ hp).trans
      (F_eq_of_add_eq_zero _ _ hq).symm
  let f : Profile n := fun t => pairReadC z i t k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have h := hback (t + 1)
    change f t + f (t + 1) = 0
    rw [show f (t + 1) = f t by
      simpa [f, show t + 1 - 1 = t by abel] using h]
    exact F_add_self _
  exact (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
private theorem pairSolution_cross {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (i j k : I n) :
    z.1.1 (i + 1) j k + z.1.1 i j (k + 1) = pairReadC z i j k + pairReadC z i j (k + 1) := by
  have hz := LinearMap.mem_ker.mp z.2
  have h := congrFun (congrFun (congrFun (congrArg Prod.snd hz) i) j) k
  simp only [cubePairPRDIMap, LinearMap.prod_apply, Pi.prod,
    LinearMap.coprod_apply, Prod.snd_zero, Pi.zero_apply, Pi.add_apply,
    cubeDiffI_apply, cubeDiffK_apply] at h
  change
    (z.1.1 i j k + z.1.1 (i + 1) j k) +
      (z.1.2 i j k + z.1.2 i j (k + 1)) = 0 at h
  apply F_eq_of_add_eq_zero
  change
    (z.1.1 (i + 1) j k + z.1.1 i j (k + 1)) +
      ((z.1.1 i j k + z.1.2 i j k) + (z.1.1 i j (k + 1) + z.1.2 i j (k + 1))) = 0
  calc
    _ = (z.1.1 i j (k + 1) + z.1.1 i j (k + 1)) +
        ((z.1.1 i j k + z.1.1 (i + 1) j k) + (z.1.2 i j k + z.1.2 i j (k + 1))) := by abel
    _ = 0 := by rw [F_add_self, zero_add, h]
private noncomputable def pairReadM {n : Nat} [NeZero n] (z : CubePairPRDISolution n) : MatrixProfile n :=
  fun i s => pairReadC z i 0 (s - i)
private noncomputable def pairReadH {n : Nat} [NeZero n] (z : CubePairPRDISolution n) : Profile n :=
  fun s => ∑ i : I n, pairReadM z i s
private theorem pairReadH_step {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (s : I n) :
    pairReadH z (s - 1) + pairReadH z s = 0 := by
  have hsum :
      (∑ i : I n, (z.1.1 (i + 1) 0 (s - 1 - i) + z.1.1 i 0 (s - i))) =
      ∑ i : I n,
        (pairReadC z i 0 (s - 1 - i) + pairReadC z i 0 (s - i)) := by
    apply Finset.sum_congr rfl
    intro i _
    simpa [show s - 1 - i + 1 = s - i by abel] using
      pairSolution_cross z i 0 (s - 1 - i)
  have hshift :
      (∑ i : I n, z.1.1 (i + 1) 0 (s - 1 - i)) =
        ∑ i : I n, z.1.1 i 0 (s - i) := by
    have h := sum_shift (n := n) (1 : I n)
      (fun i => z.1.1 i 0 (s - i))
    have hidx : ∀ i : I n, s - (i + 1) = s - 1 - i :=
      fun i => by abel
    simpa only [hidx] using h
  change
    (∑ i : I n, pairReadC z i 0 (s - 1 - i)) +
      (∑ i : I n, pairReadC z i 0 (s - i)) = 0
  rw [← Finset.sum_add_distrib, ← hsum, Finset.sum_add_distrib, hshift, F_add_self]
private theorem pairReadH_constant {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (s : I n) : pairReadH z s = pairReadH z 0 := by
  let h : Profile n := fun t => pairReadH z (-t)
  have hz : cycDiff (n := n) F h = 0 := by
    funext t
    have hs := pairReadH_step z (-t)
    rw [add_comm] at hs
    simpa [h, show -(t + 1) = -t - 1 by abel] using hs
  have hc := (cycDiff_eq_zero_iff_constant_apply F h).mp hz (-s)
  simpa [h] using hc
private noncomputable def pairReadK {n : Nat} [NeZero n] (z : CubePairPRDISolution n) : ZeroSumProfileM n (Profile n) :=
  ⟨fun i s => pairReadM z i s +
      (if i = 0 then pairReadH z s else 0), by
    apply LinearMap.mem_ker.mpr
    funext s
    simp only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.zero_apply]
    change
      (∑ i : I n, (pairReadM z i s + if i = 0 then pairReadH z s else 0)) = 0
    rw [Finset.sum_add_distrib]
    change pairReadH z s + _ = 0
    simp [F_add_self]⟩
private noncomputable def pairRead {n : Nat} [NeZero n] : CubePairPRDISolution n →ₗ[F]
      (CubeMatrixConstSumParam n × MatrixProfile n) where
  toFun z := ((pairReadK z, pairReadH z 0), fun j t => z.1.1 0 j t)
  map_add' z w := by
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        funext i s
        simp only [pairReadK, pairReadM, pairReadC, pairReadH, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Finset.sum_add_distrib]
        by_cases hi : i = 0 <;> simp [hi] <;> abel
      · simp only [pairReadH, pairReadM, pairReadC, Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply,
          Finset.sum_add_distrib]
        abel
    · rfl
  map_smul' r z := by
    have hsum (s : I n) :
        (∑ x : I n, (r * z.1.1 x 0 (s - x) + r * z.1.2 x 0 (s - x))) =
          r * ∑ x : I n,
            (z.1.1 x 0 (s - x) + z.1.2 x 0 (s - x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        funext i s
        simp only [pairReadK, pairReadM, pairReadC, pairReadH, Submodule.coe_smul_of_tower, Prod.smul_fst, Prod.smul_snd,
          Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingHom.id_apply]
        by_cases hi : i = 0
        · subst i
          simp only [if_pos]
          rw [hsum]
          ring
        · simp [hi]
          ring
      · simp only [pairReadH, pairReadM, pairReadC, Submodule.coe_smul_of_tower, Prod.smul_fst, Prod.smul_snd,
          Pi.smul_apply, Pi.add_apply, smul_eq_mul, RingHom.id_apply]
        exact hsum 0
    · rfl
private theorem pairReadM_build {n : Nat} [NeZero n] (p : CubeMatrixConstSumParam n × MatrixProfile n) (i s : I n) :
    pairReadM (pairBuildSolution p) i s = matrixConstBuild p.1 i s := by
  change
    pairB p i 0 (s - i) +
      (pairB p i 0 (s - i) + pairC p i 0 (s - i)) =
        matrixConstBuild p.1 i s
  rw [show pairB p i 0 (s - i) + (pairB p i 0 (s - i) + pairC p i 0 (s - i)) = pairC p i 0 (s - i) by
      calc
        _ = (pairB p i 0 (s - i) + pairB p i 0 (s - i)) +
            pairC p i 0 (s - i) := by abel
        _ = pairC p i 0 (s - i) := by rw [F_add_self, zero_add]]
  change matrixConstBuild p.1 i (i + (s - i)) = _
  rw [show i + (s - i) = s by abel]
private theorem pairReadH_build {n : Nat} [NeZero n] (p : CubeMatrixConstSumParam n × MatrixProfile n) (s : I n) :
    pairReadH (pairBuildSolution p) s = p.1.2 := by
  simp only [pairReadH, pairReadM_build]
  exact sum_matrixConstBuild p.1 s
private theorem pairPrefix_zero {n : Nat} [NeZero n] (X : CubeOrbitZero n) (j k : I n) : cubeDiffPrefix X 0 j k = 0 := by
  simp [cubeDiffPrefix, explicitCyclicPrimitive, explicitCyclicPrefixLinear, explicitCyclicPrefix, finPrefix_zero]
private theorem pairRead_build {n : Nat} [NeZero n] (p : CubeMatrixConstSumParam n × MatrixProfile n) :
    pairRead (pairBuildSolution p) = p := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      funext i s
      change
        pairReadM (pairBuildSolution p) i s +
            (if i = 0 then pairReadH (pairBuildSolution p) s else 0) =
          p.1.1.1 i s
      rw [pairReadM_build, pairReadH_build]
      change
        (p.1.1.1 i s + if i = 0 then p.1.2 else 0) +
            (if i = 0 then p.1.2 else 0) =
          p.1.1.1 i s
      by_cases hi : i = 0
      · subst i
        simp only [if_pos]
        calc
          p.1.1.1 0 s + p.1.2 + p.1.2 =
              p.1.1.1 0 s + (p.1.2 + p.1.2) := by abel
          _ = p.1.1.1 0 s := by rw [F_add_self, add_zero]
      · simp [hi]
    · change pairReadH (pairBuildSolution p) 0 = p.1.2
      exact pairReadH_build p 0
  · funext j t
    change pairB p 0 j t = p.2 j t
    simp [pairB, pairPrefix_zero]
private theorem matrixConstBuild_pairRead {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (i s : I n) :
    matrixConstBuild (pairRead z).1 i s = pairReadM z i s := by
  change
    (pairReadM z i s + if i = 0 then pairReadH z s else 0) +
        (if i = 0 then pairReadH z 0 else 0) =
      pairReadM z i s
  rw [pairReadH_constant z s]
  by_cases hi : i = 0
  · subst i
    simp only [if_pos]
    calc
      pairReadM z 0 s + pairReadH z 0 + pairReadH z 0 =
          pairReadM z 0 s + (pairReadH z 0 + pairReadH z 0) := by abel
      _ = pairReadM z 0 s := by rw [F_add_self, add_zero]
  · simp [hi]
private theorem pairC_buildRead {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (i j k : I n) :
    pairC (pairRead z) i j k = pairReadC z i j k := by
  change matrixConstBuild (pairRead z).1 i (i + k) = pairReadC z i j k
  rw [matrixConstBuild_pairRead]
  change pairReadC z i 0 (i + k - i) = _
  rw [show i + k - i = k by abel]
  exact (pairReadC_constant z i j k).symm
private theorem pairOrbitR_buildRead {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (j t : I n) :
    (fun i => (pairOrbitR (pairRead z)).1 i j t) = cycDiff (n := n) F (fun i => z.1.1 i j (t - i)) := by
  funext i
  have h := pairSolution_cross z i j (t - 1 - i)
  rw [show t - 1 - i + 1 = t - i by abel] at h
  change
    matrixConstBuild (pairRead z).1 i (t - 1) +
        matrixConstBuild (pairRead z).1 i t =
      z.1.1 i j (t - i) + z.1.1 (i + 1) j (t - (i + 1))
  rw [matrixConstBuild_pairRead, matrixConstBuild_pairRead]
  simp only [pairReadM]
  rw [← pairReadC_constant z i j (t - 1 - i), ← pairReadC_constant z i j (t - i)]
  rw [show t - (i + 1) = t - 1 - i by abel]
  rw [← h]
  abel
private theorem pairB_buildRead {n : Nat} [NeZero n] (z : CubePairPRDISolution n) (i j k : I n) :
    pairB (pairRead z) i j k = z.1.1 i j k := by
  let f : Profile n := fun x => z.1.1 x j (i + k - x)
  have hp := explicitCyclicPrefix_cycDiff_apply f i
  change
    cubeDiffPrefix (pairOrbitR (pairRead z)) i j (i + k) +
      z.1.1 0 j (i + k) = z.1.1 i j k
  rw [show cubeDiffPrefix (pairOrbitR (pairRead z)) i j (i + k) = explicitCyclicPrefix (cycDiff (n := n) F f) i by
        change explicitCyclicPrefix
          (fun x => (pairOrbitR (pairRead z)).1 x j (i + k)) i =
            explicitCyclicPrefix (cycDiff (n := n) F f) i
        rw [pairOrbitR_buildRead z j (i + k)]]
  rw [hp]
  simp only [f]
  rw [show i + k - 0 = i + k by simp, show i + k - i = k by abel]
  calc
    _ =
      (z.1.1 0 j (i + k) + z.1.1 0 j (i + k)) +
        z.1.1 i j k := by abel
    _ = z.1.1 i j k := by rw [F_add_self, zero_add]
private theorem pairBuild_read {n : Nat} [NeZero n] (z : CubePairPRDISolution n) : pairBuildSolution (pairRead z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · funext i j k
    exact pairB_buildRead z i j k
  · funext i j k
    change
      pairB (pairRead z) i j k + pairC (pairRead z) i j k = z.1.2 i j k
    rw [pairB_buildRead, pairC_buildRead]
    change z.1.1 i j k + (z.1.1 i j k + z.1.2 i j k) = z.1.2 i j k
    calc
      _ = (z.1.1 i j k + z.1.1 i j k) + z.1.2 i j k := by abel
      _ = z.1.2 i j k := by rw [F_add_self, zero_add]
noncomputable def cubePairPRDI_equiv {n : Nat} [NeZero n] : CubePairPRDISolution n ≃ₗ[F]
      CubeMatrixConstSumParam n × MatrixProfile n where
  toFun := pairRead
  invFun := pairBuildSolution
  left_inv := pairBuild_read
  right_inv := pairRead_build
  map_add' := map_add pairRead
  map_smul' := map_smul pairRead
noncomputable def cubeRInvariantMultiplierMap {n : Nat} [NeZero n] : (CyclicCube n × CyclicCube n) →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  LinearMap.prod
    (cubeDiffRStar.comp (LinearMap.snd F (CyclicCube n) (CyclicCube n)))
    (LinearMap.coprod cubeDiffI cubeDiffJStar)
noncomputable def CubeRInvariantMultiplierSolution (n : Nat) [NeZero n] : Submodule F (CyclicCube n × CyclicCube n) :=
  LinearMap.ker (cubeRInvariantMultiplierMap (n := n))
private theorem rSolution_invariant {n : Nat} [NeZero n] (z : CubeRInvariantMultiplierSolution n)
    (i j k : I n) : z.1.2 i j k = z.1.2 i 0 (j + k) := by
  have hz := LinearMap.mem_ker.mp z.2
  have hr : cubeDiffRStar z.1.2 = 0 := by
    calc
      cubeDiffRStar z.1.2 = (cubeRInvariantMultiplierMap z.1).1 := by rfl
      _ = 0 := congrArg Prod.fst hz
  let f : Profile n := fun t => z.1.2 i t (j + k - t)
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have ht := congrFun (congrFun (congrFun hr i) t) (j + k - t)
    change
      z.1.2 i t (j + k - t) +
        z.1.2 i (t + 1) (j + k - (t + 1)) = 0
    simpa [cubeDiffRStar_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ht
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
  simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hc
private noncomputable def rToPairRaw {n : Nat} [NeZero n] : (CyclicCube n × CyclicCube n) →ₗ[F] (CyclicCube n × CyclicCube n) where
  toFun z :=
    let Bp : CyclicCube n := fun i j k => z.1 i j (i + k - j - 1)
    let Cp : CyclicCube n := fun i _ k => z.2 i 0 (i + k)
    (Bp, Bp + Cp)
  map_add' x y := by
    apply Prod.ext <;> funext i j k
    · rfl
    · simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext i j k
      change r * x.1 i j (i + k - j - 1) + r * x.2 i 0 (i + k) =
        r * (x.1 i j (i + k - j - 1) + x.2 i 0 (i + k))
      rw [mul_add]
private theorem rToPairRaw_mem {n : Nat} [NeZero n] (z : CubeRInvariantMultiplierSolution n) :
    rToPairRaw z.1 ∈ CubePairPRDISolution n := by
  have hz := LinearMap.mem_ker.mp z.2
  have hd : cubeDiffI z.1.1 + cubeDiffJStar z.1.2 = 0 := by
    calc
      cubeDiffI z.1.1 + cubeDiffJStar z.1.2 =
          (cubeRInvariantMultiplierMap z.1).2 := by rfl
      _ = 0 := congrArg Prod.snd hz
  apply LinearMap.mem_ker.mpr
  apply Prod.ext <;> funext i j k
  · have h := congrFun (congrFun (congrFun hd i) (j - 1)) (i + k - j + 1)
    simp only [Pi.add_apply, cubeDiffI_apply, cubeDiffJStar_apply, Pi.zero_apply] at h
    rw [rSolution_invariant z i (j - 1) (i + k - j + 1)] at h
    rw [show j - 1 + 1 = j by ring] at h
    rw [rSolution_invariant z i j (i + k - j + 1)] at h
    simp only [show j - 1 + (i + k - j + 1) = i + k by ring, show j + (i + k - j + 1) = i + k + 1 by ring] at h
    simp only [cubePairPRDIMap, LinearMap.prod_apply, Pi.prod,
      LinearMap.coprod_apply, rToPairRaw, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply,
      Prod.fst_zero, Pi.zero_apply, cubeDiffP_apply, cubeDiffR_apply]
    rw [show i + 1 + k - (j - 1) - 1 = i + k - j + 1 by ring, show i + (k + 1) - (j - 1) - 1 = i + k - j + 1 by ring,
      show i + (k + 1) = i + k + 1 by ring]
    calc
      _ = (z.1.1 i j (i + k - j - 1) + z.1.1 i j (i + k - j - 1)) +
          ((z.1.1 (i + 1) (j - 1) (i + k - j + 1) + z.1.1 i (j - 1) (i + k - j + 1)) +
          (z.1.2 i 0 (i + k) + z.1.2 i 0 (i + k + 1))) := by abel
      _ = 0 := by rw [F_add_self, zero_add]; simpa [add_comm] using h
  · have h := congrFun (congrFun (congrFun hd i) j) (i + k - j)
    simp only [Pi.add_apply, cubeDiffI_apply, cubeDiffJStar_apply, Pi.zero_apply] at h
    rw [rSolution_invariant z i j (i + k - j), rSolution_invariant z i (j + 1) (i + k - j)] at h
    simp only [show j + (i + k - j) = i + k by ring, show j + 1 + (i + k - j) = i + k + 1 by ring] at h
    simp only [cubePairPRDIMap, LinearMap.prod_apply, Pi.prod,
      LinearMap.coprod_apply, rToPairRaw, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply,
      Prod.snd_zero, Pi.zero_apply, cubeDiffI_apply, cubeDiffK_apply]
    rw [show i + 1 + k - j - 1 = i + k - j by ring, show i + (k + 1) - j - 1 = i + k - j by ring,
      show i + (k + 1) = i + k + 1 by ring]
    calc
      _ = (z.1.1 i j (i + k - j - 1) + z.1.1 i j (i + k - j - 1)) +
          ((z.1.1 (i + 1) j (i + k - j) + z.1.1 i j (i + k - j)) + (z.1.2 i 0 (i + k) + z.1.2 i 0 (i + k + 1))) := by abel
      _ = 0 := by rw [F_add_self, zero_add]; simpa [add_comm] using h
private noncomputable def rToPair {n : Nat} [NeZero n] : CubeRInvariantMultiplierSolution n →ₗ[F] CubePairPRDISolution n :=
  LinearMap.codRestrict (CubePairPRDISolution n)
    (rToPairRaw.comp (CubeRInvariantMultiplierSolution n).subtype)
    rToPairRaw_mem
private noncomputable def pairToRRaw {n : Nat} [NeZero n] : (CyclicCube n × CyclicCube n) →ₗ[F] (CyclicCube n × CyclicCube n) where
  toFun z :=
    (fun i j k => z.1 i j (j + k + 1 - i), fun i j k => z.1 i 0 (j + k - i) + z.2 i 0 (j + k - i))
  map_add' x y := by
    apply Prod.ext <;> funext i j k
    · rfl
    · simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
      abel
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext i j k
      change r * x.1 i 0 (j + k - i) + r * x.2 i 0 (j + k - i) =
        r * (x.1 i 0 (j + k - i) + x.2 i 0 (j + k - i))
      rw [mul_add]
private theorem pairToRRaw_mem {n : Nat} [NeZero n] (z : CubePairPRDISolution n) :
    pairToRRaw z.1 ∈ CubeRInvariantMultiplierSolution n := by
  have hz := LinearMap.mem_ker.mp z.2
  have hd : cubeDiffI z.1.1 + cubeDiffK z.1.2 = 0 := by
    calc
      cubeDiffI z.1.1 + cubeDiffK z.1.2 =
          (cubePairPRDIMap z.1).2 := by rfl
      _ = 0 := congrArg Prod.snd hz
  apply LinearMap.mem_ker.mpr
  apply Prod.ext <;> funext i j k
  · simp only [cubeRInvariantMultiplierMap, LinearMap.prod_apply, Pi.prod,
      LinearMap.comp_apply, LinearMap.coprod_apply, pairToRRaw,
      LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.snd_apply, Prod.fst_zero, Pi.zero_apply, cubeDiffRStar_apply]
    rw [show j + 1 + (k - 1) - i = j + k - i by ring, F_add_self]
  · have h := congrFun (congrFun (congrFun hd i) j) (j + k - i)
    simp only [Pi.add_apply, cubeDiffI_apply, cubeDiffK_apply, Pi.zero_apply] at h
    simp only [cubeRInvariantMultiplierMap, LinearMap.prod_apply, Pi.prod,
      LinearMap.coprod_apply, pairToRRaw, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.add_apply,
      Prod.snd_zero, Pi.zero_apply, cubeDiffI_apply, cubeDiffJStar_apply]
    rw [show j + 1 + k - i = j + k + 1 - i by ring]
    rw [show j + k - i + 1 = j + k + 1 - i by ring] at h
    change
      z.1.1 i j (j + k + 1 - i) +
          z.1.1 (i + 1) j (j + k + 1 - (i + 1)) +
        (pairReadC z i 0 (j + k - i) + pairReadC z i 0 (j + k + 1 - i)) = 0
    rw [← pairReadC_constant z i j (j + k - i), ← pairReadC_constant z i j (j + k + 1 - i)]
    rw [show j + k + 1 - (i + 1) = j + k - i by ring]
    change
      z.1.1 i j (j + k + 1 - i) +
          z.1.1 (i + 1) j (j + k - i) +
        ((z.1.1 i j (j + k - i) + z.1.2 i j (j + k - i)) + (z.1.1 i j (j + k + 1 - i) + z.1.2 i j (j + k + 1 - i))) = 0
    calc
      _ = (z.1.1 i j (j + k + 1 - i) + z.1.1 i j (j + k + 1 - i)) +
          ((z.1.1 i j (j + k - i) + z.1.1 (i + 1) j (j + k - i)) + (z.1.2 i j (j + k - i) +
            z.1.2 i j (j + k + 1 - i))) := by abel
      _ = 0 := by rw [F_add_self, zero_add, h]
private noncomputable def pairToR {n : Nat} [NeZero n] : CubePairPRDISolution n →ₗ[F] CubeRInvariantMultiplierSolution n :=
  LinearMap.codRestrict (CubeRInvariantMultiplierSolution n)
    (pairToRRaw.comp (CubePairPRDISolution n).subtype) pairToRRaw_mem
private theorem pairToR_rToPair {n : Nat} [NeZero n] (z : CubeRInvariantMultiplierSolution n) : pairToR (rToPair z) = z := by
  apply Subtype.ext
  apply Prod.ext <;> funext i j k
  · change z.1.1 i j (i + (j + k + 1 - i) - j - 1) = z.1.1 i j k
    rw [show i + (j + k + 1 - i) - j - 1 = k by ring]
  · change
      z.1.1 i 0 (i + (j + k - i) - 0 - 1) +
          (z.1.1 i 0 (i + (j + k - i) - 0 - 1) + z.1.2 i 0 (i + (j + k - i))) = z.1.2 i j k
    rw [show i + (j + k - i) - 0 - 1 = j + k - 1 by ring, show i + (j + k - i) = j + k by ring]
    rw [show z.1.1 i 0 (j + k - 1) + (z.1.1 i 0 (j + k - 1) + z.1.2 i 0 (j + k)) = z.1.2 i 0 (j + k) by
        calc
          _ = (z.1.1 i 0 (j + k - 1) + z.1.1 i 0 (j + k - 1)) +
              z.1.2 i 0 (j + k) := by abel
          _ = z.1.2 i 0 (j + k) := by rw [F_add_self, zero_add]]
    exact (rSolution_invariant z i j k).symm
private theorem rToPair_pairToR {n : Nat} [NeZero n] (z : CubePairPRDISolution n) : rToPair (pairToR z) = z := by
  apply Subtype.ext
  apply Prod.ext <;> funext i j k
  · change (rToPairRaw (pairToRRaw z.1)).1 i j k = z.1.1 i j k
    simp only [rToPairRaw, pairToRRaw, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show j + (i + k - j - 1) + 1 - i = k by ring]
  · change (rToPairRaw (pairToRRaw z.1)).2 i j k = z.1.2 i j k
    simp only [rToPairRaw, pairToRRaw, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
    rw [show j + (i + k - j - 1) + 1 - i = k by ring, show 0 + (i + k) - i = k by ring]
    change z.1.1 i j k + pairReadC z i 0 k = z.1.2 i j k
    rw [← pairReadC_constant z i j k]
    change z.1.1 i j k + (z.1.1 i j k + z.1.2 i j k) = z.1.2 i j k
    calc
      _ = (z.1.1 i j k + z.1.1 i j k) + z.1.2 i j k := by abel
      _ = z.1.2 i j k := by rw [F_add_self, zero_add]
private noncomputable def rPairEquiv {n : Nat} [NeZero n] : CubeRInvariantMultiplierSolution n ≃ₗ[F] CubePairPRDISolution n where
  toFun := rToPair
  invFun := pairToR
  left_inv := pairToR_rToPair
  right_inv := rToPair_pairToR
  map_add' := map_add rToPair
  map_smul' := map_smul rToPair
noncomputable def cubeRInvariantMultiplier_equiv {n : Nat} [NeZero n] :
    CubeRInvariantMultiplierSolution n ≃ₗ[F] CubeMatrixConstSumParam n × MatrixProfile n :=
  rPairEquiv.trans cubePairPRDI_equiv
noncomputable def cubeStarMultiplierMap {n : Nat} [NeZero n] : ((CyclicCube n × CyclicCube n) × CyclicCube n) →ₗ[F] CyclicCube n :=
  LinearMap.coprod cubeStarIK cubeDiffJStar
noncomputable def CubeStarMultiplierSolution (n : Nat) [NeZero n] : Submodule F ((CyclicCube n × CyclicCube n) × CyclicCube n) :=
  LinearMap.ker (cubeStarMultiplierMap (n := n))
private theorem module_add_self {V : Type*} [AddCommGroup V] [Module F V] (x : V) : x + x = 0 := by
  have htwo : (1 : F) + 1 = 0 := by decide
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + 1) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]
private noncomputable def ConstantTotal {A : Type*} [AddCommGroup A] [Module F A]
    (n : Nat) [NeZero n] (T : A →ₗ[F] Profile n) : Submodule F A :=
  LinearMap.ker ((cycDiff (n := n) F).comp T)
private noncomputable def constantTotalEquiv {A : Type*} [AddCommGroup A] [Module F A] {n : Nat} [NeZero n]
    (T : A →ₗ[F] Profile n) (delta : F →ₗ[F] A) (hdelta : ∀ a : F, T (delta a) = constantFunctionLinear n F a) :
    ConstantTotal n T ≃ₗ[F] LinearMap.ker T × F where
  toFun z :=
    let a := T z.1 0
    (⟨z.1 + delta a, by
      apply LinearMap.mem_ker.mpr
      rw [map_add, hdelta]
      funext s
      have hz := LinearMap.mem_ker.mp z.2
      change cycDiff (n := n) F (T z.1) = 0 at hz
      have hc := (cycDiff_eq_zero_iff_constant_apply F (T z.1)).mp hz s
      change T z.1 s + a = 0
      rw [hc]
      exact F_add_self _⟩, a)
  invFun p := ⟨p.1.1 + delta p.2, by
    apply LinearMap.mem_ker.mpr
    change cycDiff (n := n) F (T (p.1.1 + delta p.2)) = 0
    rw [map_add, LinearMap.mem_ker.mp p.1.2, hdelta, zero_add]
    exact cycDiff_constant F p.2⟩
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext
      change (z.1 + w.1) + delta (T (z.1 + w.1) 0) =
        (z.1 + delta (T z.1 0)) + (w.1 + delta (T w.1 0))
      rw [map_add T]
      simp only [Pi.add_apply, map_add]
      abel
    · exact congrFun (map_add T z.1 w.1) 0
  map_smul' r z := by
    apply Prod.ext
    · apply Subtype.ext
      change r • z.1 + delta (T (r • z.1) 0) =
        r • (z.1 + delta (T z.1 0))
      rw [map_smul T]
      simp only [Pi.smul_apply, smul_eq_mul, smul_add]
      rw [show delta (r * T z.1 0) = r • delta (T z.1 0) by
        simpa [smul_eq_mul] using map_smul delta r (T z.1 0)]
    · exact congrFun (map_smul T r z.1) 0
  left_inv z := by
    apply Subtype.ext
    change (z.1 + delta (T z.1 0)) + delta (T z.1 0) = z.1
    rw [add_assoc, module_add_self, add_zero]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change (p.1.1 + delta p.2) +
        delta (T (p.1.1 + delta p.2) 0) = p.1.1
      rw [map_add, LinearMap.mem_ker.mp p.1.2, zero_add, hdelta]
      change (p.1.1 + delta p.2) + delta p.2 = p.1.1
      rw [add_assoc, module_add_self, add_zero]
    · have h : T (p.1.1 + delta p.2) =
          constantFunctionLinear n F p.2 := by
        rw [map_add, LinearMap.mem_ker.mp p.1.2, zero_add, hdelta]
      exact congrFun h 0
private noncomputable def affineKernelSplit {X A Y : Type*} [AddCommGroup X] [Module F X]
    [AddCommGroup A] [Module F A] [AddCommGroup Y] [Module F Y]
    (Sol : Submodule F (X × A)) (P : Submodule F A) (L : X →ₗ[F] Y) (D : A →ₗ[F] Y) (S : P →ₗ[F] X)
    (read_mem : ∀ z : Sol, z.1.2 ∈ P) (equation : ∀ z : Sol, L z.1.1 + D z.1.2 = 0) (section_eq : ∀ p : P, L (S p) = D p.1)
    (build_mem : ∀ (p : P) (k : LinearMap.ker L), (k.1 + S p, p.1) ∈ Sol) : Sol ≃ₗ[F] P × LinearMap.ker L where
  toFun z :=
    let p : P := ⟨z.1.2, read_mem z⟩
    (p, ⟨z.1.1 + S p, by
      apply LinearMap.mem_ker.mpr
      rw [map_add, section_eq, equation]⟩)
  invFun p := ⟨(p.2.1 + S p.1, p.1.1), build_mem p.1 p.2⟩
  map_add' z w := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      change (z.1.1 + w.1.1) + S ⟨z.1.2 + w.1.2, read_mem (z + w)⟩ =
        (z.1.1 + S ⟨z.1.2, read_mem z⟩) +
          (w.1.1 + S ⟨w.1.2, read_mem w⟩)
      rw [show (⟨z.1.2 + w.1.2, read_mem (z + w)⟩ : P) = ⟨z.1.2, read_mem z⟩ + ⟨w.1.2, read_mem w⟩ by ext; rfl, map_add]
      abel
  map_smul' r z := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      change r • z.1.1 + S ⟨r • z.1.2, read_mem (r • z)⟩ =
        r • (z.1.1 + S ⟨z.1.2, read_mem z⟩)
      rw [show (⟨r • z.1.2, read_mem (r • z)⟩ : P) = r • ⟨z.1.2, read_mem z⟩ by ext; rfl, map_smul, smul_add]
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change (z.1.1 + S ⟨z.1.2, read_mem z⟩) +
        S ⟨z.1.2, read_mem z⟩ = z.1.1
      rw [add_assoc, module_add_self, add_zero]
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext; rfl
    · apply Subtype.ext
      change (p.2.1 + S p.1) + S p.1 = p.2.1
      rw [add_assoc, module_add_self, add_zero]
private theorem cubePlaneSumIK_cubeDiffJStar {n : Nat} [NeZero n] (f : CyclicCube n) :
    cubePlaneSumIK (cubeDiffJStar f) = cycDiff (n := n) F (cubePlaneSumIK f) := by
  funext j
  simp only [cubePlaneSumIK, LinearMap.coe_mk, AddHom.coe_mk, cubeDiffJStar_apply, cycDiff_apply]
  change (∑ i : I n, ∑ k : I n, (f i j k + f i (j + 1) k)) =
    (∑ i : I n, ∑ k : I n, f i j k) +
      ∑ i : I n, ∑ k : I n, f i (j + 1) k
  simp_rw [Finset.sum_add_distrib]
private noncomputable def cubePlaneDelta (n : Nat) [NeZero n] : F →ₗ[F] CyclicCube n :=
  (cubePlaneSumLift n).comp (constantFunctionLinear n F)
private theorem cubePlaneSumIK_cubePlaneDelta {n : Nat} [NeZero n] (a : F) :
    cubePlaneSumIK (cubePlaneDelta n a) = constantFunctionLinear n F a :=
  cubePlaneSum_cubePlaneSumLift _
private noncomputable def starAdmissibleDiff {n : Nat} [NeZero n] : ConstantTotal n (cubePlaneSumIK (n := n)) →ₗ[F] CubePlaneZero n :=
  LinearMap.codRestrict (CubePlaneZero n)
    (cubeDiffJStar.comp (ConstantTotal n cubePlaneSumIK).subtype) (fun p => by
      apply LinearMap.mem_ker.mpr
      change cubePlaneSumIK (cubeDiffJStar p.1) = 0
      rw [cubePlaneSumIK_cubeDiffJStar]
      exact LinearMap.mem_ker.mp p.2)
private noncomputable def starAdmissibleSection {n : Nat} [NeZero n] : ConstantTotal n (cubePlaneSumIK (n := n)) →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  cubeStarPrimitive.comp starAdmissibleDiff
noncomputable def cubeStarMultiplier_equiv {n : Nat} [NeZero n] : CubeStarMultiplierSolution n ≃ₗ[F]
      (CubePlaneZero n × F) × LinearMap.ker (cubeStarIK (n := n)) := by
  let E := affineKernelSplit
    (CubeStarMultiplierSolution n)
    (ConstantTotal n (cubePlaneSumIK (n := n)))
    (cubeStarIK (n := n)) (cubeDiffJStar (n := n))
    (starAdmissibleSection (n := n))
    (fun z => by
      apply LinearMap.mem_ker.mpr
      change cycDiff (n := n) F (cubePlaneSumIK z.1.2) = 0
      rw [← cubePlaneSumIK_cubeDiffJStar]
      have hz := LinearMap.mem_ker.mp z.2
      change cubeStarIK z.1.1 + cubeDiffJStar z.1.2 = 0 at hz
      calc
        cubePlaneSumIK (cubeDiffJStar z.1.2) =
            cubePlaneSumIK (cubeStarIK z.1.1) +
              cubePlaneSumIK (cubeDiffJStar z.1.2) := by
                rw [LinearMap.mem_ker.mp (cubeStarIK_mem_planeZero z.1.1), zero_add]
        _ = cubePlaneSumIK
            (cubeStarIK z.1.1 + cubeDiffJStar z.1.2) := by rw [map_add]
        _ = 0 := by rw [hz, map_zero])
    (fun z => LinearMap.mem_ker.mp z.2)
    (fun p => cubeStarIK_cubeStarPrimitive (starAdmissibleDiff p))
    (fun p k => by
      apply LinearMap.mem_ker.mpr
      change cubeStarIK (k.1 + starAdmissibleSection p) +
        cubeDiffJStar p.1 = 0
      rw [map_add, LinearMap.mem_ker.mp k.2, zero_add]
      change cubeStarIK (cubeStarPrimitive (starAdmissibleDiff p)) +
        cubeDiffJStar p.1 = 0
      rw [cubeStarIK_cubeStarPrimitive]
      exact module_add_self _)
  exact E.trans ((constantTotalEquiv cubePlaneSumIK (cubePlaneDelta n) cubePlaneSumIK_cubePlaneDelta).prodCongr
      (LinearEquiv.refl F (LinearMap.ker cubeStarIK)))
def cubeDot {n : Nat} [NeZero n] (x y : CyclicCube n) : F :=
  ∑ q : I n × I n × I n, x q.1 q.2.1 q.2.2 * y q.1 q.2.1 q.2.2
private theorem cubeShift_pairing {n : Nat} [NeZero n] (di dj dk : I n) (x y : CyclicCube n) :
    (∑ q : I n × I n × I n, x (q.1-di) (q.2.1-dj) (q.2.2-dk)*y q.1 q.2.1 q.2.2) =
      ∑ q : I n × I n × I n, x q.1 q.2.1 q.2.2*y (q.1+di) (q.2.1+dj) (q.2.2+dk) := by
  let e := Equiv.prodCongr (Equiv.addRight (-di))
    (Equiv.prodCongr (Equiv.addRight (-dj)) (Equiv.addRight (-dk)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, sub_eq_add_neg]
private theorem cubeStepDiff_pairing {n : Nat} [NeZero n] (di dj dk : I n) (x y : CyclicCube n) :
    cubeDot (cubeStepDiff (-di) (-dj) (-dk) x) y = cubeDot x (cubeStepDiff di dj dk y) := by
  simp only [cubeDot, cubeStepDiff, LinearMap.coe_mk, AddHom.coe_mk, add_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  simpa [sub_eq_add_neg] using cubeShift_pairing di dj dk x y
theorem cubeDiffJ_pairing_adjoint {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot (cubeDiffJStar x) y = cubeDot x (cubeDiffJInv y) := by simpa [cubeDiffJStar, cubeDiffJInv] using cubeStepDiff_pairing 0 (-1) 0 x y
theorem cubeDiffP_pairing_adjoint {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot (cubeDiffPStar x) y = cubeDot x (cubeDiffP y) := by simpa [cubeDiffPStar, cubeDiffP] using cubeStepDiff_pairing 1 (-1) 0 x y
theorem cubeDiffR_pairing_adjoint {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot (cubeDiffRStar x) y = cubeDot x (cubeDiffR y) := by simpa [cubeDiffRStar, cubeDiffR] using cubeStepDiff_pairing 0 (-1) 1 x y
end
end Core4loop.SquareDiagonal.EvenP
