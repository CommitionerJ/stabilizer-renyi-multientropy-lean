import Core4loop.SquareDiagonal.EvenP.EEEE.Definitions

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace EEEEInternal

set_option maxSynthPendingDepth 16

theorem module_add_self
    {X : Type*} [AddCommGroup X] [Module F X] (x : X) :
    x + x = 0 := by
  have htwo : (1 : F) + 1 = 0 := by decide
  calc
    x + x = (1 : F) • x + (1 : F) • x := by simp
    _ = ((1 : F) + 1) • x := by rw [add_smul]
    _ = 0 := by simp [htwo]

theorem eq_of_add_eq_zero
    (x y : F) (h : x + y = 0) : x = y := by
  calc
    x = x + 0 := by simp
    _ = x + (y + y) := by rw [F_add_self]
    _ = (x + y) + y := by abel
    _ = y := by rw [h]; simp

/- The exact `i <-> k` involution used to transport the p-factor. -/

noncomputable def swapIK {n : Nat} [NeZero n] :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun f := fun i j k => f k j i
  invFun f := fun i j k => f k j i
  left_inv f := by
    change (fun i j k => f i j k) = f
    rfl
  right_inv f := by
    change (fun i j k => f i j k) = f
    rfl
  map_add' f g := by
    change (fun i j k => (f + g) k j i) =
      (fun i j k => f k j i) + fun i j k => g k j i
    rfl
  map_smul' r f := by
    change (fun i j k => (r • f) k j i) =
      r • fun i j k => f k j i
    rfl

@[simp] theorem swapIK_apply_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (swapIK f) = f := by
  funext i j k
  rfl

theorem swapIK_cubeDiffK
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffK f) = cubeDiffI (swapIK f) := by
  funext i j k
  simp [swapIK]

theorem swapIK_cubeDiffJStar
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffJStar f) = cubeDiffJStar (swapIK f) := by
  funext i j k
  simp [swapIK]

def indexSwapIK {n : Nat} :
    (I n × I n × I n) ≃ (I n × I n × I n) where
  toFun q := (q.2.2, (q.2.1, q.1))
  invFun q := (q.2.2, (q.2.1, q.1))
  left_inv q := by
    rcases q with ⟨i, ⟨j, k⟩⟩
    rfl
  right_inv q := by
    rcases q with ⟨i, ⟨j, k⟩⟩
    rfl

theorem cubeDot_swap_left
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot (swapIK x) y = cubeDot x (swapIK y) := by
  rw [cubeDot, cubeDot]
  apply Fintype.sum_equiv indexSwapIK
  intro q
  rfl

theorem cubeDiffP_swap
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    cubeDiffP (swapIK f) = swapIK (cubeDiffR f) := by
  funext i j k
  simp [swapIK]

theorem swapIK_cubeDiffPStar
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffPStar f) =
      cubeDiffRStar (swapIK f) := by
  apply cubeDot_left_ext
  intro y
  calc
    cubeDot (swapIK (cubeDiffPStar f)) y =
        cubeDot (cubeDiffPStar f) (swapIK y) :=
      cubeDot_swap_left _ _
    _ = cubeDot f (cubeDiffP (swapIK y)) :=
      cubeDiffP_pairing_adjoint _ _
    _ = cubeDot f (swapIK (cubeDiffR y)) := by
      rw [cubeDiffP_swap]
    _ = cubeDot (swapIK f) (cubeDiffR y) :=
      (cubeDot_swap_left _ _).symm
    _ = cubeDot (cubeDiffRStar (swapIK f)) y :=
      (cubeDiffR_pairing_adjoint _ _).symm

theorem swapIK_cubeDiffI
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffI f) = cubeDiffK (swapIK f) := by
  apply (swapIK (n := n)).injective
  rw [swapIK_apply_apply, swapIK_cubeDiffK, swapIK_apply_apply]

theorem swapIK_cubeDiffR
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffR f) = cubeDiffP (swapIK f) := by
  symm
  exact cubeDiffP_swap f

theorem swapIK_cubeDiffRStar
    {n : Nat} [NeZero n] (f : CyclicCube n) :
    swapIK (cubeDiffRStar f) =
      cubeDiffPStar (swapIK f) := by
  apply (swapIK (n := n)).injective
  rw [swapIK_apply_apply, swapIK_cubeDiffPStar, swapIK_apply_apply]

/- Exact factor spaces. -/

noncomputable def baseBMap
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] (CyclicCube n × CyclicCube n) :=
  LinearMap.prod cubeDiffP cubeDiffI

noncomputable def BaseBFactor
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (baseBMap (n := n))

noncomputable def baseWMap
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] (CyclicCube n × CyclicCube n) :=
  LinearMap.prod cubeDiffR cubeDiffK

noncomputable def BaseWFactor
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (baseWMap (n := n))

abbrev BaseFactor
    (n : Nat) [NeZero n] :=
  (BaseBFactor n × BaseWFactor n) × CubePairPRDISolution n

abbrev RFactor
    (n : Nat) [NeZero n] :=
  CubeRInvariantMultiplierSolution n

abbrev PFactor
    (n : Nat) [NeZero n] :=
  CubePInvariantMultiplierSolution n

abbrev StarFactor
    (n : Nat) [NeZero n] :=
  CubeStarMultiplierSolution n

noncomputable def lambda11Map
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F]
      ((CyclicCube n × CyclicCube n) × CyclicCube n) :=
  LinearMap.prod
    (LinearMap.prod cubeDiffJStar cubeDiffPStar)
    cubeDiffRStar

noncomputable def Lambda11Factor
    (n : Nat) [NeZero n] : Submodule F (CyclicCube n) :=
  LinearMap.ker (lambda11Map (n := n))

abbrev FiveFactors
    (n : Nat) [NeZero n] :=
  ((((BaseFactor n × RFactor n) × PFactor n) × StarFactor n) ×
    Lambda11Factor n)

/- Base B coordinates. -/

theorem baseB_i_constant
    {n : Nat} [NeZero n] (z : BaseBFactor n)
    (i j k : I n) :
    z.1 i j k = z.1 0 j k := by
  let f : Profile n := fun t => z.1 t j k
  have hi := congrArg Prod.snd (LinearMap.mem_ker.mp z.2)
  change cubeDiffI z.1 = 0 at hi
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have ht := congrFun (congrFun (congrFun hi t) j) k
    simpa [f] using ht
  exact (cycDiff_eq_zero_iff_constant_apply F f).mp hf i

theorem baseB_j_constant
    {n : Nat} [NeZero n] (z : BaseBFactor n)
    (j k : I n) :
    z.1 0 j k = z.1 0 0 k := by
  let f : Profile n := fun t => z.1 0 t k
  have hp0 := congrArg Prod.fst (LinearMap.mem_ker.mp z.2)
  have hi0 := congrArg Prod.snd (LinearMap.mem_ker.mp z.2)
  change cubeDiffP z.1 = 0 at hp0
  change cubeDiffI z.1 = 0 at hi0
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hp := congrFun (congrFun (congrFun hp0 0) (t + 1)) k
    have hi := congrFun (congrFun (congrFun hi0 0) t) k
    simp only [Pi.zero_apply] at hp hi
    change z.1 0 t k + z.1 0 (t + 1) k = 0
    change z.1 0 (t + 1) k +
      z.1 (0 + 1) ((t + 1) + (-1)) (k + 0) = 0 at hp
    change z.1 0 t k + z.1 (0 + 1) t k = 0 at hi
    rw [show (t + 1) + (-1) = t by abel, add_zero] at hp
    rw [(eq_of_add_eq_zero _ _ hi).trans
      (eq_of_add_eq_zero _ _ hp).symm, F_add_self]
  exact (cycDiff_eq_zero_iff_constant_apply F f).mp hf j

noncomputable def baseBBuild
    {n : Nat} [NeZero n] :
    Profile n →ₗ[F] BaseBFactor n where
  toFun h := ⟨fun _ _ k => h k, by
    apply LinearMap.mem_ker.mpr
    apply Prod.ext <;> funext i j k
    · change h k + h (k + 0) = 0
      rw [add_zero, F_add_self]
    · exact F_add_self _⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

noncomputable def baseBRead
    {n : Nat} [NeZero n] :
    BaseBFactor n →ₗ[F] Profile n where
  toFun z := fun k => z.1 0 0 k
  map_add' z w := by
    change (fun k => (z + w).1 0 0 k) =
      (fun k => z.1 0 0 k) + fun k => w.1 0 0 k
    rfl
  map_smul' r z := by
    change (fun k => (r • z).1 0 0 k) =
      r • fun k => z.1 0 0 k
    rfl

noncomputable def baseBEquiv
    {n : Nat} [NeZero n] :
    BaseBFactor n ≃ₗ[F] Profile n where
  toFun := baseBRead
  invFun := baseBBuild
  left_inv z := by
    apply Subtype.ext
    change (fun _ _ k => z.1 0 0 k) = z.1
    funext i j k
    exact ((baseB_i_constant z i j k).trans
      (baseB_j_constant z j k)).symm
  right_inv _ := by rfl
  map_add' := map_add baseBRead
  map_smul' := map_smul baseBRead

/- Base W is the same factor after the exact axis swap. -/

noncomputable def baseWToB
    {n : Nat} [NeZero n] :
    BaseWFactor n →ₗ[F] BaseBFactor n where
  toFun z := ⟨swapIK z.1, by
    have hz := LinearMap.mem_ker.mp z.2
    have hr := congrArg Prod.fst hz
    have hk := congrArg Prod.snd hz
    change cubeDiffR z.1 = 0 at hr
    change cubeDiffK z.1 = 0 at hk
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · change cubeDiffP (swapIK z.1) = 0
      rw [← swapIK_cubeDiffR, hr, map_zero]
    · change cubeDiffI (swapIK z.1) = 0
      rw [← swapIK_cubeDiffK, hk, map_zero]⟩
  map_add' z w := by
    apply Subtype.ext
    exact map_add swapIK z.1 w.1
  map_smul' r z := by
    apply Subtype.ext
    exact map_smul swapIK r z.1

noncomputable def baseBToW
    {n : Nat} [NeZero n] :
    BaseBFactor n →ₗ[F] BaseWFactor n where
  toFun z := ⟨swapIK z.1, by
    have hz := LinearMap.mem_ker.mp z.2
    have hp := congrArg Prod.fst hz
    have hi := congrArg Prod.snd hz
    change cubeDiffP z.1 = 0 at hp
    change cubeDiffI z.1 = 0 at hi
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · change cubeDiffR (swapIK z.1) = 0
      apply (swapIK (n := n)).injective
      rw [swapIK_cubeDiffR, swapIK_apply_apply, hp, map_zero]
    · change cubeDiffK (swapIK z.1) = 0
      apply (swapIK (n := n)).injective
      rw [swapIK_cubeDiffK, swapIK_apply_apply, hi, map_zero]⟩
  map_add' z w := by
    apply Subtype.ext
    exact map_add swapIK z.1 w.1
  map_smul' r z := by
    apply Subtype.ext
    exact map_smul swapIK r z.1

noncomputable def baseWEquivBaseB
    {n : Nat} [NeZero n] :
    BaseWFactor n ≃ₗ[F] BaseBFactor n where
  toFun := baseWToB
  invFun := baseBToW
  left_inv z := by
    apply Subtype.ext
    exact swapIK_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact swapIK_apply_apply z.1
  map_add' := map_add baseWToB
  map_smul' := map_smul baseWToB

noncomputable def baseWEquiv
    {n : Nat} [NeZero n] :
    BaseWFactor n ≃ₗ[F] Profile n :=
  baseWEquivBaseB.trans baseBEquiv

/- P-factor transport to the public r-factor. -/

noncomputable def swapPair
    {n : Nat} [NeZero n] :
    (CyclicCube n × CyclicCube n) ≃ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  swapIK.prodCongr swapIK

@[simp] theorem swapPair_apply_apply
    {n : Nat} [NeZero n]
    (q : CyclicCube n × CyclicCube n) :
    swapPair (swapPair q) = q := by
  apply Prod.ext <;> exact swapIK_apply_apply _

theorem rMap_swapPair
    {n : Nat} [NeZero n]
    (q : CyclicCube n × CyclicCube n) :
    cubeRInvariantMultiplierMap (swapPair q) =
      swapPair (cubePInvariantMultiplierMap q) := by
  apply Prod.ext
  · exact (swapIK_cubeDiffPStar q.2).symm
  · change
      cubeDiffI (swapIK q.1) + cubeDiffJStar (swapIK q.2) =
        swapIK (cubeDiffK q.1 + cubeDiffJStar q.2)
    rw [map_add, swapIK_cubeDiffK, swapIK_cubeDiffJStar]

theorem pMap_swapPair
    {n : Nat} [NeZero n]
    (q : CyclicCube n × CyclicCube n) :
    cubePInvariantMultiplierMap (swapPair q) =
      swapPair (cubeRInvariantMultiplierMap q) := by
  apply Prod.ext
  · exact (swapIK_cubeDiffRStar q.2).symm
  · change
      cubeDiffK (swapIK q.1) + cubeDiffJStar (swapIK q.2) =
        swapIK (cubeDiffI q.1 + cubeDiffJStar q.2)
    rw [map_add, swapIK_cubeDiffI, swapIK_cubeDiffJStar]

noncomputable def pToR
    {n : Nat} [NeZero n] :
    PFactor n →ₗ[F] RFactor n where
  toFun z := ⟨swapPair z.1, by
    apply LinearMap.mem_ker.mpr
    rw [rMap_swapPair, LinearMap.mem_ker.mp z.2]
    rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def rToP
    {n : Nat} [NeZero n] :
    RFactor n →ₗ[F] PFactor n where
  toFun z := ⟨swapPair z.1, by
    apply LinearMap.mem_ker.mpr
    rw [pMap_swapPair, LinearMap.mem_ker.mp z.2]
    rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

noncomputable def pFactorEquivR
    {n : Nat} [NeZero n] :
    PFactor n ≃ₗ[F] RFactor n where
  toFun := pToR
  invFun := rToP
  left_inv z := by
    apply Subtype.ext
    exact swapPair_apply_apply z.1
  right_inv z := by
    apply Subtype.ext
    exact swapPair_apply_apply z.1
  map_add' := map_add pToR
  map_smul' := map_smul pToR

/- The pure lambda11 factor is the constant cube. -/

theorem jStar_invariant
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffJStar (n := n)))
    (i j k : I n) :
    z.1 i j k = z.1 i 0 k := by
  let f : Profile n := fun t => z.1 i t k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp z.2) i) t) k
    simp only [Pi.zero_apply] at hz
    change z.1 i t k +
      z.1 (i + 0) (t + 1) (k + 0) = 0 at hz
    simpa [f] using hz
  exact (cycDiff_eq_zero_iff_constant_apply F f).mp hf j

theorem pStar_invariant
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffPStar (n := n)))
    (i j k : I n) :
    z.1 i j k = z.1 (i + j) 0 k := by
  let f : Profile n := fun t => z.1 (i + j - t) t k
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp z.2) (i + j - t)) t) k
    simp only [Pi.zero_apply] at hz
    change
      z.1 (i + j - t) t k +
        z.1 ((i + j - t) + (-1)) (t + 1) (k + 0) = 0 at hz
    change
      z.1 (i + j - t) t k +
        z.1 (i + j - (t + 1)) (t + 1) k = 0
    rw [show i + j - (t + 1) =
      (i + j - t) + (-1) by abel]
    simpa only [add_zero] using hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
  simpa [f, show i + j - j = i by abel] using hc

theorem rStar_invariant
    {n : Nat} [NeZero n]
    (z : LinearMap.ker (cubeDiffRStar (n := n)))
    (i j k : I n) :
    z.1 i j k = z.1 i 0 (j + k) := by
  let f : Profile n := fun t => z.1 i t (j + k - t)
  have hf : cycDiff (n := n) F f = 0 := by
    funext t
    have hz := congrFun (congrFun (congrFun
      (LinearMap.mem_ker.mp z.2) i) t) (j + k - t)
    simp only [Pi.zero_apply] at hz
    change
      z.1 i t (j + k - t) +
        z.1 (i + 0) (t + 1)
          ((j + k - t) + (-1)) = 0 at hz
    change
      z.1 i t (j + k - t) +
        z.1 i (t + 1) (j + k - (t + 1)) = 0
    rw [show j + k - (t + 1) =
      (j + k - t) + (-1) by abel]
    simpa only [add_zero] using hz
  have hc := (cycDiff_eq_zero_iff_constant_apply F f).mp hf j
  simpa [f, show j + k - j = k by abel] using hc

theorem lambda11_conditions
    {n : Nat} [NeZero n] (z : Lambda11Factor n) :
    cubeDiffJStar z.1 = 0 ∧
      cubeDiffPStar z.1 = 0 ∧
      cubeDiffRStar z.1 = 0 := by
  have hz := LinearMap.mem_ker.mp z.2
  exact ⟨congrArg (fun q => q.1.1) hz,
    congrArg (fun q => q.1.2) hz,
    congrArg Prod.snd hz⟩

theorem lambda11_invariant
    {n : Nat} [NeZero n] (z : Lambda11Factor n)
    (i j k : I n) :
    z.1 i j k = z.1 0 0 0 := by
  have hc := lambda11_conditions z
  let zj : LinearMap.ker (cubeDiffJStar (n := n)) :=
    ⟨z.1, hc.1⟩
  let zp : LinearMap.ker (cubeDiffPStar (n := n)) :=
    ⟨z.1, hc.2.1⟩
  let zr : LinearMap.ker (cubeDiffRStar (n := n)) :=
    ⟨z.1, hc.2.2⟩
  calc
    z.1 i j k = z.1 (i + j) 0 k :=
      pStar_invariant zp i j k
    _ = z.1 0 (i + j) k := by
      simpa using (pStar_invariant zp 0 (i + j) k).symm
    _ = z.1 0 0 k := jStar_invariant zj 0 (i + j) k
    _ = z.1 0 k 0 := by
      simpa using (rStar_invariant zr 0 k 0).symm
    _ = z.1 0 0 0 := jStar_invariant zj 0 k 0

noncomputable def lambda11Read
    {n : Nat} [NeZero n] :
    Lambda11Factor n →ₗ[F] F where
  toFun z := z.1 0 0 0
  map_add' z w := by
    change (z + w).1 0 0 0 = z.1 0 0 0 + w.1 0 0 0
    rfl
  map_smul' r z := by
    change (r • z).1 0 0 0 = r • z.1 0 0 0
    rfl

noncomputable def lambda11Build
    {n : Nat} [NeZero n] :
    F →ₗ[F] Lambda11Factor n where
  toFun c := ⟨fun _ _ _ => c, by
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · apply Prod.ext <;> funext i j k <;> exact F_add_self _
    · funext i j k
      exact F_add_self _⟩
  map_add' c d := by
    apply Subtype.ext
    change (fun _ _ _ => c + d) =
      (fun _ _ _ => c) + fun _ _ _ => d
    rfl
  map_smul' r c := by
    apply Subtype.ext
    change (fun _ _ _ => r • c) =
      r • fun _ _ _ => c
    rfl

noncomputable def lambda11Equiv
    {n : Nat} [NeZero n] :
    Lambda11Factor n ≃ₗ[F] F where
  toFun := lambda11Read
  invFun := lambda11Build
  left_inv z := by
    apply Subtype.ext
    funext i j k
    exact (lambda11_invariant z i j k).symm
  right_inv c := by
    change c = c
    rfl
  map_add' := map_add lambda11Read
  map_smul' := map_smul lambda11Read

/- The multiplier solution splits into the five source-first factors.
The star coordinates are `U = B10 + B11` and `V = W01 + W11`. -/

noncomputable def multiplierToFactors
    {n : Nat} [NeZero n] :
    DiamondEEEEMultiplierSolution n →ₗ[F] FiveFactors n where
  toFun z := by
    let l := z.1.1.1
    let B00 := l.1.1.1
    let B01 := l.1.1.2
    let B10 := l.1.2.1
    let B11 := l.1.2.2
    let W00 := l.2.1.1
    let W01 := l.2.1.2
    let W10 := l.2.2.1
    let W11 := l.2.2.2
    let lambda00 := z.1.2.1.1
    let lambda01 := z.1.2.1.2
    let lambda10 := z.1.2.2.1
    let lambda11 := z.1.2.2.2
    have hm := LinearMap.mem_ker.mp z.2
    have hleft := LinearMap.mem_ker.mp z.1.1.2
    have hP00 : cubeDiffP B00 = 0 := by
      have h := congrArg (fun x => x.1.1) hleft
      change cubeDiffP B00 = 0 at h
      exact h
    have hR00 : cubeDiffR W00 = 0 := by
      have h := congrArg (fun x => x.1.2) hleft
      change cubeDiffR W00 = 0 at h
      exact h
    have hPR : cubeDiffP B01 + cubeDiffR W10 = 0 := by
      have h := congrArg Prod.snd hleft
      change cubeDiffP B01 + cubeDiffR W10 = 0 at h
      exact h
    have h0 := congrFun hm (0 : Fin 11)
    have h1 := congrFun hm (1 : Fin 11)
    have h2 := congrFun hm (2 : Fin 11)
    have h3 := congrFun hm (3 : Fin 11)
    have h4 := congrFun hm (4 : Fin 11)
    have h5 := congrFun hm (5 : Fin 11)
    have h6 := congrFun hm (6 : Fin 11)
    have h7 := congrFun hm (7 : Fin 11)
    have h8 := congrFun hm (8 : Fin 11)
    have h9 := congrFun hm (9 : Fin 11)
    have h10 := congrFun hm (10 : Fin 11)
    change cubeDiffI B00 = 0 at h0
    change cubeDiffK W00 = 0 at h1
    change
      cubeDiffI (B00 + B01) +
        cubeDiffK (W00 + W10) = 0 at h2
    change
      cubeDiffI (B00 + B10) +
        cubeDiffJStar lambda01 = 0 at h3
    change cubeDiffRStar lambda01 = 0 at h4
    change
      cubeDiffK (W00 + W01) +
        cubeDiffJStar lambda10 = 0 at h5
    change cubeDiffPStar lambda10 = 0 at h6
    change
      cubeDiffI (B00 + B01 + B10 + B11) +
          cubeDiffK (W00 + W01 + W10 + W11) +
        cubeDiffJStar lambda00 = 0 at h7
    change cubeDiffJStar lambda11 = 0 at h8
    change cubeDiffPStar lambda11 = 0 at h9
    change cubeDiffRStar lambda11 = 0 at h10
    have hPair :
        cubeDiffI B01 + cubeDiffK W10 = 0 := by
      simpa [map_add, h0, h1] using h2
    have hRFactor :
        cubeDiffI B10 + cubeDiffJStar lambda01 = 0 := by
      simpa [map_add, h0] using h3
    have hPFactor :
        cubeDiffK W01 + cubeDiffJStar lambda10 = 0 := by
      simpa [map_add, h1] using h5
    have hStar :
        cubeDiffI (B10 + B11) +
            cubeDiffK (W01 + W11) +
          cubeDiffJStar lambda00 = 0 := by
      have hcancel :
          (cubeDiffI B01 + cubeDiffK W10) +
              (cubeDiffI (B10 + B11) +
                  cubeDiffK (W01 + W11) +
                cubeDiffJStar lambda00) = 0 := by
        calc
          _ =
              cubeDiffI (B00 + B01 + B10 + B11) +
                  cubeDiffK (W00 + W01 + W10 + W11) +
                cubeDiffJStar lambda00 := by
            simp only [map_add, h0, h1, zero_add]
            abel
          _ = 0 := h7
      rw [hPair, zero_add] at hcancel
      exact hcancel
    refine ((((
      ((⟨B00, ?_⟩, ⟨W00, ?_⟩), ⟨(B01, W10), ?_⟩),
      ⟨(B10, lambda01), ?_⟩),
      ⟨(W01, lambda10), ?_⟩),
      ⟨((B10 + B11, W01 + W11), lambda00), ?_⟩),
      ⟨lambda11, ?_⟩)
    · apply LinearMap.mem_ker.mpr
      exact Prod.ext hP00 h0
    · apply LinearMap.mem_ker.mpr
      exact Prod.ext hR00 h1
    · apply LinearMap.mem_ker.mpr
      exact Prod.ext hPR hPair
    · apply LinearMap.mem_ker.mpr
      exact Prod.ext h4 hRFactor
    · apply LinearMap.mem_ker.mpr
      exact Prod.ext h6 hPFactor
    · apply LinearMap.mem_ker.mpr
      exact hStar
    · apply LinearMap.mem_ker.mpr
      exact Prod.ext (Prod.ext h8 h9) h10
  map_add' z w := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Prod.ext
            · apply Prod.ext <;> apply Subtype.ext <;> rfl
            · apply Subtype.ext
              rfl
          · apply Subtype.ext
            rfl
        · apply Subtype.ext
          rfl
      · apply Subtype.ext
        apply Prod.ext
        · apply Prod.ext <;> simp
          all_goals abel
        · rfl
    · apply Subtype.ext
      rfl
  map_smul' r z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Prod.ext
            · apply Prod.ext <;> apply Subtype.ext <;> rfl
            · apply Subtype.ext
              rfl
          · apply Subtype.ext
            rfl
        · apply Subtype.ext
          rfl
      · apply Subtype.ext
        apply Prod.ext
        · apply Prod.ext <;> simp
        · rfl
    · apply Subtype.ext
      rfl

set_option maxHeartbeats 2000000 in
-- The explicit inverse discharges all eleven reconstructed constraints.
set_option synthInstance.maxHeartbeats 500000 in
-- Nested product-submodule instances are resolved only inside this owner.
noncomputable def factorsToMultiplier
    {n : Nat} [NeZero n] :
    FiveFactors n →ₗ[F] DiamondEEEEMultiplierSolution n where
  toFun q := by
    let B00 := q.1.1.1.1.1.1.1
    let W00 := q.1.1.1.1.1.2.1
    let B01 := q.1.1.1.1.2.1.1
    let W10 := q.1.1.1.1.2.1.2
    let B10 := q.1.1.1.2.1.1
    let lambda01 := q.1.1.1.2.1.2
    let W01 := q.1.1.2.1.1
    let lambda10 := q.1.1.2.1.2
    let U := q.1.2.1.1.1
    let V := q.1.2.1.1.2
    let lambda00 := q.1.2.1.2
    let lambda11 := q.2.1
    let B11 := U + B10
    let W11 := V + W01
    have hB := LinearMap.mem_ker.mp q.1.1.1.1.1.1.2
    have hW := LinearMap.mem_ker.mp q.1.1.1.1.1.2.2
    have hPair := LinearMap.mem_ker.mp q.1.1.1.1.2.2
    have hR := LinearMap.mem_ker.mp q.1.1.1.2.2
    have hP := LinearMap.mem_ker.mp q.1.1.2.2
    have hStar := LinearMap.mem_ker.mp q.1.2.2
    have hLam := LinearMap.mem_ker.mp q.2.2
    have hBP : cubeDiffP B00 = 0 := by
      exact congrArg Prod.fst hB
    have hBI : cubeDiffI B00 = 0 := by
      exact congrArg Prod.snd hB
    have hWR : cubeDiffR W00 = 0 := by
      exact congrArg Prod.fst hW
    have hWK : cubeDiffK W00 = 0 := by
      exact congrArg Prod.snd hW
    have hPairPR :
        cubeDiffP B01 + cubeDiffR W10 = 0 := by
      exact congrArg Prod.fst hPair
    have hPairIK :
        cubeDiffI B01 + cubeDiffK W10 = 0 := by
      exact congrArg Prod.snd hPair
    have hRStar : cubeDiffRStar lambda01 = 0 := by
      exact congrArg Prod.fst hR
    have hREq :
        cubeDiffI B10 + cubeDiffJStar lambda01 = 0 := by
      exact congrArg Prod.snd hR
    have hPStar : cubeDiffPStar lambda10 = 0 := by
      exact congrArg Prod.fst hP
    have hPEq :
        cubeDiffK W01 + cubeDiffJStar lambda10 = 0 := by
      exact congrArg Prod.snd hP
    have hStarEq :
        cubeDiffI U + cubeDiffK V +
          cubeDiffJStar lambda00 = 0 := by
      exact hStar
    have hLamJ : cubeDiffJStar lambda11 = 0 := by
      exact congrArg (fun x => x.1.1) hLam
    have hLamP : cubeDiffPStar lambda11 = 0 := by
      exact congrArg (fun x => x.1.2) hLam
    have hLamR : cubeDiffRStar lambda11 = 0 := by
      exact congrArg Prod.snd hLam
    let lraw : DiamondEEEELeftAmbient n :=
      (((B00, B01), (B10, B11)),
        ((W00, W01), (W10, W11)))
    have hl : lraw ∈ DiamondEEEELeftSource n := by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext
      · exact Prod.ext hBP hWR
      · exact hPairPR
    let l : DiamondEEEELeftSource n := ⟨lraw, hl⟩
    refine ⟨(l, ((lambda00, lambda01), (lambda10, lambda11))), ?_⟩
    apply LinearMap.mem_ker.mpr
    funext idx
    fin_cases idx
    · change cubeDiffI B00 = 0
      exact hBI
    · change cubeDiffK W00 = 0
      exact hWK
    · change
        cubeDiffI (B00 + B01) +
          cubeDiffK (W00 + W10) = 0
      simpa only [map_add, hBI, hWK, zero_add] using hPairIK
    · change
        cubeDiffI (B00 + B10) +
          cubeDiffJStar lambda01 = 0
      simpa only [map_add, hBI, zero_add] using hREq
    · change cubeDiffRStar lambda01 = 0
      exact hRStar
    · change
        cubeDiffK (W00 + W01) +
          cubeDiffJStar lambda10 = 0
      simpa only [map_add, hWK, zero_add] using hPEq
    · change cubeDiffPStar lambda10 = 0
      exact hPStar
    · change
        cubeDiffI (B00 + B01 + B10 + B11) +
            cubeDiffK (W00 + W01 + W10 + W11) +
          cubeDiffJStar lambda00 = 0
      calc
        _ =
            cubeDiffI B00 +
              (cubeDiffI B01 + cubeDiffK W10) +
              (cubeDiffI U + cubeDiffK V +
                cubeDiffJStar lambda00) +
              cubeDiffK W00 := by
          simp only [map_add, B11, W11]
          abel_nf
          simp [two_smul, module_add_self]
        _ = 0 := by
          rw [hBI, hPairIK, hStarEq, hWK]
          simp
    · change cubeDiffJStar lambda11 = 0
      exact hLamJ
    · change cubeDiffPStar lambda11 = 0
      exact hLamP
    · change cubeDiffRStar lambda11 = 0
      exact hLamR
  map_add' q r := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp
      all_goals abel
    · rfl
  map_smul' r q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp [smul_add]
    · rfl

set_option maxHeartbeats 2000000 in
-- The inverse laws normalize both reconstructed star coordinates.
set_option synthInstance.maxHeartbeats 500000 in
-- The five nested factors require a bounded local instance budget.
noncomputable def multiplierFiveFactorsEquiv
    {n : Nat} [NeZero n] :
    DiamondEEEEMultiplierSolution n ≃ₗ[F] FiveFactors n where
  toFun := multiplierToFactors (n := n)
  invFun := factorsToMultiplier (n := n)
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      ext <;> simp [multiplierToFactors, factorsToMultiplier]
      all_goals
        abel_nf
        simp [two_smul, module_add_self]
    · rfl
  right_inv q := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext
          · apply Prod.ext
            · apply Prod.ext <;> apply Subtype.ext <;> rfl
            · apply Subtype.ext
              rfl
          · apply Subtype.ext
            rfl
        · apply Subtype.ext
          rfl
      · apply Subtype.ext
        apply Prod.ext
        · apply Prod.ext <;>
            simp [multiplierToFactors, factorsToMultiplier]
          all_goals
            abel_nf
            simp [two_smul, module_add_self]
        · rfl
    · apply Subtype.ext
      rfl
  map_add' := map_add (multiplierToFactors (n := n))
  map_smul' := map_smul (multiplierToFactors (n := n))

theorem finrank_BaseBFactor
    {n : Nat} [NeZero n] :
    Module.finrank F (BaseBFactor n) = n := by
  rw [LinearEquiv.finrank_eq (baseBEquiv (n := n))]
  exact finrank_profile

theorem finrank_BaseWFactor
    {n : Nat} [NeZero n] :
    Module.finrank F (BaseWFactor n) = n := by
  rw [LinearEquiv.finrank_eq (baseWEquiv (n := n))]
  exact finrank_profile

theorem finrank_pair_addition_safe
    {n : Nat} [NeZero n] :
    Module.finrank F (CubePairPRDISolution n) + n =
      2 * n ^ 2 + 1 := by
  rw [LinearEquiv.finrank_eq (cubePairPRDI_equiv (n := n))]
  have hM : Module.finrank F (MatrixProfile n) = n ^ 2 := by
    simp [MatrixProfile, Module.finrank_pi_fintype, I, ZMod.card]
    ring
  have hn : n - 1 + 1 = n :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hsquare : n ^ 2 = (n - 1) * n + n := by
    calc
      n ^ 2 = n * n := pow_two n
      _ = (n - 1 + 1) * n := by rw [hn]
      _ = (n - 1) * n + n := by ring
  simp only [Module.finrank_prod, CubeMatrixConstSumParam,
    finrank_ZeroSumProfileM, finrank_profile, hM]
  simp only [Module.finrank_self]
  omega

theorem finrank_BaseFactor
    {n : Nat} [NeZero n] :
    Module.finrank F (BaseFactor n) =
      2 * n ^ 2 + n + 1 := by
  simp only [BaseFactor, Module.finrank_prod,
    finrank_BaseBFactor, finrank_BaseWFactor]
  have hpair := finrank_pair_addition_safe (n := n)
  omega

theorem finrank_RFactor_addition_safe
    {n : Nat} [NeZero n] :
    Module.finrank F (RFactor n) + n =
      2 * n ^ 2 + 1 := by
  rw [LinearEquiv.finrank_eq
    (cubeRInvariantMultiplier_equiv (n := n))]
  have hM : Module.finrank F (MatrixProfile n) = n ^ 2 := by
    simp [MatrixProfile, Module.finrank_pi_fintype, I, ZMod.card]
    ring
  have hn : n - 1 + 1 = n :=
    Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
  have hsquare : n ^ 2 = (n - 1) * n + n := by
    calc
      n ^ 2 = n * n := pow_two n
      _ = (n - 1 + 1) * n := by rw [hn]
      _ = (n - 1) * n + n := by ring
  simp only [Module.finrank_prod, CubeMatrixConstSumParam,
    finrank_ZeroSumProfileM, finrank_profile, hM]
  simp only [Module.finrank_self]
  omega

theorem finrank_PFactor_addition_safe
    {n : Nat} [NeZero n] :
    Module.finrank F (PFactor n) + n =
      2 * n ^ 2 + 1 := by
  rw [LinearEquiv.finrank_eq (pFactorEquivR (n := n))]
  exact finrank_RFactor_addition_safe

theorem finrank_StarFactor
    {n : Nat} [NeZero n] :
    Module.finrank F (StarFactor n) =
      2 * n ^ 3 + 1 := by
  rw [LinearEquiv.finrank_eq
    (cubeStarMultiplier_equiv (n := n))]
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (cubeStarIK (n := n))
  rw [cubeStarIK_range_eq_planeZero,
    finrank_ker_cubeStarIK] at hnull
  have hCube :
      Module.finrank F (CyclicCube n) = n ^ 3 := by
    simp [CyclicCube, Module.finrank_pi_fintype,
      I, ZMod.card, pow_succ, mul_assoc]
  have hPlane :
      Module.finrank F (CubePlaneZero n) + n = n ^ 3 := by
    have hdom :
        Module.finrank F (CyclicCube n × CyclicCube n) =
          2 * n ^ 3 := by
      simp only [Module.finrank_prod, hCube]
      omega
    rw [hdom] at hnull
    omega
  simp only [Module.finrank_prod, Module.finrank_self,
    finrank_ker_cubeStarIK]
  omega

theorem finrank_Lambda11Factor
    {n : Nat} [NeZero n] :
    Module.finrank F (Lambda11Factor n) = 1 := by
  rw [LinearEquiv.finrank_eq (lambda11Equiv (n := n))]
  exact Module.finrank_self F

set_option synthInstance.maxHeartbeats 500000 in
-- Local product instances keep the subtraction-safe assembly deterministic.
theorem finrank_FiveFactors_add
    {n : Nat} [NeZero n] :
    Module.finrank F (FiveFactors n) + n =
      2 * n ^ 3 + 6 * n ^ 2 + 5 := by
  letI : Module.Finite F (BaseFactor n) := inferInstance
  letI : Module.Finite F (RFactor n) := inferInstance
  letI : Module.Finite F (PFactor n) := inferInstance
  letI : Module.Finite F (StarFactor n) := inferInstance
  letI : Module.Finite F (Lambda11Factor n) := inferInstance
  letI : Module.Finite F (BaseFactor n × RFactor n) :=
    inferInstance
  letI : Module.Finite F
      ((BaseFactor n × RFactor n) × PFactor n) :=
    inferInstance
  letI : Module.Finite F
      (((BaseFactor n × RFactor n) × PFactor n) ×
        StarFactor n) :=
    inferInstance
  unfold FiveFactors
  simp only [Module.finrank_prod]
  rw [finrank_BaseBFactor, finrank_BaseWFactor,
    finrank_StarFactor,
    finrank_Lambda11Factor]
  have hPair := finrank_pair_addition_safe (n := n)
  have hR := finrank_RFactor_addition_safe (n := n)
  have hP := finrank_PFactor_addition_safe (n := n)
  omega

end EEEEInternal

theorem finrank_DiamondEEEEMultiplierSolution_add
    {n : Nat} [NeZero n] (_hn : Even n) :
    Module.finrank F (DiamondEEEEMultiplierSolution n) + n =
      2 * n ^ 3 + 6 * n ^ 2 + 5 := by
  rw [LinearEquiv.finrank_eq
    (EEEEInternal.multiplierFiveFactorsEquiv (n := n))]
  exact EEEEInternal.finrank_FiveFactors_add

end

end Core4loop.SquareDiagonal.EvenP
