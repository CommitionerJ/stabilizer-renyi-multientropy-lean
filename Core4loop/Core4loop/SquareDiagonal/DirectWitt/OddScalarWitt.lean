import Core4loop.SquareDiagonal.DirectWitt.OddHighFrequencyProjection

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop.SquareDiagonal.EvenP

noncomputable section

private theorem diamondOdd_cubeDiffI_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffI f i j k = f i j k + f (i + 1) j k :=
  rfl

private theorem diamondOdd_cubeDiffK_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffK f i j k = f i j k + f i j (k + 1) := by
  change f i j k + f (i + 0) (j + 0) (k + 1) = _
  simp

private theorem diamondOdd_cubeDiffJInv_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffJInv f i j k = f i j k + f i (j - 1) k := by
  change f i j k + f (i + 0) (j + (-1)) (k + 0) = _
  simp [sub_eq_add_neg]

private theorem diamondOdd_cubeDiffP_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffP f i j k =
      f i j k + f (i + 1) (j - 1) k := by
  change f i j k + f (i + 1) (j + (-1)) (k + 0) = _
  simp [sub_eq_add_neg]

private theorem diamondOdd_cubeDiffR_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffR f i j k =
      f i j k + f i (j - 1) (k + 1) := by
  change f i j k + f (i + 0) (j + (-1)) (k + 1) = _
  simp [sub_eq_add_neg]

private theorem diamondOdd_cubeDiffJStar_apply
    {n : Nat} [NeZero n] (f : CyclicCube n) (i j k : I n) :
    cubeDiffJStar f i j k = f i j k + f i (j + 1) k := by
  change f i j k + f (i + 0) (j + 1) (k + 0) = _
  simp

private theorem diamondOdd_cubeDot_eq_iterated_sum
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y =
      ∑ i : I n, ∑ j : I n, ∑ k : I n,
        X i j k * Y i j k := by
  simp only [cubeDot]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]

private theorem diamondOdd_cubeDot_comm
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  rw [diamondOdd_cubeDot_eq_iterated_sum,
    diamondOdd_cubeDot_eq_iterated_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

private theorem diamondOdd_cubeDot_add_left
    {n : Nat} [NeZero n] (X Y Z : CyclicCube n) :
    cubeDot (X + Y) Z = cubeDot X Z + cubeDot Y Z := by
  simp only [cubeDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem diamondOdd_cubeDot_add_right
    {n : Nat} [NeZero n] (X Y Z : CyclicCube n) :
    cubeDot X (Y + Z) = cubeDot X Y + cubeDot X Z := by
  simp only [cubeDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

abbrev DiamondOddScalarAmbient (n : Nat) [NeZero n] :=
  CyclicCube n × (CyclicCube n × CyclicCube n)

noncomputable def diamondOddScalarSourceMap
    {n : Nat} [NeZero n] :
    DiamondOddScalarAmbient n →ₗ[F] CyclicCube n where
  toFun v :=
    cubeDiffJInv v.1 +
      cubeDiffP v.2.1 +
      cubeDiffR v.2.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    rw [smul_add, smul_add]

@[simp] theorem diamondOddScalarSourceMap_apply
    {n : Nat} [NeZero n]
    (v : DiamondOddScalarAmbient n) :
    diamondOddScalarSourceMap v =
      cubeDiffJInv v.1 +
        cubeDiffP v.2.1 +
        cubeDiffR v.2.2 :=
  rfl

abbrev DiamondOddScalarSource (n : Nat) [NeZero n] :=
  LinearMap.ker (diamondOddScalarSourceMap (n := n))

noncomputable def diamondOddScalarQ
    {n : Nat} [NeZero n]
    (x : DiamondOddScalarSource n) : F :=
  cubeDot x.1.1
    (cubeDiffI x.1.2.1 + cubeDiffK x.1.2.2)

noncomputable def diamondOddPointedSSSSExtract
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddPointedSource n a b c d hn →ₗ[F]
      DiamondOddScalarSource n where
  toFun x :=
    ⟨(x.1.1
          diamondOddChannelS diamondOddChannelS diamondOddChannelS,
        x.1.2.1
          diamondOddChannelS diamondOddChannelS diamondOddChannelS,
        x.1.2.2
          diamondOddChannelS diamondOddChannelS diamondOddChannelS),
      by
        apply LinearMap.mem_ker.mpr
        rw [diamondOddScalarSourceMap_apply]
        have hcoord :=
          congrFun
            (congrFun
              (congrFun (LinearMap.mem_ker.mp x.2) diamondOddChannelS)
              diamondOddChannelS)
            diamondOddChannelS
        rw [diamondOddPointedSourceMap_apply_SSSS hn x.1] at hcoord
        exact hcoord⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

@[simp] theorem diamondOddPointedSSSSExtract_apply
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    (diamondOddPointedSSSSExtract hn x).1 =
      (x.1.1 diamondOddChannelS diamondOddChannelS diamondOddChannelS,
        x.1.2.1 diamondOddChannelS diamondOddChannelS diamondOddChannelS,
        x.1.2.2 diamondOddChannelS diamondOddChannelS diamondOddChannelS) :=
  rfl

theorem diamondOddPointedPhaseSSSS_eq_scalarQ
    {n a b c d : Nat} [NeZero n] {hn : Odd n}
    (x : DiamondOddPointedSource n a b c d hn) :
    diamondOddPointedPhaseSSSS x.1 =
      diamondOddScalarQ (diamondOddPointedSSSSExtract hn x) :=
  rfl

private def diamondOddScalarOnly3
    {T₁ T₂ T₃ V : Type*} [Zero V]
    (q₁ : Option T₁) (q₂ : Option T₂) (q₃ : Option T₃)
    (x : V) : V :=
  match q₁, q₂, q₃ with
  | none, none, none => x
  | _, _, _ => 0

private noncomputable def diamondOddPointedSSSSAmbientBuilder
    {n a b c d : Nat} [NeZero n] :
    DiamondOddScalarAmbient n →ₗ[F]
      DiamondOddPointedAmbient n a b c d where
  toFun x :=
    (fun cy cz cw => diamondOddScalarOnly3 cy cz cw x.1,
      fun cp cz cw => diamondOddScalarOnly3 cp cz cw x.2.1,
      fun cp cy cz => diamondOddScalarOnly3 cp cy cz x.2.2)
  map_add' x y := by
    apply Prod.ext
    · funext cy cz cw
      cases cy <;> cases cz <;> cases cw <;> rfl
    · apply Prod.ext
      · funext cp cz cw
        cases cp <;> cases cz <;> cases cw <;> rfl
      · funext cp cy cz
        cases cp <;> cases cy <;> cases cz <;> rfl
  map_smul' r x := by
    apply Prod.ext
    · funext cy cz cw
      cases cy <;> cases cz <;> cases cw <;> rfl
    · apply Prod.ext
      · funext cp cz cw
        cases cp <;> cases cz <;> cases cw <;> rfl
      · funext cp cy cz
        cases cp <;> cases cy <;> cases cz <;> rfl

private theorem diamondOddPointedSSSSAmbientBuilder_mem
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    diamondOddPointedSSSSAmbientBuilder
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 ∈
      DiamondOddPointedSource n a b c d hn := by
  apply LinearMap.mem_ker.mpr
  funext cp cy cw
  simp only [Pi.zero_apply]
  cases cp with
  | none =>
      cases cy with
      | none =>
          cases cw with
          | none =>
              rw [diamondOddPointedSourceMap_apply]
              change
                cubeDiffJInv x.1.1 +
                    cubeDiffP x.1.2.1 +
                  cubeDiffR x.1.2.2 = 0
              exact LinearMap.mem_ker.mp x.2
          | some wt =>
              rw [diamondOddPointedSourceMap_apply]
              change cubeDiffJInv 0 + cubeDiffP 0 = 0
              simp
      | some yt =>
          cases cw with
          | none =>
              rw [diamondOddPointedSourceMap_apply]
              change cubeDiffJInv 0 + cubeDiffR 0 = 0
              simp
          | some wt =>
              rw [diamondOddPointedSourceMap_apply]
              change cubeDiffJInv 0 = 0
              simp
  | some pt =>
      cases cy with
      | none =>
          cases cw with
          | none =>
              rw [diamondOddPointedSourceMap_apply]
              change cubeDiffP 0 + cubeDiffR 0 = 0
              simp
          | some wt =>
              rw [diamondOddPointedSourceMap_apply]
              change cubeDiffP 0 = 0
              simp
      | some yt =>
          cases cw with
          | none =>
              rw [diamondOddPointedSourceMap_apply]
              change cubeDiffR 0 = 0
              simp
          | some wt =>
              rw [diamondOddPointedSourceMap_apply]
              change (0 : CyclicCube n) = 0
              rfl

private noncomputable def diamondOddPointedSSSSBuilder
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddScalarSource n →ₗ[F]
      DiamondOddPointedSource n a b c d hn :=
  LinearMap.codRestrict
    (DiamondOddPointedSource n a b c d hn)
    ((diamondOddPointedSSSSAmbientBuilder
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (DiamondOddScalarSource n).subtype)
    (diamondOddPointedSSSSAmbientBuilder_mem hn)

private theorem diamondOddPointedSSSSExtract_builder
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    diamondOddPointedSSSSExtract
        (n := n) (a := a) (b := b) (c := c) (d := d) hn
        (diamondOddPointedSSSSBuilder
          (n := n) (a := a) (b := b) (c := c) (d := d) hn x) =
      x := by
  apply Subtype.ext
  rfl

theorem diamondOddPointedSSSSExtract_surjective
    {n a b c d : Nat} [NeZero n] (hn : Odd n) :
    Function.Surjective
      (diamondOddPointedSSSSExtract
        (n := n) (a := a) (b := b) (c := c) (d := d) hn) := by
  intro x
  exact
    ⟨diamondOddPointedSSSSBuilder
        (n := n) (a := a) (b := b) (c := c) (d := d) hn x,
      diamondOddPointedSSSSExtract_builder hn x⟩

private noncomputable def diamondOddScalarXRaw
    {n : Nat} [NeZero n] :
    DiamondOddScalarSource n →ₗ[F] CyclicCube n where
  toFun x := cubeDiffI x.1.2.1 + cubeDiffK x.1.2.2
  map_add' x y := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    simp only [Submodule.coe_smul_of_tower, Prod.smul_fst, Prod.smul_snd,
      map_smul, RingHom.id_apply]
    rw [smul_add]

private noncomputable def diamondOddScalarTotal
    {n : Nat} [NeZero n] :
    DiamondOddScalarSource n →ₗ[F] CyclicCube n where
  toFun x := x.1.1 + x.1.2.1 + x.1.2.2
  map_add' x y := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
    abel
  map_smul' r x := by
    simp only [Submodule.coe_smul_of_tower, Prod.smul_fst, Prod.smul_snd]
    rw [smul_add, smul_add]
    simp only [RingHom.id_apply]

private theorem diamondOdd_eq_of_add_eq_zero
    (a b : F) (h : a + b = 0) : a = b := by
  calc
    a = a + (b + b) := by rw [F_add_self, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

private theorem diamondOddScalar_diffJStar_total
    {n : Nat} [NeZero n]
    (x : DiamondOddScalarSource n) :
    cubeDiffJStar (diamondOddScalarTotal x) =
      diamondOddScalarXRaw x := by
  funext i j k
  have hs :=
    congrFun
      (congrFun
        (congrFun (LinearMap.mem_ker.mp x.2) i)
        (j + 1))
      k
  simp only [diamondOddScalarSourceMap_apply, Pi.add_apply,
    diamondOdd_cubeDiffJInv_apply, diamondOdd_cubeDiffP_apply,
    diamondOdd_cubeDiffR_apply, Pi.zero_apply] at hs
  simp only [diamondOddScalarTotal, diamondOddScalarXRaw,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    diamondOdd_cubeDiffJStar_apply, diamondOdd_cubeDiffI_apply,
    diamondOdd_cubeDiffK_apply]
  have hj : j + 1 - 1 = j := by abel
  rw [hj] at hs
  have hA :
      x.1.1 i (j + 1) k + x.1.1 i j k =
        (x.1.2.1 i (j + 1) k + x.1.2.1 (i + 1) j k) +
          (x.1.2.2 i (j + 1) k + x.1.2.2 i j (k + 1)) := by
    apply diamondOdd_eq_of_add_eq_zero
    simpa only [add_assoc] using hs
  calc
    (x.1.1 i j k + x.1.2.1 i j k + x.1.2.2 i j k) +
          (x.1.1 i (j + 1) k +
            x.1.2.1 i (j + 1) k +
            x.1.2.2 i (j + 1) k) =
        (x.1.1 i (j + 1) k + x.1.1 i j k) +
          (x.1.2.1 i (j + 1) k + x.1.2.1 i j k) +
          (x.1.2.2 i (j + 1) k + x.1.2.2 i j k) := by
            abel
    _ =
        ((x.1.2.1 i (j + 1) k + x.1.2.1 (i + 1) j k) +
            (x.1.2.2 i (j + 1) k +
              x.1.2.2 i j (k + 1))) +
          (x.1.2.1 i (j + 1) k + x.1.2.1 i j k) +
          (x.1.2.2 i (j + 1) k + x.1.2.2 i j k) := by
            rw [hA]
    _ =
        (x.1.2.1 i (j + 1) k + x.1.2.1 i (j + 1) k) +
          (x.1.2.2 i (j + 1) k + x.1.2.2 i (j + 1) k) +
          ((x.1.2.1 i j k + x.1.2.1 (i + 1) j k) +
            (x.1.2.2 i j k + x.1.2.2 i j (k + 1))) := by
              abel
    _ =
        (x.1.2.1 i j k + x.1.2.1 (i + 1) j k) +
          (x.1.2.2 i j k + x.1.2.2 i j (k + 1)) := by
            rw [F_add_self, F_add_self, zero_add, zero_add]

private theorem diamondOddScalarXRaw_mem
    {n : Nat} [NeZero n]
    (x : DiamondOddScalarSource n) :
    diamondOddScalarXRaw x ∈ DiamondOddJZero n := by
  apply LinearMap.mem_ker.mpr
  funext i k
  change (∑ j : I n, diamondOddScalarXRaw x i j k) = 0
  rw [← diamondOddScalar_diffJStar_total x]
  simp only [diamondOdd_cubeDiffJStar_apply]
  rw [Finset.sum_add_distrib]
  rw [sum_shift (n := n) (1 : I n)
    (fun j => diamondOddScalarTotal x i j k)]
  exact F_add_self _

private noncomputable def diamondOddScalarXJZero
    {n : Nat} [NeZero n] :
    DiamondOddScalarSource n →ₗ[F] DiamondOddJZero n :=
  LinearMap.codRestrict
    (DiamondOddJZero n)
    (diamondOddScalarXRaw (n := n))
    diamondOddScalarXRaw_mem

private noncomputable def diamondOddJPrimitive
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddJZero n →ₗ[F] CyclicCube n where
  toFun X := fun i j k =>
    (oddCyclicInverse hn
      ⟨fun t => X.1 i t k,
        congrFun (congrFun (LinearMap.mem_ker.mp X.2) i) k⟩).1 j
  map_add' X Y := by
    funext i j k
    simpa only [Submodule.coe_add, Pi.add_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 j)
        ((oddCyclicInverse hn).map_add
          ⟨fun t => X.1 i t k,
            congrFun (congrFun (LinearMap.mem_ker.mp X.2) i) k⟩
          ⟨fun t => Y.1 i t k,
            congrFun (congrFun (LinearMap.mem_ker.mp Y.2) i) k⟩)
  map_smul' r X := by
    funext i j k
    simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply] using
      congrArg (fun u : ZeroSumProfile n => u.1 j)
        ((oddCyclicInverse hn).map_smul r
          ⟨fun t => X.1 i t k,
            congrFun (congrFun (LinearMap.mem_ker.mp X.2) i) k⟩)

private theorem diamondOddJPrimitive_diff
    {n : Nat} [NeZero n] (hn : Odd n)
    (X : DiamondOddJZero n) :
    cubeDiffJStar (diamondOddJPrimitive hn X) = X.1 := by
  funext i j k
  have h :=
    congrArg (fun u : ZeroSumProfile n => u.1 j)
      (oddCyclicDiffRestrict_oddCyclicInverse hn
        ⟨fun t => X.1 i t k,
          congrFun (congrFun (LinearMap.mem_ker.mp X.2) i) k⟩)
  rw [diamondOdd_cubeDiffJStar_apply]
  simpa only [oddCyclicDiffRestrict, LinearMap.comp_apply,
    LinearMap.codRestrict_apply, Submodule.coe_subtype, cycDiff_apply,
    diamondOddJPrimitive, LinearMap.coe_mk, AddHom.coe_mk]
    using h

private noncomputable def diamondOddJNormalize
    {n : Nat} [NeZero n] (hn : Odd n) :
    CyclicCube n →ₗ[F] DiamondOddJZero n where
  toFun Y :=
    ⟨fun i j k => Y i j k + ∑ t : I n, Y i t k, by
      apply LinearMap.mem_ker.mpr
      funext i k
      change
        (∑ j : I n, (Y i j k + ∑ t : I n, Y i t k)) = 0
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      rw [show Fintype.card (I n) = n by simp [I, ZMod.card]]
      rw [nsmul_eq_mul, natCast_odd_eq_one_F hn, one_mul, F_add_self]⟩
  map_add' Y Z := by
    apply Subtype.ext
    funext i j k
    change
      (Y i j k + Z i j k) +
          ∑ t : I n, (Y i t k + Z i t k) =
        (Y i j k + ∑ t : I n, Y i t k) +
          (Z i j k + ∑ t : I n, Z i t k)
    rw [Finset.sum_add_distrib]
    abel
  map_smul' r Y := by
    apply Subtype.ext
    funext i j k
    change
      r * Y i j k + ∑ t : I n, r * Y i t k =
        r * (Y i j k + ∑ t : I n, Y i t k)
    rw [← Finset.mul_sum, mul_add]

private noncomputable def diamondOddScalarYRaw
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddScalarSource n →ₗ[F] CyclicCube n where
  toFun x :=
    x.1.2.1 + x.1.2.2 +
      diamondOddJPrimitive hn (diamondOddScalarXJZero x)
  map_add' x y := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    simp only [Submodule.coe_smul_of_tower, Prod.smul_fst, Prod.smul_snd,
      map_smul, RingHom.id_apply]
    rw [smul_add, smul_add]

private noncomputable def diamondOddScalarYJZero
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddScalarSource n →ₗ[F] DiamondOddJZero n :=
  (diamondOddJNormalize hn).comp (diamondOddScalarYRaw hn)

noncomputable def diamondOddScalarHighX
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddScalarSource n →ₗ[F] DiamondOddHighFreq n :=
  (diamondOddHighFreqProjection hn).comp diamondOddScalarXJZero

noncomputable def diamondOddScalarHighY
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddScalarSource n →ₗ[F] DiamondOddHighFreq n :=
  (diamondOddHighFreqProjection hn).comp (diamondOddScalarYJZero hn)

private noncomputable def diamondOddScalarD
    {n : Nat} [NeZero n] :
    DiamondOddScalarSource n →ₗ[F] CyclicCube n where
  toFun x := x.1.2.1 + x.1.2.2
  map_add' x y := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add]
    abel
  map_smul' r x := by
    simp only [Submodule.coe_smul_of_tower, Prod.smul_fst, Prod.smul_snd,
      RingHom.id_apply]
    rw [smul_add]

private theorem diamondOddScalar_orbit_kernel
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    let X := diamondOddScalarXJZero x
    let xp := oddOrbitSumPiRestrict X
    let yp : MatrixProfile n :=
      oddOrbitSumPi (diamondOddScalarD x) +
        (oddOrbitProfileInverseJ hn xp).1
    (xp, yp) ∈ DiamondOddOrbitRelation n hn := by
  dsimp only
  apply LinearMap.mem_ker.mpr
  rw [oddOrbitRelationMap_apply]
  have hcancel :
      (oddOrbitSumPi (diamondOddScalarD x) +
          (oddOrbitProfileInverseJ hn
            (oddOrbitSumPiRestrict
              (diamondOddScalarXJZero x))).1) +
        (oddOrbitProfileInverseJ hn
          (oddOrbitSumPiRestrict
            (diamondOddScalarXJZero x))).1 =
      oddOrbitSumPi (diamondOddScalarD x) := by
    funext j s
    simp only [Pi.add_apply]
    rw [show
      oddOrbitSumPi (diamondOddScalarD x) j s +
          (oddOrbitProfileInverseJ hn
            (oddOrbitSumPiRestrict
              (diamondOddScalarXJZero x))).1 j s +
        (oddOrbitProfileInverseJ hn
          (oddOrbitSumPiRestrict
            (diamondOddScalarXJZero x))).1 j s =
        oddOrbitSumPi (diamondOddScalarD x) j s +
          ((oddOrbitProfileInverseJ hn
            (oddOrbitSumPiRestrict
              (diamondOddScalarXJZero x))).1 j s +
           (oddOrbitProfileInverseJ hn
            (oddOrbitSumPiRestrict
              (diamondOddScalarXJZero x))).1 j s) by abel,
      F_add_self, add_zero]
  rw [hcancel]
  funext j s
  change
    oddOrbitSumPi (diamondOddScalarXRaw x) j s +
      oddMatrixDiffS (oddOrbitSumPi (diamondOddScalarD x)) j s = 0
  have hBshift :=
    sum_shift (n := n) (1 : I n)
      (fun i : I n => x.1.2.1 i j (s + 1 - i))
  have hidx (i : I n) :
      s + 1 - (i + 1) = s - i := by
    abel
  have hwidx (i : I n) :
      s - i + 1 = s + 1 - i := by
    abel
  simp_rw [hidx] at hBshift
  simp only [diamondOddScalarXRaw, diamondOddScalarD,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
    oddOrbitSumPi_apply, oddMatrixDiffS_apply,
    diamondOdd_cubeDiffI_apply, diamondOdd_cubeDiffK_apply,
    Finset.sum_add_distrib]
  rw [hBshift]
  simp_rw [hwidx]
  let b₀ := ∑ i : I n, x.1.2.1 i j (s - i)
  let b₁ := ∑ i : I n, x.1.2.1 i j (s + 1 - i)
  let w₀ := ∑ i : I n, x.1.2.2 i j (s - i)
  let w₁ := ∑ i : I n, x.1.2.2 i j (s + 1 - i)
  change (b₀ + b₁) + (w₀ + w₁) + ((b₀ + w₀) + (b₁ + w₁)) = 0
  calc
    (b₀ + b₁) + (w₀ + w₁) + ((b₀ + w₀) + (b₁ + w₁)) =
        (b₀ + b₀) + (b₁ + b₁) + (w₀ + w₀) + (w₁ + w₁) := by
          abel
    _ = 0 := by
      simp only [F_add_self, zero_add]

private noncomputable def diamondOddScalarOrbitRelation
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    DiamondOddOrbitRelation n hn :=
  let X := diamondOddScalarXJZero x
  let xp := oddOrbitSumPiRestrict X
  let yp : MatrixProfile n :=
    oddOrbitSumPi (diamondOddScalarD x) +
      (oddOrbitProfileInverseJ hn xp).1
  ⟨(xp, yp), diamondOddScalar_orbit_kernel hn x⟩

private theorem diamondOddOrbitSumPi_JPrimitive
    {n : Nat} [NeZero n] (hn : Odd n)
    (X : DiamondOddJZero n) :
    oddOrbitSumPi (diamondOddJPrimitive hn X) =
      (oddOrbitProfileInverseJ hn (oddOrbitSumPiRestrict X)).1 := by
  funext j s
  let u : I n → ZeroSumProfile n :=
    fun i =>
      ⟨fun t => X.1 i t (s - i),
        congrFun
          (congrFun (LinearMap.mem_ker.mp X.2) i)
          (s - i)⟩
  have hu :
      (∑ i : I n, u i) =
        oddOrbitColumn (oddOrbitSumPiRestrict X) s := by
    apply Subtype.ext
    funext t
    simp only [u, Submodule.coe_sum, Finset.sum_apply,
      oddOrbitColumn, oddOrbitSumPiRestrict,
      LinearMap.codRestrict_apply, LinearMap.comp_apply,
      Submodule.coe_subtype, oddOrbitSumPi,
      LinearMap.coe_mk, AddHom.coe_mk]
  change
    (∑ i : I n, (oddCyclicInverse hn (u i)).1 j) =
      (oddCyclicInverse hn
        (oddOrbitColumn (oddOrbitSumPiRestrict X) s)).1 j
  calc
    (∑ i : I n, (oddCyclicInverse hn (u i)).1 j) =
        (∑ i : I n, oddCyclicInverse hn (u i)).1 j := by
          simp only [Submodule.coe_sum, Finset.sum_apply]
    _ = (oddCyclicInverse hn (∑ i : I n, u i)).1 j := by
          rw [map_sum]
    _ = (oddCyclicInverse hn
        (oddOrbitColumn (oddOrbitSumPiRestrict X) s)).1 j := by
          rw [hu]

private theorem diamondOddOrbitSumPi_normalize_apply
    {n : Nat} [NeZero n] (hn : Odd n)
    (Y : CyclicCube n) (j s : I n) :
    oddOrbitSumPi (diamondOddJNormalize hn Y).1 j s =
      oddOrbitSumPi Y j s +
        ∑ i : I n, ∑ t : I n, Y i t (s - i) := by
  change
    (∑ i : I n,
      (Y i j (s - i) + ∑ t : I n, Y i t (s - i))) =
      (∑ i : I n, Y i j (s - i)) +
        ∑ i : I n, ∑ t : I n, Y i t (s - i)
  rw [Finset.sum_add_distrib]

private theorem diamondOddMatrixDot_normalize
    {n : Nat} [NeZero n] (hn : Odd n)
    (X : DiamondOddJZero n) (Y : CyclicCube n) :
    oddMatrixDot (oddOrbitSumPiRestrict X).1
        (oddOrbitSumPi (diamondOddJNormalize hn Y).1) =
      oddMatrixDot (oddOrbitSumPiRestrict X).1
        (oddOrbitSumPi Y) := by
  unfold oddMatrixDot
  rw [Finset.sum_comm]
  calc
    (∑ s : I n, ∑ j : I n,
        (oddOrbitSumPiRestrict X).1 j s *
          oddOrbitSumPi (diamondOddJNormalize hn Y).1 j s) =
        ∑ s : I n, ∑ j : I n,
          (oddOrbitSumPiRestrict X).1 j s *
            (oddOrbitSumPi Y j s +
              ∑ i : I n, ∑ t : I n, Y i t (s - i)) := by
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro j _
          rw [diamondOddOrbitSumPi_normalize_apply]
    _ = ∑ s : I n,
        ((∑ j : I n,
            (oddOrbitSumPiRestrict X).1 j s *
              oddOrbitSumPi Y j s) +
          (∑ j : I n, (oddOrbitSumPiRestrict X).1 j s) *
            (∑ i : I n, ∑ t : I n, Y i t (s - i))) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ s : I n, ∑ j : I n,
          (oddOrbitSumPiRestrict X).1 j s *
            oddOrbitSumPi Y j s := by
          apply Finset.sum_congr rfl
          intro s _
          have hz :
              (∑ j : I n,
                (oddOrbitSumPiRestrict X).1 j s) = 0 := by
            simpa only [sigmaMapM, LinearMap.coe_mk, AddHom.coe_mk,
              Finset.sum_apply, Pi.zero_apply] using
              congrFun
                (LinearMap.mem_ker.mp
                  (oddOrbitSumPiRestrict X).2)
                s
          rw [hz, zero_mul, add_zero]
    _ = ∑ j : I n, ∑ s : I n,
          (oddOrbitSumPiRestrict X).1 j s *
            oddOrbitSumPi Y j s := Finset.sum_comm

private theorem diamondOddOrbitSumPi_scalarYRaw
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    oddOrbitSumPi (diamondOddScalarYRaw hn x) =
      oddOrbitSumPi (diamondOddScalarD x) +
        (oddOrbitProfileInverseJ hn
          (oddOrbitSumPiRestrict (diamondOddScalarXJZero x))).1 := by
  have hy :
      diamondOddScalarYRaw hn x =
        diamondOddScalarD x +
          diamondOddJPrimitive hn (diamondOddScalarXJZero x) := by
    rfl
  rw [hy, map_add, diamondOddOrbitSumPi_JPrimitive]

private theorem diamondOdd_cubeDot_normalize
    {n : Nat} [NeZero n] (hn : Odd n)
    (X : DiamondOddJZero n) (Y : CyclicCube n) :
    cubeDot X.1 (diamondOddJNormalize hn Y).1 =
      cubeDot X.1 Y := by
  rw [diamondOdd_cubeDot_eq_iterated_sum,
    diamondOdd_cubeDot_eq_iterated_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  calc
    (∑ k : I n, ∑ j : I n,
        X.1 i j k * (diamondOddJNormalize hn Y).1 i j k) =
        ∑ k : I n, ∑ j : I n,
          X.1 i j k *
            (Y i j k + ∑ t : I n, Y i t k) := by
          rfl
    _ = ∑ k : I n,
        ((∑ j : I n, X.1 i j k * Y i j k) +
          (∑ j : I n, X.1 i j k) *
            (∑ t : I n, Y i t k)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ k : I n, ∑ j : I n,
          X.1 i j k * Y i j k := by
          apply Finset.sum_congr rfl
          intro k _
          have hz :
              (∑ j : I n, X.1 i j k) = 0 :=
            congrFun (congrFun (LinearMap.mem_ker.mp X.2) i) k
          rw [hz, zero_mul, add_zero]
    _ = ∑ j : I n, ∑ k : I n,
          X.1 i j k * Y i j k := Finset.sum_comm

private theorem diamondOddScalar_X_totalPrimitive_dot_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    cubeDot (diamondOddScalarXJZero x).1
      (diamondOddScalarTotal x +
        diamondOddJPrimitive hn (diamondOddScalarXJZero x)) = 0 := by
  rw [diamondOdd_cubeDot_eq_iterated_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k _
  let K : Profile n := fun j =>
    diamondOddScalarTotal x i j k +
      diamondOddJPrimitive hn (diamondOddScalarXJZero x) i j k
  have hKdiff : cycDiff (n := n) F K = 0 := by
    funext j
    change
      (diamondOddScalarTotal x i j k +
          diamondOddJPrimitive hn (diamondOddScalarXJZero x) i j k) +
        (diamondOddScalarTotal x i (j + 1) k +
          diamondOddJPrimitive hn (diamondOddScalarXJZero x) i (j + 1) k) =
        0
    have hC :=
      congrFun
        (congrFun
          (congrFun (diamondOddScalar_diffJStar_total x) i) j)
        k
    have hS :=
      congrFun
        (congrFun
          (congrFun
            (diamondOddJPrimitive_diff hn
              (diamondOddScalarXJZero x)) i) j)
        k
    rw [diamondOdd_cubeDiffJStar_apply] at hC hS
    have hXval :
        (diamondOddScalarXJZero x).1 i j k =
          diamondOddScalarXRaw x i j k :=
      rfl
    rw [hXval] at hS
    rw [show
      (diamondOddScalarTotal x i j k +
          diamondOddJPrimitive hn (diamondOddScalarXJZero x) i j k) +
        (diamondOddScalarTotal x i (j + 1) k +
          diamondOddJPrimitive hn (diamondOddScalarXJZero x) i (j + 1) k) =
        (diamondOddScalarTotal x i j k +
          diamondOddScalarTotal x i (j + 1) k) +
        (diamondOddJPrimitive hn (diamondOddScalarXJZero x) i j k +
          diamondOddJPrimitive hn
            (diamondOddScalarXJZero x) i (j + 1) k) by abel,
      hC, hS, F_add_self]
  have hKconst (j : I n) : K j = K 0 :=
    (cycDiff_eq_zero_iff_constant_apply F K).mp hKdiff j
  change
    (∑ j : I n,
      (diamondOddScalarXJZero x).1 i j k * K j) = 0
  simp_rw [hKconst]
  rw [← Finset.sum_mul]
  have hz :
      (∑ j : I n, (diamondOddScalarXJZero x).1 i j k) = 0 :=
    congrFun
      (congrFun
        (LinearMap.mem_ker.mp (diamondOddScalarXJZero x).2)
        i)
      k
  rw [hz, zero_mul]

private theorem diamondOddScalar_phase_eq_X_YRaw
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    diamondOddScalarQ x =
      cubeDot (diamondOddScalarXJZero x).1
        (diamondOddScalarYRaw hn x) := by
  have hzero :=
    diamondOddScalar_X_totalPrimitive_dot_zero hn x
  have hsplit :
      diamondOddScalarTotal x +
          diamondOddJPrimitive hn (diamondOddScalarXJZero x) =
        x.1.1 + diamondOddScalarYRaw hn x := by
    funext i j k
    simp only [diamondOddScalarTotal, diamondOddScalarYRaw,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
    abel
  rw [hsplit, diamondOdd_cubeDot_add_right] at hzero
  unfold diamondOddScalarQ
  change
    cubeDot x.1.1 (diamondOddScalarXJZero x).1 =
      cubeDot (diamondOddScalarXJZero x).1
        (diamondOddScalarYRaw hn x)
  rw [diamondOdd_cubeDot_comm]
  exact diamondOdd_eq_of_add_eq_zero _ _ hzero

private theorem diamondOddOrbitLift_cubeDot
    {n : Nat} [NeZero n] (hn : Odd n)
    (p q : DiamondOddOrbitProfile n) :
    cubeDot (oddOrbitLift p).1 (oddOrbitLift q).1 =
      oddMatrixDot p.1 q.1 := by
  rw [diamondOdd_cubeDot_eq_iterated_sum]
  unfold oddMatrixDot
  simp only [oddOrbitLift_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    (∑ i : I n, ∑ k : I n,
        p.1 j (i + k) * q.1 j (i + k)) =
        ∑ i : I n, ∑ s : I n,
          p.1 j s * q.1 j s := by
          apply Finset.sum_congr rfl
          intro i _
          simpa only [add_comm] using
            sum_shift (n := n) i
              (fun s : I n => p.1 j s * q.1 j s)
    _ = ∑ s : I n, ∑ _i : I n,
          p.1 j s * q.1 j s := Finset.sum_comm
    _ = ∑ s : I n, p.1 j s * q.1 j s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_const, Finset.card_univ]
          rw [show Fintype.card (I n) = n by simp [I, ZMod.card]]
          rw [nsmul_eq_mul, natCast_odd_eq_one_F hn, one_mul]

private theorem diamondOddHighFreq_pairing_of_orbit_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (X Y : DiamondOddJZero n)
    (horbit :
      oddMatrixDot (oddOrbitSumPiRestrict X).1
        (oddOrbitSumPiRestrict Y).1 = 0) :
    cubeDot X.1 Y.1 =
      oddHighFreqPairing
        (diamondOddHighFreqProjection hn Y)
        (diamondOddHighFreqProjection hn X) := by
  conv_lhs =>
    rw [diamondOddHighFreqProjection_decomposition hn X,
      diamondOddHighFreqProjection_decomposition hn Y]
  simp only [Submodule.coe_add]
  rw [diamondOdd_cubeDot_add_left,
    diamondOdd_cubeDot_add_right,
    diamondOdd_cubeDot_add_right]
  rw [diamondOddHighFreq_cubeDot_oddOrbitLift_eq_zero]
  have hcross :
      cubeDot
          (oddOrbitLift (oddOrbitSumPiRestrict X)).1
          (diamondOddHighFreqProjection hn Y).1.1 = 0 := by
    rw [diamondOdd_cubeDot_comm]
    exact diamondOddHighFreq_cubeDot_oddOrbitLift_eq_zero
      (diamondOddHighFreqProjection hn Y)
      (oddOrbitSumPiRestrict X)
  rw [hcross, diamondOddOrbitLift_cubeDot hn, horbit]
  simp only [add_zero]
  rw [oddHighFreqPairing_apply]
  rw [← diamondOdd_cubeDot_eq_iterated_sum]
  exact diamondOdd_cubeDot_comm _ _

private theorem diamondOddScalar_phase_highfreq
    {n : Nat} [NeZero n] (hn : Odd n)
    (x : DiamondOddScalarSource n) :
    diamondOddScalarQ x =
      oddHighFreqPairing
        (diamondOddScalarHighY hn x)
        (diamondOddScalarHighX hn x) := by
  rw [diamondOddScalar_phase_eq_X_YRaw hn x]
  rw [← diamondOdd_cubeDot_normalize hn
    (diamondOddScalarXJZero x) (diamondOddScalarYRaw hn x)]
  have hraw :
      oddMatrixDot
          (oddOrbitSumPiRestrict (diamondOddScalarXJZero x)).1
          (oddOrbitSumPi (diamondOddScalarYRaw hn x)) = 0 := by
    have hz :=
      diamondOddOrbitRelation_q_eq_zero hn
        (diamondOddScalarOrbitRelation hn x)
    change
      oddMatrixDot
          (oddOrbitSumPiRestrict (diamondOddScalarXJZero x)).1
          (oddOrbitSumPi (diamondOddScalarD x) +
            (oddOrbitProfileInverseJ hn
              (oddOrbitSumPiRestrict
                (diamondOddScalarXJZero x))).1) = 0 at hz
    rw [← diamondOddOrbitSumPi_scalarYRaw hn x] at hz
    exact hz
  have hnormalized :
      oddMatrixDot
          (oddOrbitSumPiRestrict (diamondOddScalarXJZero x)).1
          (oddOrbitSumPiRestrict
            (diamondOddScalarYJZero hn x)).1 = 0 := by
    change
      oddMatrixDot
          (oddOrbitSumPiRestrict (diamondOddScalarXJZero x)).1
          (oddOrbitSumPi
            (diamondOddJNormalize hn
              (diamondOddScalarYRaw hn x)).1) = 0
    rw [diamondOddMatrixDot_normalize]
    exact hraw
  exact
    diamondOddHighFreq_pairing_of_orbit_zero hn
      (diamondOddScalarXJZero x)
      (diamondOddScalarYJZero hn x)
      hnormalized

private theorem diamondOddJNormalize_of_jzero
    {n : Nat} [NeZero n] (hn : Odd n)
    (Y : DiamondOddJZero n) :
    diamondOddJNormalize hn Y.1 = Y := by
  apply Subtype.ext
  funext i j k
  change Y.1 i j k + (∑ t : I n, Y.1 i t k) = Y.1 i j k
  have hz :
      (∑ t : I n, Y.1 i t k) = 0 :=
    congrFun (congrFun (LinearMap.mem_ker.mp Y.2) i) k
  rw [hz, add_zero]

private theorem diamondOddHighFreqProjection_of_highfreq
    {n : Nat} [NeZero n] (hn : Odd n)
    (H : DiamondOddHighFreq n) :
    diamondOddHighFreqProjection hn H.1 = H := by
  apply Subtype.ext
  rw [diamondOddHighFreqProjection_apply]
  have hpi :
      oddOrbitSumPiRestrict H.1 = 0 :=
    LinearMap.mem_ker.mp H.2
  rw [hpi, map_zero, add_zero]

private theorem diamondOddHighFreq_orbitSumPi_zero
    {n : Nat} [NeZero n]
    (H : DiamondOddHighFreq n) :
    oddOrbitSumPi H.1.1 = 0 := by
  have hpi :
      oddOrbitSumPiRestrict H.1 = 0 :=
    LinearMap.mem_ker.mp H.2
  have hval := congrArg Subtype.val hpi
  change oddOrbitSumPi H.1.1 = 0 at hval
  exact hval

private theorem diamondOddOrbitSumPi_cubeDiffK_apply
    {n : Nat} [NeZero n]
    (D : CyclicCube n) (j s : I n) :
    oddOrbitSumPi (cubeDiffK D) j s =
      oddOrbitSumPi D j s + oddOrbitSumPi D j (s + 1) := by
  simp only [oddOrbitSumPi_apply, diamondOdd_cubeDiffK_apply,
    Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  abel

private theorem diamondOddScalarSourceMap_zero_of_diffJStar
    {n : Nat} [NeZero n]
    (z : DiamondOddScalarAmbient n)
    (h :
      cubeDiffJStar (z.1 + z.2.1 + z.2.2) =
        cubeDiffI z.2.1 + cubeDiffK z.2.2) :
    diamondOddScalarSourceMap z = 0 := by
  funext i j k
  have hj :=
    congrFun (congrFun (congrFun h i) (j - 1)) k
  simp only [Pi.add_apply, diamondOdd_cubeDiffJStar_apply,
    diamondOdd_cubeDiffI_apply, diamondOdd_cubeDiffK_apply] at hj
  have hidx : j - 1 + 1 = j := by abel
  rw [hidx] at hj
  simp only [diamondOddScalarSourceMap_apply, Pi.add_apply,
    diamondOdd_cubeDiffJInv_apply, diamondOdd_cubeDiffP_apply,
    diamondOdd_cubeDiffR_apply, Pi.zero_apply]
  have hC :
      (z.1 i (j - 1) k + z.2.1 i (j - 1) k +
          z.2.2 i (j - 1) k) +
        (z.1 i j k + z.2.1 i j k + z.2.2 i j k) =
      (z.2.1 i (j - 1) k + z.2.1 (i + 1) (j - 1) k) +
        (z.2.2 i (j - 1) k + z.2.2 i (j - 1) (k + 1)) := by
    exact hj
  calc
    (z.1 i j k + z.1 i (j - 1) k) +
          (z.2.1 i j k + z.2.1 (i + 1) (j - 1) k) +
        (z.2.2 i j k + z.2.2 i (j - 1) (k + 1)) =
      ((z.1 i (j - 1) k + z.2.1 i (j - 1) k +
          z.2.2 i (j - 1) k) +
        (z.1 i j k + z.2.1 i j k + z.2.2 i j k)) +
      ((z.2.1 i (j - 1) k + z.2.1 (i + 1) (j - 1) k) +
        (z.2.2 i (j - 1) k + z.2.2 i (j - 1) (k + 1))) := by
          rw [show
            ((z.1 i (j - 1) k + z.2.1 i (j - 1) k +
                z.2.2 i (j - 1) k) +
              (z.1 i j k + z.2.1 i j k + z.2.2 i j k)) +
            ((z.2.1 i (j - 1) k + z.2.1 (i + 1) (j - 1) k) +
              (z.2.2 i (j - 1) k +
                z.2.2 i (j - 1) (k + 1))) =
            (z.1 i j k + z.1 i (j - 1) k) +
              (z.2.1 i j k + z.2.1 (i + 1) (j - 1) k) +
              (z.2.2 i j k + z.2.2 i (j - 1) (k + 1)) +
              (z.2.1 i (j - 1) k + z.2.1 i (j - 1) k) +
              (z.2.2 i (j - 1) k + z.2.2 i (j - 1) k) by
                abel,
            F_add_self, F_add_self, add_zero, add_zero]
    _ = 0 := by
      rw [hC, F_add_self]

private noncomputable def diamondOddScalarPreimageD
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    CyclicCube n :=
  z.2.1.1 + diamondOddJPrimitive hn z.1.1

private theorem diamondOddScalarPreimageD_orbitSumPi_zero
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    oddOrbitSumPi (diamondOddScalarPreimageD hn z) = 0 := by
  unfold diamondOddScalarPreimageD
  rw [map_add, diamondOddHighFreq_orbitSumPi_zero,
    diamondOddOrbitSumPi_JPrimitive]
  have hz :
      oddOrbitSumPiRestrict z.1.1 = 0 :=
    LinearMap.mem_ker.mp z.1.2
  rw [hz, map_zero]
  rfl

private noncomputable def diamondOddScalarPreimageR
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    CyclicCube n :=
  z.1.1.1 + cubeDiffK (diamondOddScalarPreimageD hn z)

private theorem diamondOddScalarPreimageR_mem
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    diamondOddScalarPreimageR hn z ∈
      LinearMap.ker (oddOrbitSumPi (n := n)) := by
  apply LinearMap.mem_ker.mpr
  funext j s
  change oddOrbitSumPi (diamondOddScalarPreimageR hn z) j s = 0
  unfold diamondOddScalarPreimageR
  rw [map_add, diamondOddHighFreq_orbitSumPi_zero]
  simp only [Pi.add_apply, Pi.zero_apply, zero_add]
  rw [diamondOddOrbitSumPi_cubeDiffK_apply,
    diamondOddScalarPreimageD_orbitSumPi_zero]
  rfl

private noncomputable def diamondOddScalarPreimageRKer
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    LinearMap.ker (oddOrbitSumPi (n := n)) :=
  ⟨diamondOddScalarPreimageR hn z,
    diamondOddScalarPreimageR_mem hn z⟩

private noncomputable def diamondOddScalarPreimageB
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    CyclicCube n :=
  oddIKStarPrimitive (diamondOddScalarPreimageRKer hn z)

private theorem diamondOdd_cubeDiffIK_eq_oddIKStar
    {n : Nat} [NeZero n] (B : CyclicCube n) :
    cubeDiffI B + cubeDiffK B = oddIKStarMap B := by
  funext i j k
  simp only [Pi.add_apply, diamondOdd_cubeDiffI_apply,
    diamondOdd_cubeDiffK_apply, oddIKStarMap_apply]
  rfl

private noncomputable def diamondOddScalarPreimageAmbient
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    DiamondOddScalarAmbient n :=
  (z.2.1.1,
    (diamondOddScalarPreimageB hn z,
      diamondOddScalarPreimageB hn z +
        diamondOddScalarPreimageD hn z))

private theorem diamondOddScalarPreimageAmbient_total
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    (diamondOddScalarPreimageAmbient hn z).1 +
        (diamondOddScalarPreimageAmbient hn z).2.1 +
        (diamondOddScalarPreimageAmbient hn z).2.2 =
      diamondOddJPrimitive hn z.1.1 := by
  unfold diamondOddScalarPreimageAmbient diamondOddScalarPreimageD
  funext i j k
  simp only [Pi.add_apply]
  rw [show
    z.2.1.1 i j k + diamondOddScalarPreimageB hn z i j k +
      (diamondOddScalarPreimageB hn z i j k +
        (z.2.1.1 i j k + diamondOddJPrimitive hn z.1.1 i j k)) =
      (diamondOddScalarPreimageB hn z i j k +
        diamondOddScalarPreimageB hn z i j k) +
      (z.2.1.1 i j k + z.2.1.1 i j k) +
      diamondOddJPrimitive hn z.1.1 i j k by abel,
    F_add_self, F_add_self, zero_add, zero_add]

private theorem diamondOddScalarPreimageAmbient_X
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    cubeDiffI (diamondOddScalarPreimageAmbient hn z).2.1 +
        cubeDiffK (diamondOddScalarPreimageAmbient hn z).2.2 =
      z.1.1.1 := by
  unfold diamondOddScalarPreimageAmbient
  rw [map_add]
  rw [show
    cubeDiffI (diamondOddScalarPreimageB hn z) +
        (cubeDiffK (diamondOddScalarPreimageB hn z) +
          cubeDiffK (diamondOddScalarPreimageD hn z)) =
      (cubeDiffI (diamondOddScalarPreimageB hn z) +
        cubeDiffK (diamondOddScalarPreimageB hn z)) +
          cubeDiffK (diamondOddScalarPreimageD hn z) by abel]
  rw [diamondOdd_cubeDiffIK_eq_oddIKStar]
  unfold diamondOddScalarPreimageB
  rw [oddIKStarMap_oddIKStarPrimitive]
  change
    diamondOddScalarPreimageR hn z +
        cubeDiffK (diamondOddScalarPreimageD hn z) =
      z.1.1.1
  unfold diamondOddScalarPreimageR
  rw [show
    z.1.1.1 + cubeDiffK (diamondOddScalarPreimageD hn z) +
        cubeDiffK (diamondOddScalarPreimageD hn z) =
      z.1.1.1 +
        (cubeDiffK (diamondOddScalarPreimageD hn z) +
          cubeDiffK (diamondOddScalarPreimageD hn z)) by abel,
    F_module_add_self, add_zero]

private theorem diamondOddScalarPreimageAmbient_mem
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    diamondOddScalarPreimageAmbient hn z ∈
      DiamondOddScalarSource n := by
  apply LinearMap.mem_ker.mpr
  apply diamondOddScalarSourceMap_zero_of_diffJStar
  rw [diamondOddScalarPreimageAmbient_total,
    diamondOddJPrimitive_diff,
    diamondOddScalarPreimageAmbient_X]

private noncomputable def diamondOddScalarPreimage
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    DiamondOddScalarSource n :=
  ⟨diamondOddScalarPreimageAmbient hn z,
    diamondOddScalarPreimageAmbient_mem hn z⟩

private theorem diamondOddScalarPreimage_XJZero
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    diamondOddScalarXJZero (diamondOddScalarPreimage hn z) = z.1.1 := by
  apply Subtype.ext
  change
    cubeDiffI (diamondOddScalarPreimageAmbient hn z).2.1 +
        cubeDiffK (diamondOddScalarPreimageAmbient hn z).2.2 =
      z.1.1.1
  exact diamondOddScalarPreimageAmbient_X hn z

private theorem diamondOddScalarPreimage_highX
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    diamondOddScalarHighX hn (diamondOddScalarPreimage hn z) = z.1 := by
  change
    diamondOddHighFreqProjection hn
        (diamondOddScalarXJZero (diamondOddScalarPreimage hn z)) =
      z.1
  rw [diamondOddScalarPreimage_XJZero,
    diamondOddHighFreqProjection_of_highfreq]

private theorem diamondOddScalarPreimage_YRaw
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    diamondOddScalarYRaw hn (diamondOddScalarPreimage hn z) =
      z.2.1.1 := by
  change
    diamondOddScalarPreimageB hn z +
        (diamondOddScalarPreimageB hn z +
          diamondOddScalarPreimageD hn z) +
      diamondOddJPrimitive hn
        (diamondOddScalarXJZero (diamondOddScalarPreimage hn z)) =
      z.2.1.1
  rw [diamondOddScalarPreimage_XJZero]
  unfold diamondOddScalarPreimageD
  funext i j k
  simp only [Pi.add_apply]
  rw [show
    diamondOddScalarPreimageB hn z i j k +
        (diamondOddScalarPreimageB hn z i j k +
          (z.2.1.1 i j k + diamondOddJPrimitive hn z.1.1 i j k)) +
      diamondOddJPrimitive hn z.1.1 i j k =
      (diamondOddScalarPreimageB hn z i j k +
        diamondOddScalarPreimageB hn z i j k) +
      (diamondOddJPrimitive hn z.1.1 i j k +
        diamondOddJPrimitive hn z.1.1 i j k) +
      z.2.1.1 i j k by abel,
    F_add_self, F_add_self, zero_add, zero_add]

private theorem diamondOddScalarPreimage_highY
    {n : Nat} [NeZero n] (hn : Odd n)
    (z : DiamondOddHighFreq n × DiamondOddHighFreq n) :
    diamondOddScalarHighY hn (diamondOddScalarPreimage hn z) = z.2 := by
  change
    diamondOddHighFreqProjection hn
        (diamondOddJNormalize hn
          (diamondOddScalarYRaw hn
            (diamondOddScalarPreimage hn z))) =
      z.2
  rw [diamondOddScalarPreimage_YRaw]
  rw [show z.2.1.1 = z.2.1.1 by rfl]
  rw [show
      diamondOddJNormalize hn z.2.1.1 = z.2.1 by
        exact diamondOddJNormalize_of_jzero hn z.2.1]
  exact diamondOddHighFreqProjection_of_highfreq hn z.2

abbrev DiamondOddScalarWittCore
    (n : Nat) [NeZero n] :=
  DiamondOddHighFreq n × Module.Dual F (DiamondOddHighFreq n)

noncomputable def diamondOddScalarWittCoreQ
    {n : Nat} [NeZero n]
    (z : DiamondOddScalarWittCore n) : F :=
  z.2 z.1

noncomputable def diamondOddScalarWittMap
    {n : Nat} [NeZero n] (hn : Odd n) :
    DiamondOddScalarSource n →ₗ[F] DiamondOddScalarWittCore n where
  toFun x :=
    (diamondOddScalarHighX hn x,
      oddHighFreqPairing (diamondOddScalarHighY hn x))
  map_add' x y := by
    simp only [map_add, Prod.mk_add_mk]
  map_smul' r x := by
    simp only [map_smul, Prod.smul_mk, RingHom.id_apply]

@[simp] theorem diamondOddScalarWittMap_apply
    {n : Nat} [NeZero n]
    (hn : Odd n) (x : DiamondOddScalarSource n) :
    diamondOddScalarWittMap hn x =
      (diamondOddScalarHighX hn x,
        oddHighFreqPairing (diamondOddScalarHighY hn x)) :=
  rfl

theorem diamondOddScalarWittMap_phase
    {n : Nat} [NeZero n]
    (hn : Odd n) (x : DiamondOddScalarSource n) :
    diamondOddScalarWittCoreQ (diamondOddScalarWittMap hn x) =
      diamondOddScalarQ x := by
  change
    oddHighFreqPairing
        (diamondOddScalarHighY hn x)
        (diamondOddScalarHighX hn x) =
      diamondOddScalarQ x
  exact (diamondOddScalar_phase_highfreq hn x).symm

theorem diamondOddScalarWittMap_surjective
    {n : Nat} [NeZero n] (hn : Odd n) :
    Function.Surjective
      (diamondOddScalarWittMap (n := n) hn) := by
  intro z
  rcases oddHighFreqPairing_surjective hn z.2 with ⟨K, hK⟩
  refine
    ⟨diamondOddScalarPreimage hn (z.1, K), ?_⟩
  rw [diamondOddScalarWittMap_apply,
    diamondOddScalarPreimage_highX,
    diamondOddScalarPreimage_highY,
    hK]

end

end Core4loop.SquareDiagonal.DirectWitt
