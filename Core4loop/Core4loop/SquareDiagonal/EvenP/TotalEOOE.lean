import Core4loop.SquareDiagonal.EvenP.TotalEOOO
import Core4loop.SquareDiagonal.EvenP.TailPairing

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

private example {n d : Nat} [NeZero n] :
    AddCommMonoid
      (PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d)) :=
  inferInstance

@[reducible] private noncomputable def pointedCubeProdAddCommMonoid
    {n d : Nat} [NeZero n] :
    AddCommMonoid
      ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d)) ×
        CyclicCube n) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d)))
    (inferInstance : AddCommMonoid (CyclicCube n))

private local instance {n d : Nat} [NeZero n] :
    AddCommMonoid
      ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d)) ×
        CyclicCube n) :=
  pointedCubeProdAddCommMonoid

private example {n : Nat} [NeZero n] :
    AddCommMonoid (CyclicCube n) :=
  inferInstance

private example {n d : Nat} [NeZero n] :
    AddCommMonoid
      ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d)) ×
        CyclicCube n) :=
  inferInstance

private noncomputable def singletonFamilyEquiv
    {n : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :
    (PVec n 1 → V) ≃ₗ[F] V where
  toFun f := f zeroVec
  invFun v := fun _ => v
  left_inv f := by
    funext p
    rw [pVec_one_eq_zeroVec p]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def singletonBiFamilyEquiv
    {n : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :
    (PVec n 1 → PVec n 1 → V) ≃ₗ[F] V :=
  (singletonFamilyEquiv (n := n) (PVec n 1 → V)).trans
    (singletonFamilyEquiv (n := n) V)

private noncomputable def cubeKShiftEquiv
    {n : Nat} [NeZero n] (u : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X := fun i j k => X i j (k - u)
  invFun X := fun i j k => X i j (k + u)
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def wGaugeFamilyEquiv
    {n d : Nat} [NeZero n] :
    (PVec n d → CyclicCube n) ≃ₗ[F]
      (PVec n d → CyclicCube n) where
  toFun X wt := cubeKShiftEquiv (vecSum wt) (X wt)
  invFun X wt := (cubeKShiftEquiv (vecSum wt)).symm (X wt)
  left_inv X := by
    funext wt
    exact (cubeKShiftEquiv (vecSum wt)).symm_apply_apply (X wt)
  right_inv X := by
    funext wt
    exact (cubeKShiftEquiv (vecSum wt)).apply_symm_apply (X wt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def bWGaugedEquiv
    {n d : Nat} [NeZero n] (hd : 0 < d) :
    BFun4 n 1 1 d ≃ₗ[F] (PVec n d → CyclicCube n) :=
  (diamondBRootCubeEquiv
      (n := n) (c := 1) (d := d) Nat.zero_lt_one hd).trans
    ((singletonFamilyEquiv
      (n := n) (PVec n d → CyclicCube n)).trans
        (wGaugeFamilyEquiv (n := n) (d := d)))

private noncomputable def wRootEquiv
    {n : Nat} [NeZero n] :
    WFun4 n 1 1 1 ≃ₗ[F] CyclicCube n :=
  (diamondWRootCubeEquiv
      (n := n) (b := 1) (c := 1)
      Nat.zero_lt_one Nat.zero_lt_one).trans
    (singletonBiFamilyEquiv (n := n) (CyclicCube n))

private noncomputable def aWGaugedEquiv
    {n d : Nat} [NeZero n] (hd : 0 < d) :
    AFun4 n 1 1 d ≃ₗ[F] (PVec n d → CyclicCube n) :=
  (diamondARootCubeEquiv
      (n := n) (b := 1) (c := 1) (d := d)
      Nat.zero_lt_one Nat.zero_lt_one hd).trans
    ((singletonBiFamilyEquiv
      (n := n) (PVec n d → CyclicCube n)).trans
        (wGaugeFamilyEquiv (n := n) (d := d)))

@[simp] private theorem bWGaugedEquiv_apply
    {n d : Nat} [NeZero n] (hd : 0 < d)
    (B : BFun4 n 1 1 d) (wt : PVec n d) (i j k : I n) :
    bWGaugedEquiv hd B wt i j k =
      diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt
        i j (k - vecSum wt) := rfl

private theorem bWGaugedEquiv_eq
    {n d : Nat} [NeZero n] (hd : 0 < d)
    (B : BFun4 n 1 1 d) (wt : PVec n d) :
    bWGaugedEquiv hd B wt =
      cubeKShiftEquiv (vecSum wt)
        (diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt) :=
  rfl

@[simp] private theorem wRootEquiv_apply
    {n : Nat} [NeZero n]
    (W : WFun4 n 1 1 1) (i j k : I n) :
    wRootEquiv W i j k =
      diamondWRootCubeEquiv Nat.zero_lt_one Nat.zero_lt_one W
        zeroVec zeroVec i j k := rfl

private theorem wRootEquiv_eq
    {n : Nat} [NeZero n] (W : WFun4 n 1 1 1) :
    wRootEquiv W =
      diamondWRootCubeEquiv Nat.zero_lt_one Nat.zero_lt_one W
        zeroVec zeroVec :=
  rfl

@[simp] private theorem aWGaugedEquiv_apply
    {n d : Nat} [NeZero n] (hd : 0 < d)
    (A : AFun4 n 1 1 d) (wt : PVec n d) (i j k : I n) :
    aWGaugedEquiv hd A wt i j k =
      diamondARootCubeEquiv
          Nat.zero_lt_one Nat.zero_lt_one hd A zeroVec zeroVec wt
        i j (k - vecSum wt) := rfl

private theorem aWGaugedEquiv_eq
    {n d : Nat} [NeZero n] (hd : 0 < d)
    (A : AFun4 n 1 1 d) (wt : PVec n d) :
    aWGaugedEquiv hd A wt =
      cubeKShiftEquiv (vecSum wt)
        (diamondARootCubeEquiv
          Nat.zero_lt_one Nat.zero_lt_one hd A zeroVec zeroVec wt) :=
  rfl

private theorem sum_pVec_one
    {n : Nat} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : PVec n 1 → M) :
    (∑ p : PVec n 1, f p) = f (zeroVec : PVec n 1) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    exact (hp (pVec_one_eq_zeroVec p)).elim
  · simp

private theorem sum_eq_at_point_add_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommMonoid V] (f : S → V) :
    (∑ s, f s) = f s0 + ∑ t : PointedTail S s0, f t.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset S)) (p := fun s : S => s = s0) f).symm
  calc
    (∑ s, f s) =
        (∑ s ∈ (Finset.univ : Finset S) with s = s0, f s) +
          ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
            simpa using hpart
    _ = f s0 + ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
          congr 1
          rw [Finset.sum_eq_single s0]
          · intro s hs hne
            exact (hne (Finset.mem_filter.mp hs).2).elim
          · simp
    _ = f s0 + ∑ t : PointedTail S s0, f t.1 := by
          congr 1
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset S)) (p := fun s : S => s ≠ s0)
              (f := f)).symm

@[simp] private theorem vecSum_zero_local
    {n k : Nat} [NeZero n] :
    vecSum (zeroVec : Vec n k) = 0 := by
  unfold vecSum zeroVec
  simp

private noncomputable def leftReassocEquiv
    {n d : Nat} [NeZero n] :
    ((PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d)) ×
      CyclicCube n) ≃ₗ[F]
      (DiamondEOOELeftAmbient n ×
        DiamondEvenAxisValueTailZero n d (CyclicCube n)) where
  toFun x := (((x.1.1.1, x.1.1.2), x.2), x.1.2)
  invFun x := ((x.1.1, x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def rightShearReassocEquiv
    {n d : Nat} [NeZero n] :
    PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ≃ₗ[F]
      (DiamondEOOERightAmbient n ×
        DiamondEvenAxisValueTailZero n d (CyclicCube n)) where
  toFun x := ((x.1.2, x.1.1 + x.1.2), x.2)
  invFun x := ((x.1.1 + x.1.2, x.1.1), x.2)
  left_inv x := by
    rcases x with ⟨⟨A0, D⟩, v⟩
    simp only
    apply Prod.ext
    · apply Prod.ext
      · calc
          D + (A0 + D) = A0 + (D + D) := by abel
          _ = A0 := by
            rw [show D + D = 0 from
              (add_eq_zero_iff_eq_of_F_module D D).2 rfl, add_zero]
      · rfl
    · rfl
  right_inv x := by
    rcases x with ⟨⟨D, A1⟩, v⟩
    simp only
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · calc
          D + A1 + D = (D + D) + A1 := by abel
          _ = A1 := by
            rw [show D + D = 0 from
              (add_eq_zero_iff_eq_of_F_module D D).2 rfl, zero_add]
    · rfl
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change
          (x.1.1 + y.1.1) + (x.1.2 + y.1.2) =
            (x.1.1 + x.1.2) + (y.1.1 + y.1.2)
        funext i j k
        simp only [Pi.add_apply]
        abel
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · simp [smul_add]
    · rfl

private noncomputable def leftAmbientCoordinateEquiv
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    (BFun4 n 1 1 d × WFun4 n 1 1 1) ≃ₗ[F]
      (DiamondEOOELeftAmbient n ×
        DiamondEvenAxisValueTailZero n d (CyclicCube n)) :=
  ((bWGaugedEquiv (n := n) (d := d) (by omega)).prodCongr
      (wRootEquiv (n := n))).trans
    (((diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
          (LinearEquiv.refl F (CyclicCube n))).trans
      (leftReassocEquiv (n := n) (d := d)))

private noncomputable def rightAmbientCoordinateEquiv
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    AFun4 n 1 1 d ≃ₗ[F]
      (DiamondEOOERightAmbient n ×
        DiamondEvenAxisValueTailZero n d (CyclicCube n)) :=
  (aWGaugedEquiv (n := n) (d := d) (by omega)).trans
    ((diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2).trans
        (rightShearReassocEquiv (n := n) (d := d)))

@[simp] private theorem cubeKShiftEquiv_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeKShiftEquiv u X i j k = X i j (k - u) := rfl

@[simp] private theorem cubeKShiftEquiv_symm_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    (cubeKShiftEquiv u).symm X i j k = X i j (k + u) := rfl

private theorem cubeKShift_cubeDiffP
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeKShiftEquiv u (cubeDiffP X) =
      cubeDiffP (cubeKShiftEquiv u X) := by
  funext i j k
  simp only [cubeKShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffP_apply,
    EEOEInternal.cubeDiffP_apply]
  rfl

private theorem cubeKShift_cubeDiffI
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeKShiftEquiv u (cubeDiffI X) =
      cubeDiffI (cubeKShiftEquiv u X) := by
  funext i j k
  rfl

private theorem cubeKShift_cubeDiffJInv
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeKShiftEquiv u (cubeDiffJInv X) =
      cubeDiffJInv (cubeKShiftEquiv u X) := by
  funext i j k
  simp only [cubeKShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffJInv_apply,
    EEOEInternal.cubeDiffJInv_apply]
  rfl

private theorem cubeKShift_pairing_same
    {n : Nat} [NeZero n] (u : I n) (X Y : CyclicCube n) :
    cubeDot (cubeKShiftEquiv u X) (cubeKShiftEquiv u Y) =
      cubeDot X Y := by
  classical
  unfold cubeDot
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.refl (I n)) (Equiv.addRight (-u)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, cubeKShiftEquiv, sub_eq_add_neg]

private noncomputable def eooeWUniformConstraintMap
    {n d : Nat} [NeZero n] :
    ((PVec n d → CyclicCube n) × CyclicCube n) →ₗ[F]
      (PVec n d → CyclicCube n) where
  toFun x wt := cubeDiffP (x.1 wt) + cubeDiffR x.2
  map_add' x y := by
    funext wt
    simp
    abel
  map_smul' r x := by
    funext wt
    simp

private theorem cast_even_eq_zero
    {m : Nat} (hm : Even m) :
    (m : F) = 0 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  exact F_add_self (q : F)

private theorem cast_odd_eq_one
    {m : Nat} (hm : Odd m) :
    (m : F) = 1 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem sum_const_even
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = 0 := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, cast_even_eq_zero heven, zero_smul]

private theorem sum_const_odd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, cast_odd_eq_one hodd, one_smul]

private theorem eooeWUniformConstraint_coords
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (f : PVec n d → CyclicCube n) (W : CyclicCube n) :
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    let x := E f
    let y := E (eooeWUniformConstraintMap (f, W))
    y.1.1 = cubeDiffP x.1.1 ∧
      y.1.2 = cubeDiffP x.1.2 + cubeDiffR W ∧
      ∀ t, y.2.1 t = cubeDiffP (x.2.1 t) := by
  dsimp only
  let heven := even_card_PVec hn hd2
  let hodd := odd_card_diamondEvenAxisTailIndex hn hd2
  refine ⟨?_, ?_, ?_⟩
  · change
      (∑ s : PVec n d, (cubeDiffP (f s) + cubeDiffR W)) =
        cubeDiffP (∑ s : PVec n d, f s)
    rw [Finset.sum_add_distrib, ← map_sum,
      sum_const_even heven, add_zero]
  · change
      (∑ t : DiamondEvenAxisTailIndex n d,
          (cubeDiffP (f t.1) + cubeDiffR W)) =
        cubeDiffP
            (∑ t : DiamondEvenAxisTailIndex n d, f t.1) +
          cubeDiffR W
    rw [Finset.sum_add_distrib, ← map_sum,
      sum_const_odd hodd]
  · intro t
    change
      (cubeDiffP (f t.1) + cubeDiffR W) +
          ∑ u : DiamondEvenAxisTailIndex n d,
            (cubeDiffP (f u.1) + cubeDiffR W) =
        cubeDiffP
          (f t.1 +
            ∑ u : DiamondEvenAxisTailIndex n d, f u.1)
    rw [Finset.sum_add_distrib, ← map_sum,
      sum_const_odd hodd, map_add]
    calc
      (cubeDiffP (f t.1) + cubeDiffR W) +
            (cubeDiffP (∑ u : DiamondEvenAxisTailIndex n d, f u.1) +
              cubeDiffR W) =
          cubeDiffP (f t.1) +
              cubeDiffP (∑ u : DiamondEvenAxisTailIndex n d, f u.1) +
            (cubeDiffR W + cubeDiffR W) := by abel
      _ = _ := by
        rw [show cubeDiffR W + cubeDiffR W = 0 from
          (add_eq_zero_iff_eq_of_F_module _ _).2 rfl, add_zero]

private theorem eooeWUniformConstraint_eq_zero_iff
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (f : PVec n d → CyclicCube n) (W : CyclicCube n) :
    let x :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2 f
    eooeWUniformConstraintMap (f, W) = 0 ↔
      diamondEOOELeftConstraintMap
          (((x.1.1, x.1.2), W) :
            DiamondEOOELeftAmbient n) = 0 ∧
        ∀ t, cubeDiffP (x.2.1 t) = 0 := by
  dsimp only
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let x := E f
  let y := E (eooeWUniformConstraintMap (f, W))
  have hcoords :=
    eooeWUniformConstraint_coords hn hd2 f W
  constructor
  · intro hzero
    have hy : y = 0 := by
      change E (eooeWUniformConstraintMap (f, W)) = 0
      rw [hzero]
      exact E.map_zero
    refine ⟨?_, ?_⟩
    · apply Prod.ext
      · change cubeDiffP x.1.1 = 0
        exact hcoords.1.symm.trans
          (congrArg (fun q => q.1.1) hy)
      · change cubeDiffP x.1.2 + cubeDiffR W = 0
        exact hcoords.2.1.symm.trans
          (congrArg (fun q => q.1.2) hy)
    · intro t
      exact (hcoords.2.2 t).symm.trans
        (congrArg (fun q => q.2.1 t) hy)
  · rintro ⟨hscalar, htail⟩
    apply E.injective
    have hEzero : E (0 : PVec n d → CyclicCube n) = 0 :=
      E.map_zero
    rw [hEzero]
    apply Prod.ext
    · apply Prod.ext
      · rw [hcoords.1]
        exact congrArg Prod.fst hscalar
      · rw [hcoords.2.1]
        exact congrArg Prod.snd hscalar
    · apply Subtype.ext
      funext t
      rw [hcoords.2.2 t, htail t]
      rfl

private theorem literal_left_mem_iff_uniform
    {n d : Nat} [NeZero n] (hd2 : 2 ≤ d)
    (x : BFun4 n 1 1 d × WFun4 n 1 1 1) :
    x ∈ DiamondEvenPLeft n 1 1 d ↔
      eooeWUniformConstraintMap
        (bWGaugedEquiv (by omega) x.1, wRootEquiv x.2) = 0 := by
  simp only [DiamondEvenPLeft, LinearMap.mem_ker]
  constructor
  · intro hx
    funext wt i j k
    simp only [eooeWUniformConstraintMap,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    change
      cubeDiffP
          (bWGaugedEquiv (by omega : 0 < d) x.1 wt) i j k +
        cubeDiffR (wRootEquiv x.2) i j k = 0
    rw [bWGaugedEquiv_eq, wRootEquiv_eq,
      ← cubeKShift_cubeDiffP, cubeKShiftEquiv_apply]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hx (zeroVec : PVec n 1))
            ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
              (i, zeroVec)))
          j)
        ((diamondVecHeadTailEquiv (by omega : 0 < d)).symm
          (k - vecSum wt, wt))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      x.1 x.2 zeroVec wt i j (k - vecSum wt)] at hpoint
    simp only [sum_pVec_one, vecSum_zero_local,
      add_zero, sub_zero, Pi.zero_apply] at hpoint
    simpa only [sub_add_cancel] using hpoint
  · intro h
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew := diamondVecHeadTailEquiv (n := n) (by omega : 0 < d)
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      x.1 x.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2]
    simp only [sum_pVec_one, vecSum_zero_local,
      add_zero, sub_zero, Pi.zero_apply]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun h (ew w).2)
            (ey y).1)
          sz)
        ((ew w).1 + vecSum (ew w).2)
    simp only [eooeWUniformConstraintMap,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hpoint
    change
      cubeDiffP
          (bWGaugedEquiv (by omega : 0 < d) x.1 (ew w).2)
            (ey y).1 sz ((ew w).1 + vecSum (ew w).2) +
        cubeDiffR (wRootEquiv x.2)
          (ey y).1 sz ((ew w).1 + vecSum (ew w).2) = 0 at hpoint
    rw [bWGaugedEquiv_eq, wRootEquiv_eq,
      ← cubeKShift_cubeDiffP, cubeKShiftEquiv_apply] at hpoint
    have hpoint' :
        cubeDiffP
            (diamondBRootCubeEquiv
              Nat.zero_lt_one (by omega : 0 < d) x.1
              zeroVec (ew w).2)
            (ey y).1 sz (ew w).1 +
          cubeDiffR
            (diamondWRootCubeEquiv
              Nat.zero_lt_one Nat.zero_lt_one x.2 zeroVec zeroVec)
            (ey y).1 sz ((ew w).1 + vecSum (ew w).2) = 0 := by
      simpa only [add_sub_cancel_right] using hpoint
    exact hpoint'

private theorem leftAmbientCoordinate_mem_iff
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 1 d × WFun4 n 1 1 1) :
    x ∈ DiamondEvenPLeft n 1 1 d ↔
      (leftAmbientCoordinateEquiv hn hd2 x).1 ∈
          DiamondEOOELeftSource n ∧
        ∀ t,
          cubeDiffP ((leftAmbientCoordinateEquiv hn hd2 x).2.1 t) = 0 := by
  rw [literal_left_mem_iff_uniform hd2 x]
  let f := bWGaugedEquiv (by omega : 0 < d) x.1
  let W := wRootEquiv x.2
  let q :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 f
  have hiff :=
    eooeWUniformConstraint_eq_zero_iff hn hd2 f W
  change
    eooeWUniformConstraintMap (f, W) = 0 ↔
      (leftAmbientCoordinateEquiv hn hd2 x).1 ∈
          DiamondEOOELeftSource n ∧
        ∀ t,
          cubeDiffP ((leftAmbientCoordinateEquiv hn hd2 x).2.1 t) = 0
  simpa only [DiamondEOOELeftSource, LinearMap.mem_ker] using hiff

noncomputable abbrev EOOEWTailLeftBase
    (n : Nat) [NeZero n] :=
  LinearMap.ker (cubeDiffP (n := n))

noncomputable abbrev EOOEWTailRightBase
    (n : Nat) [NeZero n] :=
  (LinearMap.range (cubeDiffP (n := n))).comap
    (cubeDiffJInv (n := n))

private noncomputable def eooeWLeftTailPack
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d (CyclicCube n))
    (hu : ∀ t, cubeDiffP (u.1 t) = 0) :
    DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n) :=
  ⟨fun t => ⟨u.1 t, LinearMap.mem_ker.mpr (hu t)⟩, by
    apply LinearMap.mem_ker.mpr
    change
      (∑ t,
        (⟨u.1 t, LinearMap.mem_ker.mpr (hu t)⟩ :
          EOOEWTailLeftBase n)) = 0
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using pointedValueTailZero_sum u⟩

private noncomputable def eooeWLeftTailForget
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n) →ₗ[F]
      DiamondEvenAxisValueTailZero n d (CyclicCube n) where
  toFun u :=
    ⟨fun t => (u.1 t).1, by
      apply LinearMap.mem_ker.mpr
      have hu := pointedValueTailZero_sum u
      simpa only [Submodule.coe_sum] using congrArg Subtype.val hu⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

private theorem eooeWLeftTailForget_pack
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d (CyclicCube n))
    (hu : ∀ t, cubeDiffP (u.1 t) = 0) :
    eooeWLeftTailForget (eooeWLeftTailPack u hu) = u := by
  apply Subtype.ext
  rfl

private theorem eooeWLeftTailPack_forget
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n)) :
    eooeWLeftTailPack (eooeWLeftTailForget u)
        (fun t => LinearMap.mem_ker.mp (u.1 t).2) = u := by
  apply Subtype.ext
  funext t
  apply Subtype.ext
  rfl

noncomputable def diamondEvenPLeftEOOEEquiv
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    DiamondEvenPLeft n 1 1 d ≃ₗ[F]
      (DiamondEOOELeftSource n ×
        DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n)) where
  toFun l := by
    let q := leftAmbientCoordinateEquiv hn hd2 l.1
    have hq := (leftAmbientCoordinate_mem_iff hn hd2 l.1).mp l.2
    exact (⟨q.1, hq.1⟩, eooeWLeftTailPack q.2 hq.2)
  invFun q := by
    let raw :
        DiamondEOOELeftAmbient n ×
          DiamondEvenAxisValueTailZero n d (CyclicCube n) :=
      (q.1.1, eooeWLeftTailForget q.2)
    let l := (leftAmbientCoordinateEquiv hn hd2).symm raw
    refine ⟨l, (leftAmbientCoordinate_mem_iff hn hd2 l).mpr ?_⟩
    have hread : leftAmbientCoordinateEquiv hn hd2 l = raw :=
      (leftAmbientCoordinateEquiv hn hd2).apply_symm_apply raw
    refine ⟨?_, ?_⟩
    · have hfst := congrArg Prod.fst hread
      rw [hfst]
      exact q.1.2
    · intro t
      have ht := LinearMap.mem_ker.mp (q.2.1 t).2
      have htail := congrArg (fun z => z.2.1 t) hread
      calc
        cubeDiffP
            ((leftAmbientCoordinateEquiv hn hd2 l).2.1 t) =
          cubeDiffP (raw.2.1 t) :=
            congrArg cubeDiffP htail
        _ = 0 := ht
  left_inv l := by
    apply Subtype.ext
    exact
      (leftAmbientCoordinateEquiv hn hd2).symm_apply_apply l.1
  right_inv q := by
    have hread :=
      (leftAmbientCoordinateEquiv hn hd2).apply_symm_apply
        (q.1.1, eooeWLeftTailForget q.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun z => z.2.1 t) hread
  map_add' l l' := by
    have hmap :=
      (leftAmbientCoordinateEquiv hn hd2).map_add l.1 l'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) hmap
  map_smul' r l := by
    have hmap :=
      (leftAmbientCoordinateEquiv hn hd2).map_smul r l.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) hmap

private theorem literal_reachable_mem_iff_uniform_range
    {n d : Nat} [NeZero n] (hd2 : 2 ≤ d)
    (A : AFun4 n 1 1 d) :
    A ∈ DiamondEvenPReachableA n 1 1 d ↔
      (fun wt => cubeDiffJInv
          (aWGaugedEquiv (by omega : 0 < d) A wt)) ∈
        LinearMap.range
          (eooeWUniformConstraintMap (n := n) (d := d)) := by
  change
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := 1) (c := 1) (d := d) A ∈
        LinearMap.range
          (squareCompat
            (n := n) (a := 1) (b := 1) (c := 1) (d := d)) ↔ _
  constructor
  · rintro ⟨bw, hbw⟩
    refine
      ⟨(bWGaugedEquiv (by omega : 0 < d) bw.1,
          wRootEquiv bw.2), ?_⟩
    funext wt i j k
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hbw (zeroVec : PVec n 1))
            ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
              (i, zeroVec)))
          j)
        ((diamondVecHeadTailEquiv (by omega : 0 < d)).symm
          (k - vecSum wt, wt))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      bw.1 bw.2 zeroVec wt i j (k - vecSum wt)] at hpoint
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      A zeroVec wt i j (k - vecSum wt)] at hpoint
    simp only [sum_pVec_one, vecSum_zero_local,
      add_zero, sub_zero] at hpoint
    change
      cubeDiffP
          (bWGaugedEquiv (by omega : 0 < d) bw.1 wt) i j k +
        cubeDiffR (wRootEquiv bw.2) i j k =
      cubeDiffJInv
          (aWGaugedEquiv (by omega : 0 < d) A wt) i j k
    rw [bWGaugedEquiv_eq, wRootEquiv_eq, aWGaugedEquiv_eq,
      ← cubeKShift_cubeDiffP, ← cubeKShift_cubeDiffJInv,
      cubeKShiftEquiv_apply, cubeKShiftEquiv_apply]
    simpa only [sub_add_cancel] using hpoint
  · rintro ⟨fw, hfw⟩
    let B :=
      (bWGaugedEquiv (n := n) (d := d) (by omega : 0 < d)).symm fw.1
    let W := (wRootEquiv (n := n)).symm fw.2
    refine ⟨(B, W), ?_⟩
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew := diamondVecHeadTailEquiv (n := n) (by omega : 0 < d)
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      B W (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      A (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2]
    simp only [sum_pVec_one, vecSum_zero_local, add_zero, sub_zero]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hfw (ew w).2)
            (ey y).1)
          sz)
        ((ew w).1 + vecSum (ew w).2)
    have hB :
        bWGaugedEquiv (by omega : 0 < d) B = fw.1 :=
      (bWGaugedEquiv (by omega : 0 < d)).apply_symm_apply fw.1
    have hW : wRootEquiv W = fw.2 :=
      wRootEquiv.apply_symm_apply fw.2
    change
      cubeDiffP (fw.1 (ew w).2)
            (ey y).1 sz ((ew w).1 + vecSum (ew w).2) +
        cubeDiffR fw.2
            (ey y).1 sz ((ew w).1 + vecSum (ew w).2) =
      cubeDiffJInv
          (aWGaugedEquiv (by omega : 0 < d) A (ew w).2)
            (ey y).1 sz ((ew w).1 + vecSum (ew w).2) at hpoint
    rw [← hB, ← hW] at hpoint
    rw [bWGaugedEquiv_eq, wRootEquiv_eq, aWGaugedEquiv_eq,
      ← cubeKShift_cubeDiffP, ← cubeKShift_cubeDiffJInv,
      cubeKShiftEquiv_apply, cubeKShiftEquiv_apply] at hpoint
    simpa only [add_sub_cancel_right] using hpoint

private theorem src_JInv_coords_from_dual
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (A : PVec n d → CyclicCube n) :
    let D :=
      diamondEvenAxisDualCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2 A
    let S :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
          (fun wt => cubeDiffJInv (A wt))
    S.1.1 = cubeDiffJInv D.1.2 ∧
      S.1.2 = cubeDiffJInv (D.1.1 + D.1.2) ∧
      ∀ t, S.2.1 t = cubeDiffJInv (D.2.1 t) := by
  dsimp only
  let hodd := odd_card_diamondEvenAxisTailIndex hn hd2
  let tailSum :=
    ∑ t : DiamondEvenAxisTailIndex n d, A t.1
  let D :=
    ∑ t : DiamondEvenAxisTailIndex n d,
      (A t.1 + A (zeroVec : PVec n d))
  have hD : D = tailSum + A zeroVec := by
    dsimp only [D, tailSum]
    rw [Finset.sum_add_distrib, sum_const_odd hodd]
  refine ⟨?_, ?_, ?_⟩
  · change
      (∑ s : PVec n d, cubeDiffJInv (A s)) =
        cubeDiffJInv D
    rw [← map_sum]
    rw [sum_eq_at_point_add_tail (zeroVec : PVec n d) A, hD]
    congr 1
    abel
  · change
      (∑ t : DiamondEvenAxisTailIndex n d,
          cubeDiffJInv (A t.1)) =
        cubeDiffJInv (A zeroVec + D)
    rw [← map_sum, hD]
    congr 1
    calc
      tailSum =
          tailSum + (A zeroVec + A zeroVec) := by
            rw [show A zeroVec + A zeroVec = 0 from
              (add_eq_zero_iff_eq_of_F_module _ _).2 rfl, add_zero]
      _ = A zeroVec + (tailSum + A zeroVec) := by abel
  · intro t
    change
      cubeDiffJInv (A t.1) +
          ∑ u : DiamondEvenAxisTailIndex n d,
            cubeDiffJInv (A u.1) =
        cubeDiffJInv
          (A t.1 + A zeroVec + D)
    rw [← map_sum, ← map_add, hD]
    congr 1
    calc
      A t.1 + tailSum =
          A t.1 + tailSum + (A zeroVec + A zeroVec) := by
            rw [show A zeroVec + A zeroVec = 0 from
              (add_eq_zero_iff_eq_of_F_module _ _).2 rfl, add_zero]
      _ = A t.1 + A zeroVec + (tailSum + A zeroVec) := by abel

private theorem uniform_range_iff_coords
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (g : PVec n d → CyclicCube n) :
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    let x := E g
    g ∈ LinearMap.range
        (eooeWUniformConstraintMap (n := n) (d := d)) ↔
      x.1.1 ∈ LinearMap.range (cubeDiffP (n := n)) ∧
      x.1.2 ∈ LinearMap.range
        (LinearMap.coprod
          (cubeDiffP (n := n)) (cubeDiffR (n := n))) ∧
      ∀ t, x.2.1 t ∈ LinearMap.range (cubeDiffP (n := n)) := by
  classical
  dsimp only
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let x := E g
  constructor
  · rintro ⟨fw, rfl⟩
    let y := E fw.1
    have hc := eooeWUniformConstraint_coords hn hd2 fw.1 fw.2
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨y.1.1, hc.1.symm⟩
    · refine ⟨(y.1.2, fw.2), ?_⟩
      change cubeDiffP y.1.2 + cubeDiffR fw.2 = _
      exact hc.2.1.symm
    · intro t
      exact ⟨y.2.1 t, (hc.2.2 t).symm⟩
  · rintro ⟨⟨b0, hb0⟩, ⟨⟨b1, W⟩, hb1⟩, htail⟩
    choose bt hbt using htail
    let corr : CyclicCube n := ∑ t, bt t
    have hPcorr : cubeDiffP corr = 0 := by
      calc
        cubeDiffP corr =
            ∑ t : DiamondEvenAxisTailIndex n d, cubeDiffP (bt t) := by
              rw [map_sum]
        _ = ∑ t : DiamondEvenAxisTailIndex n d, x.2.1 t := by
              apply Finset.sum_congr rfl
              intro t _
              exact hbt t
        _ = 0 := pointedValueTailZero_sum x.2
    rcases diamondEvenAxisTailIndex_nonempty hn hd2 with ⟨t0⟩
    let tailFun : DiamondEvenAxisTailIndex n d → CyclicCube n :=
      fun t => if t = t0 then bt t + corr else bt t
    have htailSum : (∑ t, tailFun t) = 0 := by
      have hdelta :
          (∑ t : DiamondEvenAxisTailIndex n d,
            if t = t0 then corr else 0) = corr := by
        rw [Finset.sum_eq_single t0]
        · simp
        · intro t _ ht
          simp [ht]
        · simp
      have hpoint :
          tailFun =
            fun t => bt t + if t = t0 then corr else 0 := by
        funext t
        by_cases ht : t = t0 <;> simp [tailFun, ht]
      rw [hpoint, Finset.sum_add_distrib, hdelta]
      change corr + corr = 0
      exact (add_eq_zero_iff_eq_of_F_module _ _).2 rfl
    let tail :
        DiamondEvenAxisValueTailZero n d (CyclicCube n) :=
      ⟨tailFun, LinearMap.mem_ker.mpr htailSum⟩
    have hPtail (t : DiamondEvenAxisTailIndex n d) :
        cubeDiffP (tail.1 t) = x.2.1 t := by
      by_cases ht : t = t0
      · subst t
        simp only [tail, tailFun, if_pos]
        rw [map_add, hPcorr, add_zero]
        exact hbt t0
      · simp only [tail, tailFun, ht]
        exact hbt t
    let coords :
        PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d) :=
      ((b0, b1), tail)
    let f := E.symm coords
    refine ⟨(f, W), ?_⟩
    apply E.injective
    have hf : E f = coords := E.apply_symm_apply coords
    have hc := eooeWUniformConstraint_coords hn hd2 f W
    apply Prod.ext
    · apply Prod.ext
      · rw [hc.1]
        have hf0 := congrArg (fun z => z.1.1) hf
        calc
          cubeDiffP (E f).1.1 =
              cubeDiffP coords.1.1 := congrArg cubeDiffP hf0
          _ = x.1.1 := hb0
      · rw [hc.2.1]
        have hf1 := congrArg (fun z => z.1.2) hf
        calc
          cubeDiffP (E f).1.2 + cubeDiffR W =
              cubeDiffP coords.1.2 + cubeDiffR W :=
                congrArg
                  (fun z => cubeDiffP z + cubeDiffR W) hf1
          _ = x.1.2 := hb1
    · apply Subtype.ext
      funext t
      rw [hc.2.2 t]
      have hft := congrArg (fun z => z.2.1 t) hf
      calc
        cubeDiffP ((E f).2.1 t) =
            cubeDiffP (coords.2.1 t) :=
              congrArg cubeDiffP hft
        _ = x.2.1 t := hPtail t

private theorem rightAmbientCoordinate_mem_iff
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (A : AFun4 n 1 1 d) :
    A ∈ DiamondEvenPReachableA n 1 1 d ↔
      (rightAmbientCoordinateEquiv hn hd2 A).1 ∈
          DiamondEOOERightSource n ∧
        ∀ t,
          (rightAmbientCoordinateEquiv hn hd2 A).2.1 t ∈
            EOOEWTailRightBase n := by
  rw [literal_reachable_mem_iff_uniform_range hd2 A]
  let a := aWGaugedEquiv (by omega : 0 < d) A
  let g := fun wt => cubeDiffJInv (a wt)
  let S :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 g
  let D :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 a
  have hrange := uniform_range_iff_coords hn hd2 g
  have hJ := src_JInv_coords_from_dual hn hd2 a
  have hcoord :
      rightAmbientCoordinateEquiv hn hd2 A =
        ((D.1.2, D.1.1 + D.1.2), D.2) := rfl
  rw [hcoord]
  constructor
  · intro hg
    have hc := hrange.mp hg
    refine ⟨?_, ?_⟩
    · change
        cubeDiffJInv D.1.2 ∈
            LinearMap.range (cubeDiffP (n := n)) ∧
          cubeDiffJInv (D.1.1 + D.1.2) ∈
            LinearMap.range
              (LinearMap.coprod
                (cubeDiffP (n := n)) (cubeDiffR (n := n)))
      exact ⟨hJ.1 ▸ hc.1, hJ.2.1 ▸ hc.2.1⟩
    · intro t
      change cubeDiffJInv (D.2.1 t) ∈
        LinearMap.range (cubeDiffP (n := n))
      exact hJ.2.2 t ▸ hc.2.2 t
  · rintro ⟨hs, ht⟩
    have h0 :
        cubeDiffJInv D.1.2 ∈
          LinearMap.range (cubeDiffP (n := n)) := by
      exact hs.1
    have h1 :
        cubeDiffJInv (D.1.1 + D.1.2) ∈
          LinearMap.range
            (LinearMap.coprod
              (cubeDiffP (n := n)) (cubeDiffR (n := n))) := by
      exact hs.2
    apply hrange.mpr
    refine ⟨?_, ?_, ?_⟩
    · exact hJ.1.symm ▸ h0
    · exact hJ.2.1.symm ▸ h1
    · intro t
      have htt :
          cubeDiffJInv (D.2.1 t) ∈
            LinearMap.range (cubeDiffP (n := n)) := by
        exact ht t
      exact (hJ.2.2 t).symm ▸ htt

private noncomputable def eooeWRightTailPack
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d (CyclicCube n))
    (hu : ∀ t, u.1 t ∈ EOOEWTailRightBase n) :
    DiamondEvenAxisValueTailZero n d (EOOEWTailRightBase n) :=
  ⟨fun t => ⟨u.1 t, hu t⟩, by
    apply LinearMap.mem_ker.mpr
    change
      (∑ t,
        (⟨u.1 t, hu t⟩ :
          EOOEWTailRightBase n)) = 0
    apply Subtype.ext
    simpa only [Submodule.coe_sum] using pointedValueTailZero_sum u⟩

private noncomputable def eooeWRightTailForget
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d (EOOEWTailRightBase n) →ₗ[F]
      DiamondEvenAxisValueTailZero n d (CyclicCube n) where
  toFun u :=
    ⟨fun t => (u.1 t).1, by
      apply LinearMap.mem_ker.mpr
      have hu := pointedValueTailZero_sum u
      simpa only [Submodule.coe_sum] using congrArg Subtype.val hu⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

noncomputable def diamondEvenPReachableAEOOEEquiv
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    DiamondEvenPReachableA n 1 1 d ≃ₗ[F]
      (DiamondEOOERightSource n ×
        DiamondEvenAxisValueTailZero n d (EOOEWTailRightBase n)) where
  toFun A := by
    let q := rightAmbientCoordinateEquiv hn hd2 A.1
    have hq := (rightAmbientCoordinate_mem_iff hn hd2 A.1).mp A.2
    exact (⟨q.1, hq.1⟩, eooeWRightTailPack q.2 hq.2)
  invFun q := by
    let raw :
        DiamondEOOERightAmbient n ×
          DiamondEvenAxisValueTailZero n d (CyclicCube n) :=
      (q.1.1, eooeWRightTailForget q.2)
    let A := (rightAmbientCoordinateEquiv hn hd2).symm raw
    refine ⟨A, (rightAmbientCoordinate_mem_iff hn hd2 A).mpr ?_⟩
    have hread : rightAmbientCoordinateEquiv hn hd2 A = raw :=
      (rightAmbientCoordinateEquiv hn hd2).apply_symm_apply raw
    refine ⟨?_, ?_⟩
    · have hfst := congrArg Prod.fst hread
      rw [hfst]
      exact q.1.2
    · intro t
      have ht := (q.2.1 t).2
      have htail := congrArg (fun z => z.2.1 t) hread
      change
        cubeDiffJInv
            ((rightAmbientCoordinateEquiv hn hd2 A).2.1 t) ∈
          LinearMap.range (cubeDiffP (n := n))
      change cubeDiffJInv (raw.2.1 t) ∈
        LinearMap.range (cubeDiffP (n := n)) at ht
      have htailJ :=
        congrArg (cubeDiffJInv (n := n)) htail
      rw [htailJ]
      exact ht
  left_inv A := by
    apply Subtype.ext
    exact
      (rightAmbientCoordinateEquiv hn hd2).symm_apply_apply A.1
  right_inv q := by
    have hread :=
      (rightAmbientCoordinateEquiv hn hd2).apply_symm_apply
        (q.1.1, eooeWRightTailForget q.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun z => z.2.1 t) hread
  map_add' A A' := by
    have hmap :=
      (rightAmbientCoordinateEquiv hn hd2).map_add A.1 A'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) hmap
  map_smul' r A := by
    have hmap :=
      (rightAmbientCoordinateEquiv hn hd2).map_smul r A.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg (fun q => q.2.1 t) hmap

private theorem cubeDiffI_eq_cubeDiffJStar_of_p_zero
    {n : Nat} [NeZero n]
    (u : CyclicCube n)
    (hu : cubeDiffP u = 0) :
    cubeDiffI u = cubeDiffJStar u := by
  funext i j k
  rw [EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffJStar_apply]
  apply congrArg (u i j k + ·)
  have h := congrFun (congrFun (congrFun hu i) (j + 1)) k
  simp only [Pi.zero_apply] at h
  rw [EEOEInternal.cubeDiffP_apply] at h
  simp only [add_sub_cancel_right] at h
  exact ((add_eq_zero_iff_eq_of_F_module _ _).mp h).symm

private theorem cubeDiffPStar_eq_zero_of_p_zero
    {n : Nat} [NeZero n]
    (u : CyclicCube n)
    (hu : cubeDiffP u = 0) :
    cubeDiffPStar u = 0 := by
  funext i j k
  simp only [Pi.zero_apply]
  rw [EEOEInternal.cubeDiffPStar_apply]
  have h :=
    congrFun
      (congrFun
        (congrFun hu (i - 1)) (j + 1)) k
  simp only [Pi.zero_apply] at h
  rw [EEOEInternal.cubeDiffP_apply] at h
  rw [add_comm]
  simpa only [sub_add_cancel, add_sub_cancel_right] using h

private theorem eooeWTailBase_phase_zero
    {n : Nat} [NeZero n]
    (u : EOOEWTailLeftBase n)
    (v : EOOEWTailRightBase n) :
    cubeDot (cubeDiffI u.1) v.1 = 0 := by
  have hu : cubeDiffP u.1 = 0 :=
    LinearMap.mem_ker.mp u.2
  rcases v.2 with ⟨x, hx⟩
  rw [cubeDiffI_eq_cubeDiffJStar_of_p_zero u.1 hu,
    cubeDiffJ_pairing_adjoint, ← hx,
    ← cubeDiffP_pairing_adjoint,
    cubeDiffPStar_eq_zero_of_p_zero u.1 hu]
  simp [cubeDot]

private theorem eooeWTail_phase_zero
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n))
    (v : DiamondEvenAxisValueTailZero n d (EOOEWTailRightBase n)) :
    (∑ t, cubeDot (cubeDiffI (u.1 t).1) (v.1 t).1) = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  exact eooeWTailBase_phase_zero (u.1 t) (v.1 t)

private theorem cubeDot_comm_local
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot x y = cubeDot y x := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem cubeKShift_leftRoot_W
    {n d : Nat} [NeZero n]
    (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 1 d)
    (wt : PVec n d) :
    cubeKShiftEquiv (vecSum wt)
        (diamondARootCubeEquiv
          Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
          (diamondEvenPLeftRoot l) zeroVec zeroVec wt) =
      cubeDiffI
          (bWGaugedEquiv (by omega : 0 < d) l.1.1 wt) +
        cubeDiffK (wRootEquiv l.1.2) := by
  funext i j k
  simp only [cubeKShiftEquiv_apply, Pi.add_apply]
  change
    diamondEvenPLeftRoot l
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm (i, zeroVec))
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm (j, zeroVec))
        ((diamondVecHeadTailEquiv (by omega : 0 < d)).symm
          (k - vecSum wt, wt)) =
      _
  rw [diamondCubeReindex_leftRoot
    Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
    l zeroVec zeroVec wt i j (k - vecSum wt)]
  simp only [vecSum_zero_local, add_zero]
  rw [bWGaugedEquiv_eq, wRootEquiv_eq,
    ← cubeKShift_cubeDiffI, cubeKShiftEquiv_apply]
  simp only [sub_add_cancel]

private theorem literal_phase_gauged
    {n d : Nat} [NeZero n]
    (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 1 d)
    (A : DiamondEvenPReachableA n 1 1 d) :
    diamondEvenPCross l A =
      ∑ wt : PVec n d,
        cubeDot
          (cubeDiffI
              (bWGaugedEquiv (by omega : 0 < d) l.1.1 wt) +
            cubeDiffK (wRootEquiv l.1.2))
          (aWGaugedEquiv (by omega : 0 < d) A.1 wt) := by
  change coeffApplyA (diamondEvenPLeftRoot l) A.1 = _
  rw [diamondCubeReindex_rootPairing
    Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)]
  simp only [sum_pVec_one]
  apply Finset.sum_congr rfl
  intro wt _
  let u := vecSum wt
  let AR :=
    diamondARootCubeEquiv
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      A.1 zeroVec zeroVec wt
  let LR :=
    diamondARootCubeEquiv
      Nat.zero_lt_one Nat.zero_lt_one (by omega : 0 < d)
      (diamondEvenPLeftRoot l) zeroVec zeroVec wt
  calc
    cubeDot AR LR =
        cubeDot (cubeKShiftEquiv u AR)
          (cubeKShiftEquiv u LR) :=
      (cubeKShift_pairing_same u AR LR).symm
    _ = cubeDot
          (aWGaugedEquiv (by omega : 0 < d) A.1 wt)
          (cubeDiffI
              (bWGaugedEquiv (by omega : 0 < d) l.1.1 wt) +
            cubeDiffK (wRootEquiv l.1.2)) := by
      rw [show cubeKShiftEquiv u AR =
          aWGaugedEquiv (by omega : 0 < d) A.1 wt from rfl]
      rw [show cubeKShiftEquiv u LR =
          cubeDiffI
              (bWGaugedEquiv (by omega : 0 < d) l.1.1 wt) +
            cubeDiffK (wRootEquiv l.1.2) from
        cubeKShift_leftRoot_W hd2 l wt]
    _ = _ := cubeDot_comm_local _ _

private theorem pointedDualEvenValue_D_eq_total_sum
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (g : PVec n d → CyclicCube n) :
    (diamondEvenAxisDualCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2 g).1.2 =
      ∑ s : PVec n d, g s := by
  change
    (pointedDualEvenValueEquiv
      (PVec n d) (CyclicCube n) (zeroVec : PVec n d)
      (even_card_PVec hn hd2) g).1.2 =
        ∑ s : PVec n d, g s
  rw [pointedDualEvenValueEquiv_apply_sum,
    Finset.sum_add_distrib,
    sum_const_odd
      (odd_card_diamondEvenAxisTailIndex hn hd2)
      (g (zeroVec : PVec n d)),
    sum_eq_at_point_add_tail (zeroVec : PVec n d) g]
  abel

private theorem total_pairing_in_pointed_coordinates
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (f g : PVec n d → CyclicCube n)
    (W : CyclicCube n) :
    let x :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2 f
    let y :=
      diamondEvenAxisDualCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2 g
    (∑ s : PVec n d,
        cubeDot (cubeDiffI (f s) + cubeDiffK W) (g s)) =
      cubeDot
          (cubeDiffI (x.1.1 + x.1.2) + cubeDiffK W)
          y.1.2 +
        cubeDot (cubeDiffI x.1.1) (y.1.1 + y.1.2) +
        ∑ t, cubeDot (cubeDiffI (x.2.1 t)) (y.2.1 t) := by
  dsimp only
  let beta : CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
    EEOEInternal.cubeDotDual.comp cubeDiffI
  have hpair :=
    pointedEvenValue_pairing
      (zeroVec : PVec n d)
      (even_card_PVec hn hd2)
      beta f g
  change
    (∑ s : PVec n d, cubeDot (cubeDiffI (f s)) (g s)) =
      cubeDot
          (cubeDiffI
            ((diamondEvenAxisSrcCoordEquiv
              (CyclicCube n) hn hd2 f).1.1))
          ((diamondEvenAxisDualCoordEquiv
            (CyclicCube n) hn hd2 g).1.1) +
        cubeDot
          (cubeDiffI
            ((diamondEvenAxisSrcCoordEquiv
              (CyclicCube n) hn hd2 f).1.2))
          ((diamondEvenAxisDualCoordEquiv
            (CyclicCube n) hn hd2 g).1.2) +
        ∑ t,
          cubeDot
            (cubeDiffI
              ((diamondEvenAxisSrcCoordEquiv
                (CyclicCube n) hn hd2 f).2.1 t))
            ((diamondEvenAxisDualCoordEquiv
              (CyclicCube n) hn hd2 g).2.1 t) at hpair
  have hconst :
      (∑ s : PVec n d, cubeDot (cubeDiffK W) (g s)) =
        cubeDot (cubeDiffK W) (∑ s : PVec n d, g s) := by
    change
      (∑ s : PVec n d,
          EEOEInternal.cubeDotDual (cubeDiffK W) (g s)) =
        EEOEInternal.cubeDotDual (cubeDiffK W)
          (∑ s : PVec n d, g s)
    rw [map_sum]
  simp_rw [EEOEInternal.cubeDot_add_left]
  rw [Finset.sum_add_distrib, hpair, hconst,
    ← pointedDualEvenValue_D_eq_total_sum hn hd2 g]
  simp only [map_add, EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

private theorem diamondEvenPCross_EOOE_phase_split
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 1 d)
    (A : DiamondEvenPReachableA n 1 1 d) :
    diamondEvenPCross l A =
      diamondEOOECross
          (diamondEvenPLeftEOOEEquiv hn hd2 l).1
          (diamondEvenPReachableAEOOEEquiv hn hd2 A).1 +
        ∑ t,
          cubeDot
            (cubeDiffI
              ((diamondEvenPLeftEOOEEquiv hn hd2 l).2.1 t).1)
            ((diamondEvenPReachableAEOOEEquiv hn hd2 A).2.1 t).1 := by
  rw [literal_phase_gauged hd2 l A,
    total_pairing_in_pointed_coordinates hn hd2]
  rfl

private noncomputable def eooeWTailBaseCross
    {n : Nat} [NeZero n] :
    EOOEWTailLeftBase n →ₗ[F]
      Module.Dual F (EOOEWTailRightBase n) :=
  (BWSymmetryInternal.restrictDual
      (EOOEWTailRightBase n)).comp
    ((EEOEInternal.cubeDotDual.comp cubeDiffI).comp
      (EOOEWTailLeftBase n).subtype)

noncomputable def eooeWTailCross
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n d (EOOEWTailRightBase n)) :=
  diamondTailAmplify (eooeWTailBaseCross (n := n))

theorem eooeWTailCross_eq_zero
    {n d : Nat} [NeZero n] :
    eooeWTailCross (n := n) (d := d) = 0 := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  change
    (∑ t, cubeDot (cubeDiffI (u.1 t).1) (v.1 t).1) = 0
  exact eooeWTail_phase_zero u v

-- Typeclass synthesis unfolds the nested restricted tail dual.
set_option synthInstance.maxHeartbeats 200000 in
-- The nested restricted tail dual needs more than the project default.
noncomputable def diamondEOOETotalBlockCross
    {n d : Nat} [NeZero n] :
    (DiamondEOOELeftSource n ×
        DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n)) →ₗ[F]
      Module.Dual F
        (DiamondEOOERightSource n ×
          DiamondEvenAxisValueTailZero n d (EOOEWTailRightBase n)) :=
  diamondCrossProd
    (diamondEOOECross (n := n))
    (eooeWTailCross (n := n) (d := d))

theorem diamondEvenPCross_EOOE_phase
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 1 d)
    (A : DiamondEvenPReachableA n 1 1 d) :
    diamondEOOETotalBlockCross
        (diamondEvenPLeftEOOEEquiv hn hd2 l)
        (diamondEvenPReachableAEOOEEquiv hn hd2 A) =
      diamondEvenPCross l A := by
  unfold diamondEOOETotalBlockCross
  change
    diamondEOOECross
          (diamondEvenPLeftEOOEEquiv hn hd2 l).1
          (diamondEvenPReachableAEOOEEquiv hn hd2 A).1 +
        (∑ t,
          cubeDot
            (cubeDiffI
              ((diamondEvenPLeftEOOEEquiv hn hd2 l).2.1 t).1)
            ((diamondEvenPReachableAEOOEEquiv hn hd2 A).2.1 t).1) =
      diamondEvenPCross l A
  exact (diamondEvenPCross_EOOE_phase_split hn hd2 l A).symm

-- The transport equivalence synthesizes both nested restricted source modules.
set_option synthInstance.maxHeartbeats 200000 in
-- The nested restricted source modules need a larger synthesis budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the full transport bridge needs more than the project default.
noncomputable def diamondEvenPCross_EOOE_rangeEquiv
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := 1) (c := 1) (d := d)) ≃ₗ[F]
      LinearMap.range
        (diamondEOOETotalBlockCross (n := n) (d := d)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (L := DiamondEvenPLeft n 1 1 d)
    (R := DiamondEvenPReachableA n 1 1 d)
    (L' :=
      DiamondEOOELeftSource n ×
        DiamondEvenAxisValueTailZero n d (EOOEWTailLeftBase n))
    (R' :=
      DiamondEOOERightSource n ×
        DiamondEvenAxisValueTailZero n d (EOOEWTailRightBase n))
    (diamondEvenPCross
      (n := n) (b := 1) (c := 1) (d := d))
    (diamondEOOETotalBlockCross (n := n) (d := d))
    (diamondEvenPLeftEOOEEquiv hn hd2)
    (diamondEvenPReachableAEOOEEquiv hn hd2)
    (diamondEvenPCross_EOOE_phase hn hd2)

-- The final range calculation elaborates the transported product cross.
set_option synthInstance.maxHeartbeats 200000 in
-- The restricted product range needs a larger synthesis budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the transported product calculation needs additional heartbeats.
theorem rank_diamondEvenPCross_EOOE
    {n d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hd2 : 2 ≤ d) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := 1) (d := d))) =
      n * (n - 1) ^ 2 := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := 1) (d := d))) =
        Module.finrank F
          (LinearMap.range
            (diamondEOOETotalBlockCross
              (n := n) (d := d))) :=
      LinearEquiv.finrank_eq
        (diamondEvenPCross_EOOE_rangeEquiv hn hd2)
    _ =
        Module.finrank F
            (LinearMap.range (diamondEOOECross (n := n))) +
          Module.finrank F
            (LinearMap.range
              (eooeWTailCross (n := n) (d := d))) := by
      exact
        finrank_range_diamondCrossProd
          (diamondEOOECross (n := n))
          (eooeWTailCross (n := n) (d := d))
    _ = n * (n - 1) ^ 2 := by
      rw [rank_diamondEvenP_cross_EOOE_scalar hn2 hn]
      rw [eooeWTailCross_eq_zero]
      simp



end

end Core4loop.SquareDiagonal.EvenP
