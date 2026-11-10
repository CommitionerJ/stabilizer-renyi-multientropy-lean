import Core4loop.SquareDiagonal.EvenP.TotalEOOO
import Core4loop.SquareDiagonal.EvenP.TailPrototypeBlocks

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

noncomputable abbrev EOEOZTailLeftBase
    (n : Nat) [NeZero n] :=
  DiamondEOOOLeftAmbient n

noncomputable abbrev EOEOZTailRightBase
    (n : Nat) [NeZero n] :=
  CyclicCube n

private noncomputable def totalEOEOBRootZEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    BFun4 n 1 c 1 ≃ₗ[F] (PVec n c → CyclicCube n) where
  toFun B zt :=
    diamondBRootCubeEquiv hc Nat.zero_lt_one B zt zeroVec
  invFun f :=
    (diamondBRootCubeEquiv hc Nat.zero_lt_one).symm
      (fun zt _ => f zt)
  left_inv B := by
    apply (diamondBRootCubeEquiv hc Nat.zero_lt_one).injective
    funext zt wt
    rw [pVec_one_eq_zeroVec wt]
    exact
      (diamondBRootCubeEquiv
        (n := n) hc Nat.zero_lt_one).apply_symm_apply _ ▸ rfl
  right_inv f := by
    funext zt
    exact congrFun
      (congrFun
        ((diamondBRootCubeEquiv hc Nat.zero_lt_one).apply_symm_apply
          (fun zt _ => f zt)) zt)
      zeroVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEOWRootZEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    WFun4 n 1 1 c ≃ₗ[F] (PVec n c → CyclicCube n) where
  toFun W zt :=
    diamondWRootCubeEquiv Nat.zero_lt_one hc W zeroVec zt
  invFun f :=
    (diamondWRootCubeEquiv Nat.zero_lt_one hc).symm
      (fun _ zt => f zt)
  left_inv W := by
    apply (diamondWRootCubeEquiv Nat.zero_lt_one hc).injective
    funext yt zt
    rw [pVec_one_eq_zeroVec yt]
    exact
      (diamondWRootCubeEquiv
        (n := n) Nat.zero_lt_one hc).apply_symm_apply _ ▸ rfl
  right_inv f := by
    funext zt
    exact congrFun
      (congrFun
        ((diamondWRootCubeEquiv Nat.zero_lt_one hc).apply_symm_apply
          (fun _ zt => f zt)) zeroVec)
      zt
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEOARootZEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    AFun4 n 1 c 1 ≃ₗ[F] (PVec n c → CyclicCube n) where
  toFun A zt :=
    diamondARootCubeEquiv Nat.zero_lt_one hc Nat.zero_lt_one A
      zeroVec zt zeroVec
  invFun f :=
    (diamondARootCubeEquiv Nat.zero_lt_one hc Nat.zero_lt_one).symm
      (fun _ zt _ => f zt)
  left_inv A := by
    apply
      (diamondARootCubeEquiv
        Nat.zero_lt_one hc Nat.zero_lt_one).injective
    funext yt zt wt
    rw [pVec_one_eq_zeroVec yt, pVec_one_eq_zeroVec wt]
    exact
      (diamondARootCubeEquiv
        (n := n) Nat.zero_lt_one hc
          Nat.zero_lt_one).apply_symm_apply _ ▸ rfl
  right_inv f := by
    funext zt
    exact congrFun
      (congrFun
        (congrFun
          ((diamondARootCubeEquiv
            Nat.zero_lt_one hc Nat.zero_lt_one).apply_symm_apply
              (fun _ zt _ => f zt))
          zeroVec)
        zt)
      zeroVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEOFamilyPairEquiv
    {S U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] :
    ((S → U) × (S → V)) ≃ₗ[F] (S → U × V) where
  toFun x s := (x.1 s, x.2 s)
  invFun f := (fun s => (f s).1, fun s => (f s).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEOCubeJShift
    {n : Nat} [NeZero n] (u : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X i (j - u) k
  invFun X i j k := X i (j + u) k
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEOPairJGauge
    {n c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n × CyclicCube n) ≃ₗ[F]
      (PVec n c → CyclicCube n × CyclicCube n) where
  toFun f z :=
    (totalEOEOCubeJShift (vecSum z) (f z).1,
      totalEOEOCubeJShift (vecSum z) (f z).2)
  invFun f z :=
    ((totalEOEOCubeJShift (vecSum z)).symm (f z).1,
      (totalEOEOCubeJShift (vecSum z)).symm (f z).2)
  left_inv f := by
    funext z
    exact Prod.ext
      ((totalEOEOCubeJShift (vecSum z)).symm_apply_apply (f z).1)
      ((totalEOEOCubeJShift (vecSum z)).symm_apply_apply (f z).2)
  right_inv f := by
    funext z
    exact Prod.ext
      ((totalEOEOCubeJShift (vecSum z)).apply_symm_apply (f z).1)
      ((totalEOEOCubeJShift (vecSum z)).apply_symm_apply (f z).2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEOAJGauge
    {n c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) ≃ₗ[F]
      (PVec n c → CyclicCube n) where
  toFun f z := totalEOEOCubeJShift (vecSum z) (f z)
  invFun f z := (totalEOEOCubeJShift (vecSum z)).symm (f z)
  left_inv f := by
    funext z
    exact (totalEOEOCubeJShift (vecSum z)).symm_apply_apply (f z)
  right_inv f := by
    funext z
    exact (totalEOEOCubeJShift (vecSum z)).apply_symm_apply (f z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEOBWZGaugedEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    (BFun4 n 1 c 1 × WFun4 n 1 1 c) ≃ₗ[F]
      (PVec n c → CyclicCube n × CyclicCube n) :=
  (((totalEOEOBRootZEquiv (n := n) hc).prodCongr
      (totalEOEOWRootZEquiv (n := n) hc)).trans
    (totalEOEOFamilyPairEquiv (S := PVec n c)
      (U := CyclicCube n) (V := CyclicCube n))).trans
    (totalEOEOPairJGauge (n := n) (c := c))

private noncomputable def totalEOEOAZGaugedEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    AFun4 n 1 c 1 ≃ₗ[F] (PVec n c → CyclicCube n) :=
  (totalEOEOARootZEquiv (n := n) hc).trans
    (totalEOEOAJGauge (n := n) (c := c))

@[simp] private theorem totalEOEOBWZGaugedEquiv_fst_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (x : BFun4 n 1 c 1 × WFun4 n 1 1 c)
    (zt : PVec n c) (i j k : I n) :
    (totalEOEOBWZGaugedEquiv hc x zt).1 i j k =
      diamondBRootCubeEquiv hc Nat.zero_lt_one x.1 zt zeroVec
        i (j - vecSum zt) k := rfl

@[simp] private theorem totalEOEOBWZGaugedEquiv_snd_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (x : BFun4 n 1 c 1 × WFun4 n 1 1 c)
    (zt : PVec n c) (i j k : I n) :
    (totalEOEOBWZGaugedEquiv hc x zt).2 i j k =
      diamondWRootCubeEquiv Nat.zero_lt_one hc x.2 zeroVec zt
        i (j - vecSum zt) k := rfl

@[simp] private theorem totalEOEOAZGaugedEquiv_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (A : AFun4 n 1 c 1) (zt : PVec n c) (i j k : I n) :
    totalEOEOAZGaugedEquiv hc A zt i j k =
      diamondARootCubeEquiv Nat.zero_lt_one hc Nat.zero_lt_one
        A zeroVec zt zeroVec i (j - vecSum zt) k := rfl

@[simp] private theorem totalEOEOCubeJShift_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    totalEOEOCubeJShift u X i j k = X i (j - u) k := rfl

@[simp] private theorem totalEOEOCubeJShift_symm_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    (totalEOEOCubeJShift u).symm X i j k = X i (j + u) k := rfl

private theorem totalEOEOCubeJShift_cubeDiffP
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    totalEOEOCubeJShift u (cubeDiffP X) =
      cubeDiffP (totalEOEOCubeJShift u X) := by
  funext i j k
  simp only [totalEOEOCubeJShift_apply]
  rw [EEOEInternal.cubeDiffP_apply, EEOEInternal.cubeDiffP_apply]
  congr 2
  abel

private theorem totalEOEOCubeJShift_cubeDiffR
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    totalEOEOCubeJShift u (cubeDiffR X) =
      cubeDiffR (totalEOEOCubeJShift u X) := by
  funext i j k
  simp only [totalEOEOCubeJShift_apply]
  rw [EEOEInternal.cubeDiffR_apply, EEOEInternal.cubeDiffR_apply]
  congr 2
  abel

private theorem totalEOEOCubeJShift_cubeDiffI
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    totalEOEOCubeJShift u (cubeDiffI X) =
      cubeDiffI (totalEOEOCubeJShift u X) := by
  funext i j k
  simp only [totalEOEOCubeJShift_apply]
  rw [EEOEInternal.cubeDiffI_apply, EEOEInternal.cubeDiffI_apply]
  rfl

private theorem totalEOEOCubeJShift_cubeDiffK
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    totalEOEOCubeJShift u (cubeDiffK X) =
      cubeDiffK (totalEOEOCubeJShift u X) := by
  funext i j k
  simp only [totalEOEOCubeJShift_apply]
  rw [EEOEInternal.cubeDiffK_apply, EEOEInternal.cubeDiffK_apply]
  rfl

private theorem totalEOEOCubeJShift_cubeDiffJInv
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    totalEOEOCubeJShift u (cubeDiffJInv X) =
      cubeDiffJInv (totalEOEOCubeJShift u X) := by
  funext i j k
  simp only [totalEOEOCubeJShift_apply]
  rw [EEOEInternal.cubeDiffJInv_apply,
    EEOEInternal.cubeDiffJInv_apply]
  congr 2
  abel

private theorem totalEOEOCubeJShift_pairing_same
    {n : Nat} [NeZero n] (u : I n) (X Y : CyclicCube n) :
    cubeDot (totalEOEOCubeJShift u X) (totalEOEOCubeJShift u Y) =
      cubeDot X Y := by
  classical
  unfold cubeDot
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.addRight (-u)) (Equiv.refl (I n)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, totalEOEOCubeJShift, sub_eq_add_neg]

@[simp] private theorem totalEOEOBWZGaugedEquiv_cubeDiffP_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (x : BFun4 n 1 c 1 × WFun4 n 1 1 c)
    (zt : PVec n c) (i j k : I n) :
    cubeDiffP (totalEOEOBWZGaugedEquiv hc x zt).1 i j k =
      cubeDiffP
        (diamondBRootCubeEquiv hc Nat.zero_lt_one x.1 zt zeroVec)
        i (j - vecSum zt) k := by
  rw [show (totalEOEOBWZGaugedEquiv hc x zt).1 =
      totalEOEOCubeJShift (vecSum zt)
        (diamondBRootCubeEquiv hc Nat.zero_lt_one x.1 zt zeroVec)
    from rfl]
  rw [← totalEOEOCubeJShift_cubeDiffP]
  rfl

@[simp] private theorem totalEOEOBWZGaugedEquiv_cubeDiffR_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (x : BFun4 n 1 c 1 × WFun4 n 1 1 c)
    (zt : PVec n c) (i j k : I n) :
    cubeDiffR (totalEOEOBWZGaugedEquiv hc x zt).2 i j k =
      cubeDiffR
        (diamondWRootCubeEquiv Nat.zero_lt_one hc x.2 zeroVec zt)
        i (j - vecSum zt) k := by
  rw [show (totalEOEOBWZGaugedEquiv hc x zt).2 =
      totalEOEOCubeJShift (vecSum zt)
        (diamondWRootCubeEquiv Nat.zero_lt_one hc x.2 zeroVec zt)
    from rfl]
  rw [← totalEOEOCubeJShift_cubeDiffR]
  rfl

@[simp] private theorem totalEOEOAZGaugedEquiv_cubeDiffJInv_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (A : AFun4 n 1 c 1) (zt : PVec n c) (i j k : I n) :
    cubeDiffJInv (totalEOEOAZGaugedEquiv hc A zt) i j k =
      cubeDiffJInv
        (diamondARootCubeEquiv
          Nat.zero_lt_one hc Nat.zero_lt_one A zeroVec zt zeroVec)
        i (j - vecSum zt) k := by
  rw [show totalEOEOAZGaugedEquiv hc A zt =
      totalEOEOCubeJShift (vecSum zt)
        (diamondARootCubeEquiv Nat.zero_lt_one hc Nat.zero_lt_one
          A zeroVec zt zeroVec)
    from rfl]
  rw [← totalEOEOCubeJShift_cubeDiffJInv]
  rfl

@[simp] private theorem totalEOEOVecSum_zero
    {n k : Nat} [NeZero n] :
    vecSum (zeroVec : Vec n k) = 0 := by
  unfold vecSum zeroVec
  simp

private noncomputable def totalEOEOLeftAmbientReassoc
    {n c : Nat} [NeZero n] :
    PointedEvenValueCoords
        (PVec n c) (CyclicCube n × CyclicCube n)
        (zeroVec : PVec n c) ≃ₗ[F]
      (DiamondEOEOLeftAmbient n ×
        DiamondEvenAxisValueTailZero n c
          (DiamondEOOOLeftAmbient n)) where
  toFun x :=
    ((((x.1.1).1, (x.1.2).1), ((x.1.1).2, (x.1.2).2)), x.2)
  invFun x :=
    (((x.1.1.1, x.1.2.1), (x.1.1.2, x.1.2.2)), x.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def totalEOEORightShearReassoc
    {n c : Nat} [NeZero n] :
    PointedEvenValueCoords
        (PVec n c) (CyclicCube n) (zeroVec : PVec n c) ≃ₗ[F]
      (DiamondEOEORightAmbient n ×
        DiamondEvenAxisValueTailZero n c (CyclicCube n)) where
  toFun x := ((x.1.2, x.1.1 + x.1.2), x.2)
  invFun x := ((x.1.1 + x.1.2, x.1.1), x.2)
  left_inv x := by
    rcases x with ⟨⟨A0, D⟩, T⟩
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
    rcases x with ⟨⟨D, A1⟩, T⟩
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

private noncomputable def totalEOEOLeftAmbientCoords
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c) :
    (BFun4 n 1 c 1 × WFun4 n 1 1 c) ≃ₗ[F]
      (DiamondEOEOLeftAmbient n ×
        DiamondEvenAxisValueTailZero n c
          (DiamondEOOOLeftAmbient n)) :=
  (totalEOEOBWZGaugedEquiv (n := n) (by omega)).trans
    ((diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (DiamondEOOOLeftAmbient n) hn hc2).trans
      (totalEOEOLeftAmbientReassoc (n := n) (c := c)))

private noncomputable def totalEOEORightAmbientCoords
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c) :
    AFun4 n 1 c 1 ≃ₗ[F]
      (DiamondEOEORightAmbient n ×
        DiamondEvenAxisValueTailZero n c (CyclicCube n)) :=
  (totalEOEOAZGaugedEquiv (n := n) (by omega)).trans
    ((diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2).trans
      (totalEOEORightShearReassoc (n := n) (c := c)))

private noncomputable def totalEOEOEOEOFamilyConstraint
    {n c : Nat} [NeZero n] :
    (PVec n c → DiamondEOOOLeftAmbient n) →ₗ[F] CyclicCube n where
  toFun f :=
    cubeDiffP (∑ z, (f z).1) + cubeDiffR (∑ z, (f z).2)
  map_add' f g := by
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Finset.sum_add_distrib, map_add]
    abel
  map_smul' r f := by
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd]
    rw [← Finset.smul_sum, ← Finset.smul_sum,
      map_smul, map_smul, smul_add]
    rfl

private theorem totalEOEOEOEOFamilyConstraint_coords
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c)
    (f : PVec n c → DiamondEOOOLeftAmbient n) :
    totalEOEOEOEOFamilyConstraint f =
      diamondEOEOLeftConstraintMap
        (totalEOEOLeftAmbientReassoc
          (diamondEvenAxisSrcCoordEquiv
            (n := n) (k := c) (DiamondEOOOLeftAmbient n)
            hn hc2 f)).1 := by
  simp only [totalEOEOEOEOFamilyConstraint, LinearMap.coe_mk,
    AddHom.coe_mk, totalEOEOLeftAmbientReassoc,
    LinearEquiv.coe_mk, diamondEOEOLeftConstraintMap,
    diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv,
    pointedSrcEvenValueRead, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Prod.fst_sum, Prod.snd_sum]

private theorem totalEOEOLiteralLeft_mem_iff_uniform
    {n c : Nat} [NeZero n] (hc2 : 2 ≤ c)
    (x : BFun4 n 1 c 1 × WFun4 n 1 1 c) :
    x ∈ DiamondEvenPLeft n 1 c 1 ↔
      totalEOEOEOEOFamilyConstraint
        (totalEOEOBWZGaugedEquiv (by omega) x) = 0 := by
  simp only [DiamondEvenPLeft, LinearMap.mem_ker]
  constructor
  · intro hx
    funext i j k
    simp only [totalEOEOEOEOFamilyConstraint, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.zero_apply]
    change
      (cubeDiffP
          (∑ zt : PVec n c,
            (totalEOEOBWZGaugedEquiv
              (by omega : 0 < c) x zt).1) +
        cubeDiffR
          (∑ zt : PVec n c,
            (totalEOEOBWZGaugedEquiv
              (by omega : 0 < c) x zt).2)) i j k = 0
    rw [map_sum, map_sum, ← Finset.sum_add_distrib,
      Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hx (zeroVec : PVec n 1))
            ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
              (i, zeroVec)))
          j)
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
          (k, zeroVec))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      x.1 x.2 zeroVec zeroVec i j k] at hpoint
    simp only [totalEOEOVecSum_zero, add_zero,
      Pi.zero_apply] at hpoint
    simpa only [Pi.add_apply,
      totalEOEOBWZGaugedEquiv_cubeDiffP_apply,
      totalEOEOBWZGaugedEquiv_cubeDiffR_apply] using hpoint
  · intro h
    simp only [totalEOEOEOEOFamilyConstraint, LinearMap.coe_mk,
      AddHom.coe_mk] at h
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      x.1 x.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2,
      pVec_one_eq_zeroVec (ew w).2]
    simp only [totalEOEOVecSum_zero, Pi.zero_apply]
    have hpoint :=
      congrFun (congrFun (congrFun h (ey y).1) sz) (ew w).1
    rw [map_sum, map_sum, ← Finset.sum_add_distrib,
      Finset.sum_apply, Finset.sum_apply, Finset.sum_apply] at hpoint
    simpa only [Pi.add_apply, Pi.zero_apply,
      totalEOEOVecSum_zero, add_zero,
      totalEOEOBWZGaugedEquiv_cubeDiffP_apply,
      totalEOEOBWZGaugedEquiv_cubeDiffR_apply] using hpoint

private theorem totalEOEOLeft_mem_iff_coords
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c)
    (x : BFun4 n 1 c 1 × WFun4 n 1 1 c) :
    x ∈ DiamondEvenPLeft n 1 c 1 ↔
      (totalEOEOLeftAmbientCoords hn hc2 x).1 ∈
        DiamondEOEOLeftSource n := by
  rw [totalEOEOLiteralLeft_mem_iff_uniform hc2 x]
  change
    totalEOEOEOEOFamilyConstraint
        (totalEOEOBWZGaugedEquiv (by omega : 0 < c) x) = 0 ↔
      diamondEOEOLeftConstraintMap
        (totalEOEOLeftAmbientCoords hn hc2 x).1 = 0
  rw [totalEOEOEOEOFamilyConstraint_coords hn hc2]
  rfl

noncomputable def diamondEvenPLeftEOEOEquiv
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c) :
    DiamondEvenPLeft n 1 c 1 ≃ₗ[F]
      (DiamondEOEOLeftSource n ×
        DiamondEvenAxisValueTailZero n c
          (EOEOZTailLeftBase n)) where
  toFun l := by
    let q := totalEOEOLeftAmbientCoords hn hc2 l.1
    exact
      (⟨q.1, (totalEOEOLeft_mem_iff_coords hn hc2 l.1).mp l.2⟩, q.2)
  invFun z := by
    let raw :
        DiamondEOEOLeftAmbient n ×
          DiamondEvenAxisValueTailZero n c
            (DiamondEOOOLeftAmbient n) :=
      (z.1.1, z.2)
    let l := (totalEOEOLeftAmbientCoords hn hc2).symm raw
    refine ⟨l, (totalEOEOLeft_mem_iff_coords hn hc2 l).mpr ?_⟩
    have hread : totalEOEOLeftAmbientCoords hn hc2 l = raw :=
      (totalEOEOLeftAmbientCoords hn hc2).apply_symm_apply raw
    have hfst := congrArg Prod.fst hread
    rw [hfst]
    exact z.1.2
  left_inv l := by
    apply Subtype.ext
    exact (totalEOEOLeftAmbientCoords hn hc2).symm_apply_apply l.1
  right_inv z := by
    have hread :=
      (totalEOEOLeftAmbientCoords hn hc2).apply_symm_apply
        (z.1.1, z.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · change
        (totalEOEOLeftAmbientCoords hn hc2
          ((totalEOEOLeftAmbientCoords hn hc2).symm
            (z.1.1, z.2))).2 = z.2
      exact congrArg Prod.snd hread
  map_add' l m := by
    have hmap :=
      (totalEOEOLeftAmbientCoords hn hc2).map_add l.1 m.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · change
        (totalEOEOLeftAmbientCoords hn hc2 ((l + m).1)).2 =
          (totalEOEOLeftAmbientCoords hn hc2 l.1).2 +
            (totalEOEOLeftAmbientCoords hn hc2 m.1).2
      exact congrArg Prod.snd hmap
  map_smul' r l := by
    have hmap :=
      (totalEOEOLeftAmbientCoords hn hc2).map_smul r l.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · change
        (totalEOEOLeftAmbientCoords hn hc2 ((r • l).1)).2 =
          r • (totalEOEOLeftAmbientCoords hn hc2 l.1).2
      exact congrArg Prod.snd hmap

private theorem totalEOEOLiteralReachable_mem_iff_total_range
    {n c : Nat} [NeZero n] (hc2 : 2 ≤ c)
    (A : AFun4 n 1 c 1) :
    A ∈ DiamondEvenPReachableA n 1 c 1 ↔
      cubeDiffJInv
          (∑ z : PVec n c,
            totalEOEOAZGaugedEquiv (by omega : 0 < c) A z) ∈
        LinearMap.range
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n))) := by
  change
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := 1) (c := c) (d := 1) A ∈
      LinearMap.range
        (squareCompat
          (n := n) (a := 1) (b := 1) (c := c) (d := 1)) ↔ _
  constructor
  · rintro ⟨bw, hbw⟩
    let f :=
      totalEOEOBWZGaugedEquiv (n := n) (c := c)
        (by omega : 0 < c) bw
    refine ⟨(∑ z, (f z).1, ∑ z, (f z).2), ?_⟩
    funext i j k
    rw [LinearMap.coprod_apply, map_sum, map_sum, map_sum,
      ← Finset.sum_add_distrib, Finset.sum_apply,
      Finset.sum_apply, Finset.sum_apply]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hbw (zeroVec : PVec n 1))
            ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
              (i, zeroVec)))
          j)
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
          (k, zeroVec))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      bw.1 bw.2 zeroVec zeroVec i j k] at hpoint
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      A zeroVec zeroVec i j k] at hpoint
    simp only [totalEOEOVecSum_zero, add_zero] at hpoint
    simp only [Finset.sum_apply] at hpoint ⊢
    simpa only [f, Pi.add_apply,
      totalEOEOBWZGaugedEquiv_cubeDiffP_apply,
      totalEOEOBWZGaugedEquiv_cubeDiffR_apply,
      totalEOEOAZGaugedEquiv_cubeDiffJInv_apply] using hpoint
  · rintro ⟨u, hu⟩
    classical
    let f : PVec n c → DiamondEOOOLeftAmbient n :=
      fun z => if z = (zeroVec : PVec n c) then u else 0
    have hsum : (∑ z, f z) = u := by
      rw [Finset.sum_eq_single (zeroVec : PVec n c)]
      · simp [f]
      · intro z _ hz
        simp [f, hz]
      · simp
    let bw :=
      (totalEOEOBWZGaugedEquiv
        (n := n) (c := c) (by omega : 0 < c)).symm f
    have hbw :
        totalEOEOBWZGaugedEquiv
          (n := n) (c := c) (by omega : 0 < c) bw = f :=
      (totalEOEOBWZGaugedEquiv
        (n := n) (c := c) (by omega : 0 < c)).apply_symm_apply f
    refine ⟨bw, ?_⟩
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      bw.1 bw.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      A (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2,
      pVec_one_eq_zeroVec (ew w).2]
    simp only [totalEOEOVecSum_zero, add_zero]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun hu (ey y).1) sz)
        (ew w).1
    rw [LinearMap.coprod_apply] at hpoint
    have hfst : (∑ z, (f z).1) = u.1 := by
      simpa only [Prod.fst_sum] using congrArg Prod.fst hsum
    have hsnd : (∑ z, (f z).2) = u.2 := by
      simpa only [Prod.snd_sum] using congrArg Prod.snd hsum
    rw [← hfst, ← hsnd, map_sum, map_sum, map_sum,
      ← Finset.sum_add_distrib, Finset.sum_apply,
      Finset.sum_apply, Finset.sum_apply] at hpoint
    simp only [Finset.sum_apply] at hpoint
    rw [← hbw] at hpoint
    simpa only [Pi.add_apply,
      totalEOEOBWZGaugedEquiv_cubeDiffP_apply,
      totalEOEOBWZGaugedEquiv_cubeDiffR_apply,
      totalEOEOAZGaugedEquiv_cubeDiffJInv_apply] using hpoint

private theorem totalEOEOSum_eq_point_add_tail
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
              (s := (Finset.univ : Finset S))
              (p := fun s : S => s ≠ s0) (f := f)).symm

private theorem totalEOEOCast_odd_eq_one
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem totalEOEOSum_const_odd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    totalEOEOCast_odd_eq_one hodd, one_smul]

private theorem totalEOEODual_D_eq_total_sum
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c)
    (g : PVec n c → CyclicCube n) :
    (diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2 g).1.2 =
      ∑ z, g z := by
  change
    (∑ t : DiamondEvenAxisTailIndex n c,
      (g t.1 + g (zeroVec : PVec n c))) =
      ∑ z : PVec n c, g z
  rw [Finset.sum_add_distrib,
    totalEOEOSum_const_odd
      (odd_card_diamondEvenAxisTailIndex hn hc2),
    totalEOEOSum_eq_point_add_tail (zeroVec : PVec n c) g]
  abel

private theorem totalEOEORight_mem_iff_coords
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c)
    (A : AFun4 n 1 c 1) :
    A ∈ DiamondEvenPReachableA n 1 c 1 ↔
      (totalEOEORightAmbientCoords hn hc2 A).1 ∈
        DiamondEOEORightSource n := by
  rw [totalEOEOLiteralReachable_mem_iff_total_range hc2 A]
  let g :=
    totalEOEOAZGaugedEquiv (n := n) (c := c) (by omega : 0 < c) A
  let D :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (CyclicCube n) hn hc2 g
  have hD := totalEOEODual_D_eq_total_sum hn hc2 g
  change
    cubeDiffJInv (∑ z, g z) ∈
        LinearMap.range
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n))) ↔
      ((D.1.2, D.1.1 + D.1.2) :
        DiamondEOEORightAmbient n) ∈
          DiamondEOEORightSource n
  rw [← hD]
  change
    cubeDiffJInv D.1.2 ∈
        LinearMap.range
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n))) ↔
      cubeDiffJInv D.1.2 ∈
        LinearMap.range
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n))) ∧ True
  simp

noncomputable def diamondEvenPReachableAEOEOEquiv
    {n c : Nat} [NeZero n] (hn : Even n) (hc2 : 2 ≤ c) :
    DiamondEvenPReachableA n 1 c 1 ≃ₗ[F]
      (DiamondEOEORightSource n ×
        DiamondEvenAxisValueTailZero n c (EOEOZTailRightBase n)) where
  toFun A := by
    let q := totalEOEORightAmbientCoords hn hc2 A.1
    exact
      (⟨q.1, (totalEOEORight_mem_iff_coords hn hc2 A.1).mp A.2⟩, q.2)
  invFun z := by
    let raw :
        DiamondEOEORightAmbient n ×
          DiamondEvenAxisValueTailZero n c (CyclicCube n) :=
      (z.1.1, z.2)
    let A := (totalEOEORightAmbientCoords hn hc2).symm raw
    refine ⟨A, (totalEOEORight_mem_iff_coords hn hc2 A).mpr ?_⟩
    have hread : totalEOEORightAmbientCoords hn hc2 A = raw :=
      (totalEOEORightAmbientCoords hn hc2).apply_symm_apply raw
    have hfst := congrArg Prod.fst hread
    rw [hfst]
    exact z.1.2
  left_inv A := by
    apply Subtype.ext
    exact (totalEOEORightAmbientCoords hn hc2).symm_apply_apply A.1
  right_inv z := by
    have hread :=
      (totalEOEORightAmbientCoords hn hc2).apply_symm_apply
        (z.1.1, z.2)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · change
        (totalEOEORightAmbientCoords hn hc2
          ((totalEOEORightAmbientCoords hn hc2).symm
            (z.1.1, z.2))).2 = z.2
      exact congrArg Prod.snd hread
  map_add' A A' := by
    have hmap :=
      (totalEOEORightAmbientCoords hn hc2).map_add A.1 A'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · change
        (totalEOEORightAmbientCoords hn hc2 ((A + A').1)).2 =
          (totalEOEORightAmbientCoords hn hc2 A.1).2 +
            (totalEOEORightAmbientCoords hn hc2 A'.1).2
      exact congrArg Prod.snd hmap
  map_smul' r A := by
    have hmap :=
      (totalEOEORightAmbientCoords hn hc2).map_smul r A.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · change
        (totalEOEORightAmbientCoords hn hc2 ((r • A).1)).2 =
          r • (totalEOEORightAmbientCoords hn hc2 A.1).2
      exact congrArg Prod.snd hmap

private theorem totalEOEOSum_pVec_one
    {n : Nat} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : PVec n 1 → M) :
    (∑ p : PVec n 1, f p) = f (zeroVec : PVec n 1) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    exact (hp (pVec_one_eq_zeroVec p)).elim
  · simp

private theorem totalEOEOCubeDot_comm
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  classical
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private theorem totalEOEOCubeJShift_leftRoot_Z
    {n c : Nat} [NeZero n] (hc2 : 2 ≤ c)
    (l : DiamondEvenPLeft n 1 c 1) (zt : PVec n c) :
    totalEOEOCubeJShift (vecSum zt)
        (diamondARootCubeEquiv
          Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
          (diamondEvenPLeftRoot l) zeroVec zt zeroVec) =
      cubeDiffI
          (totalEOEOBWZGaugedEquiv
            (by omega : 0 < c) l.1 zt).1 +
        cubeDiffK
          (totalEOEOBWZGaugedEquiv
            (by omega : 0 < c) l.1 zt).2 := by
  funext i j k
  rw [totalEOEOCubeJShift_apply]
  change
    diamondEvenPLeftRoot l
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
          (i, zeroVec))
        ((diamondVecHeadTailEquiv (by omega : 0 < c)).symm
          (j - vecSum zt, zt))
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
          (k, zeroVec)) =
      _
  rw [diamondCubeReindex_leftRoot
    Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
    l zeroVec zt zeroVec i (j - vecSum zt) k]
  simp only [totalEOEOVecSum_zero, add_zero]
  rw [show
      (totalEOEOBWZGaugedEquiv
        (by omega : 0 < c) l.1 zt).1 =
        totalEOEOCubeJShift (vecSum zt)
          (diamondBRootCubeEquiv
            (by omega : 0 < c) Nat.zero_lt_one
            l.1.1 zt zeroVec) from rfl]
  rw [show
      (totalEOEOBWZGaugedEquiv
        (by omega : 0 < c) l.1 zt).2 =
        totalEOEOCubeJShift (vecSum zt)
          (diamondWRootCubeEquiv
            Nat.zero_lt_one (by omega : 0 < c)
            l.1.2 zeroVec zt) from rfl]
  rw [← totalEOEOCubeJShift_cubeDiffI,
    ← totalEOEOCubeJShift_cubeDiffK]
  rfl

private theorem totalEOEOLiteral_phase_gauged
    {n c : Nat} [NeZero n] (hc2 : 2 ≤ c)
    (l : DiamondEvenPLeft n 1 c 1)
    (A : DiamondEvenPReachableA n 1 c 1) :
    diamondEvenPCross l A =
      ∑ z : PVec n c,
        diamondTailFreeStarCross
            (totalEOEOBWZGaugedEquiv
              (by omega : 0 < c) l.1 z)
          (totalEOEOAZGaugedEquiv
            (by omega : 0 < c) A.1 z) := by
  change coeffApplyA (diamondEvenPLeftRoot l) A.1 = _
  rw [diamondCubeReindex_rootPairing
    Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one]
  rw [totalEOEOSum_pVec_one]
  simp_rw [totalEOEOSum_pVec_one]
  apply Finset.sum_congr rfl
  intro z _
  let u := vecSum z
  let AR :=
    diamondARootCubeEquiv
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      A.1 zeroVec z zeroVec
  let LR :=
    diamondARootCubeEquiv
      Nat.zero_lt_one (by omega : 0 < c) Nat.zero_lt_one
      (diamondEvenPLeftRoot l) zeroVec z zeroVec
  calc
    cubeDot AR LR =
        cubeDot (totalEOEOCubeJShift u AR)
          (totalEOEOCubeJShift u LR) :=
      (totalEOEOCubeJShift_pairing_same u AR LR).symm
    _ = cubeDot
          (totalEOEOAZGaugedEquiv
            (by omega : 0 < c) A.1 z)
          (cubeDiffI
              (totalEOEOBWZGaugedEquiv
                (by omega : 0 < c) l.1 z).1 +
            cubeDiffK
              (totalEOEOBWZGaugedEquiv
                (by omega : 0 < c) l.1 z).2) := by
      rw [show totalEOEOCubeJShift u AR =
          totalEOEOAZGaugedEquiv
            (by omega : 0 < c) A.1 z from rfl]
      rw [show totalEOEOCubeJShift u LR =
          cubeDiffI
              (totalEOEOBWZGaugedEquiv
                (by omega : 0 < c) l.1 z).1 +
            cubeDiffK
              (totalEOEOBWZGaugedEquiv
                (by omega : 0 < c) l.1 z).2 from
        totalEOEOCubeJShift_leftRoot_Z hc2 l z]
    _ = _ := totalEOEOCubeDot_comm _ _

set_option maxHeartbeats 1000000 in
-- Expanding the pointed pairing normal form needs additional heartbeats.
private theorem totalEOEOTotal_pairing_in_pointed_coordinates
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (f : PVec n c → DiamondEOOOLeftAmbient n)
    (g : PVec n c → CyclicCube n) :
    let x :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c) (DiamondEOOOLeftAmbient n) hn hc2 f
    let y :=
      diamondEvenAxisDualCoordEquiv
        (n := n) (k := c) (CyclicCube n) hn hc2 g
    (∑ z : PVec n c, diamondTailFreeStarCross (f z) (g z)) =
      BWSymmetryInternal.pairPhase
          (diamondEOEOCoeffMap
            (((x.1.1).1, (x.1.2).1),
              ((x.1.1).2, (x.1.2).2)))
          (y.1.2, y.1.1 + y.1.2) +
        ∑ t, diamondTailFreeStarCross (x.2.1 t) (y.2.1 t) := by
  dsimp only
  have hpair :=
    pointedEvenValue_pairing
      (zeroVec : PVec n c)
      (even_card_PVec hn hc2)
      (diamondTailFreeStarCross (n := n)) f g
  rw [hpair]
  change
    cubeDot
        (cubeDiffI
            ((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.1).1 +
          cubeDiffK
            ((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.1).2)
        ((diamondEvenAxisDualCoordEquiv
          (CyclicCube n) hn hc2 g).1.1) +
      cubeDot
        (cubeDiffI
            ((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.2).1 +
          cubeDiffK
            ((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.2).2)
        ((diamondEvenAxisDualCoordEquiv
          (CyclicCube n) hn hc2 g).1.2) +
      (∑ t,
        diamondTailFreeStarCross
          ((diamondEvenAxisSrcCoordEquiv
            (DiamondEOOOLeftAmbient n) hn hc2 f).2.1 t)
          ((diamondEvenAxisDualCoordEquiv
            (CyclicCube n) hn hc2 g).2.1 t)) =
      BWSymmetryInternal.pairPhase
        (diamondEOEOCoeffMap
          ((((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.1).1,
            ((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.2).1),
           (((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.1).2,
            ((diamondEvenAxisSrcCoordEquiv
              (DiamondEOOOLeftAmbient n) hn hc2 f).1.2).2)))
        (((diamondEvenAxisDualCoordEquiv
            (CyclicCube n) hn hc2 g).1.2,
          (diamondEvenAxisDualCoordEquiv
              (CyclicCube n) hn hc2 g).1.1 +
            (diamondEvenAxisDualCoordEquiv
              (CyclicCube n) hn hc2 g).1.2)) +
      ∑ t,
        diamondTailFreeStarCross
          ((diamondEvenAxisSrcCoordEquiv
            (DiamondEOOOLeftAmbient n) hn hc2 f).2.1 t)
          ((diamondEvenAxisDualCoordEquiv
            (CyclicCube n) hn hc2 g).2.1 t)
  simp only [diamondEOEOCoeffMap, LinearMap.coe_mk, AddHom.coe_mk,
    BWSymmetryInternal.pairPhase]
  simp only [map_add,
    EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

noncomputable def eoeoZTailCross
    {n c : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n c
        (EOEOZTailLeftBase n) →ₗ[F]
      Module.Dual F
        (DiamondEvenAxisValueTailZero n c (EOEOZTailRightBase n)) :=
  diamondTailAmplify (diamondTailFreeStarCross (n := n))

theorem rank_eoeoZTailCross
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range (eoeoZTailCross (n := n) (c := c))) =
      (n ^ (c - 1) - 2) * n * (n - 1) * (n + 1) := by
  change
    Module.finrank F
        (LinearMap.range
          (diamondTailAmplify
            (n := n) (k := c) (diamondTailFreeStarCross (n := n)))) =
      _
  rw [finrank_range_diamondTailAmplify hn2 hn hc2,
    finrank_diamondEvenAxisTailZero hn2 hn hc2,
    rank_diamondTailFreeStarCross]
  simp only [Nat.mul_assoc]

set_option synthInstance.maxHeartbeats 200000 in
-- The nested scalar-tail product dual needs a larger synthesis budget.
noncomputable def diamondEOEOTotalBlockCross
    {n c : Nat} [NeZero n] :
    (DiamondEOEOLeftSource n ×
        DiamondEvenAxisValueTailZero n c
          (EOEOZTailLeftBase n)) →ₗ[F]
      Module.Dual F
        (DiamondEOEORightSource n ×
          DiamondEvenAxisValueTailZero n c (EOEOZTailRightBase n)) :=
  diamondCrossProd
    (diamondEOEOCross (n := n))
    (eoeoZTailCross (n := n) (c := c))

private theorem totalEOEOPhaseSplit
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (l : DiamondEvenPLeft n 1 c 1)
    (A : DiamondEvenPReachableA n 1 c 1) :
    diamondEvenPCross l A =
      diamondEOEOCross
          (diamondEvenPLeftEOEOEquiv hn hc2 l).1
          (diamondEvenPReachableAEOEOEquiv hn hc2 A).1 +
        ∑ t,
          diamondTailFreeStarCross
            ((diamondEvenPLeftEOEOEquiv hn hc2 l).2.1 t)
            ((diamondEvenPReachableAEOEOEquiv hn hc2 A).2.1 t) := by
  rw [totalEOEOLiteral_phase_gauged hc2 l A]
  rw [totalEOEOTotal_pairing_in_pointed_coordinates hn hc2]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The restricted scalar-tail product needs a larger synthesis budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the pointwise total phase square needs additional heartbeats.
theorem diamondEvenPCross_EOEO_phase
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (l : DiamondEvenPLeft n 1 c 1)
    (A : DiamondEvenPReachableA n 1 c 1) :
    diamondEOEOTotalBlockCross
        (diamondEvenPLeftEOEOEquiv hn hc2 l)
        (diamondEvenPReachableAEOEOEquiv hn hc2 A) =
      diamondEvenPCross l A := by
  unfold diamondEOEOTotalBlockCross
  change
    diamondEOEOCross
          (diamondEvenPLeftEOEOEquiv hn hc2 l).1
          (diamondEvenPReachableAEOEOEquiv hn hc2 A).1 +
        (∑ t,
          diamondTailFreeStarCross
            ((diamondEvenPLeftEOEOEquiv hn hc2 l).2.1 t)
            ((diamondEvenPReachableAEOEOEquiv hn hc2 A).2.1 t)) =
      diamondEvenPCross l A
  exact (totalEOEOPhaseSplit hn hc2 l A).symm

set_option synthInstance.maxHeartbeats 200000 in
-- The nested restricted source products need a larger synthesis budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the full range transport needs additional heartbeats.
noncomputable def diamondEvenPCross_EOEO_rangeEquiv
    {n c : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := 1) (c := c) (d := 1)) ≃ₗ[F]
      LinearMap.range
        (diamondEOEOTotalBlockCross (n := n) (c := c)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (L := DiamondEvenPLeft n 1 c 1)
    (R := DiamondEvenPReachableA n 1 c 1)
    (L' :=
      DiamondEOEOLeftSource n ×
        DiamondEvenAxisValueTailZero n c
          (EOEOZTailLeftBase n))
    (R' :=
      DiamondEOEORightSource n ×
        DiamondEvenAxisValueTailZero n c (EOEOZTailRightBase n))
    (diamondEvenPCross
      (n := n) (b := 1) (c := c) (d := 1))
    (diamondEOEOTotalBlockCross (n := n) (c := c))
    (diamondEvenPLeftEOEOEquiv hn hc2)
    (diamondEvenPReachableAEOEOEquiv hn hc2)
    (diamondEvenPCross_EOEO_phase hn hc2)

set_option synthInstance.maxHeartbeats 200000 in
-- The transported product range needs a larger synthesis budget.
set_option maxHeartbeats 1000000 in
-- Elaborating the final range calculation needs additional heartbeats.
theorem rank_diamondEvenPCross_EOEO
    {n c : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hc2 : 2 ≤ c) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := c) (d := 1))) =
      2 * n ^ 2 * (n - 1) +
        (n ^ (c - 1) - 2) * n * (n - 1) * (n + 1) := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := c) (d := 1))) =
        Module.finrank F
          (LinearMap.range
            (diamondEOEOTotalBlockCross
              (n := n) (c := c))) :=
      LinearEquiv.finrank_eq
        (diamondEvenPCross_EOEO_rangeEquiv hn hc2)
    _ =
        Module.finrank F
            (LinearMap.range (diamondEOEOCross (n := n))) +
          Module.finrank F
            (LinearMap.range
              (eoeoZTailCross (n := n) (c := c))) := by
      exact
        finrank_range_diamondCrossProd
          (diamondEOEOCross (n := n))
          (eoeoZTailCross (n := n) (c := c))
    _ =
        2 * n ^ 2 * (n - 1) +
          (n ^ (c - 1) - 2) * n * (n - 1) * (n + 1) := by
      rw [rank_diamondEvenP_cross_EOEO_scalar hn2 hn]
      rw [show eoeoZTailCross (n := n) (c := c) =
          diamondTailAmplify
            (n := n) (k := c)
            (diamondTailFreeStarCross (n := n)) from rfl]
      rw [finrank_range_diamondTailAmplify
        (n := n) (k := c) hn2 hn hc2
        (diamondTailFreeStarCross (n := n))]
      rw [finrank_diamondEvenAxisTailZero hn2 hn hc2,
        rank_diamondTailFreeStarCross]
      ring

end

end Core4loop.SquareDiagonal.EvenP
