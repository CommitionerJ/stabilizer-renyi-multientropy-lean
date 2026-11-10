import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RootGauge

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

private noncomputable def dSingletonFamilyEquiv
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

private noncomputable def dWRootZEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    WFun4 n 1 1 c ≃ₗ[F] (PVec n c → CyclicCube n) :=
  (diamondWRootCubeEquiv
      (n := n) (b := 1) (c := c) Nat.zero_lt_one hc).trans
    (dSingletonFamilyEquiv (n := n)
      (PVec n c → CyclicCube n))

private noncomputable def dFamilyPairEquiv
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

private noncomputable def dCubeJKShiftEquiv
    {n : Nat} [NeZero n] (u v : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X i (j - u) (k - v)
  invFun X i j k := X i (j + u) (k + v)
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem dCubeJKShiftEquiv_apply
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n)
    (i j k : I n) :
    dCubeJKShiftEquiv u v X i j k =
      X i (j - u) (k - v) := rfl

private noncomputable def dRootGaugeEquiv
    {n c d : Nat} [NeZero n] :
    (PVec n c → (PVec n d → CyclicCube n) × CyclicCube n) ≃ₗ[F]
      (PVec n c → (PVec n d → CyclicCube n) × CyclicCube n) where
  toFun f z :=
    (fun w =>
      dCubeJKShiftEquiv (vecSum z) (vecSum w) ((f z).1 w),
     dCubeJKShiftEquiv (vecSum z) 0 (f z).2)
  invFun f z :=
    (fun w =>
      (dCubeJKShiftEquiv (vecSum z) (vecSum w)).symm ((f z).1 w),
     (dCubeJKShiftEquiv (vecSum z) 0).symm (f z).2)
  left_inv f := by
    funext z
    apply Prod.ext
    · funext w
      exact
        (dCubeJKShiftEquiv (vecSum z) (vecSum w)).symm_apply_apply
          ((f z).1 w)
    · exact
        (dCubeJKShiftEquiv (vecSum z) 0).symm_apply_apply (f z).2
  right_inv f := by
    funext z
    apply Prod.ext
    · funext w
      exact
        (dCubeJKShiftEquiv (vecSum z) (vecSum w)).apply_symm_apply
          ((f z).1 w)
    · exact
        (dCubeJKShiftEquiv (vecSum z) 0).apply_symm_apply (f z).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def dLiteralRootGaugeEquiv
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    (BFun4 n 1 c d × WFun4 n 1 1 c) ≃ₗ[F]
      (PVec n c → (PVec n d → CyclicCube n) × CyclicCube n) :=
  (((diamondBRootCubeEquiv
      (n := n) (c := c) (d := d) hc hd).prodCongr
        (dWRootZEquiv (n := n) (c := c) hc)).trans
      (dFamilyPairEquiv
        (S := PVec n c)
        (U := PVec n d → CyclicCube n)
        (V := CyclicCube n))).trans
    (dRootGaugeEquiv (n := n) (c := c) (d := d))

@[simp] private theorem dLiteralRootGaugeEquiv_B_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (z : PVec n c) (w : PVec n d) (i j k : I n) :
    ((dLiteralRootGaugeEquiv hc hd x z).1 w) i j k =
      diamondBRootCubeEquiv hc hd x.1 z w
        i (j - vecSum z) (k - vecSum w) := rfl

@[simp] private theorem dLiteralRootGaugeEquiv_W_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (z : PVec n c) (i j k : I n) :
    (dLiteralRootGaugeEquiv hc hd x z).2 i j k =
      diamondWRootCubeEquiv Nat.zero_lt_one hc x.2 zeroVec z
        i (j - vecSum z) k := by
  change
    dCubeJKShiftEquiv (vecSum z) 0
        (diamondWRootCubeEquiv Nat.zero_lt_one hc x.2 zeroVec z)
        i j k =
      _
  simp [dCubeJKShiftEquiv]

private theorem dLiteralRootGaugeEquiv_B_eq
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (z : PVec n c) (w : PVec n d) :
    (dLiteralRootGaugeEquiv hc hd x z).1 w =
      dCubeJKShiftEquiv (vecSum z) (vecSum w)
        (diamondBRootCubeEquiv hc hd x.1 z w) := rfl

private theorem dLiteralRootGaugeEquiv_W_eq
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (z : PVec n c) :
    (dLiteralRootGaugeEquiv hc hd x z).2 =
      dCubeJKShiftEquiv (vecSum z) 0
        (diamondWRootCubeEquiv Nat.zero_lt_one hc x.2 zeroVec z) := by
  rfl

private noncomputable def dTailValueCongr
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (e : U ≃ₗ[F] V) :
    DiamondEvenAxisValueTailZero n k U ≃ₗ[F]
      DiamondEvenAxisValueTailZero n k V where
  toFun x :=
    ⟨fun t => e (x.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, e (x.1 t)) = 0
      rw [← map_sum, pointedValueTailZero_sum, map_zero]⟩
  invFun x :=
    ⟨fun t => e.symm (x.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, e.symm (x.1 t)) = 0
      rw [← map_sum, pointedValueTailZero_sum, map_zero]⟩
  left_inv x := by
    apply Subtype.ext
    funext t
    exact e.symm_apply_apply (x.1 t)
  right_inv x := by
    apply Subtype.ext
    funext t
    exact e.apply_symm_apply (x.1 t)
  map_add' x y := by
    apply Subtype.ext
    funext t
    exact e.map_add (x.1 t) (y.1 t)
  map_smul' r x := by
    apply Subtype.ext
    funext t
    exact e.map_smul r (x.1 t)

private noncomputable def dTailProdEquiv
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] :
    DiamondEvenAxisValueTailZero n k (U × V) ≃ₗ[F]
      (DiamondEvenAxisValueTailZero n k U ×
        DiamondEvenAxisValueTailZero n k V) where
  toFun x :=
    (⟨fun t => (x.1 t).1, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (x.1 t).1) = 0
        have hx := pointedValueTailZero_sum x
        simpa only [Prod.fst_sum] using congrArg Prod.fst hx⟩,
     ⟨fun t => (x.1 t).2, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (x.1 t).2) = 0
        have hx := pointedValueTailZero_sum x
        simpa only [Prod.snd_sum] using congrArg Prod.snd hx⟩)
  invFun x :=
    ⟨fun t => (x.1.1 t, x.2.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, (x.1.1 t, x.2.1 t)) = 0
      apply Prod.ext
      · rw [Prod.fst_sum]
        exact pointedValueTailZero_sum x.1
      · rw [Prod.snd_sum]
        exact pointedValueTailZero_sum x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[reducible] private noncomputable def dPointedCubeProdAddCommMonoid
    {n d : Nat} [NeZero n] :
    AddCommMonoid
      (PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
        CyclicCube n) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d)))
    (inferInstance : AddCommMonoid (CyclicCube n))

private local instance {n d : Nat} [NeZero n] :
    AddCommMonoid
      (PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
        CyclicCube n) :=
  dPointedCubeProdAddCommMonoid

private noncomputable def dEOEEHeadReassoc
    {n d : Nat} [NeZero n] :
    ((PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
        CyclicCube n) ×
      (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
        CyclicCube n)) ≃ₗ[F]
      (DiamondEOEELeftAmbient n ×
        DiamondEvenAxisValueTailZero n d
          (CyclicCube n × CyclicCube n)) where
  toFun x :=
    let scalar : DiamondEOEELeftAmbient n :=
      (((x.1.1.1.1, x.1.1.1.2),
        (x.2.1.1.1, x.2.1.1.2)),
       (x.1.2, x.2.2))
    let tail :
        DiamondEvenAxisValueTailZero n d
          (CyclicCube n × CyclicCube n) :=
      (dTailProdEquiv
        (n := n) (k := d)
        (U := CyclicCube n) (V := CyclicCube n)).symm
          (x.1.1.2, x.2.1.2)
    (scalar, tail)
  invFun x :=
    let t :=
      dTailProdEquiv
        (n := n) (k := d)
        (U := CyclicCube n) (V := CyclicCube n) x.2
    let first :
        PointedEvenValueCoords
            (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
          CyclicCube n :=
      (((x.1.1.1.1, x.1.1.1.2), t.1), x.1.2.1)
    let second :
        PointedEvenValueCoords
            (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
          CyclicCube n :=
      (((x.1.1.2.1, x.1.1.2.2), t.2), x.1.2.2)
    (first, second)
  left_inv x := by
    rcases x with ⟨⟨q, W0⟩, ⟨r, W1⟩⟩
    simp only
    have h :=
      (dTailProdEquiv
        (n := n) (k := d)
        (U := CyclicCube n) (V := CyclicCube n)).apply_symm_apply
          (q.2, r.2)
    rw [h]
  right_inv x := by
    rcases x with ⟨s, t⟩
    simp only
    have h :=
      (dTailProdEquiv
        (n := n) (k := d)
        (U := CyclicCube n) (V := CyclicCube n)).symm_apply_apply t
    rw [h]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact
        (dTailProdEquiv
          (n := n) (k := d)
          (U := CyclicCube n) (V := CyclicCube n)).symm.map_add
            (x.1.1.2, x.2.1.2) (y.1.1.2, y.2.1.2)
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · exact
        (dTailProdEquiv
          (n := n) (k := d)
          (U := CyclicCube n) (V := CyclicCube n)).symm.map_smul
            r (x.1.1.2, x.2.1.2)

private noncomputable def dEOEEZLocalReassoc
    {n d : Nat} [NeZero n] :
    (PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
      CyclicCube n) ≃ₗ[F]
      (DiamondEOOELeftAmbient n ×
        DiamondEvenAxisValueTailZero n d (CyclicCube n)) where
  toFun x := (((x.1.1.1, x.1.1.2), x.2), x.1.2)
  invFun x := (((x.1.1.1, x.1.1.2), x.2), x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def dEOEEZLocalCoordEquiv
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    ((PVec n d → CyclicCube n) × CyclicCube n) ≃ₗ[F]
      (DiamondEOOELeftAmbient n ×
        DiamondEvenAxisValueTailZero n d (CyclicCube n)) :=
  ((diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
    (LinearEquiv.refl F (CyclicCube n))).trans
      (dEOEEZLocalReassoc (n := n) (d := d))

private noncomputable def dEOEEOuterTailEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    DiamondEvenAxisValueTailZero n c
        ((PVec n d → CyclicCube n) × CyclicCube n) ≃ₗ[F]
      (DiamondEvenAxisValueTailZero n c
          (DiamondEOOELeftAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n)) :=
  (dTailValueCongr
      (n := n) (k := c)
      (dEOEEZLocalCoordEquiv
        (n := n) (d := d) hn hd2)).trans
    (dTailProdEquiv
      (n := n) (k := c)
      (U := DiamondEOOELeftAmbient n)
      (V := DiamondEvenAxisValueTailZero n d
        (CyclicCube n)))

private noncomputable def dEOEEHeadEquiv
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d) :
    (((PVec n d → CyclicCube n) × CyclicCube n) ×
      ((PVec n d → CyclicCube n) × CyclicCube n)) ≃ₗ[F]
      (DiamondEOEELeftAmbient n ×
        DiamondEvenAxisValueTailZero n d
          (CyclicCube n × CyclicCube n)) :=
  ((((diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
      (LinearEquiv.refl F (CyclicCube n))).prodCongr
    ((diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
      (LinearEquiv.refl F (CyclicCube n)))).trans
    (dEOEEHeadReassoc (n := n) (d := d)))

private noncomputable def dEOEEFinalAssoc
    {n c d : Nat} [NeZero n] :
    ((DiamondEOEELeftAmbient n ×
        DiamondEvenAxisValueTailZero n d
          (CyclicCube n × CyclicCube n)) ×
      (DiamondEvenAxisValueTailZero n c
          (DiamondEOOELeftAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n))) ≃ₗ[F]
      (DiamondEOEELeftAmbient n ×
        (DiamondEvenAxisValueTailZero n d
            (CyclicCube n × CyclicCube n) ×
          (DiamondEvenAxisValueTailZero n c
              (DiamondEOOELeftAmbient n) ×
            DiamondMixedTailZero n c d (CyclicCube n)))) :=
  LinearEquiv.prodAssoc F
    (DiamondEOEELeftAmbient n)
    (DiamondEvenAxisValueTailZero n d
      (CyclicCube n × CyclicCube n))
    (DiamondEvenAxisValueTailZero n c
        (DiamondEOOELeftAmbient n) ×
      DiamondMixedTailZero n c d (CyclicCube n))

private noncomputable def dEOEEAfterGaugeCoords
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    (PVec n c → (PVec n d → CyclicCube n) × CyclicCube n) ≃ₗ[F]
      (DiamondEOEELeftAmbient n ×
        (DiamondEvenAxisValueTailZero n d
            (CyclicCube n × CyclicCube n) ×
          (DiamondEvenAxisValueTailZero n c
              (DiamondEOOELeftAmbient n) ×
            DiamondMixedTailZero n c d (CyclicCube n)))) :=
  (diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c)
      ((PVec n d → CyclicCube n) × CyclicCube n)
      hn hc2).trans
    (((dEOEEHeadEquiv
        (n := n) (d := d) hn hd2).prodCongr
      (dEOEEOuterTailEquiv
        (n := n) (c := c) (d := d) hn hd2)).trans
      (dEOEEFinalAssoc (n := n) (c := c) (d := d)))

noncomputable def totalEOEELeftAmbientCoords
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    (BFun4 n 1 c d × WFun4 n 1 1 c) ≃ₗ[F]
      (DiamondEOEELeftAmbient n ×
        (DiamondEvenAxisValueTailZero n d
            (CyclicCube n × CyclicCube n) ×
          (DiamondEvenAxisValueTailZero n c
              (DiamondEOOELeftAmbient n) ×
            DiamondMixedTailZero n c d (CyclicCube n)))) :=
  (dLiteralRootGaugeEquiv
      (n := n) (c := c) (d := d) (by omega) (by omega)).trans
    (dEOEEAfterGaugeCoords
      (n := n) (c := c) (d := d) hn hc2 hd2)

private theorem dEOEEAfterGaugeCoords_scalar
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c →
      (PVec n d → CyclicCube n) × CyclicCube n) :
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (dEOEEAfterGaugeCoords hn hc2 hd2 f).1 =
      ((((E Z.1.1.1).1.1, (E Z.1.1.1).1.2),
        ((E Z.1.2.1).1.1, (E Z.1.2.1).1.2)),
       (Z.1.1.2, Z.1.2.2)) := by
  rfl

private theorem dEOEEAfterGaugeCoords_WTail_fst
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c →
      (PVec n d → CyclicCube n) × CyclicCube n)
    (t : DiamondEvenAxisTailIndex n d) :
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (((dEOEEAfterGaugeCoords hn hc2 hd2 f).2.1.1 t).1) =
      (E Z.1.1.1).2.1 t := by
  rfl

private theorem dEOEEAfterGaugeCoords_WTail_snd
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c →
      (PVec n d → CyclicCube n) × CyclicCube n)
    (t : DiamondEvenAxisTailIndex n d) :
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (((dEOEEAfterGaugeCoords hn hc2 hd2 f).2.1.1 t).2) =
      (E Z.1.2.1).2.1 t := by
  rfl

private theorem dEOEEAfterGaugeCoords_ZTail
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c →
      (PVec n d → CyclicCube n) × CyclicCube n)
    (t : DiamondEvenAxisTailIndex n c) :
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (dEOEEAfterGaugeCoords hn hc2 hd2 f).2.2.1.1 t =
      (((E (Z.2.1 t).1).1.1, (E (Z.2.1 t).1).1.2),
        (Z.2.1 t).2) := by
  rfl

private theorem dEOEEAfterGaugeCoords_ZWTail
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c →
      (PVec n d → CyclicCube n) × CyclicCube n)
    (zt : DiamondEvenAxisTailIndex n c)
    (wt : DiamondEvenAxisTailIndex n d) :
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (((dEOEEAfterGaugeCoords hn hc2 hd2 f).2.2.2.1 zt).1 wt) =
      (E (Z.2.1 zt).1).2.1 wt := by
  rfl

theorem totalEOEELeftAmbientCoords_scalar
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c) :
    let Bshift : PVec n c → PVec n d → CyclicCube n :=
      fun z w i j k =>
        diamondBRootCubeEquiv (by omega : 0 < c) (by omega : 0 < d)
            x.1 z w
          i (j - vecSum z) (k - vecSum w)
    let Wshift : PVec n c → CyclicCube n :=
      fun z i j k =>
        diamondWRootCubeEquiv Nat.zero_lt_one (by omega : 0 < c)
            x.2 zeroVec z
          i (j - vecSum z) k
    (totalEOEELeftAmbientCoords hn hc2 hd2 x).1 =
      (((((∑ w : PVec n d, ∑ z : PVec n c, Bshift z w),
          (∑ wt : DiamondEvenAxisTailIndex n d,
            ∑ z : PVec n c, Bshift z wt.1)),
         ((∑ w : PVec n d,
            ∑ zt : DiamondEvenAxisTailIndex n c, Bshift zt.1 w),
          (∑ wt : DiamondEvenAxisTailIndex n d,
            ∑ zt : DiamondEvenAxisTailIndex n c,
              Bshift zt.1 wt.1))),
        ((∑ z : PVec n c, Wshift z),
          (∑ zt : DiamondEvenAxisTailIndex n c, Wshift zt.1))) :
        DiamondEOEELeftAmbient n) := by
  dsimp only
  let f :=
    dLiteralRootGaugeEquiv
      (n := n) (c := c) (d := d)
      (by omega : 0 < c) (by omega : 0 < d) x
  rw [show totalEOEELeftAmbientCoords hn hc2 hd2 x =
      dEOEEAfterGaugeCoords hn hc2 hd2 f from rfl]
  rw [dEOEEAfterGaugeCoords_scalar]
  simp only [diamondEvenAxisSrcCoordEquiv,
    pointedSrcEvenValueEquiv_apply_sigma,
    pointedSrcEvenValueEquiv_apply_K,
    Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, f,
    dLiteralRootGaugeEquiv_B_eq,
    dLiteralRootGaugeEquiv_W_eq]
  ext i j k <;>
    simp only [Finset.sum_apply, dCubeJKShiftEquiv_apply, sub_zero]

noncomputable def totalEOEELeftLiteralFamily
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c) :
    PVec n c → (PVec n d → CyclicCube n) × CyclicCube n :=
  fun z =>
    (fun w i j k =>
      diamondBRootCubeEquiv hc hd x.1 z w
        i (j - vecSum z) (k - vecSum w),
     fun i j k =>
      diamondWRootCubeEquiv Nat.zero_lt_one hc x.2 zeroVec z
        i (j - vecSum z) k)

private theorem totalEOEELeftLiteralFamily_eq_rootGauge
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c) :
    totalEOEELeftLiteralFamily hc hd x =
      dLiteralRootGaugeEquiv hc hd x := by
  funext z
  apply Prod.ext
  · funext w i j k
    rfl
  · funext i j k
    symm
    exact dLiteralRootGaugeEquiv_W_apply hc hd x z i j k

theorem totalEOEELeftAmbientCoords_WTail
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (t : DiamondEvenAxisTailIndex n d) :
    let f :=
      totalEOEELeftLiteralFamily
        (by omega : 0 < c) (by omega : 0 < d) x
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (totalEOEELeftAmbientCoords hn hc2 hd2 x).2.1.1 t =
      ((E Z.1.1.1).2.1 t, (E Z.1.2.1).2.1 t) := by
  dsimp only
  rw [totalEOEELeftLiteralFamily_eq_rootGauge]
  rw [show totalEOEELeftAmbientCoords hn hc2 hd2 x =
      dEOEEAfterGaugeCoords hn hc2 hd2
        (dLiteralRootGaugeEquiv
          (n := n) (c := c) (d := d)
          (by omega : 0 < c) (by omega : 0 < d) x) from rfl]
  apply Prod.ext
  · exact dEOEEAfterGaugeCoords_WTail_fst hn hc2 hd2 _ t
  · exact dEOEEAfterGaugeCoords_WTail_snd hn hc2 hd2 _ t

theorem totalEOEELeftAmbientCoords_ZTail
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (t : DiamondEvenAxisTailIndex n c) :
    let f :=
      totalEOEELeftLiteralFamily
        (by omega : 0 < c) (by omega : 0 < d) x
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (totalEOEELeftAmbientCoords hn hc2 hd2 x).2.2.1.1 t =
      (((E (Z.2.1 t).1).1.1, (E (Z.2.1 t).1).1.2),
        (Z.2.1 t).2) := by
  dsimp only
  rw [totalEOEELeftLiteralFamily_eq_rootGauge]
  rw [show totalEOEELeftAmbientCoords hn hc2 hd2 x =
      dEOEEAfterGaugeCoords hn hc2 hd2
        (dLiteralRootGaugeEquiv
          (n := n) (c := c) (d := d)
          (by omega : 0 < c) (by omega : 0 < d) x) from rfl]
  exact dEOEEAfterGaugeCoords_ZTail hn hc2 hd2 _ t

theorem totalEOEELeftAmbientCoords_ZWTail
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c)
    (zt : DiamondEvenAxisTailIndex n c)
    (wt : DiamondEvenAxisTailIndex n d) :
    let f :=
      totalEOEELeftLiteralFamily
        (by omega : 0 < c) (by omega : 0 < d) x
    let Z :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    (((totalEOEELeftAmbientCoords hn hc2 hd2 x).2.2.2.1 zt).1 wt) =
      (E (Z.2.1 zt).1).2.1 wt := by
  dsimp only
  rw [totalEOEELeftLiteralFamily_eq_rootGauge]
  rw [show totalEOEELeftAmbientCoords hn hc2 hd2 x =
      dEOEEAfterGaugeCoords hn hc2 hd2
        (dLiteralRootGaugeEquiv
          (n := n) (c := c) (d := d)
          (by omega : 0 < c) (by omega : 0 < d) x) from rfl]
  exact dEOEEAfterGaugeCoords_ZWTail hn hc2 hd2 _ zt wt

private noncomputable def dTotalEOEEUniformConstraint
    {n c d : Nat} [NeZero n] :
    (PVec n c → (PVec n d → CyclicCube n) × CyclicCube n) →ₗ[F]
      (PVec n d → CyclicCube n) where
  toFun f w :=
    cubeDiffP (∑ z, (f z).1 w) +
      cubeDiffR (∑ z, (f z).2)
  map_add' f g := by
    funext w
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add,
      Finset.sum_add_distrib, map_add]
    abel
  map_smul' r f := by
    funext w
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd]
    rw [← Finset.smul_sum, ← Finset.smul_sum,
      map_smul, map_smul, smul_add]
    simp only [RingHom.id_apply]

@[simp] private theorem dCubeJKShift_cubeDiffP_apply
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffP (dCubeJKShiftEquiv u v X) i j k =
      cubeDiffP X i (j - u) (k - v) := by
  rw [EEOEInternal.cubeDiffP_apply,
    EEOEInternal.cubeDiffP_apply]
  simp only [dCubeJKShiftEquiv_apply]
  congr 2
  abel

@[simp] private theorem dCubeJKShift_cubeDiffR_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffR (dCubeJKShiftEquiv u 0 X) i j k =
      cubeDiffR X i (j - u) k := by
  rw [EEOEInternal.cubeDiffR_apply,
    EEOEInternal.cubeDiffR_apply]
  simp only [dCubeJKShiftEquiv_apply, sub_zero]
  congr 2
  · abel

@[simp] private theorem dVecSum_zero
    {n k : Nat} [NeZero n] :
    vecSum (zeroVec : Vec n k) = 0 := by
  unfold vecSum zeroVec
  simp

private theorem dLiteralLeft_mem_iff_uniform
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c) :
    x ∈ DiamondEvenPLeft n 1 c d ↔
      dTotalEOEEUniformConstraint
        (dLiteralRootGaugeEquiv hc hd x) = 0 := by
  simp only [DiamondEvenPLeft, LinearMap.mem_ker]
  constructor
  · intro hx
    funext wt i j k
    simp only [dTotalEOEEUniformConstraint,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
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
        ((diamondVecHeadTailEquiv hd).symm
          (k - vecSum wt, wt))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one hc hd
      x.1 x.2 zeroVec wt i j (k - vecSum wt)] at hpoint
    simp only [dVecSum_zero, add_zero, Pi.zero_apply] at hpoint
    simpa only [Pi.add_apply,
      dLiteralRootGaugeEquiv_B_eq,
      dLiteralRootGaugeEquiv_W_eq,
      dCubeJKShift_cubeDiffP_apply,
      dCubeJKShift_cubeDiffR_apply,
      sub_add_cancel] using hpoint
  · intro h
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew := diamondVecHeadTailEquiv (n := n) hd
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one hc hd
      x.1 x.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2]
    simp only [dVecSum_zero, add_zero, Pi.zero_apply]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun h (ew w).2)
            (ey y).1)
          sz)
        ((ew w).1 + vecSum (ew w).2)
    simp only [dTotalEOEEUniformConstraint,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hpoint
    rw [map_sum, map_sum, ← Finset.sum_add_distrib,
      Finset.sum_apply, Finset.sum_apply, Finset.sum_apply] at hpoint
    simpa only [Pi.add_apply,
      dLiteralRootGaugeEquiv_B_eq,
      dLiteralRootGaugeEquiv_W_eq,
      dCubeJKShift_cubeDiffP_apply,
      dCubeJKShift_cubeDiffR_apply,
      add_sub_cancel_right] using hpoint

private noncomputable def dEOEEWUniformConstraint
    {n d : Nat} [NeZero n] :
    ((PVec n d → CyclicCube n) × CyclicCube n) →ₗ[F]
      (PVec n d → CyclicCube n) where
  toFun x w := cubeDiffP (x.1 w) + cubeDiffR x.2
  map_add' x y := by
    funext w
    simp
    abel
  map_smul' r x := by
    funext w
    simp

private theorem dTotalUniform_eq_WUniform_outer
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c)
    (f : PVec n c →
      (PVec n d → CyclicCube n) × CyclicCube n) :
    let q :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := c)
        ((PVec n d → CyclicCube n) × CyclicCube n)
        hn hc2 f
    dTotalEOEEUniformConstraint f =
      dEOEEWUniformConstraint q.1.1 := by
  dsimp only
  funext w
  simp only [dTotalEOEEUniformConstraint,
    dEOEEWUniformConstraint, LinearMap.coe_mk, AddHom.coe_mk,
    diamondEvenAxisSrcCoordEquiv, pointedSrcEvenValueEquiv,
    LinearEquiv.coe_mk, pointedSrcEvenValueRead]
  simp only [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]

private theorem dCast_even_eq_zero
    {m : Nat} (hm : Even m) :
    (m : F) = 0 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  exact F_add_self (q : F)

private theorem dCast_odd_eq_one
    {m : Nat} (hm : Odd m) :
    (m : F) = 1 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem dSum_const_even
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = 0 := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, dCast_even_eq_zero heven, zero_smul]

private theorem dSum_const_odd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, dCast_odd_eq_one hodd, one_smul]

private theorem dEOEEWUniformConstraint_coords
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (f : PVec n d → CyclicCube n) (W : CyclicCube n) :
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    let x := E f
    let y := E (dEOEEWUniformConstraint (f, W))
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
      dSum_const_even heven, add_zero]
  · change
      (∑ t : DiamondEvenAxisTailIndex n d,
          (cubeDiffP (f t.1) + cubeDiffR W)) =
        cubeDiffP
            (∑ t : DiamondEvenAxisTailIndex n d, f t.1) +
          cubeDiffR W
    rw [Finset.sum_add_distrib, ← map_sum,
      dSum_const_odd hodd]
  · intro t
    change
      (cubeDiffP (f t.1) + cubeDiffR W) +
          ∑ u : DiamondEvenAxisTailIndex n d,
            (cubeDiffP (f u.1) + cubeDiffR W) =
        cubeDiffP
          (f t.1 +
            ∑ u : DiamondEvenAxisTailIndex n d, f u.1)
    rw [Finset.sum_add_distrib, ← map_sum,
      dSum_const_odd hodd, map_add]
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

private theorem dEOEEWUniformConstraint_eq_zero_iff
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (f g : PVec n d → CyclicCube n)
    (W V : CyclicCube n) :
    let E :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2
    let x := E f
    let z := E g
    dEOEEWUniformConstraint (f, W) = 0 ↔
      diamondEOEELeftConstraintMap
        ((((x.1.1, x.1.2), (z.1.1, z.1.2)), (W, V)) :
          DiamondEOEELeftAmbient n) = 0 ∧
        ∀ t, cubeDiffP (x.2.1 t) = 0 := by
  dsimp only
  let E :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let x := E f
  let y := E (dEOEEWUniformConstraint (f, W))
  have hcoords :=
    dEOEEWUniformConstraint_coords hn hd2 f W
  constructor
  · intro hzero
    have hy : y = 0 := by
      change E (dEOEEWUniformConstraint (f, W)) = 0
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

theorem totalEOEELeft_mem_iff
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 c d × WFun4 n 1 1 c) :
    x ∈ DiamondEvenPLeft n 1 c d ↔
      (totalEOEELeftAmbientCoords hn hc2 hd2 x).1 ∈
          DiamondEOEELeftSource n ∧
        ∀ t,
          cubeDiffP
            (((totalEOEELeftAmbientCoords hn hc2 hd2 x).2.1.1 t).1) =
              0 := by
  rw [dLiteralLeft_mem_iff_uniform (by omega) (by omega) x]
  let f :=
    dLiteralRootGaugeEquiv
      (n := n) (c := c) (d := d)
      (by omega : 0 < c) (by omega : 0 < d) x
  let Z :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c)
      ((PVec n d → CyclicCube n) × CyclicCube n)
      hn hc2 f
  have houter :=
    dTotalUniform_eq_WUniform_outer
      (n := n) (c := c) (d := d) hn hc2 f
  change
    dTotalEOEEUniformConstraint f = 0 ↔
      (totalEOEELeftAmbientCoords hn hc2 hd2 x).1 ∈
          DiamondEOEELeftSource n ∧
        ∀ t,
          cubeDiffP
            (((totalEOEELeftAmbientCoords hn hc2 hd2 x).2.1.1 t).1) =
              0
  rw [houter]
  have hiff :=
    dEOEEWUniformConstraint_eq_zero_iff
      (n := n) (d := d) hn hd2
      Z.1.1.1 Z.1.2.1 Z.1.1.2 Z.1.2.2
  change
    dEOEEWUniformConstraint Z.1.1 = 0 ↔
      diamondEOEELeftConstraintMap
          (totalEOEELeftAmbientCoords hn hc2 hd2 x).1 = 0 ∧
        ∀ t,
          cubeDiffP
            (((totalEOEELeftAmbientCoords hn hc2 hd2 x).2.1.1 t).1) =
              0
  rw [show totalEOEELeftAmbientCoords hn hc2 hd2 x =
      dEOEEAfterGaugeCoords hn hc2 hd2 f from rfl]
  simpa only [Z,
    dEOEEAfterGaugeCoords_scalar,
    dEOEEAfterGaugeCoords_WTail_fst] using hiff

noncomputable abbrev TotalEOEELeftSourceTarget
    (n c d : Nat) [NeZero n] :=
  DiamondEOEELeftSource n ×
    (DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) ×
      (DiamondEvenAxisValueTailZero n c (DiamondEOOELeftAmbient n) ×
        DiamondMixedTailZero n c d (CyclicCube n)))

private noncomputable def dLeftWTailPack
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d
      (CyclicCube n × CyclicCube n))
    (hu : ∀ t, cubeDiffP (u.1 t).1 = 0) :
    DiamondEvenAxisValueTailZero n d (DiamondEOEEWLeftSource n) :=
  ⟨fun t =>
      (⟨(u.1 t).1, LinearMap.mem_ker.mpr (hu t)⟩, (u.1 t).2),
    by
      apply LinearMap.mem_ker.mpr
      change
        (∑ t,
          ((⟨(u.1 t).1, LinearMap.mem_ker.mpr (hu t)⟩ :
              EEOEInternal.PBlockLeft n),
            (u.1 t).2)) = 0
      have hsum := pointedValueTailZero_sum u
      apply Prod.ext
      · apply Subtype.ext
        simpa only [Submodule.coe_sum, Prod.fst_sum] using
          congrArg Prod.fst hsum
      · simpa only [Prod.snd_sum] using congrArg Prod.snd hsum⟩

private noncomputable def dLeftWTailForget
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d
        (DiamondEOEEWLeftSource n) →ₗ[F]
      DiamondEvenAxisValueTailZero n d
        (CyclicCube n × CyclicCube n) where
  toFun u :=
    ⟨fun t => ((u.1 t).1.1, (u.1 t).2), by
      apply LinearMap.mem_ker.mpr
      have hu := pointedValueTailZero_sum u
      change
        (∑ t, (((u.1 t).1.1, (u.1 t).2) :
          CyclicCube n × CyclicCube n)) = 0
      apply Prod.ext
      · have hfst := congrArg Prod.fst hu
        simpa only [Prod.fst_sum, Submodule.coe_sum] using
          congrArg Subtype.val hfst
      · simpa only [Prod.snd_sum] using congrArg Prod.snd hu⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

noncomputable def leftSourceEquiv
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    DiamondEvenPLeft n 1 c d ≃ₗ[F]
      TotalEOEELeftSourceTarget n c d where
  toFun l := by
    let q := totalEOEELeftAmbientCoords hn hc2 hd2 l.1
    have hq := (totalEOEELeft_mem_iff hn hc2 hd2 l.1).mp l.2
    exact
      (⟨q.1, hq.1⟩,
        (dLeftWTailPack q.2.1 hq.2, (q.2.2.1, q.2.2.2)))
  invFun q := by
    let raw :
        DiamondEOEELeftAmbient n ×
          (DiamondEvenAxisValueTailZero n d
              (CyclicCube n × CyclicCube n) ×
            (DiamondEvenAxisValueTailZero n c
                (DiamondEOOELeftAmbient n) ×
              DiamondMixedTailZero n c d (CyclicCube n))) :=
      (q.1.1,
        (dLeftWTailForget q.2.1, (q.2.2.1, q.2.2.2)))
    let l := (totalEOEELeftAmbientCoords hn hc2 hd2).symm raw
    refine ⟨l, (totalEOEELeft_mem_iff hn hc2 hd2 l).mpr ?_⟩
    have hread : totalEOEELeftAmbientCoords hn hc2 hd2 l = raw :=
      (totalEOEELeftAmbientCoords hn hc2 hd2).apply_symm_apply raw
    refine ⟨?_, ?_⟩
    · have hfst := congrArg Prod.fst hread
      rw [hfst]
      exact q.1.2
    · intro t
      have ht := LinearMap.mem_ker.mp (q.2.1.1 t).1.2
      have htail := congrArg (fun z => z.2.1.1 t) hread
      change
        cubeDiffP
            (((totalEOEELeftAmbientCoords hn hc2 hd2 l).2.1.1 t).1) =
          0
      change cubeDiffP ((raw.2.1.1 t).1) = 0 at ht
      have htailFst := congrArg Prod.fst htail
      rw [htailFst]
      exact ht
  left_inv l := by
    apply Subtype.ext
    exact (totalEOEELeftAmbientCoords hn hc2 hd2).symm_apply_apply l.1
  right_inv q := by
    have hread :=
      (totalEOEELeftAmbientCoords hn hc2 hd2).apply_symm_apply
        (q.1.1,
          (dLeftWTailForget q.2.1, (q.2.2.1, q.2.2.2)))
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · apply Prod.ext
      · apply Subtype.ext
        funext t
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 t).1) hread
        · exact congrArg (fun z => (z.2.1.1 t).2) hread
      · apply Prod.ext
        · exact congrArg (fun z => z.2.2.1) hread
        · exact congrArg (fun z => z.2.2.2) hread
  map_add' l l' := by
    have hmap :=
      (totalEOEELeftAmbientCoords hn hc2 hd2).map_add l.1 l'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext t
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 t).1) hmap
        · exact congrArg (fun z => (z.2.1.1 t).2) hmap
      · apply Prod.ext
        · exact congrArg (fun z => z.2.2.1) hmap
        · exact congrArg (fun z => z.2.2.2) hmap
  map_smul' r l := by
    have hmap :=
      (totalEOEELeftAmbientCoords hn hc2 hd2).map_smul r l.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext t
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg (fun z => (z.2.1.1 t).1) hmap
        · exact congrArg (fun z => (z.2.1.1 t).2) hmap
      · apply Prod.ext
        · exact congrArg (fun z => z.2.2.1) hmap
        · exact congrArg (fun z => z.2.2.2) hmap


end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP
