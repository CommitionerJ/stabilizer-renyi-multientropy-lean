import Core4loop.SquareDiagonal.EvenP.TotalEOOE
import Core4loop.SquareDiagonal.EvenP.TotalEOEO
import Core4loop.SquareDiagonal.EvenP.EOEEWBlock

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

namespace TailCoordHelpers

noncomputable def tailZeroCongr
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (e : U ≃ₗ[F] V) :
    PointedValueTailZero S U s0 ≃ₗ[F]
      PointedValueTailZero S V s0 where
  toFun x :=
    ⟨fun t => e (x.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, e (x.1 t)) = 0
      rw [← map_sum, pointedValueTailZero_sum x, map_zero]⟩
  invFun x :=
    ⟨fun t => e.symm (x.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, e.symm (x.1 t)) = 0
      rw [← map_sum, pointedValueTailZero_sum x, map_zero]⟩
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

noncomputable def tailZeroProdEquiv
    {S U V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] :
    PointedValueTailZero S (U × V) s0 ≃ₗ[F]
      (PointedValueTailZero S U s0 ×
        PointedValueTailZero S V s0) where
  toFun x :=
    (⟨fun t => (x.1 t).1, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (x.1 t).1) = 0
        simpa only [Prod.fst_sum] using
          congrArg Prod.fst (pointedValueTailZero_sum x)⟩,
      ⟨fun t => (x.1 t).2, by
        apply LinearMap.mem_ker.mpr
        change (∑ t, (x.1 t).2) = 0
        simpa only [Prod.snd_sum] using
          congrArg Prod.snd (pointedValueTailZero_sum x)⟩)
  invFun x :=
    ⟨fun t => (x.1.1 t, x.2.1 t), by
      apply LinearMap.mem_ker.mpr
      change (∑ t, (x.1.1 t, x.2.1 t)) = 0
      apply Prod.ext
      · rw [Prod.fst_sum]
        exact pointedValueTailZero_sum x.1
      · rw [Prod.snd_sum]
        exact pointedValueTailZero_sum x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' r x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

noncomputable abbrev NestedSrcEvenTarget
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U] :=
  ((U × U) × (U × U)) ×
    (PointedValueTailZero T (U × U) t0 ×
      (PointedValueTailZero S (U × U) s0 ×
        PointedValueTailZero S
          (PointedValueTailZero T U t0) s0))

private noncomputable def nestedSrcRawEquiv
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (hS : Even (Fintype.card S))
    (hT : Even (Fintype.card T)) :
    (S → T → U) ≃ₗ[F]
      ((PointedEvenValueCoords T U t0 ×
          PointedEvenValueCoords T U t0) ×
        PointedValueTailZero S
          (PointedEvenValueCoords T U t0) s0) :=
  (pointedSrcEvenValueEquiv S (T → U) s0 hS).trans
    (((pointedSrcEvenValueEquiv T U t0 hT).prodCongr
        (pointedSrcEvenValueEquiv T U t0 hT)).prodCongr
      (tailZeroCongr s0
        (pointedSrcEvenValueEquiv T U t0 hT)))

private noncomputable def nestedSrcReassocEquiv
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U] :
    ((PointedEvenValueCoords T U t0 ×
        PointedEvenValueCoords T U t0) ×
      PointedValueTailZero S
        (PointedEvenValueCoords T U t0) s0) ≃ₗ[F]
      NestedSrcEvenTarget S T U s0 t0 where
  toFun x :=
    let w :=
      (tailZeroProdEquiv (S := T) (U := U) (V := U) t0).symm
        (x.1.1.2, x.1.2.2)
    let zm :=
      tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0 x.2
    ((x.1.1.1, x.1.2.1), (w, (zm.1, zm.2)))
  invFun x :=
    let w :=
      tailZeroProdEquiv (S := T) (U := U) (V := U) t0 x.2.1
    let zm :=
      (tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0).symm
          (x.2.2.1, x.2.2.2)
    (((x.1.1, w.1), (x.1.2, w.2)), zm)
  left_inv x := by
    dsimp only
    have hw :=
      (tailZeroProdEquiv
        (S := T) (U := U) (V := U) t0).apply_symm_apply
          (x.1.1.2, x.1.2.2)
    have hzm :=
      (tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0).symm_apply_apply x.2
    rw [hw, hzm]
  right_inv x := by
    dsimp only
    have hw :=
      (tailZeroProdEquiv
        (S := T) (U := U) (V := U) t0).symm_apply_apply x.2.1
    have hzm :=
      (tailZeroProdEquiv
        (S := S) (U := U × U)
        (V := PointedValueTailZero T U t0) s0).apply_symm_apply
          (x.2.2.1, x.2.2.2)
    rw [hw, hzm]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact
          (tailZeroProdEquiv
            (S := T) (U := U) (V := U) t0).symm.map_add
              (x.1.1.2, x.1.2.2) (y.1.1.2, y.1.2.2)
      · exact
          (tailZeroProdEquiv
            (S := S) (U := U × U)
            (V := PointedValueTailZero T U t0) s0).map_add x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact
          (tailZeroProdEquiv
            (S := T) (U := U) (V := U) t0).symm.map_smul
              r (x.1.1.2, x.1.2.2)
      · exact
          (tailZeroProdEquiv
            (S := S) (U := U × U)
            (V := PointedValueTailZero T U t0) s0).map_smul r x.2

noncomputable def nestedSrcEvenValueEquiv
    (S T U : Type*) [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [Fintype T] (t0 : T)
    [Fintype (PointedTail T t0)]
    [AddCommGroup U] [Module F U]
    (hS : Even (Fintype.card S))
    (hT : Even (Fintype.card T)) :
    (S → T → U) ≃ₗ[F]
      NestedSrcEvenTarget S T U s0 t0 :=
  (nestedSrcRawEquiv S T U s0 t0 hS hT).trans
    (nestedSrcReassocEquiv S T U s0 t0)

end TailCoordHelpers

/-!
This nonproduction scratch isolates the literal T3.5 root-family and gauge
layer.  In particular, the literal W type is `WFun4 n 1 1 c`, not
`WFun4 n 1 c 1`.
-/

noncomputable def bRootFamilyEquiv
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    BFun4 n 1 c d ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) :=
  diamondBRootCubeEquiv hc hd

noncomputable def wRootFamilyEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    WFun4 n 1 1 c ≃ₗ[F]
      (PVec n c → CyclicCube n) where
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

noncomputable def aRootFamilyEquiv
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    AFun4 n 1 c d ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) where
  toFun A zt wt :=
    diamondARootCubeEquiv Nat.zero_lt_one hc hd A zeroVec zt wt
  invFun f :=
    (diamondARootCubeEquiv Nat.zero_lt_one hc hd).symm
      (fun _ zt wt => f zt wt)
  left_inv A := by
    apply
      (diamondARootCubeEquiv
        Nat.zero_lt_one hc hd).injective
    funext yt zt wt
    rw [pVec_one_eq_zeroVec yt]
    exact
      (diamondARootCubeEquiv
        (n := n) Nat.zero_lt_one hc hd).apply_symm_apply _ ▸ rfl
  right_inv f := by
    funext zt wt
    exact congrFun
      (congrFun
        (congrFun
          ((diamondARootCubeEquiv Nat.zero_lt_one hc hd).apply_symm_apply
            (fun _ zt wt => f zt wt))
          zeroVec)
        zt)
      wt
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem bRootFamilyEquiv_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    bRootFamilyEquiv hc hd B zt wt i j k =
      diamondBRootCubeEquiv hc hd B zt wt i j k :=
  rfl

@[simp] theorem wRootFamilyEquiv_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (W : WFun4 n 1 1 c) (zt : PVec n c) (i j k : I n) :
    wRootFamilyEquiv hc W zt i j k =
      diamondWRootCubeEquiv Nat.zero_lt_one hc W zeroVec zt i j k :=
  rfl

@[simp] theorem aRootFamilyEquiv_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    aRootFamilyEquiv hc hd A zt wt i j k =
      diamondARootCubeEquiv Nat.zero_lt_one hc hd
        A zeroVec zt wt i j k :=
  rfl

noncomputable def cubeJShiftEquiv
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

noncomputable def cubeJKShiftEquiv
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

@[simp] theorem cubeJShiftEquiv_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeJShiftEquiv u X i j k = X i (j - u) k :=
  rfl

@[simp] theorem cubeJShiftEquiv_symm_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    (cubeJShiftEquiv u).symm X i j k = X i (j + u) k :=
  rfl

@[simp] theorem cubeJKShiftEquiv_apply
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeJKShiftEquiv u v X i j k = X i (j - u) (k - v) :=
  rfl

@[simp] theorem cubeJKShiftEquiv_symm_apply
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n)
    (i j k : I n) :
    (cubeJKShiftEquiv u v).symm X i j k =
      X i (j + u) (k + v) :=
  rfl

noncomputable def jGaugeFamilyEquiv
    {n c : Nat} [NeZero n] :
    (PVec n c → CyclicCube n) ≃ₗ[F]
      (PVec n c → CyclicCube n) where
  toFun f zt := cubeJShiftEquiv (vecSum zt) (f zt)
  invFun f zt := (cubeJShiftEquiv (vecSum zt)).symm (f zt)
  left_inv f := by
    funext zt
    exact (cubeJShiftEquiv (vecSum zt)).symm_apply_apply (f zt)
  right_inv f := by
    funext zt
    exact (cubeJShiftEquiv (vecSum zt)).apply_symm_apply (f zt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def jkGaugeBiFamilyEquiv
    {n c d : Nat} [NeZero n] :
    (PVec n c → PVec n d → CyclicCube n) ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) where
  toFun f zt wt :=
    cubeJKShiftEquiv (vecSum zt) (vecSum wt) (f zt wt)
  invFun f zt wt :=
    (cubeJKShiftEquiv (vecSum zt) (vecSum wt)).symm (f zt wt)
  left_inv f := by
    funext zt wt
    exact
      (cubeJKShiftEquiv
        (vecSum zt) (vecSum wt)).symm_apply_apply (f zt wt)
  right_inv f := by
    funext zt wt
    exact
      (cubeJKShiftEquiv
        (vecSum zt) (vecSum wt)).apply_symm_apply (f zt wt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def bGaugedRootFamilyEquiv
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    BFun4 n 1 c d ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) :=
  (bRootFamilyEquiv hc hd).trans
    (jkGaugeBiFamilyEquiv (n := n) (c := c) (d := d))

noncomputable def wGaugedRootFamilyEquiv
    {n c : Nat} [NeZero n] (hc : 0 < c) :
    WFun4 n 1 1 c ≃ₗ[F]
      (PVec n c → CyclicCube n) :=
  (wRootFamilyEquiv hc).trans
    (jGaugeFamilyEquiv (n := n) (c := c))

noncomputable def aGaugedRootFamilyEquiv
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d) :
    AFun4 n 1 c d ≃ₗ[F]
      (PVec n c → PVec n d → CyclicCube n) :=
  (aRootFamilyEquiv hc hd).trans
    (jkGaugeBiFamilyEquiv (n := n) (c := c) (d := d))

@[simp] theorem bGaugedRootFamilyEquiv_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    bGaugedRootFamilyEquiv hc hd B zt wt i j k =
      diamondBRootCubeEquiv hc hd B zt wt
        i (j - vecSum zt) (k - vecSum wt) :=
  rfl

@[simp] theorem wGaugedRootFamilyEquiv_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (W : WFun4 n 1 1 c) (zt : PVec n c) (i j k : I n) :
    wGaugedRootFamilyEquiv hc W zt i j k =
      diamondWRootCubeEquiv Nat.zero_lt_one hc W zeroVec zt
        i (j - vecSum zt) k :=
  rfl

@[simp] theorem aGaugedRootFamilyEquiv_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n 1 c d) (zt : PVec n c) (wt : PVec n d)
    (i j k : I n) :
    aGaugedRootFamilyEquiv hc hd A zt wt i j k =
      diamondARootCubeEquiv Nat.zero_lt_one hc hd
        A zeroVec zt wt i (j - vecSum zt) (k - vecSum wt) :=
  rfl

@[simp] theorem bGaugedRootFamilyEquiv_symm_root_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (f : PVec n c → PVec n d → CyclicCube n)
    (zt : PVec n c) (wt : PVec n d) (i j k : I n) :
    diamondBRootCubeEquiv hc hd
        ((bGaugedRootFamilyEquiv hc hd).symm f) zt wt i j k =
      f zt wt i (j + vecSum zt) (k + vecSum wt) := by
  change
    bRootFamilyEquiv hc hd
        ((bRootFamilyEquiv hc hd).symm
          ((jkGaugeBiFamilyEquiv
            (n := n) (c := c) (d := d)).symm f))
        zt wt i j k =
      _
  rw [(bRootFamilyEquiv hc hd).apply_symm_apply]
  rfl

@[simp] theorem wGaugedRootFamilyEquiv_symm_root_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (f : PVec n c → CyclicCube n)
    (zt : PVec n c) (i j k : I n) :
    diamondWRootCubeEquiv Nat.zero_lt_one hc
        ((wGaugedRootFamilyEquiv hc).symm f)
        zeroVec zt i j k =
      f zt i (j + vecSum zt) k := by
  change
    wRootFamilyEquiv hc
        ((wRootFamilyEquiv hc).symm
          ((jGaugeFamilyEquiv (n := n) (c := c)).symm f))
        zt i j k =
      _
  rw [(wRootFamilyEquiv hc).apply_symm_apply]
  rfl

@[simp] theorem aGaugedRootFamilyEquiv_symm_root_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (f : PVec n c → PVec n d → CyclicCube n)
    (zt : PVec n c) (wt : PVec n d) (i j k : I n) :
    diamondARootCubeEquiv Nat.zero_lt_one hc hd
        ((aGaugedRootFamilyEquiv hc hd).symm f)
        zeroVec zt wt i j k =
      f zt wt i (j + vecSum zt) (k + vecSum wt) := by
  change
    aRootFamilyEquiv hc hd
        ((aRootFamilyEquiv hc hd).symm
          ((jkGaugeBiFamilyEquiv
            (n := n) (c := c) (d := d)).symm f))
        zt wt i j k =
      _
  rw [(aRootFamilyEquiv hc hd).apply_symm_apply]
  rfl

theorem bGaugedRootFamilyEquiv_symm_apply_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) :
    (bGaugedRootFamilyEquiv hc hd).symm
        (bGaugedRootFamilyEquiv hc hd B) = B :=
  (bGaugedRootFamilyEquiv hc hd).symm_apply_apply B

theorem wGaugedRootFamilyEquiv_symm_apply_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (W : WFun4 n 1 1 c) :
    (wGaugedRootFamilyEquiv hc).symm
        (wGaugedRootFamilyEquiv hc W) = W :=
  (wGaugedRootFamilyEquiv hc).symm_apply_apply W

theorem aGaugedRootFamilyEquiv_symm_apply_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (A : AFun4 n 1 c d) :
    (aGaugedRootFamilyEquiv hc hd).symm
        (aGaugedRootFamilyEquiv hc hd A) = A :=
  (aGaugedRootFamilyEquiv hc hd).symm_apply_apply A

theorem bGaugedRootFamilyEquiv_apply_symm_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (f : PVec n c → PVec n d → CyclicCube n) :
    bGaugedRootFamilyEquiv hc hd
        ((bGaugedRootFamilyEquiv hc hd).symm f) = f :=
  (bGaugedRootFamilyEquiv hc hd).apply_symm_apply f

theorem wGaugedRootFamilyEquiv_apply_symm_apply
    {n c : Nat} [NeZero n] (hc : 0 < c)
    (f : PVec n c → CyclicCube n) :
    wGaugedRootFamilyEquiv hc
        ((wGaugedRootFamilyEquiv hc).symm f) = f :=
  (wGaugedRootFamilyEquiv hc).apply_symm_apply f

theorem aGaugedRootFamilyEquiv_apply_symm_apply
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (f : PVec n c → PVec n d → CyclicCube n) :
    aGaugedRootFamilyEquiv hc hd
        ((aGaugedRootFamilyEquiv hc hd).symm f) = f :=
  (aGaugedRootFamilyEquiv hc hd).apply_symm_apply f

theorem cubeJShift_cubeDiffP
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeJShiftEquiv u (cubeDiffP X) =
      cubeDiffP (cubeJShiftEquiv u X) := by
  funext i j k
  simp only [cubeJShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffP_apply, EEOEInternal.cubeDiffP_apply]
  congr 2
  abel

theorem cubeJShift_cubeDiffR
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeJShiftEquiv u (cubeDiffR X) =
      cubeDiffR (cubeJShiftEquiv u X) := by
  funext i j k
  simp only [cubeJShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffR_apply, EEOEInternal.cubeDiffR_apply]
  congr 2
  abel

theorem cubeJShift_cubeDiffI
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeJShiftEquiv u (cubeDiffI X) =
      cubeDiffI (cubeJShiftEquiv u X) := by
  funext i j k
  simp only [cubeJShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffI_apply, EEOEInternal.cubeDiffI_apply]
  rfl

theorem cubeJShift_cubeDiffK
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeJShiftEquiv u (cubeDiffK X) =
      cubeDiffK (cubeJShiftEquiv u X) := by
  funext i j k
  simp only [cubeJShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffK_apply, EEOEInternal.cubeDiffK_apply]
  rfl

theorem cubeJShift_cubeDiffJInv
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n) :
    cubeJShiftEquiv u (cubeDiffJInv X) =
      cubeDiffJInv (cubeJShiftEquiv u X) := by
  funext i j k
  simp only [cubeJShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffJInv_apply,
    EEOEInternal.cubeDiffJInv_apply]
  congr 2
  abel

theorem cubeJKShift_cubeDiffP
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n) :
    cubeJKShiftEquiv u v (cubeDiffP X) =
      cubeDiffP (cubeJKShiftEquiv u v X) := by
  funext i j k
  simp only [cubeJKShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffP_apply, EEOEInternal.cubeDiffP_apply]
  congr 2
  abel

theorem cubeJKShift_cubeDiffR
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n) :
    cubeJKShiftEquiv u v (cubeDiffR X) =
      cubeDiffR (cubeJKShiftEquiv u v X) := by
  funext i j k
  simp only [cubeJKShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffR_apply, EEOEInternal.cubeDiffR_apply]
  congr 2 <;> abel

theorem cubeJKShift_cubeDiffI
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n) :
    cubeJKShiftEquiv u v (cubeDiffI X) =
      cubeDiffI (cubeJKShiftEquiv u v X) := by
  funext i j k
  simp only [cubeJKShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffI_apply, EEOEInternal.cubeDiffI_apply]
  rfl

theorem cubeJKShift_cubeDiffK
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n) :
    cubeJKShiftEquiv u v (cubeDiffK X) =
      cubeDiffK (cubeJKShiftEquiv u v X) := by
  funext i j k
  simp only [cubeJKShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffK_apply, EEOEInternal.cubeDiffK_apply]
  congr 2
  abel

theorem cubeJKShift_cubeDiffJInv
    {n : Nat} [NeZero n] (u v : I n) (X : CyclicCube n) :
    cubeJKShiftEquiv u v (cubeDiffJInv X) =
      cubeDiffJInv (cubeJKShiftEquiv u v X) := by
  funext i j k
  simp only [cubeJKShiftEquiv_apply]
  rw [EEOEInternal.cubeDiffJInv_apply,
    EEOEInternal.cubeDiffJInv_apply]
  congr 2
  abel

theorem cubeJShift_pairing_same
    {n : Nat} [NeZero n] (u : I n) (X Y : CyclicCube n) :
    cubeDot (cubeJShiftEquiv u X) (cubeJShiftEquiv u Y) =
      cubeDot X Y := by
  classical
  unfold cubeDot
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.addRight (-u)) (Equiv.refl (I n)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, cubeJShiftEquiv, sub_eq_add_neg]

theorem cubeJKShift_pairing_same
    {n : Nat} [NeZero n] (u v : I n) (X Y : CyclicCube n) :
    cubeDot (cubeJKShiftEquiv u v X) (cubeJKShiftEquiv u v Y) =
      cubeDot X Y := by
  classical
  unfold cubeDot
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.refl (I n))
      (Equiv.prodCongr (Equiv.addRight (-u)) (Equiv.addRight (-v)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, cubeJKShiftEquiv, sub_eq_add_neg]

theorem b_a_gauged_root_pairing
    {n c d : Nat} [NeZero n] (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (A : AFun4 n 1 c d)
    (zt : PVec n c) (wt : PVec n d) :
    cubeDot
        (bGaugedRootFamilyEquiv hc hd B zt wt)
        (aGaugedRootFamilyEquiv hc hd A zt wt) =
      cubeDot
        (bRootFamilyEquiv hc hd B zt wt)
        (aRootFamilyEquiv hc hd A zt wt) := by
  exact cubeJKShift_pairing_same
    (vecSum zt) (vecSum wt)
    (bRootFamilyEquiv hc hd B zt wt)
    (aRootFamilyEquiv hc hd A zt wt)


end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP
