import Core4loop.SquareDiagonal.EvenP.EEOE
import Core4loop.SquareDiagonal.EvenP.CubeReindex
import Core4loop.SquareDiagonal.EvenP.TailPairing

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
-- The frozen completion-first source certificate uses one file-wide budget.
set_option linter.style.setOption false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 500000

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace T37LeftP0

private theorem cast_card_eq_zero_of_even
    {m : Nat} (hm : Even m) : (m : F) = 0 := by
  rcases hm with ⟨q, hq⟩
  rw [hq]
  push_cast
  exact F_add_self _

private theorem sum_const_eq_zero_of_even
    {S V : Type*} [Fintype S]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S)) (v : V) :
    (∑ _ : S, v) = 0 := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    cast_card_eq_zero_of_even heven, zero_smul]

private theorem sum_src_build_eq_sigma
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommGroup V] [Module F V]
    (heven : Even (Fintype.card S))
    (x : PointedEvenValueCoords S V s0) :
    (∑ s : S, pointedSrcEvenValueBuild S V s0 x s) = x.1.1 := by
  have h :=
    congrArg (fun q => q.1.1)
      ((pointedSrcEvenValueEquiv S V s0 heven).apply_symm_apply x)
  simpa only [pointedSrcEvenValueEquiv_apply_sigma] using h

private theorem add_eq_zero_of_eq
    {V : Type*} [AddCommGroup V] [Module F V]
    {x y : V} (h : x = y) :
    x + y = 0 := by
  exact (add_eq_zero_iff_eq_of_F_module x y).2 h

theorem totalEEOE_gauged_coords_iff
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (Bc :
      PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d))
    (Wc :
      PointedEvenValueCoords
        (PVec n b) (CyclicCube n) (zeroVec : PVec n b)) :
    (∀ s : PVec n b, ∀ t : PVec n d,
      cubeDiffP
          (pointedSrcEvenValueBuild
            (PVec n d) (CyclicCube n) (zeroVec : PVec n d) Bc t) +
        cubeDiffR
          (pointedSrcEvenValueBuild
            (PVec n b) (CyclicCube n) (zeroVec : PVec n b) Wc s) =
        0) ↔
      cubeDiffP Bc.1.1 = 0 ∧
      cubeDiffR Wc.1.1 = 0 ∧
      cubeDiffP Bc.1.2 + cubeDiffR Wc.1.2 = 0 ∧
      (∀ t : PointedTail (PVec n d) (zeroVec : PVec n d),
        cubeDiffP (Bc.2.1 t) = 0) ∧
      (∀ s : PointedTail (PVec n b) (zeroVec : PVec n b),
        cubeDiffR (Wc.2.1 s) = 0) := by
  let EB :=
    pointedSrcEvenValueEquiv
      (PVec n d) (CyclicCube n) (zeroVec : PVec n d)
      (even_card_PVec hn hd2)
  let EW :=
    pointedSrcEvenValueEquiv
      (PVec n b) (CyclicCube n) (zeroVec : PVec n b)
      (even_card_PVec hn hb2)
  let B : PVec n d → CyclicCube n := EB.symm Bc
  let W : PVec n b → CyclicCube n := EW.symm Wc
  have hBsum : (∑ t : PVec n d, B t) = Bc.1.1 := by
    exact
      sum_src_build_eq_sigma
        (zeroVec : PVec n d) (even_card_PVec hn hd2) Bc
  have hWsum : (∑ s : PVec n b, W s) = Wc.1.1 := by
    exact
      sum_src_build_eq_sigma
        (zeroVec : PVec n b) (even_card_PVec hn hb2) Wc
  have hB0 : B (zeroVec : PVec n d) = Bc.1.1 + Bc.1.2 := by
    exact pointedSrcEvenValueBuild_at_point (zeroVec : PVec n d) Bc
  have hW0 : W (zeroVec : PVec n b) = Wc.1.1 + Wc.1.2 := by
    exact pointedSrcEvenValueBuild_at_point (zeroVec : PVec n b) Wc
  change
    (∀ s : PVec n b, ∀ t : PVec n d,
      cubeDiffP (B t) + cubeDiffR (W s) = 0) ↔ _
  constructor
  · intro h
    have hPBsum :
        cubeDiffP (∑ t : PVec n d, B t) = 0 := by
      have hsum :
          (∑ t : PVec n d,
              (cubeDiffP (B t) +
                cubeDiffR (W (zeroVec : PVec n b)))) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        exact h (zeroVec : PVec n b) t
      rw [Finset.sum_add_distrib, ← map_sum,
        sum_const_eq_zero_of_even (even_card_PVec hn hd2),
        add_zero] at hsum
      exact hsum
    have hP : cubeDiffP Bc.1.1 = 0 := by
      rw [hBsum] at hPBsum
      exact hPBsum
    have hRWsum :
        cubeDiffR (∑ s : PVec n b, W s) = 0 := by
      have hsum :
          (∑ s : PVec n b,
              (cubeDiffP (B (zeroVec : PVec n d)) +
                cubeDiffR (W s))) = 0 := by
        apply Finset.sum_eq_zero
        intro s _
        exact h s (zeroVec : PVec n d)
      rw [Finset.sum_add_distrib,
        sum_const_eq_zero_of_even (even_card_PVec hn hb2),
        ← map_sum, zero_add] at hsum
      exact hsum
    have hR : cubeDiffR Wc.1.1 = 0 := by
      rw [hWsum] at hRWsum
      exact hRWsum
    have hK : cubeDiffP Bc.1.2 + cubeDiffR Wc.1.2 = 0 := by
      have h00 := h (zeroVec : PVec n b) (zeroVec : PVec n d)
      rw [hB0, hW0, map_add, map_add, hP, hR] at h00
      simpa only [zero_add, add_zero, add_assoc] using h00
    have hBTail :
        ∀ t : PointedTail (PVec n d) (zeroVec : PVec n d),
          cubeDiffP (Bc.2.1 t) = 0 := by
      intro t
      have ht := h (zeroVec : PVec n b) t.1
      have h0 := h (zeroVec : PVec n b) (zeroVec : PVec n d)
      have hBt :
          B t.1 = Bc.2.1 t + Bc.1.2 := by
        exact pointedSrcEvenValueBuild_at_tail
          (zeroVec : PVec n d) Bc t
      rw [hBt, map_add] at ht
      rw [hB0, map_add] at h0
      have ht' :
          cubeDiffP (Bc.2.1 t) +
                (cubeDiffP Bc.1.2 +
                  cubeDiffR (W (zeroVec : PVec n b))) =
            (0 : CyclicCube n) := by
        simpa only [add_assoc] using ht
      have h0' :
          cubeDiffP Bc.1.1 +
                (cubeDiffP Bc.1.2 +
                  cubeDiffR (W (zeroVec : PVec n b))) =
            (0 : CyclicCube n) := by
        simpa only [add_assoc] using h0
      have heq :
          cubeDiffP (Bc.2.1 t) +
                (cubeDiffP Bc.1.2 +
                  cubeDiffR (W (zeroVec : PVec n b))) =
            cubeDiffP Bc.1.1 +
                (cubeDiffP Bc.1.2 +
                  cubeDiffR (W (zeroVec : PVec n b))) := by
        exact ht'.trans h0'.symm
      exact (add_right_cancel heq).trans hP
    have hWTail :
        ∀ s : PointedTail (PVec n b) (zeroVec : PVec n b),
          cubeDiffR (Wc.2.1 s) = 0 := by
      intro s
      have hs := h s.1 (zeroVec : PVec n d)
      have h0 := h (zeroVec : PVec n b) (zeroVec : PVec n d)
      have hWs :
          W s.1 = Wc.2.1 s + Wc.1.2 := by
        exact pointedSrcEvenValueBuild_at_tail
          (zeroVec : PVec n b) Wc s
      rw [hWs, map_add] at hs
      rw [hW0, map_add] at h0
      have hs' :
          cubeDiffR (Wc.2.1 s) +
                (cubeDiffP (B (zeroVec : PVec n d)) +
                  cubeDiffR Wc.1.2) =
            (0 : CyclicCube n) := by
        simpa only [add_assoc, add_left_comm, add_comm] using hs
      have h0' :
          cubeDiffR Wc.1.1 +
                (cubeDiffP (B (zeroVec : PVec n d)) +
                  cubeDiffR Wc.1.2) =
            (0 : CyclicCube n) := by
        simpa only [add_assoc, add_left_comm, add_comm] using h0
      have heq :
          cubeDiffR (Wc.2.1 s) +
                (cubeDiffP (B (zeroVec : PVec n d)) +
                  cubeDiffR Wc.1.2) =
            cubeDiffR Wc.1.1 +
                (cubeDiffP (B (zeroVec : PVec n d)) +
                  cubeDiffR Wc.1.2) := by
        exact hs'.trans h0'.symm
      exact (add_right_cancel heq).trans hR
    exact ⟨hP, hR, hK, hBTail, hWTail⟩
  · rintro ⟨hP, hR, hK, hBTail, hWTail⟩
    intro s t
    by_cases ht : t = (zeroVec : PVec n d)
    · subst t
      rw [hB0, map_add, hP, zero_add]
      by_cases hs : s = (zeroVec : PVec n b)
      · subst s
        rw [hW0, map_add, hR, zero_add]
        exact hK
      · let st : PointedTail (PVec n b) (zeroVec : PVec n b) :=
          ⟨s, hs⟩
        have hWs : W s = Wc.2.1 st + Wc.1.2 := by
          exact pointedSrcEvenValueBuild_at_tail
            (zeroVec : PVec n b) Wc st
        rw [hWs, map_add, hWTail st, zero_add]
        exact hK
    · let tt : PointedTail (PVec n d) (zeroVec : PVec n d) :=
        ⟨t, ht⟩
      have hBt : B t = Bc.2.1 tt + Bc.1.2 := by
        exact pointedSrcEvenValueBuild_at_tail
          (zeroVec : PVec n d) Bc tt
      rw [hBt, map_add, hBTail tt, zero_add]
      by_cases hs : s = (zeroVec : PVec n b)
      · subst s
        rw [hW0, map_add, hR, zero_add]
        exact hK
      · let st : PointedTail (PVec n b) (zeroVec : PVec n b) :=
          ⟨s, hs⟩
        have hWs : W s = Wc.2.1 st + Wc.1.2 := by
          exact pointedSrcEvenValueBuild_at_tail
            (zeroVec : PVec n b) Wc st
        rw [hWs, map_add, hWTail st, zero_add]
        exact hK

theorem totalEEOE_gauged_source_iff
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (B : PVec n d → CyclicCube n)
    (W : PVec n b → CyclicCube n) :
    (∀ s : PVec n b, ∀ t : PVec n d,
      cubeDiffP (B t) + cubeDiffR (W s) = 0) ↔
      cubeDiffP
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := d) (CyclicCube n) hn hd2 B).1.1) = 0 ∧
      cubeDiffR
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := b) (CyclicCube n) hn hb2 W).1.1) = 0 ∧
      cubeDiffP
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := d) (CyclicCube n) hn hd2 B).1.2) +
        cubeDiffR
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := b) (CyclicCube n) hn hb2 W).1.2) = 0 ∧
      (∀ t : DiamondEvenAxisTailIndex n d,
        cubeDiffP
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := d) (CyclicCube n) hn hd2 B).2.1 t) = 0) ∧
      (∀ s : DiamondEvenAxisTailIndex n b,
        cubeDiffR
          ((diamondEvenAxisSrcCoordEquiv
            (n := n) (k := b) (CyclicCube n) hn hb2 W).2.1 s) = 0) := by
  let EB :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let EW :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := b) (CyclicCube n) hn hb2
  have h :=
    totalEEOE_gauged_coords_iff
      hn hb2 hd2 (EB B) (EW W)
  change
    (∀ s : PVec n b, ∀ t : PVec n d,
      cubeDiffP ((EB.symm (EB B)) t) +
        cubeDiffR ((EW.symm (EW W)) s) = 0) ↔ _ at h
  rw [EB.symm_apply_apply, EW.symm_apply_apply] at h
  exact h

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

noncomputable def t37BRootWFamilyEquiv
    {n d : Nat} [NeZero n] (hd : 0 < d) :
    BFun4 n 1 1 d ≃ₗ[F] (PVec n d → CyclicCube n) :=
  (diamondBRootCubeEquiv
      (n := n) (c := 1) (d := d) Nat.zero_lt_one hd).trans
    (singletonFamilyEquiv (n := n) (PVec n d → CyclicCube n))

noncomputable def t37WRootYFamilyEquiv
    {n b : Nat} [NeZero n] (hb : 0 < b) :
    WFun4 n 1 b 1 ≃ₗ[F] (PVec n b → CyclicCube n) where
  toFun W yt :=
    diamondWRootCubeEquiv hb Nat.zero_lt_one W yt zeroVec
  invFun f :=
    (diamondWRootCubeEquiv hb Nat.zero_lt_one).symm
      (fun yt _ => f yt)
  left_inv W := by
    apply (diamondWRootCubeEquiv hb Nat.zero_lt_one).injective
    funext yt zt
    rw [pVec_one_eq_zeroVec zt]
    exact
      (diamondWRootCubeEquiv
        (n := n) hb Nat.zero_lt_one).apply_symm_apply _ ▸ rfl
  right_inv f := by
    funext yt
    exact congrFun
      (congrFun
        ((diamondWRootCubeEquiv hb Nat.zero_lt_one).apply_symm_apply
          (fun yt _ => f yt))
        yt)
      zeroVec
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def t37CubeKShiftEquiv
    {n : Nat} [NeZero n] (u : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X i j (k - u)
  invFun X i j k := X i j (k + u)
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def t37CubeIShiftEquiv
    {n : Nat} [NeZero n] (u : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X (i - u) j k
  invFun X i j k := X (i + u) j k
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def t37KGaugeFamilyEquiv
    {n d : Nat} [NeZero n] :
    (PVec n d → CyclicCube n) ≃ₗ[F]
      (PVec n d → CyclicCube n) where
  toFun f wt := t37CubeKShiftEquiv (vecSum wt) (f wt)
  invFun f wt := (t37CubeKShiftEquiv (vecSum wt)).symm (f wt)
  left_inv f := by
    funext wt
    exact (t37CubeKShiftEquiv (vecSum wt)).symm_apply_apply (f wt)
  right_inv f := by
    funext wt
    exact (t37CubeKShiftEquiv (vecSum wt)).apply_symm_apply (f wt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def t37IGaugeFamilyEquiv
    {n b : Nat} [NeZero n] :
    (PVec n b → CyclicCube n) ≃ₗ[F]
      (PVec n b → CyclicCube n) where
  toFun f yt := t37CubeIShiftEquiv (vecSum yt) (f yt)
  invFun f yt := (t37CubeIShiftEquiv (vecSum yt)).symm (f yt)
  left_inv f := by
    funext yt
    exact (t37CubeIShiftEquiv (vecSum yt)).symm_apply_apply (f yt)
  right_inv f := by
    funext yt
    exact (t37CubeIShiftEquiv (vecSum yt)).apply_symm_apply (f yt)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def t37BGaugedWFamilyEquiv
    {n d : Nat} [NeZero n] (hd : 0 < d) :
    BFun4 n 1 1 d ≃ₗ[F] (PVec n d → CyclicCube n) :=
  (t37BRootWFamilyEquiv hd).trans
    (t37KGaugeFamilyEquiv (n := n) (d := d))

noncomputable def t37WGaugedYFamilyEquiv
    {n b : Nat} [NeZero n] (hb : 0 < b) :
    WFun4 n 1 b 1 ≃ₗ[F] (PVec n b → CyclicCube n) :=
  (t37WRootYFamilyEquiv hb).trans
    (t37IGaugeFamilyEquiv (n := n) (b := b))

@[simp] theorem t37BGaugedWFamilyEquiv_apply
    {n d : Nat} [NeZero n] (hd : 0 < d)
    (B : BFun4 n 1 1 d) (wt : PVec n d) (i j k : I n) :
    t37BGaugedWFamilyEquiv hd B wt i j k =
      diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt
        i j (k - vecSum wt) :=
  rfl

@[simp] theorem t37WGaugedYFamilyEquiv_apply
    {n b : Nat} [NeZero n] (hb : 0 < b)
    (W : WFun4 n 1 b 1) (yt : PVec n b) (i j k : I n) :
    t37WGaugedYFamilyEquiv hb W yt i j k =
      diamondWRootCubeEquiv hb Nat.zero_lt_one W yt zeroVec
        (i - vecSum yt) j k :=
  rfl

@[simp] private theorem t37CubeKShift_cubeDiffP_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffP (t37CubeKShiftEquiv u X) i j k =
      cubeDiffP X i j (k - u) := by
  rw [EEOEInternal.cubeDiffP_apply, EEOEInternal.cubeDiffP_apply]
  rfl

@[simp] private theorem t37CubeIShift_cubeDiffR_apply
    {n : Nat} [NeZero n] (u : I n) (X : CyclicCube n)
    (i j k : I n) :
    cubeDiffR (t37CubeIShiftEquiv u X) i j k =
      cubeDiffR X (i - u) j k := by
  rw [EEOEInternal.cubeDiffR_apply, EEOEInternal.cubeDiffR_apply]
  rfl

@[simp] theorem t37BGauged_cubeDiffP_apply
    {n d : Nat} [NeZero n] (hd : 0 < d)
    (B : BFun4 n 1 1 d) (wt : PVec n d) (i j k : I n) :
    cubeDiffP (t37BGaugedWFamilyEquiv hd B wt) i j k =
      cubeDiffP
        (diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt)
        i j (k - vecSum wt) := by
  exact
    t37CubeKShift_cubeDiffP_apply
      (vecSum wt)
      (diamondBRootCubeEquiv Nat.zero_lt_one hd B zeroVec wt)
      i j k

@[simp] theorem t37WGauged_cubeDiffR_apply
    {n b : Nat} [NeZero n] (hb : 0 < b)
    (W : WFun4 n 1 b 1) (yt : PVec n b) (i j k : I n) :
    cubeDiffR (t37WGaugedYFamilyEquiv hb W yt) i j k =
      cubeDiffR
        (diamondWRootCubeEquiv hb Nat.zero_lt_one W yt zeroVec)
        (i - vecSum yt) j k := by
  exact
    t37CubeIShift_cubeDiffR_apply
      (vecSum yt)
      (diamondWRootCubeEquiv hb Nat.zero_lt_one W yt zeroVec)
      i j k

@[simp] private theorem t37VecSum_zero
    {n k : Nat} [NeZero n] :
    vecSum (zeroVec : Vec n k) = 0 := by
  unfold vecSum zeroVec
  simp

private theorem t37Sum_pVec_one
    {n : Nat} [NeZero n]
    {V : Type*} [AddCommMonoid V]
    (f : PVec n 1 → V) :
    (∑ z : PVec n 1, f z) = f zeroVec := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro z _ hz
    exact (hz (pVec_one_eq_zeroVec z)).elim
  · simp

noncomputable def t37LiteralGaugeEquiv
    {n b d : Nat} [NeZero n] (hb : 0 < b) (hd : 0 < d) :
    (BFun4 n 1 1 d × WFun4 n 1 b 1) ≃ₗ[F]
      ((PVec n d → CyclicCube n) × (PVec n b → CyclicCube n)) :=
  (t37BGaugedWFamilyEquiv hd).prodCongr (t37WGaugedYFamilyEquiv hb)

theorem t37Literal_mem_iff_gauged_pointwise
    {n b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (x : BFun4 n 1 1 d × WFun4 n 1 b 1) :
    x ∈ DiamondEvenPLeft n b 1 d ↔
      ∀ yt : PVec n b, ∀ wt : PVec n d,
        cubeDiffP ((t37LiteralGaugeEquiv hb hd x).1 wt) +
          cubeDiffR ((t37LiteralGaugeEquiv hb hd x).2 yt) = 0 := by
  simp only [DiamondEvenPLeft, LinearMap.mem_ker]
  constructor
  · intro hx yt wt
    funext i j k
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hx (zeroVec : PVec n 1))
            ((diamondVecHeadTailEquiv hb).symm
              (i - vecSum yt, yt)))
          j)
        ((diamondVecHeadTailEquiv hd).symm
          (k - vecSum wt, wt))
    rw [diamondCubeReindex_squareCompat
      hb Nat.zero_lt_one hd
      x.1 x.2 yt wt (i - vecSum yt) j (k - vecSum wt)] at hpoint
    rw [t37Sum_pVec_one] at hpoint
    simp only [t37VecSum_zero, sub_zero, Pi.zero_apply] at hpoint
    simpa only [t37LiteralGaugeEquiv, LinearEquiv.prodCongr_apply,
      Pi.add_apply, t37BGauged_cubeDiffP_apply,
      t37WGauged_cubeDiffR_apply, Pi.zero_apply,
      sub_add_cancel] using hpoint
  · intro h
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) hb
    let ew := diamondVecHeadTailEquiv (n := n) hd
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      hb Nat.zero_lt_one hd
      x.1 x.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [t37Sum_pVec_one]
    simp only [t37VecSum_zero, sub_zero]
    have hpoint :=
      congrFun
        (congrFun
          (congrFun
            (h (ey y).2 (ew w).2)
            ((ey y).1 + vecSum (ey y).2))
          sz)
        ((ew w).1 + vecSum (ew w).2)
    simpa only [t37LiteralGaugeEquiv, LinearEquiv.prodCongr_apply,
      Pi.add_apply, t37BGauged_cubeDiffP_apply,
      t37WGauged_cubeDiffR_apply, Pi.zero_apply,
      add_sub_cancel_right] using hpoint

noncomputable abbrev T37LeftAmbientTarget
    (n b d : Nat) [NeZero n] :=
  DiamondEEOELeftAmbient n ×
    (DiamondEvenAxisValueTailZero n b (CyclicCube n) ×
      DiamondEvenAxisValueTailZero n d (CyclicCube n))

@[reducible] private noncomputable def
    t37PointedCoordsProdAddCommMonoid
    {n b d : Nat} [NeZero n] :
    AddCommMonoid
      (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
        PointedEvenValueCoords
          (PVec n b) (CyclicCube n) (zeroVec : PVec n b)) :=
  @Prod.instAddCommMonoid _ _
    (inferInstance :
      AddCommMonoid
        (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d)))
    (inferInstance :
      AddCommMonoid
        (PointedEvenValueCoords
          (PVec n b) (CyclicCube n) (zeroVec : PVec n b)))

private local instance {n b d : Nat} [NeZero n] :
    AddCommMonoid
      (PointedEvenValueCoords
          (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
        PointedEvenValueCoords
          (PVec n b) (CyclicCube n) (zeroVec : PVec n b)) :=
  t37PointedCoordsProdAddCommMonoid

private noncomputable def t37LeftAmbientReassoc
    {n b d : Nat} [NeZero n] :
    (PointedEvenValueCoords
        (PVec n d) (CyclicCube n) (zeroVec : PVec n d) ×
      PointedEvenValueCoords
        (PVec n b) (CyclicCube n) (zeroVec : PVec n b)) ≃ₗ[F]
      T37LeftAmbientTarget n b d where
  toFun q := ((q.1.1, q.2.1), (q.2.2, q.1.2))
  invFun q := ((q.1.1, q.2.2), (q.1.2, q.2.1))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def t37LeftAmbientCoords
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    (BFun4 n 1 1 d × WFun4 n 1 b 1) ≃ₗ[F]
      T37LeftAmbientTarget n b d :=
  (t37LiteralGaugeEquiv (by omega) (by omega)).trans
    (((diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2).prodCongr
      (diamondEvenAxisSrcCoordEquiv
        (n := n) (k := b) (CyclicCube n) hn hb2)).trans
      (t37LeftAmbientReassoc (n := n) (b := b) (d := d)))

@[simp] theorem t37LeftAmbientCoords_scalar
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 1 d × WFun4 n 1 b 1) :
    (t37LeftAmbientCoords hn hb2 hd2 x).1 =
      (((diamondEvenAxisSrcCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2)
        ((t37LiteralGaugeEquiv (by omega) (by omega) x).1)).1,
       ((diamondEvenAxisSrcCoordEquiv
          (n := n) (k := b) (CyclicCube n) hn hb2)
        ((t37LiteralGaugeEquiv (by omega) (by omega) x).2)).1) :=
  rfl

@[simp] theorem t37LeftAmbientCoords_YTail
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 1 d × WFun4 n 1 b 1) :
    (t37LeftAmbientCoords hn hb2 hd2 x).2.1 =
      ((diamondEvenAxisSrcCoordEquiv
          (n := n) (k := b) (CyclicCube n) hn hb2)
        ((t37LiteralGaugeEquiv (by omega) (by omega) x).2)).2 :=
  rfl

@[simp] theorem t37LeftAmbientCoords_WTail
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 1 d × WFun4 n 1 b 1) :
    (t37LeftAmbientCoords hn hb2 hd2 x).2.2 =
      ((diamondEvenAxisSrcCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2)
        ((t37LiteralGaugeEquiv (by omega) (by omega) x).1)).2 :=
  rfl

theorem t37LiteralLeft_mem_iff_coords
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (x : BFun4 n 1 1 d × WFun4 n 1 b 1) :
    x ∈ DiamondEvenPLeft n b 1 d ↔
      (t37LeftAmbientCoords hn hb2 hd2 x).1 ∈
          DiamondEEOELeftSource n ∧
      (∀ yt : DiamondEvenAxisTailIndex n b,
        cubeDiffR
          ((t37LeftAmbientCoords hn hb2 hd2 x).2.1.1 yt) = 0) ∧
      (∀ wt : DiamondEvenAxisTailIndex n d,
        cubeDiffP
          ((t37LeftAmbientCoords hn hb2 hd2 x).2.2.1 wt) = 0) := by
  rw [t37Literal_mem_iff_gauged_pointwise (by omega) (by omega)]
  rw [totalEEOE_gauged_source_iff hn hb2 hd2]
  simp only [t37LeftAmbientCoords_scalar,
    t37LeftAmbientCoords_YTail, t37LeftAmbientCoords_WTail]
  let EB :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let EW :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := b) (CyclicCube n) hn hb2
  let g := t37LiteralGaugeEquiv (by omega : 0 < b) (by omega : 0 < d) x
  change
    cubeDiffP (EB g.1).1.1 = 0 ∧
      cubeDiffR (EW g.2).1.1 = 0 ∧
      cubeDiffP (EB g.1).1.2 + cubeDiffR (EW g.2).1.2 = 0 ∧
      (∀ wt, cubeDiffP ((EB g.1).2.1 wt) = 0) ∧
      (∀ yt, cubeDiffR ((EW g.2).2.1 yt) = 0) ↔
    ((EB g.1).1, (EW g.2).1) ∈ DiamondEEOELeftSource n ∧
      (∀ yt, cubeDiffR ((EW g.2).2.1 yt) = 0) ∧
      (∀ wt, cubeDiffP ((EB g.1).2.1 wt) = 0)
  constructor
  · rintro ⟨hP, hR, hK, hW, hY⟩
    refine ⟨?_, hY, hW⟩
    apply LinearMap.mem_ker.mpr
    apply Prod.ext
    · exact Prod.ext hP hR
    · exact hK
  · rintro ⟨hscalar, hY, hW⟩
    have hs := LinearMap.mem_ker.mp hscalar
    exact
      ⟨congrArg (fun q => q.1.1) hs,
       congrArg (fun q => q.1.2) hs,
       congrArg Prod.snd hs,
       hW, hY⟩

private noncomputable def t37YTailPack
    {n b : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n b (CyclicCube n))
    (hu : ∀ yt : DiamondEvenAxisTailIndex n b,
      cubeDiffR (u.1 yt) = 0) :
    DiamondEvenAxisValueTailZero n b
      (EEOEInternal.RBlockLeft n) :=
  ⟨fun yt =>
      ⟨u.1 yt, LinearMap.mem_ker.mpr (hu yt)⟩,
    by
      apply LinearMap.mem_ker.mpr
      change
        (∑ yt,
          (⟨u.1 yt, LinearMap.mem_ker.mpr (hu yt)⟩ :
            EEOEInternal.RBlockLeft n)) = 0
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using
        pointedValueTailZero_sum u⟩

private noncomputable def t37YTailForget
    {n b : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n b
        (EEOEInternal.RBlockLeft n) →ₗ[F]
      DiamondEvenAxisValueTailZero n b (CyclicCube n) where
  toFun u :=
    ⟨fun yt => (u.1 yt).1, by
      apply LinearMap.mem_ker.mpr
      have hu := pointedValueTailZero_sum u
      change (∑ yt, (u.1 yt).1) = 0
      simpa only [Submodule.coe_sum] using
        congrArg Subtype.val hu⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

private noncomputable def t37WTailPack
    {n d : Nat} [NeZero n]
    (u : DiamondEvenAxisValueTailZero n d (CyclicCube n))
    (hu : ∀ wt : DiamondEvenAxisTailIndex n d,
      cubeDiffP (u.1 wt) = 0) :
    DiamondEvenAxisValueTailZero n d
      (EEOEInternal.PBlockLeft n) :=
  ⟨fun wt =>
      ⟨u.1 wt, LinearMap.mem_ker.mpr (hu wt)⟩,
    by
      apply LinearMap.mem_ker.mpr
      change
        (∑ wt,
          (⟨u.1 wt, LinearMap.mem_ker.mpr (hu wt)⟩ :
            EEOEInternal.PBlockLeft n)) = 0
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using
        pointedValueTailZero_sum u⟩

private noncomputable def t37WTailForget
    {n d : Nat} [NeZero n] :
    DiamondEvenAxisValueTailZero n d
        (EEOEInternal.PBlockLeft n) →ₗ[F]
      DiamondEvenAxisValueTailZero n d (CyclicCube n) where
  toFun u :=
    ⟨fun wt => (u.1 wt).1, by
      apply LinearMap.mem_ker.mpr
      have hu := pointedValueTailZero_sum u
      change (∑ wt, (u.1 wt).1) = 0
      simpa only [Submodule.coe_sum] using
        congrArg Subtype.val hu⟩
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' r u := by
    apply Subtype.ext
    rfl

noncomputable abbrev T37MixedLeftZero
    (n b d : Nat) [NeZero n] :=
  DiamondMixedTailZero n b d
    (⊥ : Submodule F (CyclicCube n))

noncomputable abbrev T37LeftSourceTarget
    (n b d : Nat) [NeZero n] :=
  DiamondEEOELeftSource n ×
    (DiamondEvenAxisValueTailZero n b
        (EEOEInternal.RBlockLeft n) ×
      (DiamondEvenAxisValueTailZero n d
          (EEOEInternal.PBlockLeft n) ×
        T37MixedLeftZero n b d))

private theorem t37MixedLeftZero_eq_zero
    {n b d : Nat} [NeZero n]
    (q : T37MixedLeftZero n b d) :
    q = 0 := by
  apply Subtype.ext
  funext yt
  apply Subtype.ext
  funext wt
  exact Subsingleton.elim _ _

noncomputable def t37LeftSourceEquiv
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    DiamondEvenPLeft n b 1 d ≃ₗ[F]
      T37LeftSourceTarget n b d where
  toFun l := by
    let q := t37LeftAmbientCoords hn hb2 hd2 l.1
    have hq := (t37LiteralLeft_mem_iff_coords hn hb2 hd2 l.1).mp l.2
    exact
      (⟨q.1, hq.1⟩,
        (t37YTailPack q.2.1 hq.2.1,
          (t37WTailPack q.2.2 hq.2.2, 0)))
  invFun q := by
    let raw : T37LeftAmbientTarget n b d :=
      (q.1.1, (t37YTailForget q.2.1, t37WTailForget q.2.2.1))
    let l := (t37LeftAmbientCoords hn hb2 hd2).symm raw
    refine
      ⟨l, (t37LiteralLeft_mem_iff_coords hn hb2 hd2 l).mpr ?_⟩
    have hread : t37LeftAmbientCoords hn hb2 hd2 l = raw :=
      (t37LeftAmbientCoords hn hb2 hd2).apply_symm_apply raw
    refine ⟨?_, ?_, ?_⟩
    · have hscalar := congrArg Prod.fst hread
      rw [hscalar]
      exact q.1.2
    · intro yt
      have ht := LinearMap.mem_ker.mp (q.2.1.1 yt).2
      change
        cubeDiffR
          ((t37LeftAmbientCoords hn hb2 hd2 l).2.1.1 yt) = 0
      calc
        cubeDiffR
            ((t37LeftAmbientCoords hn hb2 hd2 l).2.1.1 yt) =
          cubeDiffR (raw.2.1.1 yt) :=
            congrArg (fun z => cubeDiffR (z.2.1.1 yt)) hread
        _ = 0 := by
          simpa only [raw, t37YTailForget] using ht
    · intro wt
      have ht := LinearMap.mem_ker.mp (q.2.2.1.1 wt).2
      change
        cubeDiffP
          ((t37LeftAmbientCoords hn hb2 hd2 l).2.2.1 wt) = 0
      calc
        cubeDiffP
            ((t37LeftAmbientCoords hn hb2 hd2 l).2.2.1 wt) =
          cubeDiffP (raw.2.2.1 wt) :=
            congrArg (fun z => cubeDiffP (z.2.2.1 wt)) hread
        _ = 0 := by
          simpa only [raw, t37WTailForget] using ht
  left_inv l := by
    apply Subtype.ext
    exact
      (t37LeftAmbientCoords hn hb2 hd2).symm_apply_apply l.1
  right_inv q := by
    have hread :=
      (t37LeftAmbientCoords hn hb2 hd2).apply_symm_apply
        (q.1.1, (t37YTailForget q.2.1, t37WTailForget q.2.2.1))
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hread
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Subtype.ext
        exact congrArg (fun z => z.2.1.1 yt) hread
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Subtype.ext
          exact congrArg (fun z => z.2.2.1 wt) hread
        · exact (t37MixedLeftZero_eq_zero q.2.2.2).symm
  map_add' l l' := by
    have hmap :=
      (t37LeftAmbientCoords hn hb2 hd2).map_add l.1 l'.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Subtype.ext
        exact congrArg (fun z => z.2.1.1 yt) hmap
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Subtype.ext
          exact congrArg (fun z => z.2.2.1 wt) hmap
        · rfl
  map_smul' r l := by
    have hmap :=
      (t37LeftAmbientCoords hn hb2 hd2).map_smul r l.1
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hmap
    · apply Prod.ext
      · apply Subtype.ext
        funext yt
        apply Subtype.ext
        exact congrArg (fun z => z.2.1.1 yt) hmap
      · apply Prod.ext
        · apply Subtype.ext
          funext wt
          apply Subtype.ext
          exact congrArg (fun z => z.2.2.1 wt) hmap
        · rfl

end T37LeftP0

end

end Core4loop.SquareDiagonal.EvenP
