import Core4loop.SquareDiagonal.EvenP.TotalEOEE.RootGauge

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace TotalEOEEInternal

private theorem sum_pVec_one
    {n : Nat} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : PVec n 1 → M) :
    (∑ p : PVec n 1, f p) = f (zeroVec : PVec n 1) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    exact (hp (pVec_one_eq_zeroVec p)).elim
  · simp

@[simp] private theorem vecSum_zero_local
    {n k : Nat} [NeZero n] :
    vecSum (zeroVec : Vec n k) = 0 := by
  unfold vecSum zeroVec
  simp

private theorem sum_eq_at_point_add_tail_local
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

private theorem cast_odd_eq_one_local
    {m : Nat} (hm : Odd m) :
    (m : F) = 1 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem sum_const_odd_local
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F, cast_odd_eq_one_local hodd, one_smul]

private theorem cubeDot_comm_local
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem cubeJKShift_leftRoot_ZW
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (l : DiamondEvenPLeft n 1 c d)
    (zt : PVec n c) (wt : PVec n d) :
    cubeJKShiftEquiv (vecSum zt) (vecSum wt)
        (diamondARootCubeEquiv Nat.zero_lt_one hc hd
          (diamondEvenPLeftRoot l) zeroVec zt wt) =
      cubeDiffI (bGaugedRootFamilyEquiv hc hd l.1.1 zt wt) +
        cubeDiffK (wGaugedRootFamilyEquiv hc l.1.2 zt) := by
  funext i j k
  simp only [cubeJKShiftEquiv_apply, Pi.add_apply]
  change
    diamondEvenPLeftRoot l
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
          (i, zeroVec))
        ((diamondVecHeadTailEquiv hc).symm
          (j - vecSum zt, zt))
        ((diamondVecHeadTailEquiv hd).symm
          (k - vecSum wt, wt)) =
      _
  rw [diamondCubeReindex_leftRoot
    Nat.zero_lt_one hc hd l zeroVec zt wt
      i (j - vecSum zt) (k - vecSum wt)]
  simp only [vecSum_zero_local, add_zero]
  rw [show
      bGaugedRootFamilyEquiv hc hd l.1.1 zt wt =
        cubeJKShiftEquiv (vecSum zt) (vecSum wt)
          (diamondBRootCubeEquiv hc hd l.1.1 zt wt) from rfl]
  rw [show
      wGaugedRootFamilyEquiv hc l.1.2 zt =
        cubeJShiftEquiv (vecSum zt)
          (diamondWRootCubeEquiv
            Nat.zero_lt_one hc l.1.2 zeroVec zt) from rfl]
  rw [← cubeJKShift_cubeDiffI, ← cubeJShift_cubeDiffK]
  simp only [cubeJKShiftEquiv_apply, cubeJShiftEquiv_apply]
  simp

theorem literal_phase_gauged_ZW
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    diamondEvenPCross l A =
      ∑ zt : PVec n c, ∑ wt : PVec n d,
        cubeDot
          (cubeDiffI
              (bGaugedRootFamilyEquiv hc hd l.1.1 zt wt) +
            cubeDiffK
              (wGaugedRootFamilyEquiv hc l.1.2 zt))
          (aGaugedRootFamilyEquiv hc hd A.1 zt wt) := by
  change coeffApplyA (diamondEvenPLeftRoot l) A.1 = _
  rw [diamondCubeReindex_rootPairing Nat.zero_lt_one hc hd]
  rw [sum_pVec_one]
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  let u := vecSum zt
  let v := vecSum wt
  let AR :=
    diamondARootCubeEquiv Nat.zero_lt_one hc hd
      A.1 zeroVec zt wt
  let LR :=
    diamondARootCubeEquiv Nat.zero_lt_one hc hd
      (diamondEvenPLeftRoot l) zeroVec zt wt
  calc
    cubeDot AR LR =
        cubeDot (cubeJKShiftEquiv u v AR)
          (cubeJKShiftEquiv u v LR) :=
      (cubeJKShift_pairing_same u v AR LR).symm
    _ = cubeDot
          (aGaugedRootFamilyEquiv hc hd A.1 zt wt)
          (cubeDiffI
              (bGaugedRootFamilyEquiv hc hd l.1.1 zt wt) +
            cubeDiffK
              (wGaugedRootFamilyEquiv hc l.1.2 zt)) := by
      rw [show cubeJKShiftEquiv u v AR =
          aGaugedRootFamilyEquiv hc hd A.1 zt wt from rfl]
      rw [show cubeJKShiftEquiv u v LR =
          cubeDiffI
              (bGaugedRootFamilyEquiv hc hd l.1.1 zt wt) +
            cubeDiffK
              (wGaugedRootFamilyEquiv hc l.1.2 zt) from
        cubeJKShift_leftRoot_ZW hc hd l zt wt]
    _ = _ := cubeDot_comm_local _ _

noncomputable abbrev RawOuterLeft
    (n d : Nat) [NeZero n] :=
  (PVec n d → CyclicCube n) × CyclicCube n

noncomputable abbrev RawOuterRight
    (n d : Nat) [NeZero n] :=
  PVec n d → CyclicCube n

def rawLocalPhase
    {n d : Nat} [NeZero n]
    (u : RawOuterLeft n d) (v : RawOuterRight n d) : F :=
  ∑ wt : PVec n d,
    cubeDot (cubeDiffI (u.1 wt) + cubeDiffK u.2) (v wt)

noncomputable def rawLocalCross
    {n d : Nat} [NeZero n] :
    RawOuterLeft n d →ₗ[F] Module.Dual F (RawOuterRight n d) :=
  LinearMap.mk₂ F rawLocalPhase
    (by
      intro u u' v
      simp only [rawLocalPhase, Prod.fst_add, Prod.snd_add,
        Pi.add_apply, map_add, EEOEInternal.cubeDot_add_left,
        Finset.sum_add_distrib]
      abel)
    (by
      intro r u v
      simp only [rawLocalPhase, Prod.smul_fst, Prod.smul_snd,
        Pi.smul_apply, map_smul]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro wt _
      rw [← smul_add]
      exact EEOEInternal.cubeDot_smul_left _ _ _)
    (by
      intro u v v'
      simp only [rawLocalPhase, Pi.add_apply,
        EEOEInternal.cubeDot_add_right, Finset.sum_add_distrib])
    (by
      intro r u v
      simp only [rawLocalPhase, Pi.smul_apply,
        EEOEInternal.cubeDot_smul_right, Finset.smul_sum])

@[simp] theorem rawLocalCross_apply
    {n d : Nat} [NeZero n]
    (u : RawOuterLeft n d) (v : RawOuterRight n d) :
    rawLocalCross u v = rawLocalPhase u v :=
  rfl

def rawInnerScalarPhase
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (u : RawOuterLeft n d) (v : RawOuterRight n d) : F :=
  let x :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 u.1
  let y :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 v
  cubeDot (cubeDiffI (x.1.1 + x.1.2) + cubeDiffK u.2) y.1.2 +
    cubeDot (cubeDiffI x.1.1) (y.1.1 + y.1.2)

def rawInnerTailPhase
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (u : RawOuterLeft n d) (v : RawOuterRight n d) : F :=
  let x :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 u.1
  let y :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2 v
  ∑ t,
    cubeDot (cubeDiffI (x.2.1 t)) (y.2.1 t)

private theorem pointedDual_D_eq_total_sum
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
    Finset.sum_add_distrib]
  rw [show
      (∑ _ : DiamondEvenAxisTailIndex n d,
        g (zeroVec : PVec n d)) =
        g (zeroVec : PVec n d) by
      exact sum_const_odd_local
        (odd_card_diamondEvenAxisTailIndex hn hd2)
        (g (zeroVec : PVec n d))]
  rw [show
      (∑ s : PVec n d, g s) =
        g (zeroVec : PVec n d) +
          ∑ t : DiamondEvenAxisTailIndex n d, g t.1 by
      exact sum_eq_at_point_add_tail_local
        (zeroVec : PVec n d) g]
  abel

theorem rawLocalPhase_eq_scalar_add_tail
    {n d : Nat} [NeZero n]
    (hn : Even n) (hd2 : 2 ≤ d)
    (u : RawOuterLeft n d) (v : RawOuterRight n d) :
    rawLocalPhase u v =
      rawInnerScalarPhase hn hd2 u v +
        rawInnerTailPhase hn hd2 u v := by
  let beta : CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
    EEOEInternal.cubeDotDual.comp cubeDiffI
  have hpair :=
    pointedEvenValue_pairing
      (zeroVec : PVec n d)
      (even_card_PVec hn hd2)
      beta u.1 v
  change
    (∑ s : PVec n d, cubeDot (cubeDiffI (u.1 s)) (v s)) =
      cubeDot
          (cubeDiffI
            ((diamondEvenAxisSrcCoordEquiv
              (CyclicCube n) hn hd2 u.1).1.1))
          ((diamondEvenAxisDualCoordEquiv
            (CyclicCube n) hn hd2 v).1.1) +
        cubeDot
          (cubeDiffI
            ((diamondEvenAxisSrcCoordEquiv
              (CyclicCube n) hn hd2 u.1).1.2))
          ((diamondEvenAxisDualCoordEquiv
            (CyclicCube n) hn hd2 v).1.2) +
        ∑ t,
          cubeDot
            (cubeDiffI
              ((diamondEvenAxisSrcCoordEquiv
                (CyclicCube n) hn hd2 u.1).2.1 t))
            ((diamondEvenAxisDualCoordEquiv
              (CyclicCube n) hn hd2 v).2.1 t) at hpair
  have hconst :
      (∑ s : PVec n d, cubeDot (cubeDiffK u.2) (v s)) =
        cubeDot (cubeDiffK u.2) (∑ s : PVec n d, v s) := by
    change
      (∑ s : PVec n d,
          EEOEInternal.cubeDotDual (cubeDiffK u.2) (v s)) =
        EEOEInternal.cubeDotDual (cubeDiffK u.2)
          (∑ s : PVec n d, v s)
    rw [map_sum]
  simp only [rawLocalPhase, rawInnerScalarPhase, rawInnerTailPhase]
  simp_rw [EEOEInternal.cubeDot_add_left]
  rw [Finset.sum_add_distrib, hpair, hconst,
    ← pointedDual_D_eq_total_sum hn hd2 v]
  simp only [map_add, EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

def rawOuterScalarBlock
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) : F :=
  let x :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (RawOuterLeft n d) hn hc2 f
  let y :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (RawOuterRight n d) hn hc2 g
  rawInnerScalarPhase hn hd2 x.1.1 y.1.1 +
    rawInnerScalarPhase hn hd2 x.1.2 y.1.2

def rawOuterWBlock
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) : F :=
  let x :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (RawOuterLeft n d) hn hc2 f
  let y :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (RawOuterRight n d) hn hc2 g
  rawInnerTailPhase hn hd2 x.1.1 y.1.1 +
    rawInnerTailPhase hn hd2 x.1.2 y.1.2

def rawOuterZBlock
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) : F :=
  let x :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (RawOuterLeft n d) hn hc2 f
  let y :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (RawOuterRight n d) hn hc2 g
  ∑ t, rawInnerScalarPhase hn hd2 (x.2.1 t) (y.2.1 t)

def rawOuterZWBlock
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) : F :=
  let x :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := c) (RawOuterLeft n d) hn hc2 f
  let y :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := c) (RawOuterRight n d) hn hc2 g
  ∑ t, rawInnerTailPhase hn hd2 (x.2.1 t) (y.2.1 t)

set_option maxHeartbeats 1000000 in
-- Expanding both pointed finite sums needs more than the project default.
theorem raw_total_pairing_Z_then_W
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (f : PVec n c → RawOuterLeft n d)
    (g : PVec n c → RawOuterRight n d) :
    (∑ zt : PVec n c, rawLocalPhase (f zt) (g zt)) =
      rawOuterScalarBlock hn hc2 hd2 f g +
        rawOuterWBlock hn hc2 hd2 f g +
        rawOuterZBlock hn hc2 hd2 f g +
        rawOuterZWBlock hn hc2 hd2 f g := by
  have houter :=
    pointedEvenValue_pairing
      (zeroVec : PVec n c)
      (even_card_PVec hn hc2)
      (rawLocalCross (n := n) (d := d)) f g
  have houter' :
      (∑ zt : PVec n c, rawLocalPhase (f zt) (g zt)) =
        rawLocalPhase
            ((diamondEvenAxisSrcCoordEquiv
              (RawOuterLeft n d) hn hc2 f).1.1)
            ((diamondEvenAxisDualCoordEquiv
              (RawOuterRight n d) hn hc2 g).1.1) +
          rawLocalPhase
            ((diamondEvenAxisSrcCoordEquiv
              (RawOuterLeft n d) hn hc2 f).1.2)
            ((diamondEvenAxisDualCoordEquiv
              (RawOuterRight n d) hn hc2 g).1.2) +
          ∑ t,
            rawLocalPhase
              ((diamondEvenAxisSrcCoordEquiv
                (RawOuterLeft n d) hn hc2 f).2.1 t)
              ((diamondEvenAxisDualCoordEquiv
                (RawOuterRight n d) hn hc2 g).2.1 t) := by
    simpa only [rawLocalCross_apply] using houter
  rw [houter']
  rw [rawLocalPhase_eq_scalar_add_tail hn hd2,
    rawLocalPhase_eq_scalar_add_tail hn hd2]
  simp_rw [rawLocalPhase_eq_scalar_add_tail hn hd2]
  rw [Finset.sum_add_distrib]
  simp only [rawOuterScalarBlock, rawOuterWBlock,
    rawOuterZBlock, rawOuterZWBlock]
  abel

noncomputable def literalOuterLeftFamily
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (l : DiamondEvenPLeft n 1 c d) :
    PVec n c → RawOuterLeft n d :=
  fun zt =>
    (fun wt => bGaugedRootFamilyEquiv hc hd l.1.1 zt wt,
      wGaugedRootFamilyEquiv hc l.1.2 zt)

noncomputable def literalOuterRightFamily
    {n c d : Nat} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (A : DiamondEvenPReachableA n 1 c d) :
    PVec n c → RawOuterRight n d :=
  fun zt wt =>
    aGaugedRootFamilyEquiv hc hd A.1 zt wt

set_option maxHeartbeats 4000000 in
-- Rewriting the literal source into all four raw blocks is elaboration-heavy.
theorem literal_phase_four_raw_blocks
    {n c d : Nat} [NeZero n]
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n 1 c d)
    (A : DiamondEvenPReachableA n 1 c d) :
    diamondEvenPCross l A =
      rawOuterScalarBlock hn hc2 hd2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)
          (literalOuterRightFamily
            (by omega : 0 < c) (by omega : 0 < d) A) +
        rawOuterWBlock hn hc2 hd2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)
          (literalOuterRightFamily
            (by omega : 0 < c) (by omega : 0 < d) A) +
        rawOuterZBlock hn hc2 hd2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)
          (literalOuterRightFamily
            (by omega : 0 < c) (by omega : 0 < d) A) +
        rawOuterZWBlock hn hc2 hd2
          (literalOuterLeftFamily
            (by omega : 0 < c) (by omega : 0 < d) l)
          (literalOuterRightFamily
            (by omega : 0 < c) (by omega : 0 < d) A) := by
  calc
    diamondEvenPCross l A =
        ∑ zt : PVec n c, ∑ wt : PVec n d,
          cubeDot
            (cubeDiffI
                (bGaugedRootFamilyEquiv
                  (by omega : 0 < c) (by omega : 0 < d)
                  l.1.1 zt wt) +
              cubeDiffK
                (wGaugedRootFamilyEquiv
                  (by omega : 0 < c) l.1.2 zt))
            (aGaugedRootFamilyEquiv
              (by omega : 0 < c) (by omega : 0 < d)
              A.1 zt wt) :=
      literal_phase_gauged_ZW
        (by omega : 0 < c) (by omega : 0 < d) l A
    _ =
        ∑ zt : PVec n c,
          rawLocalPhase
            (literalOuterLeftFamily
              (by omega : 0 < c) (by omega : 0 < d) l zt)
            (literalOuterRightFamily
              (by omega : 0 < c) (by omega : 0 < d) A zt) := by
      rfl
    _ = _ :=
      raw_total_pairing_Z_then_W hn hc2 hd2
        (literalOuterLeftFamily
          (by omega : 0 < c) (by omega : 0 < d) l)
        (literalOuterRightFamily
          (by omega : 0 < c) (by omega : 0 < d) A)

end TotalEOEEInternal

end

end Core4loop.SquareDiagonal.EvenP
