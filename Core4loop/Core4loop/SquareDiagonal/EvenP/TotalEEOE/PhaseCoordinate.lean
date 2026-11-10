import Core4loop.SquareDiagonal.EvenP.TotalEEOE.LeftSource
import Core4loop.SquareDiagonal.EvenP.TotalEEOE.RightReachable
import Core4loop.SquareDiagonal.EvenP.TotalEEOE.PhaseBase
import Core4loop.SquareDiagonal.EvenP.TailPrototypeBlocks

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
-- The frozen pointwise phase certificate uses one file-wide elaboration budget.
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace T37PhaseD

open T37LeftP0 T37RightP1

noncomputable def dT37G
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n)
    (wt : PVec n d) : CyclicCube n :=
  ∑ yt, A yt wt

noncomputable def dT37H
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : PVec n b) : CyclicCube n :=
  ∑ wt, A yt wt

noncomputable def dT37D
    {n b d : Nat} [NeZero n]
    (A : PVec n b → PVec n d → CyclicCube n) :
    CyclicCube n :=
  ∑ wt, dT37G A wt

noncomputable def dT37BetaI
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp (cubeDiffI (n := n))

noncomputable def dT37BetaK
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp (cubeDiffK (n := n))

def dT37GaugedPhase
    {n b d : Nat} [NeZero n]
    (B : PVec n d → CyclicCube n)
    (W : PVec n b → CyclicCube n)
    (A : PVec n b → PVec n d → CyclicCube n) : F :=
  ∑ yt, ∑ wt,
    cubeDot (cubeDiffI (B wt) + cubeDiffK (W yt)) (A yt wt)

private theorem dT37SumAtPointTail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    [AddCommMonoid V] (f : S → V) :
    (∑ s, f s) = f s0 + ∑ t : PointedTail S s0, f t.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset S))
      (p := fun s : S => s = s0) f).symm
  calc
    (∑ s, f s) =
        (∑ s ∈ (Finset.univ : Finset S) with s = s0, f s) +
          ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
            simpa using hpart
    _ = f s0 +
        ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
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

private theorem dT37CastOddEqOne
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, rfl⟩
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem dT37SumConstOdd
    {T V : Type*} [Fintype T]
    [AddCommGroup V] [Module F V]
    (hodd : Odd (Fintype.card T)) (v : V) :
    (∑ _ : T, v) = v := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    dT37CastOddEqOne hodd, one_smul]

theorem dT37AxisDualK_eq_totalSum
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Even n) (hk2 : 2 ≤ k)
    (g : PVec n k → V) :
    (diamondEvenAxisDualCoordEquiv
        (n := n) (k := k) V hn hk2 g).1.2 =
      ∑ s, g s := by
  change
    (∑ t : DiamondEvenAxisTailIndex n k,
      (g t.1 + g (zeroVec : PVec n k))) =
        ∑ s : PVec n k, g s
  rw [Finset.sum_add_distrib,
    dT37SumConstOdd
      (odd_card_diamondEvenAxisTailIndex hn hk2),
    dT37SumAtPointTail (zeroVec : PVec n k) g]
  abel

theorem dT37Right_scalar_explicit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n) :
    (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 A).1 =
      ((dT37D A, dT37G A zeroVec + dT37D A),
       (dT37H A zeroVec + dT37D A,
        A zeroVec zeroVec + dT37G A zeroVec +
          dT37H A zeroVec + dT37D A)) := by
  have h :=
    T37RightP1.t37RightCoordinate_scalar_explicit
      hn hb2 hd2 A
  change
    (T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 A).1 =
      ((dT37D A, dT37G A zeroVec + dT37D A),
       (dT37H A zeroVec + dT37D A,
        A zeroVec zeroVec + dT37G A zeroVec +
          dT37H A zeroVec + dT37D A)) at h
  exact h

theorem dT37Right_Y_first_explicit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (yt : DiamondEvenAxisTailIndex n b) :
    ((T37RightP1.t37GaugedRightCoordinateEquiv
        hn hb2 hd2 A).2.1.1 yt).1 =
      dT37H A yt.1 + dT37H A zeroVec + dT37D A := by
  have h :=
    congrArg Prod.fst
      (T37RightP1.t37RightCoordinate_Y_explicit
        hn hb2 hd2 A yt)
  change
    ((T37RightP1.t37GaugedRightCoordinateEquiv
        hn hb2 hd2 A).2.1.1 yt).1 =
      dT37H A yt.1 + dT37H A zeroVec + dT37D A at h
  exact h

theorem dT37Right_W_first_explicit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : PVec n b → PVec n d → CyclicCube n)
    (wt : DiamondEvenAxisTailIndex n d) :
    ((T37RightP1.t37GaugedRightCoordinateEquiv
        hn hb2 hd2 A).2.2.1.1 wt).1 =
      dT37G A wt.1 + dT37G A zeroVec + dT37D A := by
  have h :=
    congrArg Prod.fst
      (T37RightP1.t37RightCoordinate_W_explicit
        hn hb2 hd2 A wt)
  change
    ((T37RightP1.t37GaugedRightCoordinateEquiv
        hn hb2 hd2 A).2.2.1.1 wt).1 =
      dT37G A wt.1 + dT37G A zeroVec + dT37D A at h
  exact h

def dT37BScalarPhase
    {n b d : Nat} [NeZero n]
    (Bc : PointedEvenValueCoords
      (PVec n d) (CyclicCube n) zeroVec)
    (q : T37RightP1.T37RightAmbientTarget n b d) : F :=
  cubeDot (cubeDiffI (Bc.1.1 + Bc.1.2)) q.1.1.1 +
    cubeDot (cubeDiffI Bc.1.1) q.1.1.2

def dT37WScalarPhase
    {n b d : Nat} [NeZero n]
    (Wc : PointedEvenValueCoords
      (PVec n b) (CyclicCube n) zeroVec)
    (q : T37RightP1.T37RightAmbientTarget n b d) : F :=
  cubeDot (cubeDiffK (Wc.1.1 + Wc.1.2)) q.1.1.1 +
    cubeDot (cubeDiffK Wc.1.1) q.1.2.1

def dT37BFirstTailPhase
    {n b d : Nat} [NeZero n]
    (Bc : PointedEvenValueCoords
      (PVec n d) (CyclicCube n) zeroVec)
    (q : T37RightP1.T37RightAmbientTarget n b d) : F :=
  ∑ wt : DiamondEvenAxisTailIndex n d,
    cubeDot (cubeDiffI (Bc.2.1 wt)) (q.2.2.1.1 wt).1

def dT37WFirstTailPhase
    {n b d : Nat} [NeZero n]
    (Wc : PointedEvenValueCoords
      (PVec n b) (CyclicCube n) zeroVec)
    (q : T37RightP1.T37RightAmbientTarget n b d) : F :=
  ∑ yt : DiamondEvenAxisTailIndex n b,
    cubeDot (cubeDiffK (Wc.2.1 yt)) (q.2.1.1 yt).1

theorem dT37GaugedPhase_split_BW
    {n b d : Nat} [NeZero n]
    (B : PVec n d → CyclicCube n)
    (W : PVec n b → CyclicCube n)
    (A : PVec n b → PVec n d → CyclicCube n) :
    dT37GaugedPhase B W A =
      (∑ wt, dT37BetaI (B wt) (dT37G A wt)) +
        ∑ yt, dT37BetaK (W yt) (dT37H A yt) := by
  unfold dT37GaugedPhase dT37BetaI dT37BetaK
  simp only [LinearMap.comp_apply, EEOEInternal.cubeDotDual,
    EEOEInternal.cubeDot_add_left, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro wt _
    change
      (∑ yt, EEOEInternal.cubeDotDual
          (cubeDiffI (B wt)) (A yt wt)) =
        EEOEInternal.cubeDotDual
          (cubeDiffI (B wt)) (∑ yt, A yt wt)
    rw [map_sum]
  · apply Finset.sum_congr rfl
    intro yt _
    change
      (∑ wt, EEOEInternal.cubeDotDual
          (cubeDiffK (W yt)) (A yt wt)) =
        EEOEInternal.cubeDotDual
          (cubeDiffK (W yt)) (∑ wt, A yt wt)
    rw [map_sum]

theorem dT37B_pairing_coordinates
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (B : PVec n d → CyclicCube n)
    (A : PVec n b → PVec n d → CyclicCube n) :
    let Bc :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := d) (CyclicCube n) hn hd2 B
    let q :=
      T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 A
    (∑ wt, dT37BetaI (B wt) (dT37G A wt)) =
      dT37BScalarPhase Bc q + dT37BFirstTailPhase Bc q := by
  dsimp only
  let EB :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
  let DG :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := d) (CyclicCube n) hn hd2
        (dT37G A)
  have h :=
    pointedEvenValue_pairing
      (zeroVec : PVec n d) (even_card_PVec hn hd2)
      (dT37BetaI (n := n)) B (dT37G A)
  have hDGK : DG.1.2 = dT37D A :=
    dT37AxisDualK_eq_totalSum
      (CyclicCube n) hn hd2 (dT37G A)
  have hDG0 : DG.1.1 = dT37G A zeroVec := rfl
  have hDGtail :
      ∀ wt : DiamondEvenAxisTailIndex n d,
        DG.2.1 wt =
          dT37G A wt.1 + dT37G A zeroVec + dT37D A := by
    intro wt
    change
      dT37G A wt.1 + dT37G A zeroVec + DG.1.2 =
        dT37G A wt.1 + dT37G A zeroVec + dT37D A
    rw [hDGK]
  rw [h]
  unfold dT37BScalarPhase dT37BFirstTailPhase
  rw [dT37Right_scalar_explicit hn hb2 hd2 A]
  simp_rw [dT37Right_W_first_explicit hn hb2 hd2 A]
  change
    dT37BetaI (EB B).1.1 DG.1.1 +
        dT37BetaI (EB B).1.2 DG.1.2 +
        (∑ wt, dT37BetaI ((EB B).2.1 wt) (DG.2.1 wt)) =
      _
  rw [hDG0, hDGK]
  simp_rw [hDGtail]
  simp only [EB, dT37BetaI, LinearMap.comp_apply,
    EEOEInternal.cubeDotDual, LinearMap.coe_mk, AddHom.coe_mk, map_add,
    EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  abel_nf
  simp only [two_smul, F_add_self, add_zero]

theorem dT37W_pairing_coordinates
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (W : PVec n b → CyclicCube n)
    (A : PVec n b → PVec n d → CyclicCube n) :
    let Wc :=
      diamondEvenAxisSrcCoordEquiv
        (n := n) (k := b) (CyclicCube n) hn hb2 W
    let q :=
      T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 A
    (∑ yt, dT37BetaK (W yt) (dT37H A yt)) =
      dT37WScalarPhase Wc q + dT37WFirstTailPhase Wc q := by
  dsimp only
  let EW :=
    diamondEvenAxisSrcCoordEquiv
      (n := n) (k := b) (CyclicCube n) hn hb2
  let DH :=
    diamondEvenAxisDualCoordEquiv
      (n := n) (k := b) (CyclicCube n) hn hb2
        (dT37H A)
  have h :=
    pointedEvenValue_pairing
      (zeroVec : PVec n b) (even_card_PVec hn hb2)
      (dT37BetaK (n := n)) W (dT37H A)
  have hDHK : DH.1.2 = dT37D A := by
    rw [dT37AxisDualK_eq_totalSum]
    unfold dT37D dT37G dT37H
    rw [Finset.sum_comm]
  have hDH0 : DH.1.1 = dT37H A zeroVec := rfl
  have hDHtail :
      ∀ yt : DiamondEvenAxisTailIndex n b,
        DH.2.1 yt =
          dT37H A yt.1 + dT37H A zeroVec + dT37D A := by
    intro yt
    change
      dT37H A yt.1 + dT37H A zeroVec + DH.1.2 =
        dT37H A yt.1 + dT37H A zeroVec + dT37D A
    rw [hDHK]
  rw [h]
  unfold dT37WScalarPhase dT37WFirstTailPhase
  rw [dT37Right_scalar_explicit hn hb2 hd2 A]
  simp_rw [dT37Right_Y_first_explicit hn hb2 hd2 A]
  change
    dT37BetaK (EW W).1.1 DH.1.1 +
        dT37BetaK (EW W).1.2 DH.1.2 +
        (∑ yt, dT37BetaK ((EW W).2.1 yt) (DH.2.1 yt)) =
      _
  rw [hDH0, hDHK]
  simp_rw [hDHtail]
  simp only [EW, dT37BetaK, LinearMap.comp_apply,
    EEOEInternal.cubeDotDual, LinearMap.coe_mk, AddHom.coe_mk, map_add,
    EEOEInternal.cubeDot_add_left,
    EEOEInternal.cubeDot_add_right]
  abel_nf
  simp only [two_smul, F_add_self, add_zero]

theorem dT37AmbientScalar_split
    {n b d : Nat} [NeZero n]
    (Bc : PointedEvenValueCoords
      (PVec n d) (CyclicCube n) zeroVec)
    (Wc : PointedEvenValueCoords
      (PVec n b) (CyclicCube n) zeroVec)
    (q : T37RightP1.T37RightAmbientTarget n b d) :
    EEOEInternal.ambientPhase
        (diamondEEOECoeffMap (Bc.1, Wc.1)) q.1 =
      dT37BScalarPhase Bc q + dT37WScalarPhase Wc q := by
  simp only [EEOEInternal.ambientPhase, diamondEEOECoeffMap,
    dT37BScalarPhase, dT37WScalarPhase,
    LinearMap.coe_mk, AddHom.coe_mk, map_add,
    EEOEInternal.cubeDot_add_left]
  simp only [cubeDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero]
  abel

theorem dT37GaugedPhase_coordinate_ledger
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (B : PVec n d → CyclicCube n)
    (W : PVec n b → CyclicCube n)
    (A : PVec n b → PVec n d → CyclicCube n) :
    let lq :=
      (((diamondEvenAxisSrcCoordEquiv
          (n := n) (k := d) (CyclicCube n) hn hd2 B).1,
        (diamondEvenAxisSrcCoordEquiv
          (n := n) (k := b) (CyclicCube n) hn hb2 W).1))
    let rq :=
      T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2 A
    dT37GaugedPhase B W A =
      EEOEInternal.ambientPhase
          (diamondEEOECoeffMap lq) rq.1 +
        (∑ yt : DiamondEvenAxisTailIndex n b,
          cubeDot
            (cubeDiffK
              ((diamondEvenAxisSrcCoordEquiv
                (n := n) (k := b) (CyclicCube n)
                hn hb2 W).2.1 yt))
            (rq.2.1.1 yt).1) +
        (∑ wt : DiamondEvenAxisTailIndex n d,
          cubeDot
            (cubeDiffI
              ((diamondEvenAxisSrcCoordEquiv
                (n := n) (k := d) (CyclicCube n)
                hn hd2 B).2.1 wt))
            (rq.2.2.1.1 wt).1) := by
  dsimp only
  rw [dT37GaugedPhase_split_BW,
    dT37B_pairing_coordinates hn hb2 hd2 B A,
    dT37W_pairing_coordinates hn hb2 hd2 W A]
  rw [dT37AmbientScalar_split]
  unfold dT37BFirstTailPhase dT37WFirstTailPhase
  abel

private noncomputable def dT37PhaseCubeIKShift
    {n : Nat} [NeZero n] (ui uk : I n) :
    CyclicCube n ≃ₗ[F] CyclicCube n where
  toFun X i j k := X (i - ui) j (k - uk)
  invFun X i j k := X (i + ui) j (k + uk)
  left_inv X := by
    funext i j k
    simp
  right_inv X := by
    funext i j k
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] private theorem dT37PhaseCubeIKShift_apply
    {n : Nat} [NeZero n] (ui uk : I n)
    (X : CyclicCube n) (i j k : I n) :
    dT37PhaseCubeIKShift ui uk X i j k =
      X (i - ui) j (k - uk) :=
  rfl

private theorem dT37PhaseCubeIKShift_pairing_same
    {n : Nat} [NeZero n] (ui uk : I n)
    (X Y : CyclicCube n) :
    cubeDot
        (dT37PhaseCubeIKShift ui uk X)
        (dT37PhaseCubeIKShift ui uk Y) =
      cubeDot X Y := by
  classical
  unfold cubeDot
  let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
    Equiv.prodCongr (Equiv.addRight (-ui))
      (Equiv.prodCongr (Equiv.refl (I n))
        (Equiv.addRight (-uk)))
  apply Fintype.sum_equiv e
  intro q
  simp [e, dT37PhaseCubeIKShift, sub_eq_add_neg]

noncomputable def dT37PhaseAGauge
    {n b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (A : AFun4 n b 1 d) :
    PVec n b → PVec n d → CyclicCube n :=
  fun yt wt =>
    dT37PhaseCubeIKShift (vecSum yt) (vecSum wt)
      (diamondARootCubeEquiv hb Nat.zero_lt_one hd
        A yt zeroVec wt)

@[simp] theorem dT37PhaseAGauge_apply
    {n b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (A : AFun4 n b 1 d)
    (yt : PVec n b) (wt : PVec n d)
    (i j k : I n) :
    dT37PhaseAGauge hb hd A yt wt i j k =
      diamondARootCubeEquiv hb Nat.zero_lt_one hd
        A yt zeroVec wt
        (i - vecSum yt) j (k - vecSum wt) :=
  rfl

theorem dT37RightAmbientEquiv_eq_phaseCoords
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (A : AFun4 n b 1 d) :
    T37RightP1.t37RightAmbientEquiv hn hb2 hd2 A =
      T37RightP1.t37GaugedRightCoordinateEquiv hn hb2 hd2
        (dT37PhaseAGauge
          (by omega : 0 < b) (by omega : 0 < d) A) := by
  rfl

theorem dT37PhaseCubeIKShift_leftRoot
    {n b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (l : DiamondEvenPLeft n b 1 d)
    (yt : PVec n b) (wt : PVec n d) :
    dT37PhaseCubeIKShift (vecSum yt) (vecSum wt)
        (diamondARootCubeEquiv hb Nat.zero_lt_one hd
          (diamondEvenPLeftRoot l) yt zeroVec wt) =
      cubeDiffI
          (T37LeftP0.t37BGaugedWFamilyEquiv hd l.1.1 wt) +
        cubeDiffK
          (T37LeftP0.t37WGaugedYFamilyEquiv hb l.1.2 yt) := by
  funext i j k
  simp only [dT37PhaseCubeIKShift_apply, Pi.add_apply]
  change
    diamondEvenPLeftRoot l
        ((diamondVecHeadTailEquiv hb).symm
          (i - vecSum yt, yt))
        ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
          (j, zeroVec))
        ((diamondVecHeadTailEquiv hd).symm
          (k - vecSum wt, wt)) =
      _
  rw [diamondCubeReindex_leftRoot
    hb Nat.zero_lt_one hd l yt zeroVec wt
      (i - vecSum yt) j (k - vecSum wt)]
  rw [EEOEInternal.cubeDiffI_apply, EEOEInternal.cubeDiffK_apply]
  rw [EEOEInternal.cubeDiffI_apply, EEOEInternal.cubeDiffK_apply]
  simp only [
    T37LeftP0.t37BGaugedWFamilyEquiv_apply,
    T37LeftP0.t37WGaugedYFamilyEquiv_apply]
  congr 1 <;> abel

private theorem dT37SumPVecOne
    {n : Nat} [NeZero n]
    {V : Type*} [AddCommMonoid V]
    (f : PVec n 1 → V) :
    (∑ z : PVec n 1, f z) = f zeroVec := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro z _ hz
    exact (hz (pVec_one_eq_zeroVec z)).elim
  · simp

private theorem dT37CubeDotComm
    {n : Nat} [NeZero n] (X Y : CyclicCube n) :
    cubeDot X Y = cubeDot Y X := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem dT37LiteralPhaseGauged
    {n b d : Nat} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    diamondEvenPCross l A =
      ∑ yt : PVec n b, ∑ wt : PVec n d,
        cubeDot
          (cubeDiffI
              (T37LeftP0.t37BGaugedWFamilyEquiv hd l.1.1 wt) +
            cubeDiffK
              (T37LeftP0.t37WGaugedYFamilyEquiv hb l.1.2 yt))
          (dT37PhaseAGauge hb hd A.1 yt wt) := by
  change coeffApplyA (diamondEvenPLeftRoot l) A.1 = _
  rw [diamondCubeReindex_rootPairing hb Nat.zero_lt_one hd]
  simp_rw [dT37SumPVecOne]
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro wt _
  let ui := vecSum yt
  let uk := vecSum wt
  let AR :=
    diamondARootCubeEquiv hb Nat.zero_lt_one hd
      A.1 yt zeroVec wt
  let LR :=
    diamondARootCubeEquiv hb Nat.zero_lt_one hd
      (diamondEvenPLeftRoot l) yt zeroVec wt
  calc
    cubeDot AR LR =
        cubeDot
          (dT37PhaseCubeIKShift ui uk AR)
          (dT37PhaseCubeIKShift ui uk LR) :=
      (dT37PhaseCubeIKShift_pairing_same ui uk AR LR).symm
    _ =
        cubeDot
          (dT37PhaseAGauge hb hd A.1 yt wt)
          (cubeDiffI
              (T37LeftP0.t37BGaugedWFamilyEquiv hd l.1.1 wt) +
            cubeDiffK
              (T37LeftP0.t37WGaugedYFamilyEquiv hb l.1.2 yt)) := by
      rw [show
        dT37PhaseCubeIKShift ui uk AR =
          dT37PhaseAGauge hb hd A.1 yt wt from rfl]
      rw [show
        dT37PhaseCubeIKShift ui uk LR =
          cubeDiffI
              (T37LeftP0.t37BGaugedWFamilyEquiv hd l.1.1 wt) +
            cubeDiffK
              (T37LeftP0.t37WGaugedYFamilyEquiv hb l.1.2 yt) from
        dT37PhaseCubeIKShift_leftRoot hb hd l yt wt]
    _ = _ := dT37CubeDotComm _ _

theorem dT37LiteralPhaseCoordinateSplit
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    diamondEvenPCross l A =
      diamondEEOECross
          (T37LeftP0.t37LeftSourceEquiv
            hn hb2 hd2 l).1
          (T37RightP1.t37RightReachableEquiv
            hn hb2 hd2 A).1 +
        (∑ yt : DiamondEvenAxisTailIndex n b,
          cubeDot
            (cubeDiffK
              ((T37LeftP0.t37LeftSourceEquiv
                hn hb2 hd2 l).2.1.1 yt).1)
            ((T37RightP1.t37RightReachableEquiv
              hn hb2 hd2 A).2.1.1 yt).1.1) +
        (∑ wt : DiamondEvenAxisTailIndex n d,
          cubeDot
            (cubeDiffI
              ((T37LeftP0.t37LeftSourceEquiv
                hn hb2 hd2 l).2.2.1.1 wt).1)
            ((T37RightP1.t37RightReachableEquiv
              hn hb2 hd2 A).2.2.1.1 wt).1.1) := by
  rw [dT37LiteralPhaseGauged
    (by omega : 0 < b) (by omega : 0 < d) l A]
  change
    dT37GaugedPhase
        (T37LeftP0.t37BGaugedWFamilyEquiv
          (by omega : 0 < d) l.1.1)
        (T37LeftP0.t37WGaugedYFamilyEquiv
          (by omega : 0 < b) l.1.2)
        (dT37PhaseAGauge
          (by omega : 0 < b) (by omega : 0 < d) A.1)
      = _
  rw [dT37GaugedPhase_coordinate_ledger hn hb2 hd2]
  rw [← dT37RightAmbientEquiv_eq_phaseCoords hn hb2 hd2 A.1]
  rfl

private theorem dT37CubeDiffI_eq_JStar_of_P_zero
    {n : Nat} [NeZero n]
    (u : CyclicCube n)
    (hu : cubeDiffP u = 0) :
    cubeDiffI u = cubeDiffJStar u := by
  funext i j k
  rw [EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffJStar_apply]
  have h :=
    congrFun (congrFun (congrFun hu i) (j + 1)) k
  simp only [Pi.zero_apply] at h
  rw [EEOEInternal.cubeDiffP_apply] at h
  rw [show (j + 1) - 1 = j by abel] at h
  exact (EEOEInternal.eq_of_add_eq_zero h).symm ▸ rfl

theorem dT37PBlock_JKernel_phase_zero
    {n : Nat} [NeZero n]
    (u : EEOEInternal.PBlockLeft n)
    (v : T37RightP1.T37JKernel n) :
    cubeDot (cubeDiffI u.1) v.1 = 0 := by
  have hu : cubeDiffP u.1 = 0 :=
    LinearMap.mem_ker.mp u.2
  have hv : cubeDiffJInv v.1 = 0 :=
    LinearMap.mem_ker.mp v.2
  rw [dT37CubeDiffI_eq_JStar_of_P_zero u.1 hu,
    cubeDiffJ_pairing_adjoint, hv]
  simp [cubeDot]

theorem dT37RBlock_JKernel_phase_zero
    {n : Nat} [NeZero n]
    (u : EEOEInternal.RBlockLeft n)
    (v : T37RightP1.T37JKernel n) :
    cubeDot (cubeDiffK u.1) v.1 = 0 := by
  let up : EEOEInternal.PBlockLeft n :=
    EEOEInternal.rLeftEquivP u
  let vp : T37RightP1.T37JKernel n :=
    ⟨EEOEInternal.swapIK v.1, by
      apply LinearMap.mem_ker.mpr
      rw [← EEOEInternal.swapIK_cubeDiffJInv,
        LinearMap.mem_ker.mp v.2, map_zero]⟩
  have hzero :
      cubeDot (cubeDiffI up.1) vp.1 = 0 :=
    dT37PBlock_JKernel_phase_zero up vp
  change cubeDot (cubeDiffK u.1) v.1 = 0
  calc
    cubeDot (cubeDiffK u.1) v.1 =
        cubeDot
          (EEOEInternal.swapIK (cubeDiffK u.1))
          (EEOEInternal.swapIK v.1) :=
      (EEOEInternal.cubeDot_swap_both
        (cubeDiffK u.1) v.1).symm
    _ =
        cubeDot
          (cubeDiffI (EEOEInternal.swapIK u.1))
          (EEOEInternal.swapIK v.1) := by
      rw [EEOEInternal.swapIK_cubeDiffK]
    _ = 0 := hzero

theorem dT37LiteralYFirstPhase_eq_zero
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    (∑ yt : DiamondEvenAxisTailIndex n b,
      cubeDot
        (cubeDiffK
          ((T37LeftP0.t37LeftSourceEquiv
            hn hb2 hd2 l).2.1.1 yt).1)
        ((T37RightP1.t37RightReachableEquiv
          hn hb2 hd2 A).2.1.1 yt).1.1) = 0 := by
  apply Finset.sum_eq_zero
  intro yt _
  exact
    dT37RBlock_JKernel_phase_zero
      ((T37LeftP0.t37LeftSourceEquiv
        hn hb2 hd2 l).2.1.1 yt)
      ((T37RightP1.t37RightReachableEquiv
        hn hb2 hd2 A).2.1.1 yt).1

theorem dT37LiteralWFirstPhase_eq_zero
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    (∑ wt : DiamondEvenAxisTailIndex n d,
      cubeDot
        (cubeDiffI
          ((T37LeftP0.t37LeftSourceEquiv
            hn hb2 hd2 l).2.2.1.1 wt).1)
        ((T37RightP1.t37RightReachableEquiv
          hn hb2 hd2 A).2.2.1.1 wt).1.1) = 0 := by
  apply Finset.sum_eq_zero
  intro wt _
  exact
    dT37PBlock_JKernel_phase_zero
      ((T37LeftP0.t37LeftSourceEquiv
        hn hb2 hd2 l).2.2.1.1 wt)
      ((T37RightP1.t37RightReachableEquiv
        hn hb2 hd2 A).2.2.1.1 wt).1

theorem dT37LiteralPhase_eq_scalar
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    diamondEvenPCross l A =
      diamondEEOECross
        (T37LeftP0.t37LeftSourceEquiv
          hn hb2 hd2 l).1
        (T37RightP1.t37RightReachableEquiv
          hn hb2 hd2 A).1 := by
  rw [dT37LiteralPhaseCoordinateSplit hn hb2 hd2 l A,
    dT37LiteralYFirstPhase_eq_zero hn hb2 hd2 l A,
    dT37LiteralWFirstPhase_eq_zero hn hb2 hd2 l A]
  simp

def dT37FrozenBlockPhase
    {n b d : Nat} [NeZero n]
    (l : T37LeftP0.T37LeftSourceTarget n b d)
    (A : T37RightP1.T37RightReachableTarget n b d) : F :=
  diamondEEOECross l.1 A.1 +
    (∑ yt : DiamondEvenAxisTailIndex n b,
      t37YBaseCross (l.2.1.1 yt) (A.2.1.1 yt)) +
    (∑ wt : DiamondEvenAxisTailIndex n d,
      t37WBaseCross (l.2.2.1.1 wt) (A.2.2.1.1 wt)) +
    diamondMixedTailAmplify
      (n := n) (k := b) (l := d)
      (t37MixedBaseCross (n := n)) l.2.2.2 A.2.2.2

theorem dT37FrozenBlockPhase_eq_scalar
    {n b d : Nat} [NeZero n]
    (l : T37LeftP0.T37LeftSourceTarget n b d)
    (A : T37RightP1.T37RightReachableTarget n b d) :
    dT37FrozenBlockPhase l A = diamondEEOECross l.1 A.1 := by
  unfold dT37FrozenBlockPhase
  rw [t37YBaseCross_eq_zero, t37WBaseCross_eq_zero,
    t37MixedBaseCross_eq_zero]
  simp [diamondMixedTailAmplify]

theorem dT37FrozenPointwisePhaseSquare
    {n b d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hd2 : 2 ≤ d)
    (l : DiamondEvenPLeft n b 1 d)
    (A : DiamondEvenPReachableA n b 1 d) :
    dT37FrozenBlockPhase
        (T37LeftP0.t37LeftSourceEquiv hn hb2 hd2 l)
        (T37RightP1.t37RightReachableEquiv hn hb2 hd2 A) =
      diamondEvenPCross l A := by
  rw [dT37FrozenBlockPhase_eq_scalar]
  exact (dT37LiteralPhase_eq_scalar hn hb2 hd2 l A).symm

end T37PhaseD

end

end Core4loop.SquareDiagonal.EvenP
