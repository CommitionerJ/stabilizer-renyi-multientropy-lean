import Core4loop.SquareDiagonal.EvenP.CubeReindex
import Core4loop.SquareDiagonal.EvenP.BranchRanks

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

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

private noncomputable def singletonBiFamilyEquiv
    {n : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :
    (PVec n 1 → PVec n 1 → V) ≃ₗ[F] V where
  toFun f := f zeroVec zeroVec
  invFun v := fun _ _ => v
  left_inv f := by
    funext p q
    rw [pVec_one_eq_zeroVec p, pVec_one_eq_zeroVec q]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def singletonTriFamilyEquiv
    {n : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :
    (PVec n 1 → PVec n 1 → PVec n 1 → V) ≃ₗ[F] V where
  toFun f := f zeroVec zeroVec zeroVec
  invFun v := fun _ _ _ => v
  left_inv f := by
    funext p q r
    rw [pVec_one_eq_zeroVec p, pVec_one_eq_zeroVec q,
      pVec_one_eq_zeroVec r]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def leftAmbientEquiv
    {n : Nat} [NeZero n] :
    (BFun4 n 1 1 1 × WFun4 n 1 1 1) ≃ₗ[F]
      DiamondEOOOLeftAmbient n :=
  ((diamondBRootCubeEquiv (n := n) (c := 1) (d := 1)
      Nat.zero_lt_one Nat.zero_lt_one).prodCongr
    (diamondWRootCubeEquiv (n := n) (b := 1) (c := 1)
      Nat.zero_lt_one Nat.zero_lt_one)).trans
    ((singletonBiFamilyEquiv (n := n) (CyclicCube n)).prodCongr
      (singletonBiFamilyEquiv (n := n) (CyclicCube n)))

private noncomputable def aAmbientEquiv
    {n : Nat} [NeZero n] :
    AFun4 n 1 1 1 ≃ₗ[F] CyclicCube n :=
  (diamondARootCubeEquiv
      (n := n) (b := 1) (c := 1) (d := 1)
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one).trans
    (singletonTriFamilyEquiv (n := n) (CyclicCube n))

@[simp] private theorem leftAmbientEquiv_apply
    {n : Nat} [NeZero n]
    (x : BFun4 n 1 1 1 × WFun4 n 1 1 1) :
    leftAmbientEquiv x =
      (diamondBRootCubeEquiv Nat.zero_lt_one Nat.zero_lt_one x.1
          zeroVec zeroVec,
        diamondWRootCubeEquiv Nat.zero_lt_one Nat.zero_lt_one x.2
          zeroVec zeroVec) := by
  rfl

@[simp] private theorem aAmbientEquiv_apply
    {n : Nat} [NeZero n] (A : AFun4 n 1 1 1) :
    aAmbientEquiv A =
      diamondARootCubeEquiv
        Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one A
        zeroVec zeroVec zeroVec := by
  rfl

private theorem leftAmbientEquiv_mem_iff
    {n : Nat} [NeZero n]
    (x : BFun4 n 1 1 1 × WFun4 n 1 1 1) :
    x ∈ DiamondEvenPLeft n 1 1 1 ↔
      leftAmbientEquiv x ∈ DiamondEOOOLeftSource n := by
  simp only [DiamondEvenPLeft, DiamondEOOOLeftSource,
    LinearMap.mem_ker]
  constructor
  · intro hx
    funext i j k
    have hpoint := congrFun (congrFun (congrFun (congrFun hx
      (zeroVec : PVec n 1))
      ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
        (i, zeroVec))) j)
      ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
        (k, zeroVec))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
      x.1 x.2 zeroVec zeroVec i j k] at hpoint
    simp only [sum_pVec_one, vecSum_zero_local, add_zero, sub_zero] at hpoint
    simpa [diamondEOOOLeftConstraintMap] using hpoint
  · intro hx
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
      x.1 x.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2,
      pVec_one_eq_zeroVec (ew w).2]
    simp only [sum_pVec_one, vecSum_zero_local, add_zero, sub_zero]
    have hpoint := congrFun (congrFun (congrFun hx
      (ey y).1) sz) (ew w).1
    simpa [diamondEOOOLeftConstraintMap] using hpoint

noncomputable def diamondEvenPLeftEOOOEquiv
    {n : Nat} [NeZero n] :
    DiamondEvenPLeft n 1 1 1 ≃ₗ[F] DiamondEOOOLeftSource n where
  toFun l :=
    ⟨leftAmbientEquiv l.1,
      (leftAmbientEquiv_mem_iff l.1).mp l.2⟩
  invFun q :=
    ⟨leftAmbientEquiv.symm q.1,
      (leftAmbientEquiv_mem_iff
        (leftAmbientEquiv.symm q.1)).mpr q.2⟩
  left_inv l := by
    apply Subtype.ext
    exact leftAmbientEquiv.symm_apply_apply l.1
  right_inv q := by
    apply Subtype.ext
    exact leftAmbientEquiv.apply_symm_apply q.1
  map_add' l l' := by
    apply Subtype.ext
    exact leftAmbientEquiv.map_add l.1 l'.1
  map_smul' r l := by
    apply Subtype.ext
    exact leftAmbientEquiv.map_smul r l.1

private theorem aAmbientEquiv_mem_iff
    {n : Nat} [NeZero n]
    (A : AFun4 n 1 1 1) :
    A ∈ DiamondEvenPReachableA n 1 1 1 ↔
      aAmbientEquiv A ∈ DiamondEOOORightSource n := by
  change
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := 1) (c := 1) (d := 1) A ∈
        LinearMap.range
          (squareCompat
            (n := n) (a := 1) (b := 1) (c := 1) (d := 1)) ↔
      cubeDiffJInv (aAmbientEquiv A) ∈
        LinearMap.range
          (LinearMap.coprod
            (cubeDiffP (n := n)) (cubeDiffR (n := n)))
  constructor
  · rintro ⟨bw, hbw⟩
    refine ⟨leftAmbientEquiv bw, ?_⟩
    funext i j k
    have hpoint := congrFun (congrFun (congrFun (congrFun hbw
      (zeroVec : PVec n 1))
      ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
        (i, zeroVec))) j)
      ((diamondVecHeadTailEquiv Nat.zero_lt_one).symm
        (k, zeroVec))
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
      bw.1 bw.2 zeroVec zeroVec i j k] at hpoint
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
      A zeroVec zeroVec i j k] at hpoint
    simp only [sum_pVec_one, vecSum_zero_local,
      add_zero, sub_zero] at hpoint
    simpa [diamondEOOOLeftConstraintMap] using hpoint
  · rintro ⟨q, hq⟩
    let bw := leftAmbientEquiv.symm q
    refine ⟨bw, ?_⟩
    funext p y sz w
    rw [pVec_one_eq_zeroVec p]
    let ey := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    let ew := diamondVecHeadTailEquiv (n := n) Nat.zero_lt_one
    have hy : ey.symm (ey y) = y := ey.symm_apply_apply y
    have hw : ew.symm (ew w) = w := ew.symm_apply_apply w
    rw [← hy, ← hw]
    rw [diamondCubeReindex_squareCompat
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
      bw.1 bw.2 (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [diamondCubeReindex_AConstraint
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
      A (ey y).2 (ew w).2 (ey y).1 sz (ew w).1]
    rw [pVec_one_eq_zeroVec (ey y).2,
      pVec_one_eq_zeroVec (ew w).2]
    simp only [sum_pVec_one, vecSum_zero_local,
      add_zero, sub_zero]
    have hbw : leftAmbientEquiv bw = q :=
      leftAmbientEquiv.apply_symm_apply q
    have hB := congrArg Prod.fst hbw
    have hW := congrArg Prod.snd hbw
    have hpoint := congrFun (congrFun (congrFun hq
      (ey y).1) sz) (ew w).1
    simpa [bw, diamondEOOOLeftConstraintMap] using hpoint

noncomputable def diamondEvenPReachableAEOOOEquiv
    {n : Nat} [NeZero n] :
    DiamondEvenPReachableA n 1 1 1 ≃ₗ[F]
      DiamondEOOORightSource n where
  toFun A :=
    ⟨aAmbientEquiv A.1,
      (aAmbientEquiv_mem_iff A.1).mp A.2⟩
  invFun q :=
    ⟨aAmbientEquiv.symm q.1,
      (aAmbientEquiv_mem_iff
        (aAmbientEquiv.symm q.1)).mpr q.2⟩
  left_inv A := by
    apply Subtype.ext
    exact aAmbientEquiv.symm_apply_apply A.1
  right_inv q := by
    apply Subtype.ext
    exact aAmbientEquiv.apply_symm_apply q.1
  map_add' A A' := by
    apply Subtype.ext
    exact aAmbientEquiv.map_add A.1 A'.1
  map_smul' r A := by
    apply Subtype.ext
    exact aAmbientEquiv.map_smul r A.1

private theorem cubeDot_comm_local
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot x y = cubeDot y x := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem diamondEvenPCross_EOOO_phase
    {n : Nat} [NeZero n]
    (l : DiamondEvenPLeft n 1 1 1)
    (A : DiamondEvenPReachableA n 1 1 1) :
    diamondEOOOCross
        (diamondEvenPLeftEOOOEquiv l)
        (diamondEvenPReachableAEOOOEquiv A)
      =
    diamondEvenPCross l A := by
  change
    cubeDot
        (cubeDiffI (leftAmbientEquiv l.1).1 +
          cubeDiffK (leftAmbientEquiv l.1).2)
        (aAmbientEquiv A.1) =
      coeffApplyA (diamondEvenPLeftRoot l) A.1
  rw [diamondCubeReindex_rootPairing
    Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one]
  simp only [sum_pVec_one]
  have hroot :
      diamondARootCubeEquiv
          Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
          (diamondEvenPLeftRoot l) zeroVec zeroVec zeroVec =
        cubeDiffI (leftAmbientEquiv l.1).1 +
          cubeDiffK (leftAmbientEquiv l.1).2 := by
    funext i j k
    have h := diamondCubeReindex_leftRoot
      Nat.zero_lt_one Nat.zero_lt_one Nat.zero_lt_one
      l zeroVec zeroVec zeroVec i j k
    simpa only [vecSum_zero_local, add_zero] using h
  rw [hroot]
  exact cubeDot_comm_local _ _

noncomputable def diamondEvenPCross_EOOO_rangeEquiv
    {n : Nat} [NeZero n] :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := 1) (c := 1) (d := 1))
      ≃ₗ[F]
    LinearMap.range (diamondEOOOCross (n := n)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (diamondEvenPCross
      (n := n) (b := 1) (c := 1) (d := 1))
    (diamondEOOOCross (n := n))
    (diamondEvenPLeftEOOOEquiv (n := n))
    (diamondEvenPReachableAEOOOEquiv (n := n))
    (diamondEvenPCross_EOOO_phase (n := n))

theorem rank_diamondEvenPCross_EOOO
    {n : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := 1) (d := 1)))
      =
    n * (n - 1) ^ 2 := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := 1) (c := 1) (d := 1))) =
        Module.finrank F
          (LinearMap.range (diamondEOOOCross (n := n))) :=
      LinearEquiv.finrank_eq
        (diamondEvenPCross_EOOO_rangeEquiv (n := n))
    _ = n * (n - 1) ^ 2 :=
      rank_diamondEvenP_cross_EOOO_scalar hn2 hn

end

end Core4loop.SquareDiagonal.EvenP
