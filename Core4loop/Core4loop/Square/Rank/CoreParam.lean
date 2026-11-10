import Core4loop.Square.Rank.PairRank
import Core4loop.Square.Rank.Core

open scoped BigOperators

namespace Core4loop

abbrev SquareCoreParam (n : ℕ) [NeZero n] := MatrixZeroSum n × LineZeroSum n

theorem finrank_SquareCoreParam {n : ℕ} [NeZero n] :
    Module.finrank F (SquareCoreParam n) = 2 * (n - 1) ^ 2 + (n - 1) := by
  rw [Module.finrank_prod, finrank_MatrixZeroSum, finrank_LineZeroSum]
  let m := n - 1
  change m ^ 2 + m * n = 2 * m ^ 2 + m
  have hnpos : 0 < n := NeZero.pos n
  have hn : n = m + 1 := by
    dsimp [m]
    omega
  rw [hn]
  ring

noncomputable def coreRootShear {n : ℕ} [NeZero n]
    (R : SquareRootCore n) (t sy sw : I n) : F :=
  rootCoreEval R sy (t - sy - sw) sw

noncomputable def corePVal {n : ℕ} [NeZero n]
    (R : SquareRootCore n) (S : SquareCompatCore n)
    (t r : I n) : F :=
  rootCoreEval R 0 (t - r) r + compatCoreEval S 0 (t - r) r

noncomputable def SquareCoreAllowed.readS0
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) : MatrixZeroSum n :=
  x.1.2 0

@[simp]
theorem SquareCoreAllowed_readS0_apply
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) (sy sw : I n) :
    (SquareCoreAllowed.readS0 x).1 sy sw = (x.1.2 0).1 sy sw := rfl

noncomputable def SquareCoreAllowed.readLineVal
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) : I n → Profile n :=
  fun t r => corePVal x.1.1 x.1.2 t r

@[simp]
theorem SquareCoreAllowed_readLineVal_apply
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) (t r : I n) :
    SquareCoreAllowed.readLineVal x t r =
      corePVal x.1.1 x.1.2 t r := rfl

lemma coreP_step
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n)
    (t sy sw : I n) :
    rootCoreEval x.1.1 sy (t - sy - sw) sw +
        compatCoreEval x.1.2 sy (t - sy - sw) sw =
      rootCoreEval x.1.1 (sy + 1) (t - sy - sw) (sw - 1) +
        compatCoreEval x.1.2 (sy + 1) (t - sy - sw) (sw - 1) := by
  let z : I n := t - sy - sw
  have hallowed := (mem_SquareCoreAllowed_iff (n := n) x.1).1 x.2
  have hB := (hallowed sy z sw).1
  have hW := (hallowed (sy + 1) z (sw - 1)).2
  have hsum :
      squareCoreCurlB x.1.1 x.1.2 sy z sw +
        squareCoreCurlW x.1.1 x.1.2 (sy + 1) z (sw - 1) = 0 := by
    rw [hB, hW]
    simp
  unfold squareCoreCurlB squareCoreCurlW rootCoreEval compatCoreEval at hsum
  dsimp [z] at hsum
  have hzB : sy + (t - sy - sw) + sw = t := by abel
  have hzB' : sy + 1 + (t - sy - sw) + sw = t + 1 := by abel
  have hzW : sy + 1 + (t - sy - sw) + (sw - 1) = t := by abel
  have hzW' : sy + 1 + (t - sy - sw) + ((sw - 1) + 1) = t + 1 := by abel
  have hsw : sw - 1 + 1 = sw := by abel
  rw [hzB, hzB', hzW, hzW', hsw] at hsum
  ring_nf at hsum
  have htwo : (2 : F) = 0 := by decide
  have htarget :
      (x.1.1 (t - sy - sw)).1 sy sw +
          (x.1.2 t).1 sy sw +
        ((x.1.1 (t - sy - sw)).1 (sy + 1) (sw - 1) +
          (x.1.2 t).1 (sy + 1) (sw - 1)) = 0 := by
    simpa [htwo, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
  apply F_eq_of_add_eq_zero
  have hzB₂ : sy + (t + -sy + -sw) + sw = t := by abel
  have hzW₂ : sy + 1 + (t + -sy + -sw) + (sw + -1) = t := by abel
  simpa [rootCoreEval, compatCoreEval, corePVal, sub_eq_add_neg, hzB₂, hzW₂] using htarget

lemma coreP_independent
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n)
    (t sy sw : I n) :
    rootCoreEval x.1.1 sy (t - sy - sw) sw +
        compatCoreEval x.1.2 sy (t - sy - sw) sw =
      corePVal x.1.1 x.1.2 t (sy + sw) := by
  let r : I n := sy + sw
  let g : I n → F := fun s =>
    rootCoreEval x.1.1 s (t - s - (r - s)) (r - s) +
      compatCoreEval x.1.2 s (t - s - (r - s)) (r - s)
  have hconst : ∀ s : I n, g (s + 1) = g s := by
    intro s
    unfold g
    have hcoord : r - (s + 1) = r - s - 1 := by abel
    have hz : t - (s + 1) - (r - s - 1) = t - s - (r - s) := by abel
    rw [hcoord, hz]
    exact (coreP_step (n := n) x t s (r - s)).symm
  have hread := zmod_step_const g hconst sy
  have hleft₁ : r - sy = sw := by
    dsimp [r]
    abel
  have hleft₂ : t - sy - (r - sy) = t - sy - sw := by
    rw [hleft₁]
  have hright₁ : r - 0 = sy + sw := by
    dsimp [r]
    abel
  have hright₂ : t - 0 - (r - 0) = t - (sy + sw) := by
    rw [hright₁]
    abel
  change
    rootCoreEval x.1.1 sy (t - sy - (r - sy)) (r - sy) +
        compatCoreEval x.1.2 sy (t - sy - (r - sy)) (r - sy) =
      rootCoreEval x.1.1 0 (t - 0 - (r - 0)) (r - 0) +
        compatCoreEval x.1.2 0 (t - 0 - (r - 0)) (r - 0)
    at hread
  rw [hleft₁, hright₁] at hread
  have hright₂' : t - 0 - (sy + sw) = t - (sy + sw) := by abel
  rw [hright₂'] at hread
  simpa [corePVal] using hread

lemma sum_add_add_eq_sum_third_of_same_sum
    {n : ℕ} [NeZero n] (A B C : I n → F)
    (hAB : (∑ i : I n, A i) = ∑ i : I n, B i) :
    (∑ i : I n, ((A i + B i + C i) : F)) = ∑ i : I n, C i := by
  calc
    (∑ i : I n, ((A i + B i + C i) : F))
        = (∑ i : I n, ((A i + B i) : F)) + ∑ i : I n, C i := by
            rw [Finset.sum_add_distrib]
    _ = ((∑ i : I n, A i) + ∑ i : I n, B i) + ∑ i : I n, C i := by
            congr 1
            rw [Finset.sum_add_distrib]
    _ = ((∑ i : I n, B i) + ∑ i : I n, B i) + ∑ i : I n, C i := by
            rw [hAB]
    _ = 0 + ∑ i : I n, C i := by
            rw [F_add_self]
    _ = ∑ i : I n, C i := by
            simp

lemma diag_sum_eq_col_sum_of_step
    {n : ℕ} [NeZero n]
    (P H : I n → I n → F)
    (hHrow : ∀ t : I n, (∑ r : I n, H t r) = 0)
    (hstep : ∀ t r : I n,
      H (t + 1) r + H t r = P t (r - 1) + P t r)
    (r0 : I n) :
    (∑ r : I n, ((P r r) + (H r r) : F)) =
      ∑ t : I n, P t r0 := by
  classical
  have hHmem : ∀ t : I n, (fun r : I n => H t r) ∈ ZeroSumProfile n := by
    intro t
    apply LinearMap.mem_ker.mpr
    exact hHrow t
  have hHrange : ∀ t : I n,
      (fun r : I n => H t r) ∈ LinearMap.range (cycDiff (n := n) F) := by
    intro t
    rw [range_cycDiff_eq_ZeroSumProfile]
    exact hHmem t
  let U : I n → Profile n := fun t => Classical.choose (hHrange t)
  have hU : ∀ t r : I n, H t r = U t r + U t (r + 1) := by
    intro t r
    have hs := Classical.choose_spec (hHrange t)
    have hr := congrFun hs r
    simpa [U, cycDiff] using hr.symm
  let C : I n → I n → F := fun t r => U (t + 1) r + U t r + P t (r - 1)
  let c : I n → F := fun t => C t 0
  have hCstep : ∀ t r : I n, C t (r + 1) = C t r := by
    intro t r
    apply F_eq_of_add_eq_zero
    have hstepU :
        (U (t + 1) r + U (t + 1) (r + 1)) +
            (U t r + U t (r + 1)) =
          P t (r - 1) + P t r := by
      simpa [hU (t + 1) r, hU t r, add_assoc, add_comm, add_left_comm]
        using hstep t r
    have hsum :
        (U (t + 1) (r + 1) + U t (r + 1) + P t r) +
            (U (t + 1) r + U t r + P t (r - 1)) = 0 := by
      calc
        (U (t + 1) (r + 1) + U t (r + 1) + P t r) +
            (U (t + 1) r + U t r + P t (r - 1))
            =
          ((U (t + 1) r + U (t + 1) (r + 1)) +
              (U t r + U t (r + 1))) +
            (P t (r - 1) + P t r) := by
              ring
        _ = (P t (r - 1) + P t r) + (P t (r - 1) + P t r) := by
              rw [hstepU]
        _ = 0 := F_add_self _
    simpa [C, add_assoc, add_comm, add_left_comm] using hsum
  have hCconst : ∀ t r : I n, C t r = c t := by
    intro t r
    exact zmod_step_const (fun r => C t r) (hCstep t) r
  have hP_decomp : ∀ t r : I n,
      P t r = U (t + 1) (r + 1) + U t (r + 1) + c t := by
    intro t r
    have h := hCconst t (r + 1)
    unfold C c at h
    have hrsub : r + 1 - 1 = r := by abel
    rw [hrsub] at h
    apply F_eq_of_add_eq_zero
    calc
      P t r + (U (t + 1) (r + 1) + U t (r + 1) + c t)
          = (U (t + 1) (r + 1) + U t (r + 1) + P t r) + c t := by
              ring
      _ = c t + c t := by
              rw [h]
      _ = 0 := F_add_self _
  have hdiag :
      (∑ r : I n, ((P r r) + (H r r) : F)) = ∑ t : I n, c t := by
    calc
      (∑ r : I n, ((P r r) + (H r r) : F))
          =
        ∑ r : I n,
          (((U (r + 1) (r + 1) + U r (r + 1) + c r) +
            (U r r + U r (r + 1))) : F) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [hP_decomp r r, hU r r]
      _ = ∑ r : I n, ((U (r + 1) (r + 1) + U r r + c r) : F) := by
            refine Finset.sum_congr rfl ?_
            intro r _
            calc
              ((U (r + 1) (r + 1) + U r (r + 1) + c r) +
                  (U r r + U r (r + 1)) : F)
                  =
                (U (r + 1) (r + 1) + U r r + c r) +
                  (U r (r + 1) + U r (r + 1)) := by
                  ring
              _ = (U (r + 1) (r + 1) + U r r + c r) + 0 := by
                  rw [F_add_self]
              _ = U (r + 1) (r + 1) + U r r + c r := by
                  simp
      _ = ∑ r : I n, c r := by
            have hshift :
                (∑ r : I n, U (r + 1) (r + 1)) =
                  ∑ r : I n, U r r := by
              simpa using
                ((Equiv.addRight (1 : I n)).sum_comp
                  (Finset.univ : Finset (I n)) (fun r : I n => U r r))
            exact
              sum_add_add_eq_sum_third_of_same_sum
                (fun r : I n => U (r + 1) (r + 1))
                (fun r : I n => U r r) c hshift
  have hcol :
      (∑ t : I n, P t r0) = ∑ t : I n, c t := by
    calc
      (∑ t : I n, P t r0)
          = ∑ t : I n, ((U (t + 1) (r0 + 1) + U t (r0 + 1) + c t) : F) := by
            refine Finset.sum_congr rfl ?_
            intro t _
            rw [hP_decomp t r0]
      _ = ∑ t : I n, c t := by
            have hshift :
                (∑ t : I n, U (t + 1) (r0 + 1)) =
                  ∑ t : I n, U t (r0 + 1) := by
              simpa using
                ((Equiv.addRight (1 : I n)).sum_comp
                  (Finset.univ : Finset (I n))
                  (fun t : I n => U t (r0 + 1)))
            exact
              sum_add_add_eq_sum_third_of_same_sum
                (fun t : I n => U (t + 1) (r0 + 1))
                (fun t : I n => U t (r0 + 1)) c hshift
  exact hdiag.trans hcol.symm

lemma coreS_step_zero
    {n : ℕ} [NeZero n]
    (x : SquareCoreAllowed n) (t r : I n) :
    compatCoreEval x.1.2 0 (t + 1 - r) r +
        compatCoreEval x.1.2 0 (t - r) r =
      corePVal x.1.1 x.1.2 t (r - 1) +
        corePVal x.1.1 x.1.2 t r := by
  have hallowed := (mem_SquareCoreAllowed_iff (n := n) x.1).1 x.2
  have hW := (hallowed 0 (t + 1 - r) (r - 1)).2
  apply F_eq_of_add_eq_zero
  unfold squareCoreCurlW at hW
  unfold corePVal
  have hz : t + 1 - r - 1 = t - r := by abel
  have hr : r - 1 + 1 = r := by abel
  have hp : t - (r - 1) = t + 1 - r := by abel
  rw [hz, hr] at hW
  rw [hp]
  have htwo : (2 : F) = 0 := by decide
  ring_nf
  simpa [sub_eq_add_neg, htwo, add_assoc, add_comm, add_left_comm] using hW

lemma coreS_step
    {n : ℕ} [NeZero n]
    (x : SquareCoreAllowed n) (t sy sw : I n) :
    compatCoreEval x.1.2 sy (t + 1 - sy - sw) sw +
        compatCoreEval x.1.2 sy (t - sy - sw) sw =
      corePVal x.1.1 x.1.2 t (sy + sw - 1) +
        corePVal x.1.1 x.1.2 t (sy + sw) := by
  let z : I n := t + 1 - sy - sw
  have hallowed := (mem_SquareCoreAllowed_iff (n := n) x.1).1 x.2
  have hW := (hallowed sy z (sw - 1)).2
  have hP₁ :
      rootCoreEval x.1.1 sy z (sw - 1) +
          compatCoreEval x.1.2 sy z (sw - 1) =
        corePVal x.1.1 x.1.2 t (sy + sw - 1) := by
    have hz : t - sy - (sw - 1) = z := by
      dsimp [z]
      abel
    have hr : sy + (sw - 1) = sy + sw - 1 := by abel
    simpa [hz, hr] using coreP_independent (n := n) x t sy (sw - 1)
  have hP₂ :
      rootCoreEval x.1.1 sy (z - 1) sw +
          compatCoreEval x.1.2 sy (z - 1) sw =
        corePVal x.1.1 x.1.2 t (sy + sw) := by
    have hz : t - sy - sw = z - 1 := by
      dsimp [z]
      abel
    simpa [hz] using coreP_independent (n := n) x t sy sw
  apply F_eq_of_add_eq_zero
  unfold squareCoreCurlW at hW
  have hsw : sw - 1 + 1 = sw := by abel
  rw [hsw] at hW
  have hz : z - 1 = t - sy - sw := by
    dsimp [z]
    abel
  have hz' : z = t + 1 - sy - sw := rfl
  rw [← hz]
  have htwo : (2 : F) = 0 := by decide
  calc
    (compatCoreEval x.1.2 sy z sw + compatCoreEval x.1.2 sy (z - 1) sw) +
        (corePVal x.1.1 x.1.2 t (sy + sw - 1) +
          corePVal x.1.1 x.1.2 t (sy + sw))
        =
      (rootCoreEval x.1.1 sy z (sw - 1) +
          rootCoreEval x.1.1 sy (z - 1) sw +
          compatCoreEval x.1.2 sy z (sw - 1) +
          compatCoreEval x.1.2 sy z sw) +
        (compatCoreEval x.1.2 sy (z - 1) sw +
          compatCoreEval x.1.2 sy (z - 1) sw) := by
          rw [← hP₁, ← hP₂]
          ring
    _ = 0 + (compatCoreEval x.1.2 sy (z - 1) sw +
          compatCoreEval x.1.2 sy (z - 1) sw) := by
          rw [hW]
    _ = 0 := by
          rw [F_add_self]
          simp

lemma coreP_sum_t_zero_aux
    {n : ℕ} [NeZero n]
    (x : SquareCoreAllowed n) (r : I n) :
    (∑ t : I n, corePVal x.1.1 x.1.2 t r) = 0 := by
  let P : I n → I n → F := fun t r => corePVal x.1.1 x.1.2 t r
  let H : I n → I n → F := fun t r => compatCoreEval x.1.2 0 (t - r) r
  have hHrow : ∀ t : I n, (∑ r : I n, H t r) = 0 := by
    intro t
    calc
      (∑ r : I n, H t r)
          = ∑ r : I n, (x.1.2 t).1 0 r := by
            refine Finset.sum_congr rfl ?_
            intro r _
            unfold H compatCoreEval
            have hcoord : 0 + (t - r) + r = t := by abel
            rw [hcoord]
      _ = 0 := matrix_row_zero (x.1.2 t) 0
  have hstep : ∀ t r : I n,
      H (t + 1) r + H t r = P t (r - 1) + P t r := by
    intro t r
    exact coreS_step_zero (n := n) x t r
  have hdiag := diag_sum_eq_col_sum_of_step (n := n) P H hHrow hstep r
  have hdiag_zero : (∑ q : I n, ((P q q) + (H q q) : F)) = 0 := by
    calc
      (∑ q : I n, ((P q q) + (H q q) : F))
          = ∑ q : I n, rootCoreEval x.1.1 0 0 q := by
            refine Finset.sum_congr rfl ?_
            intro q _
            unfold P H corePVal
            have hqq : q - q = 0 := by abel
            rw [hqq]
            have htwo : (2 : F) = 0 := by decide
            ring_nf
            simp [htwo]
      _ = 0 := by
            simpa [rootCoreEval] using matrix_row_zero (x.1.1 0) 0
  rw [hdiag_zero] at hdiag
  exact hdiag.symm

lemma coreP_line_zero
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) :
    SquareCoreAllowed.readLineVal x ∈ LineZeroSum n := by
  apply LinearMap.mem_ker.mpr
  change (∑ t : I n, SquareCoreAllowed.readLineVal x t) = 0
  funext r
  simp only [Finset.sum_apply, Pi.zero_apply, SquareCoreAllowed.readLineVal]
  exact coreP_sum_t_zero_aux (n := n) x r

noncomputable def SquareCoreAllowed.readLine
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) : LineZeroSum n :=
  ⟨SquareCoreAllowed.readLineVal x, coreP_line_zero (n := n) x⟩

@[simp]
theorem SquareCoreAllowed_readLine_apply
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) (t r : I n) :
    (SquareCoreAllowed.readLine x).1 t r =
      corePVal x.1.1 x.1.2 t r := rfl

noncomputable def SquareCoreAllowedRead
    {n : ℕ} [NeZero n] :
    SquareCoreAllowed n →ₗ[F] SquareCoreParam n where
  toFun x := (SquareCoreAllowed.readS0 x, SquareCoreAllowed.readLine x)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      funext sy sw
      rfl
    · apply Subtype.ext
      funext t r
      unfold SquareCoreAllowed.readLine SquareCoreAllowed.readLineVal corePVal
      unfold rootCoreEval compatCoreEval
      simp [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      ring
  map_smul' a x := by
    apply Prod.ext
    · apply Subtype.ext
      funext sy sw
      rfl
    · apply Subtype.ext
      funext t r
      unfold SquareCoreAllowed.readLine SquareCoreAllowed.readLineVal corePVal
      unfold rootCoreEval compatCoreEval
      simp [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

noncomputable def coreIncrMatrix
    {n : ℕ} [NeZero n] (P : LineZeroSum n) (t : I n) : MatrixZeroSum n :=
  ⟨fun sy sw => P.1 t (sy + sw - 1) + P.1 t (sy + sw), by
    constructor
    · apply LinearMap.mem_ker.mpr
      funext sy
      change (∑ sw : I n, ((P.1 t (sy + sw - 1)) + (P.1 t (sy + sw)) : F)) = 0
      rw [Finset.sum_add_distrib]
      have hshift :
          (∑ sw : I n, P.1 t (sy + sw - 1)) =
            ∑ sw : I n, P.1 t (sy + sw) := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          ((((Equiv.addRight (1 : I n)).sum_comp
            (Finset.univ : Finset (I n))
            (fun sw : I n => P.1 t (sy + sw - 1))) (by simp)).symm)
      rw [hshift]
      exact F_add_self _
    · apply LinearMap.mem_ker.mpr
      funext sw
      change (∑ sy : I n, ((P.1 t (sy + sw - 1)) + (P.1 t (sy + sw)) : F)) = 0
      rw [Finset.sum_add_distrib]
      have hshift :
          (∑ sy : I n, P.1 t (sy + sw - 1)) =
            ∑ sy : I n, P.1 t (sy + sw) := by
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
          ((((Equiv.addRight (1 : I n)).sum_comp
            (Finset.univ : Finset (I n))
            (fun sy : I n => P.1 t (sy + sw - 1))) (by simp)).symm)
      rw [hshift]
      exact F_add_self _⟩

lemma lineZeroSum_coord_zero {n : ℕ} [NeZero n]
    (P : LineZeroSum n) (r : I n) :
    (∑ t : I n, P.1 t r) = 0 := by
  have hsum : sigmaMapM (n := n) (Profile n) P.1 = 0 :=
    LinearMap.mem_ker.mp P.2
  change (∑ t : I n, P.1 t) = 0 at hsum
  simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun hsum r

noncomputable def coreIncrFamily
    {n : ℕ} [NeZero n] (P : LineZeroSum n) :
    ZeroSumProfileM n (MatrixZeroSum n) :=
  ⟨fun t => coreIncrMatrix (n := n) P t, by
    apply LinearMap.mem_ker.mpr
    change (∑ t : I n, coreIncrMatrix (n := n) P t) = 0
    apply Subtype.ext
    funext sy sw
    change ((Submodule.subtype (MatrixZeroSum n))
        (∑ t : I n, coreIncrMatrix (n := n) P t)) sy sw = 0
    rw [map_sum]
    simp only [Finset.sum_apply]
    change (∑ t : I n, ((P.1 t (sy + sw - 1)) + (P.1 t (sy + sw)) : F)) = 0
    rw [Finset.sum_add_distrib]
    rw [lineZeroSum_coord_zero (n := n) P (sy + sw - 1),
      lineZeroSum_coord_zero (n := n) P (sy + sw)]
    simp⟩

noncomputable def coreBuildJ
    {n : ℕ} [NeZero n] (P : LineZeroSum n) : I n → MatrixZeroSum n :=
  cycPrimitiveM (n := n) (MatrixZeroSum n) (coreIncrFamily (n := n) P)

lemma coreBuildJ_step
    {n : ℕ} [NeZero n] (P : LineZeroSum n) (t : I n) :
    coreBuildJ (n := n) P t + coreBuildJ (n := n) P (t + 1) =
      coreIncrMatrix (n := n) P t := by
  have h :=
    congrArg Subtype.val
      (cycDiff_cycPrimitiveM (n := n) (MatrixZeroSum n)
        (coreIncrFamily (n := n) P))
  change cycDiff (n := n) (MatrixZeroSum n) (coreBuildJ (n := n) P) =
      (fun t => coreIncrMatrix (n := n) P t) at h
  have ht := congrFun h t
  simpa [cycDiff] using ht

noncomputable def coreBuildS
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) : SquareCompatCore n :=
  fun t => S0 + coreBuildJ (n := n) P t + coreBuildJ (n := n) P 0

lemma coreBuildS_zero
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) :
    coreBuildS (n := n) S0 P 0 = S0 := by
  apply Subtype.ext
  funext sy sw
  unfold coreBuildS
  change S0.1 sy sw + (coreBuildJ (n := n) P 0).1 sy sw +
      (coreBuildJ (n := n) P 0).1 sy sw = S0.1 sy sw
  have htwo : (2 : F) = 0 := by decide
  ring_nf
  simp [htwo]

lemma coreBuildS_step
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n)
    (t sy sw : I n) :
    (coreBuildS (n := n) S0 P t).1 sy sw +
        (coreBuildS (n := n) S0 P (t + 1)).1 sy sw =
      P.1 t (sy + sw - 1) + P.1 t (sy + sw) := by
  have hJ := coreBuildJ_step (n := n) P t
  have hJcoord :
      (coreBuildJ (n := n) P t).1 sy sw +
          (coreBuildJ (n := n) P (t + 1)).1 sy sw =
        (coreIncrMatrix (n := n) P t).1 sy sw := by
    have h := congrArg Subtype.val hJ
    exact congrFun (congrFun h sy) sw
  unfold coreBuildS
  change
    (S0.1 sy sw + (coreBuildJ (n := n) P t).1 sy sw +
        (coreBuildJ (n := n) P 0).1 sy sw) +
      (S0.1 sy sw + (coreBuildJ (n := n) P (t + 1)).1 sy sw +
        (coreBuildJ (n := n) P 0).1 sy sw) =
      P.1 t (sy + sw - 1) + P.1 t (sy + sw)
  calc
    (S0.1 sy sw + (coreBuildJ (n := n) P t).1 sy sw +
        (coreBuildJ (n := n) P 0).1 sy sw) +
      (S0.1 sy sw + (coreBuildJ (n := n) P (t + 1)).1 sy sw +
        (coreBuildJ (n := n) P 0).1 sy sw)
        =
      ((coreBuildJ (n := n) P t).1 sy sw +
          (coreBuildJ (n := n) P (t + 1)).1 sy sw) +
        (S0.1 sy sw + S0.1 sy sw) +
        ((coreBuildJ (n := n) P 0).1 sy sw +
          (coreBuildJ (n := n) P 0).1 sy sw) := by
          ring
    _ = ((coreBuildJ (n := n) P t).1 sy sw +
          (coreBuildJ (n := n) P (t + 1)).1 sy sw) + 0 + 0 := by
          rw [F_add_self, F_add_self]
    _ = (coreIncrMatrix (n := n) P t).1 sy sw := by
          rw [hJcoord]
          simp
    _ = P.1 t (sy + sw - 1) + P.1 t (sy + sw) := rfl

noncomputable def coreBuildAVal
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) (z : I n) : MatrixProfile n :=
  fun sy sw =>
    (coreBuildS (n := n) S0 P (sy + z + sw)).1 sy sw +
      P.1 (sy + z + sw) (sy + sw)

lemma coreBuildA_row_zero
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) (z sy : I n) :
    (∑ sw : I n, coreBuildAVal (n := n) S0 P z sy sw) = 0 := by
  let PP : I n → I n → F := fun u r => P.1 (u + z) r
  let HH : I n → I n → F :=
    fun u r => (coreBuildS (n := n) S0 P (u + z)).1 sy (r - sy)
  have hHrow : ∀ u : I n, (∑ r : I n, HH u r) = 0 := by
    intro u
    unfold HH
    have hshift :
        (∑ r : I n, (coreBuildS (n := n) S0 P (u + z)).1 sy (r - sy)) =
          ∑ sw : I n, (coreBuildS (n := n) S0 P (u + z)).1 sy sw := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (((Equiv.addRight (-sy)).sum_comp
          (Finset.univ : Finset (I n))
          (fun sw : I n => (coreBuildS (n := n) S0 P (u + z)).1 sy sw)) (by simp))
    rw [hshift]
    exact matrix_row_zero (coreBuildS (n := n) S0 P (u + z)) sy
  have hstep : ∀ u r : I n,
      HH (u + 1) r + HH u r = PP u (r - 1) + PP u r := by
    intro u r
    unfold HH PP
    have ht : u + 1 + z = u + z + 1 := by abel
    have hr : sy + (r - sy) = r := by abel
    have h := coreBuildS_step (n := n) S0 P (u + z) sy (r - sy)
    rw [ht]
    simpa [hr, add_assoc, add_comm, add_left_comm] using h
  have hdiag := diag_sum_eq_col_sum_of_step (n := n) PP HH hHrow hstep 0
  have hcolzero : (∑ u : I n, PP u 0) = 0 := by
    unfold PP
    have hshift :
        (∑ u : I n, P.1 (u + z) 0) = ∑ t : I n, P.1 t 0 := by
      simpa using
        (((Equiv.addRight z).sum_comp
          (Finset.univ : Finset (I n)) (fun t : I n => P.1 t 0)) (by simp))
    rw [hshift]
    exact lineZeroSum_coord_zero (n := n) P 0
  have hdiag_zero : (∑ u : I n, ((PP u u) + (HH u u) : F)) = 0 := by
    rw [hdiag, hcolzero]
  calc
    (∑ sw : I n, coreBuildAVal (n := n) S0 P z sy sw)
        = ∑ u : I n, coreBuildAVal (n := n) S0 P z sy (u - sy) := by
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
            ((((Equiv.addRight (-sy)).sum_comp
              (Finset.univ : Finset (I n))
              (fun sw : I n => coreBuildAVal (n := n) S0 P z sy sw)) (by simp)).symm)
    _ = ∑ u : I n, ((PP u u) + (HH u u) : F) := by
          refine Finset.sum_congr rfl ?_
          intro u _
          unfold coreBuildAVal PP HH
          have ht : sy + z + (u - sy) = u + z := by abel
          have hr : sy + (u - sy) = u := by abel
          rw [ht, hr]
          ring
    _ = 0 := hdiag_zero

lemma coreBuildA_col_zero
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) (z sw : I n) :
    (∑ sy : I n, coreBuildAVal (n := n) S0 P z sy sw) = 0 := by
  let PP : I n → I n → F := fun u r => P.1 (u + z) r
  let HH : I n → I n → F :=
    fun u r => (coreBuildS (n := n) S0 P (u + z)).1 (r - sw) sw
  have hHrow : ∀ u : I n, (∑ r : I n, HH u r) = 0 := by
    intro u
    unfold HH
    have hshift :
        (∑ r : I n, (coreBuildS (n := n) S0 P (u + z)).1 (r - sw) sw) =
          ∑ sy : I n, (coreBuildS (n := n) S0 P (u + z)).1 sy sw := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (((Equiv.addRight (-sw)).sum_comp
          (Finset.univ : Finset (I n))
          (fun sy : I n => (coreBuildS (n := n) S0 P (u + z)).1 sy sw)) (by simp))
    rw [hshift]
    exact matrix_col_zero (coreBuildS (n := n) S0 P (u + z)) sw
  have hstep : ∀ u r : I n,
      HH (u + 1) r + HH u r = PP u (r - 1) + PP u r := by
    intro u r
    unfold HH PP
    have ht : u + 1 + z = u + z + 1 := by abel
    have hr : r - sw + sw = r := by abel
    have h := coreBuildS_step (n := n) S0 P (u + z) (r - sw) sw
    rw [ht]
    simpa [hr, add_assoc, add_comm, add_left_comm] using h
  have hdiag := diag_sum_eq_col_sum_of_step (n := n) PP HH hHrow hstep 0
  have hcolzero : (∑ u : I n, PP u 0) = 0 := by
    unfold PP
    have hshift :
        (∑ u : I n, P.1 (u + z) 0) = ∑ t : I n, P.1 t 0 := by
      simpa using
        (((Equiv.addRight z).sum_comp
          (Finset.univ : Finset (I n)) (fun t : I n => P.1 t 0)) (by simp))
    rw [hshift]
    exact lineZeroSum_coord_zero (n := n) P 0
  have hdiag_zero : (∑ u : I n, ((PP u u) + (HH u u) : F)) = 0 := by
    rw [hdiag, hcolzero]
  calc
    (∑ sy : I n, coreBuildAVal (n := n) S0 P z sy sw)
        = ∑ u : I n, coreBuildAVal (n := n) S0 P z (u - sw) sw := by
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
            ((((Equiv.addRight (-sw)).sum_comp
              (Finset.univ : Finset (I n))
              (fun sy : I n => coreBuildAVal (n := n) S0 P z sy sw)) (by simp)).symm)
    _ = ∑ u : I n, ((PP u u) + (HH u u) : F) := by
          refine Finset.sum_congr rfl ?_
          intro u _
          unfold coreBuildAVal PP HH
          have ht : u - sw + z + sw = u + z := by abel
          have hr : u - sw + sw = u := by abel
          rw [ht, hr]
          ring
    _ = 0 := hdiag_zero

lemma coreBuildA_mem_MatrixZeroSum
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) (z : I n) :
    coreBuildAVal (n := n) S0 P z ∈ MatrixZeroSum n := by
  constructor
  · apply LinearMap.mem_ker.mpr
    funext sy
    exact coreBuildA_row_zero (n := n) S0 P z sy
  · apply LinearMap.mem_ker.mpr
    funext sw
    exact coreBuildA_col_zero (n := n) S0 P z sw

noncomputable def coreBuildR
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) : SquareRootCore n :=
  fun z => ⟨coreBuildAVal (n := n) S0 P z,
    coreBuildA_mem_MatrixZeroSum (n := n) S0 P z⟩

lemma coreBuild_allowed_prop
    {n : ℕ} [NeZero n]
    (S0 : MatrixZeroSum n) (P : LineZeroSum n) :
    SquareCoreAllowedProp (coreBuildR (n := n) S0 P)
      (coreBuildS (n := n) S0 P) := by
  intro sy sz sw
  constructor
  · let t : I n := sy + sz + sw
    have hstep := coreBuildS_step (n := n) S0 P t (sy + 1) sw
    have htR : sy + 1 + (sz - 1) + sw = t := by
      dsimp [t]
      abel
    have htC : sy + 1 + sz + sw = t + 1 := by
      dsimp [t]
      abel
    have hr : sy + 1 + sw - 1 = sy + sw := by abel
    rw [hr] at hstep
    unfold squareCoreCurlB rootCoreEval compatCoreEval coreBuildR coreBuildAVal
    dsimp [t] at htR htC hstep
    dsimp
    rw [htR, htC]
    have hstep' :
        (coreBuildS (n := n) S0 P (sy + (sz + sw))).1 (sy + 1) sw +
            (coreBuildS (n := n) S0 P (sy + (sz + (sw + 1)))).1 (sy + 1) sw =
          P.1 (sy + (sz + sw)) (sy + sw) +
            P.1 (sy + (sz + sw)) (sy + (sw + 1)) := by
      simpa [add_assoc, add_comm, add_left_comm] using hstep
    have htwo : (2 : F) = 0 := by decide
    have hsum :
        (P.1 (sy + (sz + sw)) (sy + sw) +
            P.1 (sy + (sz + sw)) (sy + (sw + 1))) +
          ((coreBuildS (n := n) S0 P (sy + (sz + sw))).1 (sy + 1) sw +
            (coreBuildS (n := n) S0 P (sy + (sz + (sw + 1)))).1 (sy + 1) sw) = 0 := by
      rw [← hstep']
      exact F_add_self _
    ring_nf
    simp [htwo]
    simpa [add_assoc, add_comm, add_left_comm] using hsum
  · let t : I n := sy + sz + sw
    have hstep := coreBuildS_step (n := n) S0 P t sy (sw + 1)
    have htR : sy + (sz - 1) + (sw + 1) = t := by
      dsimp [t]
      abel
    have htC : sy + sz + (sw + 1) = t + 1 := by
      dsimp [t]
      abel
    have hr : sy + (sw + 1) - 1 = sy + sw := by abel
    rw [hr] at hstep
    unfold squareCoreCurlW rootCoreEval compatCoreEval coreBuildR coreBuildAVal
    dsimp [t] at htR htC hstep
    dsimp
    rw [htR, htC]
    have hstep' :
        (coreBuildS (n := n) S0 P (sy + (sz + sw))).1 sy (sw + 1) +
            (coreBuildS (n := n) S0 P (sy + (sz + (sw + 1)))).1 sy (sw + 1) =
          P.1 (sy + (sz + sw)) (sy + sw) +
            P.1 (sy + (sz + sw)) (sy + (sw + 1)) := by
      simpa [add_assoc, add_comm, add_left_comm] using hstep
    have htwo : (2 : F) = 0 := by decide
    have hsum :
        (P.1 (sy + (sz + sw)) (sy + sw) +
            P.1 (sy + (sz + sw)) (sy + (sw + 1))) +
          ((coreBuildS (n := n) S0 P (sy + (sz + sw))).1 sy (sw + 1) +
            (coreBuildS (n := n) S0 P (sy + (sz + (sw + 1)))).1 sy (sw + 1)) = 0 := by
      rw [← hstep']
      exact F_add_self _
    ring_nf
    simp [htwo]
    simpa [add_assoc, add_comm, add_left_comm] using hsum

noncomputable def SquareCoreAllowedBuildFun
    {n : ℕ} [NeZero n] :
    SquareCoreParam n → SquareCoreAllowed n :=
  fun p =>
    ⟨(coreBuildR (n := n) p.1 p.2, coreBuildS (n := n) p.1 p.2),
      (mem_SquareCoreAllowed_iff (n := n)
        (coreBuildR (n := n) p.1 p.2, coreBuildS (n := n) p.1 p.2)).2
        (coreBuild_allowed_prop (n := n) p.1 p.2)⟩

@[simp]
theorem SquareCoreAllowedBuildFun_root_apply
    {n : ℕ} [NeZero n] (p : SquareCoreParam n) (z sy sw : I n) :
    ((SquareCoreAllowedBuildFun (n := n) p).1.1 z).1 sy sw =
      coreBuildAVal (n := n) p.1 p.2 z sy sw := rfl

@[simp]
theorem SquareCoreAllowedBuildFun_compat_apply
    {n : ℕ} [NeZero n] (p : SquareCoreParam n) (t sy sw : I n) :
    ((SquareCoreAllowedBuildFun (n := n) p).1.2 t).1 sy sw =
      (coreBuildS (n := n) p.1 p.2 t).1 sy sw := rfl

theorem SquareCoreAllowedRead_buildFun
    {n : ℕ} [NeZero n] (p : SquareCoreParam n) :
    SquareCoreAllowedRead (n := n) (SquareCoreAllowedBuildFun (n := n) p) = p := by
  apply Prod.ext
  · exact coreBuildS_zero (n := n) p.1 p.2
  · apply Subtype.ext
    funext t r
    unfold SquareCoreAllowedRead SquareCoreAllowed.readLine SquareCoreAllowed.readLineVal
    unfold SquareCoreAllowedBuildFun corePVal rootCoreEval compatCoreEval coreBuildR coreBuildAVal
    dsimp
    have ht : 0 + (t - r) + r = t := by abel
    have hr : 0 + r = r := by abel
    rw [ht, hr]
    have htwo : (2 : F) = 0 := by decide
    ring_nf
    simp [htwo]

lemma coreBuildS_read_eq
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) :
    coreBuildS (n := n) (SquareCoreAllowed.readS0 x) (SquareCoreAllowed.readLine x) =
      x.1.2 := by
  funext t
  apply Subtype.ext
  funext sy sw
  let S0 : MatrixZeroSum n := SquareCoreAllowed.readS0 x
  let P : LineZeroSum n := SquareCoreAllowed.readLine x
  let D : I n → F := fun u =>
    (coreBuildS (n := n) S0 P u).1 sy sw + (x.1.2 u).1 sy sw
  have hconst : ∀ u : I n, D (u + 1) = D u := by
    intro u
    apply F_eq_of_add_eq_zero
    have hb := coreBuildS_step (n := n) S0 P u sy sw
    have ho := coreS_step (n := n) x u sy sw
    unfold compatCoreEval at ho
    have ho₁ : sy + (u + 1 - sy - sw) + sw = u + 1 := by abel
    have ho₀ : sy + (u - sy - sw) + sw = u := by abel
    rw [ho₁, ho₀] at ho
    have ho' :
        (x.1.2 (u + 1)).1 sy sw + (x.1.2 u).1 sy sw =
          P.1 u (sy + sw - 1) + P.1 u (sy + sw) := by
      dsimp [P]
      simpa [SquareCoreAllowed.readLine, SquareCoreAllowed.readLineVal] using ho
    unfold D
    calc
      ((coreBuildS (n := n) S0 P (u + 1)).1 sy sw + (x.1.2 (u + 1)).1 sy sw) +
          ((coreBuildS (n := n) S0 P u).1 sy sw + (x.1.2 u).1 sy sw)
          =
        ((coreBuildS (n := n) S0 P u).1 sy sw +
            (coreBuildS (n := n) S0 P (u + 1)).1 sy sw) +
          ((x.1.2 (u + 1)).1 sy sw + (x.1.2 u).1 sy sw) := by
            ring
      _ = (P.1 u (sy + sw - 1) + P.1 u (sy + sw)) +
          (P.1 u (sy + sw - 1) + P.1 u (sy + sw)) := by
            rw [hb, ho']
      _ = 0 := F_add_self _
  have hread := zmod_step_const D hconst t
  have hzero : D 0 = 0 := by
    unfold D S0
    rw [coreBuildS_zero]
    exact F_add_self _
  have htzero : D t = 0 := by
    rw [hread, hzero]
  apply F_eq_of_add_eq_zero
  exact htzero

theorem SquareCoreAllowedBuildFun_read
    {n : ℕ} [NeZero n] (x : SquareCoreAllowed n) :
    SquareCoreAllowedBuildFun (n := n) (SquareCoreAllowedRead (n := n) x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · change
      coreBuildR (n := n) (SquareCoreAllowed.readS0 x) (SquareCoreAllowed.readLine x) =
        x.1.1
    funext z
    apply Subtype.ext
    funext sy sw
    let t : I n := sy + z + sw
    have hSall := coreBuildS_read_eq (n := n) x
    have hScoord :
        (coreBuildS (n := n) (SquareCoreAllowed.readS0 x)
            (SquareCoreAllowed.readLine x) t).1 sy sw =
          (x.1.2 t).1 sy sw := by
      have h := congrFun hSall t
      exact congrFun (congrFun (congrArg Subtype.val h) sy) sw
    have hP := coreP_independent (n := n) x t sy sw
    have hz : t - sy - sw = z := by
      dsimp [t]
      abel
    rw [hz] at hP
    unfold coreBuildR coreBuildAVal
    dsimp [t]
    rw [hScoord]
    unfold corePVal at hP
    unfold rootCoreEval compatCoreEval at hP
    have ht : sy + z + sw = t := by
      dsimp [t]
    rw [ht] at hP
    change (x.1.2 t).1 sy sw +
        (rootCoreEval x.1.1 0 (t - (sy + sw)) (sy + sw) +
          compatCoreEval x.1.2 0 (t - (sy + sw)) (sy + sw)) =
      (x.1.1 z).1 sy sw
    have hP' :
        (x.1.1 z).1 sy sw + (x.1.2 t).1 sy sw =
          rootCoreEval x.1.1 0 (t - (sy + sw)) (sy + sw) +
            compatCoreEval x.1.2 0 (t - (sy + sw)) (sy + sw) := by
      simpa [rootCoreEval, compatCoreEval, corePVal, ht] using hP
    calc
      (x.1.2 t).1 sy sw +
          (rootCoreEval x.1.1 0 (t - (sy + sw)) (sy + sw) +
            compatCoreEval x.1.2 0 (t - (sy + sw)) (sy + sw))
          =
        (x.1.2 t).1 sy sw + ((x.1.1 z).1 sy sw + (x.1.2 t).1 sy sw) := by
          rw [← hP']
      _ = (x.1.1 z).1 sy sw := by
          have htwo : (2 : F) = 0 := by decide
          ring_nf
          simp [htwo]
  · change
      coreBuildS (n := n) (SquareCoreAllowed.readS0 x) (SquareCoreAllowed.readLine x) =
        x.1.2
    exact coreBuildS_read_eq (n := n) x

noncomputable def SquareCoreAllowedEquivParam
    {n : ℕ} [NeZero n] :
    SquareCoreAllowed n ≃ₗ[F] SquareCoreParam n where
  toFun := SquareCoreAllowedRead (n := n)
  invFun := SquareCoreAllowedBuildFun (n := n)
  left_inv := SquareCoreAllowedBuildFun_read (n := n)
  right_inv := SquareCoreAllowedRead_buildFun (n := n)
  map_add' x y := (SquareCoreAllowedRead (n := n)).map_add x y
  map_smul' a x := (SquareCoreAllowedRead (n := n)).map_smul a x

theorem finrank_SquareCoreAllowed {n : ℕ} [NeZero n] :
    Module.finrank F (SquareCoreAllowed n) =
      2 * (n - 1) ^ 2 + (n - 1) := by
  calc
    Module.finrank F (SquareCoreAllowed n)
        = Module.finrank F (SquareCoreParam n) := by
            exact LinearEquiv.finrank_eq (SquareCoreAllowedEquivParam (n := n))
    _ = 2 * (n - 1) ^ 2 + (n - 1) := finrank_SquareCoreParam (n := n)

end Core4loop
