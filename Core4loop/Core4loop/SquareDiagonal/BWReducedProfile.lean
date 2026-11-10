import Core4loop.SquareDiagonal.BWPairPresentation
import Core4loop.Square.Rank.IntersectionModel
import Core4loop.Square.Rank.CoreParam

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

theorem sqdiag_exists_linearMap_apply_eq_one_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module F V]
    (L : V →ₗ[F] F) (hL : L ≠ 0) :
    ∃ v : V, L v = 1 := by
  have hnonzero : ∃ v : V, L v ≠ 0 := by
    by_contra hforall
    apply hL
    ext v
    by_contra hv
    exact hforall ⟨v, hv⟩
  rcases hnonzero with ⟨v, hv⟩
  exact ⟨v, F_ne_zero_eq_one _ hv⟩

theorem sqdiag_linearMap_surjective_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module F V]
    (L : V →ₗ[F] F) (hL : L ≠ 0) :
    Function.Surjective L := by
  rcases sqdiag_exists_linearMap_apply_eq_one_of_ne_zero L hL with ⟨v, hv⟩
  intro s
  by_cases hs : s = 0
  · refine ⟨0, ?_⟩
    rw [hs]
    exact L.map_zero
  · refine ⟨v, ?_⟩
    rw [F_ne_zero_eq_one s hs]
    exact hv

theorem sqdiag_linearMap_range_eq_top_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module F V]
    (L : V →ₗ[F] F) (hL : L ≠ 0) :
    LinearMap.range L = ⊤ :=
  LinearMap.range_eq_top.mpr
    (sqdiag_linearMap_surjective_of_ne_zero L hL)

@[simp]
theorem sqdiagAmbient_vertical_root_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hy : y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d) :
    (sqdiagAdjointAmbientPairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 :=
  sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) y hy

theorem sqdiagRootCoeffApply_add_coeff
    {n b c d : ℕ} [NeZero n]
    (A B R : RootTarget n b c d) :
    sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
        (A + B) R =
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R +
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R :=
  sqdiagRootCoeffApply_add_left
    (n := n) (b := b) (c := c) (d := d) A B R

theorem sqdiagRootCoeffApply_add_root
    {n b c d : ℕ} [NeZero n]
    (A R S : RootTarget n b c d) :
    sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
        A (R + S) =
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R +
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A S :=
  sqdiagRootCoeffApply_add_right
    (n := n) (b := b) (c := c) (d := d) A R S

theorem sqdiagRootCoeffApply_zero_coeff
    {n b c d : ℕ} [NeZero n]
    (R : RootTarget n b c d) :
    sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
        (0 : RootTarget n b c d) R = 0 := by
  simp [sqdiagRootCoeffApply]

theorem sqdiagRootCoeffApply_zero_root
    {n b c d : ℕ} [NeZero n]
    (A : RootTarget n b c d) :
    sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
        A (0 : RootTarget n b c d) = 0 := by
  simp [sqdiagRootCoeffApply]

theorem sqdiagRootCoeffApply_smul_coeff
    {n b c d : ℕ} [NeZero n]
    (r : F) (A R : RootTarget n b c d) :
    sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
        (r • A) R =
      r • sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R :=
  sqdiagRootCoeffApply_smul_left
    (n := n) (b := b) (c := c) (d := d) r A R

theorem sqdiagKCAdjointCoeff_add
    {n a b c d : ℕ} [NeZero n]
    (A B : RootTarget n b c d) :
    sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) (A + B) =
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A +
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B :=
  (sqdiagKCAdjointMap
    (n := n) (a := a) (b := b) (c := c) (d := d)).map_add A B

theorem sqdiagKCAdjointCoeff_zero
    {n a b c d : ℕ} [NeZero n] :
    sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (0 : RootTarget n b c d) = 0 :=
  (sqdiagKCAdjointMap
    (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero

theorem sqdiagKCAdjointCoeff_smul
    {n a b c d : ℕ} [NeZero n]
    (r : F) (A : RootTarget n b c d) :
    sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) (r • A) =
      r • sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A :=
  (sqdiagKCAdjointMap
    (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r A

def sqdiagAdjointAmbientVerticalRootScalarReachable
    (n a b c d : ℕ) [NeZero n]
    (R : RootTarget n b c d) (s : F) : Prop :=
  ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
    y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
      ∃ B : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) B =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R = s

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_zero
    {n a b c d : ℕ} [NeZero n]
    (R : RootTarget n b c d) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R 0 := by
  refine ⟨0, ?_, 0, ?_, ?_⟩
  · exact
      (sqdiagAdjointAmbientPairPresentationVertical n a b c d).zero_mem
  · simp [sqdiagKCAdjointCoeff_zero]
  · exact
      sqdiagRootCoeffApply_zero_coeff
        (n := n) (b := b) (c := c) (d := d) R

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_KCAdjointCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (A R : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A = 0) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
      (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) := by
  refine ⟨0, ?_, A, ?_, rfl⟩
  · exact
      (sqdiagAdjointAmbientPairPresentationVertical n a b c d).zero_mem
  · simp [hA]

theorem sqdiagAdjointAmbientPairingMatchVertical_witness_of_KCAdjointCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (A R : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A = 0) :
    ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
        ∃ B : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
            sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) B R =
              sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) A R :=
  sqdiagAdjointAmbientVerticalRootScalarReachable_of_KCAdjointCoeff_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) A R hA

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_add
    {n a b c d : ℕ} [NeZero n]
    {R : RootTarget n b c d} {s t : F}
    (hs : sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R s)
    (ht : sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R t) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R (s + t) := by
  rcases hs with ⟨ys, hys, Bs, hBs, hsval⟩
  rcases ht with ⟨yt, hyt, Bt, hBt, htval⟩
  refine ⟨ys + yt, ?_, Bs + Bt, ?_, ?_⟩
  · exact
      (sqdiagAdjointAmbientPairPresentationVertical n a b c d).add_mem hys hyt
  · calc
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) (Bs + Bt) =
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) Bs +
            sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) Bt := by
            exact
              sqdiagKCAdjointCoeff_add
                (n := n) (a := a) (b := b) (c := c) (d := d) Bs Bt
      _ =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) ys.1).2 +
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) yt.1).2 := by
            rw [hBs, hBt]
      _ =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) (ys + yt).1).2 := by
            simp
  · calc
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
          (Bs + Bt) R =
          sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) Bs R +
            sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) Bt R := by
            exact
              sqdiagRootCoeffApply_add_coeff
                (n := n) (b := b) (c := c) (d := d) Bs Bt R
      _ = s + t := by rw [hsval, htval]

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_same_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (A B R : RootTarget n b c d)
    (hcoeff :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A)
    (hB :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
        (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R)) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
      (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) := by
  let K : RootTarget n b c d := A + B
  have hKzero :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) K = 0 := by
    calc
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) K =
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A +
            sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B := by
            exact
              sqdiagKCAdjointCoeff_add
                (n := n) (a := a) (b := b) (c := c) (d := d) A B
      _ =
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A +
            sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A := by
            rw [hcoeff]
      _ = 0 := by
            exact (add_eq_zero_iff_eq_of_F_module _ _).mpr rfl
  have hK :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
        (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) K R) :=
    sqdiagAdjointAmbientVerticalRootScalarReachable_of_KCAdjointCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) K R hKzero
  have hsum :=
    sqdiagAdjointAmbientVerticalRootScalarReachable_add
      (n := n) (a := a) (b := b) (c := c) (d := d) hB hK
  have hroot :
      B + K = A := by
    calc
      B + K = A + (B + B) := by
        simp [K, add_left_comm]
      _ = A + 0 := by
        rw [(add_eq_zero_iff_eq_of_F_module B B).mpr rfl]
      _ = A := by simp
  have hscalar :
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R +
          sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) K R =
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R := by
    have happ :=
      sqdiagRootCoeffApply_add_coeff
        (n := n) (b := b) (c := c) (d := d) B K R
    rw [hroot] at happ
    exact happ.symm
  simpa [hscalar] using hsum

set_option maxHeartbeats 800000 in
-- Scalar multiplication through the nested ambient presentation subtype stresses elaboration.
set_option synthInstance.maxHeartbeats 200000 in
-- Scalar multiplication through the nested ambient presentation subtype stresses instance search.
theorem sqdiagAdjointAmbientVerticalRootScalarReachable_smul
    {n a b c d : ℕ} [NeZero n]
    (r : F) {R : RootTarget n b c d} {s : F}
    (hs : sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R s) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R (r • s) := by
  rcases hs with ⟨y, hy, B, hB, hsval⟩
  refine ⟨r • y, ?_, r • B, ?_, ?_⟩
  · exact
      (sqdiagAdjointAmbientPairPresentationVertical n a b c d).smul_mem r hy
  · calc
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) (r • B) =
          r • sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) B := by
            exact
              sqdiagKCAdjointCoeff_smul
                (n := n) (a := a) (b := b) (c := c) (d := d) r B
      _ =
          r •
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 := by
            rw [hB]
      _ =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) (r • y).1).2 := by
            simp
  · calc
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
          (r • B) R =
          r • sqdiagRootCoeffApply
            (n := n) (b := b) (c := c) (d := d) B R := by
            exact
              sqdiagRootCoeffApply_smul_coeff
                (n := n) (b := b) (c := c) (d := d) r B R
      _ = r • s := by rw [hsval]

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_eq
    {n a b c d : ℕ} [NeZero n]
    {R : RootTarget n b c d} {s t : F}
    (hst : s = t)
    (hs : sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R s) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R t := by
  simpa [hst] using hs

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_one
    {n a b c d : ℕ} [NeZero n]
    {R : RootTarget n b c d}
    (hOne : sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R 1)
    (s : F) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R s := by
  fin_cases s
  · exact
      sqdiagAdjointAmbientVerticalRootScalarReachable_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) R
  · exact hOne

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_rangePair
    {n a b c d : ℕ} [NeZero n]
    (R : ↑(ZDiffSpace (n := n) (b := b) (c := c) (d := d)))
    (y : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hy : y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d)
    (hcoeff :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∈
        LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))
    {s : F}
    (hs :
      sqdiagAdjointRangePair (n := n) (a := a) (b := b) (c := c) (d := d) R
          ⟨(sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2,
            hcoeff⟩ =
        s) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R.1 s := by
  rcases hcoeff with ⟨B, hB⟩
  refine ⟨y, hy, B, hB, ?_⟩
  have hC :
      (⟨(sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2,
          ⟨B, hB⟩⟩ :
        ↑(LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))) =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) B,
          ⟨B, rfl⟩⟩ := by
    apply Subtype.ext
    exact hB.symm
  rw [← hs]
  rw [hC]
  exact
    (sqdiagAdjointRangePair_mk_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) R B
    ).symm

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_eq_zero_of_mem_verticalOrthogonal
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2)
    {s : F}
    (hs :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 s) :
    s = 0 := by
  rcases hs with ⟨y, hy, B, hB, hsval⟩
  have hyroot :=
    sqdiagAdjointAmbientPairPresentationVertical_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y hy
  have heq :=
    sqdiagAdjointAmbientPairPresentation_rootCoeff_equation_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d)
      x hx y hyroot A B hA hB
  have hAzero :
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 := by
    rw [hyroot]
    exact
      sqdiagRootCoeffApply_zero_root
        (n := n) (b := b) (c := c) (d := d) A
  have hBzero :
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0 := by
    rw [hAzero] at heq
    simpa using heq
  exact hsval.symm.trans hBzero

theorem sqdiagAdjointAmbientPairPresentation_targetScalar_eq_rangePair
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    sqdiagAdjointRangePair
        (n := n) (a := a) (b := b) (c := c) (d := d)
        ⟨(sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1,
          sqdiagAdjointAmbientPairPresentation_root_mem_ZDiff
            (n := n) (a := a) (b := b) (c := c) (d := d) x⟩
        ⟨(sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2,
          ⟨A, hA⟩⟩ =
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  have hC :
      (⟨(sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2,
          ⟨A, hA⟩⟩ :
        ↑(LinearMap.range
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d)))) =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    exact hA.symm
  rw [hC]
  exact
    sqdiagAdjointRangePair_mk_apply
      (n := n) (a := a) (b := b) (c := c) (d := d)
      ⟨(sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1,
        sqdiagAdjointAmbientPairPresentation_root_mem_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) x⟩
      A

def sqdiagAdjointAmbientVerticalRootScalarRange
    (n a b c d : ℕ) [NeZero n]
    (R : RootTarget n b c d) : Submodule F F where
  carrier := {s | sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R s}
  zero_mem' :=
    sqdiagAdjointAmbientVerticalRootScalarReachable_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) R
  add_mem' := by
    intro s t hs ht
    exact
      sqdiagAdjointAmbientVerticalRootScalarReachable_add
        (n := n) (a := a) (b := b) (c := c) (d := d) hs ht
  smul_mem' := by
    intro r s hs
    exact
      sqdiagAdjointAmbientVerticalRootScalarReachable_smul
        (n := n) (a := a) (b := b) (c := c) (d := d) r hs

@[simp]
theorem sqdiagAdjointAmbientVerticalRootScalarRange_mem
    {n a b c d : ℕ} [NeZero n]
    {R : RootTarget n b c d} {s : F} :
    s ∈ sqdiagAdjointAmbientVerticalRootScalarRange n a b c d R ↔
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R s :=
  Iff.rfl

theorem sqdiagAdjointAmbientVerticalRootScalarRange_eq_top_of_one
    {n a b c d : ℕ} [NeZero n]
    {R : RootTarget n b c d}
    (hOne : (1 : F) ∈ sqdiagAdjointAmbientVerticalRootScalarRange n a b c d R) :
    sqdiagAdjointAmbientVerticalRootScalarRange n a b c d R = ⊤ := by
  ext s
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    exact
      sqdiagAdjointAmbientVerticalRootScalarReachable_of_one
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (R := R) hOne s

theorem sqdiagAdjointAmbientVerticalRootScalarRange_eq_top_of_nonzero
    {n a b c d : ℕ} [NeZero n]
    {R : RootTarget n b c d} {s : F}
    (hs : s ∈ sqdiagAdjointAmbientVerticalRootScalarRange n a b c d R)
    (hne : s ≠ 0) :
    sqdiagAdjointAmbientVerticalRootScalarRange n a b c d R = ⊤ := by
  have hsOne :
      (1 : F) ∈ sqdiagAdjointAmbientVerticalRootScalarRange n a b c d R := by
    simpa [F_ne_zero_eq_one s hne] using hs
  exact
    sqdiagAdjointAmbientVerticalRootScalarRange_eq_top_of_one
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (R := R) hsOne

theorem sqdiagAdjointAmbientPairingMatchVertical_of_scalarRange
    {n a b c d : ℕ} [NeZero n]
    (hreach :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
                (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∈
              sqdiagAdjointAmbientVerticalRootScalarRange n a b c d
                (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d :=
by
  intro x hx A hA
  rcases hreach x hx A hA with ⟨y, hy, B, hB, hscalar⟩
  exact ⟨y, hy, B, hB, hscalar⟩

theorem sqdiagAdjointAmbientPairingMatchVertical_of_scalarRange_nonzero
    {n a b c d : ℕ} [NeZero n]
    (hreach :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∃ s : F,
            s ∈
              sqdiagAdjointAmbientVerticalRootScalarRange n a b c d
                (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∧
            s ≠ 0) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d := by
  refine
    sqdiagAdjointAmbientPairingMatchVertical_of_scalarRange
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_
  intro x hx A hA
  rcases hreach x hx with ⟨s, hs, hne⟩
  have htop :=
    sqdiagAdjointAmbientVerticalRootScalarRange_eq_top_of_nonzero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (R := (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1)
      hs hne
  rw [htop]
  exact Submodule.mem_top

theorem sqdiagAdjointAmbientPairingMatchVertical_of_scalarRange_three
    {n a b c d : ℕ} [NeZero n]
    (hparts :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            ∃ s123 s134 s13 : F,
              s123 ∈
                  sqdiagAdjointAmbientVerticalRootScalarRange n a b c d
                    (sqdiagAdjointAmbientPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∧
                s134 ∈
                  sqdiagAdjointAmbientVerticalRootScalarRange n a b c d
                    (sqdiagAdjointAmbientPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∧
                s13 ∈
                  sqdiagAdjointAmbientVerticalRootScalarRange n a b c d
                    (sqdiagAdjointAmbientPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∧
                sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
                    (sqdiagAdjointAmbientPairAdd
                      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
                  s123 + s134 + s13) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d := by
  refine
    sqdiagAdjointAmbientPairingMatchVertical_of_scalarRange
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_
  intro x hx A hA
  rcases hparts x hx A hA with
    ⟨s123, s134, s13, h123, h134, h13, hsum⟩
  rw [hsum]
  exact
    (sqdiagAdjointAmbientVerticalRootScalarRange n a b c d
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1).add_mem
      ((sqdiagAdjointAmbientVerticalRootScalarRange n a b c d
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1).add_mem
        h123 h134)
      h13

theorem sqdiagAdjointAmbientPairingMatchVertical_of_scalarReachable
    {n a b c d : ℕ} [NeZero n]
    (hreach :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1
              (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
                (sqdiagAdjointAmbientPairAdd
                  (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1)) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d := by
  intro x hx A hA
  rcases hreach x hx A hA with ⟨y, hy, B, hB, hscalar⟩
  exact ⟨y, hy, B, hB, hscalar⟩

theorem sqdiagAdjointAmbientPairingMatchVertical_of_rootCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (hzero :
      ∀ (x : SqdiagAdjointAmbientPairPresentation n a b c d),
        x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d →
          ∀ A : RootTarget n b c d,
            sqdiagKCAdjointCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) A =
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 →
            sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
              (sqdiagAdjointAmbientPairAdd
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 = 0) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d := by
  intro x hx A hA
  refine ⟨0, ?_, 0, ?_, ?_⟩
  · exact (sqdiagAdjointAmbientPairPresentationVertical n a b c d).zero_mem
  · simp [sqdiagKCAdjointCoeff_zero]
  · exact
      (sqdiagRootCoeffApply_zero_coeff
        (n := n) (b := b) (c := c) (d := d)
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1).trans
        (hzero x hx A hA).symm

theorem sqdiagAdjointAmbientPairingMatchVertical_of_reducedRelationQ_zero
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d :=
  sqdiagAdjointAmbientPairingMatchVertical_of_rootCoeff_zero
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairPresentation_verticalOrthogonal_coeff_rootCoeff_zero_of_reducedRelationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) hred)

theorem sqdiagReducedRelationQ_eq_zero_of_ambientPairingMatchVertical
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagAdjointAmbientPairingMatchVertical n a b c d)
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) z = 0 := by
  refine
    sqdiagReducedRelationQ_eq_zero_of_pairPresentationQ_eq_zero_on_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ z hz
  intro x hx
  refine
    sqdiagAdjointPairPresentationQ_eq_zero_of_ambientPairPresentationQ_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro y hy
  exact
    sqdiagAdjointAmbientPairPresentationQ_eq_zero_of_pairing_match_vertical
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch y hy

theorem sqdiagAdjointAmbientPairingMatchVertical_iff_reducedRelationQ_zero
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d ↔
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0 := by
  constructor
  · exact
      sqdiagReducedRelationQ_eq_zero_of_ambientPairingMatchVertical
        (n := n) (a := a) (b := b) (c := c) (d := d)
  · exact
      sqdiagAdjointAmbientPairingMatchVertical_of_reducedRelationQ_zero
        (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagReducedRelationQ_eq_rootCoeffApply_of_coeff_eq
    {n a b c d : ℕ} [NeZero n]
    (z : SqdiagReducedRelation n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        z.1.2.1) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) z =
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A z.1.1.1 := by
  unfold sqdiagReducedRelationQ
  have hcoeff :
      z.1.2 =
        ⟨sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A,
          ⟨A, rfl⟩⟩ := by
    apply Subtype.ext
    simpa [sqdiagKCAdjointMap_apply] using hA.symm
  rw [hcoeff]
  exact
    sqdiagAdjointRangePair_mk_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) z.1.1 A

def sqdiagReducedRelationRootZeroACoeffScalarMatch
    (n a b c d : ℕ) [NeZero n] : Prop :=
  ∀ z : SqdiagReducedRelation n a b c d,
    z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
      ∀ A : RootTarget n b c d,
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          z.1.2.1 →
          ∃ B : RootTarget n b c d,
            B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d ∧
              sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
                  B z.1.1.1 =
                sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
                  A z.1.1.1

theorem sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffScalarMatch
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d)
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) z = 0 := by
  rcases z.1.2.2 with ⟨A, hAraw⟩
  have hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        z.1.2.1 := by
    simpa [sqdiagKCAdjointMap_apply] using hAraw
  rcases hmatch z hz A hA with ⟨B, hB, hscalar⟩
  have hBzero :
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
          B z.1.1.1 = 0 :=
    (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d) z).mp hz B hB
  have hAzero :
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
          A z.1.1.1 = 0 := by
    rw [← hscalar]
    exact hBzero
  exact
      (sqdiagReducedRelationQ_eq_rootCoeffApply_of_coeff_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) z A hA).trans hAzero

theorem sqdiagReducedRelationQ_eq_zero_of_coeff_mem_rootZeroACoeffSpace
    {n a b c d : ℕ} [NeZero n]
    (z : SqdiagReducedRelation n a b c d)
    (hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        z.1.2.1)
    (hAroot : A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) :
    sqdiagReducedRelationQ
        (n := n) (a := a) (b := b) (c := c) (d := d) z = 0 := by
  have hscalar :
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
          A z.1.1.1 = 0 :=
    (sqdiagReducedRelation_mem_verticalOrthogonal_iff_annihilates_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d) z).mp hz A hAroot
  exact
    (sqdiagReducedRelationQ_eq_rootCoeffApply_of_coeff_eq
      (n := n) (a := a) (b := b) (c := c) (d := d) z A hA).trans hscalar

theorem sqdiagReducedRelationRootZeroACoeffScalarMatch_of_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hred :
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0) :
    sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d := by
  intro z hz A hA
  refine ⟨0, ?_, ?_⟩
  · exact (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d).zero_mem
  · have hq :=
      sqdiagReducedRelationQ_eq_rootCoeffApply_of_coeff_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) z A hA
    have hAzero :
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d)
            A z.1.1.1 = 0 := by
      have hq0 := hred z hz
      rw [hq] at hq0
      exact hq0
    exact
      (sqdiagRootCoeffApply_zero_coeff
        (n := n) (b := b) (c := c) (d := d) z.1.1.1).trans hAzero.symm

theorem sqdiagReducedRelationRootZeroACoeffScalarMatch_iff_Q_zero
    {n a b c d : ℕ} [NeZero n] :
    sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d ↔
      ∀ z : SqdiagReducedRelation n a b c d,
        z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d →
          sqdiagReducedRelationQ z = 0 := by
  constructor
  · exact
      sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffScalarMatch
        (n := n) (a := a) (b := b) (c := c) (d := d)
  · exact
      sqdiagReducedRelationRootZeroACoeffScalarMatch_of_Q_zero
        (n := n) (a := a) (b := b) (c := c) (d := d)

theorem sqdiagAdjointAmbientPairingMatchVertical_iff_reducedRootZeroACoeffScalarMatch
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d ↔
      sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d := by
  rw [sqdiagAdjointAmbientPairingMatchVertical_iff_reducedRelationQ_zero,
    sqdiagReducedRelationRootZeroACoeffScalarMatch_iff_Q_zero]

theorem sqdiagAdjointAmbientPairingMatchVertical_of_reducedRootZeroACoeffScalarMatch
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d :=
  sqdiagAdjointAmbientPairingMatchVertical_of_reducedRelationQ_zero
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagReducedRelationQ_eq_zero_of_rootZeroACoeffScalarMatch
      (n := n) (a := a) (b := b) (c := c) (d := d) hmatch)

set_option synthInstance.maxHeartbeats 500000 in
-- The separation predicate quantifies over nested reduced-relation and root-target subtypes.
theorem sqdiagAdjointAmbientPairingMatchVertical_of_rootZeroACoeffSpace_separates_reducedRoot
    {n a b c d : ℕ} [NeZero n]
    (hsep :
      ∀ z : SqdiagReducedRelation n a b c d,
        (∀ A : RootTarget n b c d,
          A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
            sqdiagRootCoeffApply A z.1.1.1 = 0) →
        z.1.1.1 = 0) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d :=
  sqdiagAdjointAmbientPairingMatchVertical_of_rootCoeff_zero
    (n := n) (a := a) (b := b) (c := c) (d := d)
    (sqdiagAdjointAmbientPairPresentation_verticalOrthogonal_coeff_rootCoeff_zero_of_rootZeroACoeffSpace_separates_reducedRoot
      (n := n) (a := a) (b := b) (c := c) (d := d) hsep)

theorem sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_B_source_root_zero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (A : RootTarget n b c d)
    (hroot :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B = 0)
    (hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
          B 0 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d := by
  let raw : (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d :=
    ((B, 0), A)
  have hgraph :
      raw ∈
        sqdiagBWAAdjointGraphSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
    constructor
    · change
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, 0) ∈
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)
      have hzero :
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, 0) = 0 := by
        rw [K_yw_eq_KBMap_add_KWMap, hroot]
        simpa using
          (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
      rw [hzero]
      exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).zero_mem
    · simpa [raw] using hcoeff
  let x : SqdiagBWAAdjointGraph n a b c d := ⟨raw, hgraph⟩
  have hxroot : x ∈ sqdiagBWAAdjointGraphRootZero n a b c d := by
    rw [LinearMap.mem_ker]
    change K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, 0) = 0
    rw [K_yw_eq_KBMap_add_KWMap, hroot]
    simpa using
      (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
  refine ⟨⟨x, hxroot⟩, ?_⟩
  rfl

theorem sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_W_source_root_zero
    {n a b c d : ℕ} [NeZero n]
    (W : WFun4 n a b c) (A : RootTarget n b c d)
    (hroot :
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W = 0)
    (hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
          0 W =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d := by
  let raw : (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d :=
    ((0, W), A)
  have hgraph :
      raw ∈
        sqdiagBWAAdjointGraphSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
    constructor
    · change
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (0, W) ∈
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)
      have hzero :
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (0, W) = 0 := by
        rw [K_yw_eq_KBMap_add_KWMap, hroot]
        simpa using
          (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
      rw [hzero]
      exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).zero_mem
    · simpa [raw] using hcoeff
  let x : SqdiagBWAAdjointGraph n a b c d := ⟨raw, hgraph⟩
  have hxroot : x ∈ sqdiagBWAAdjointGraphRootZero n a b c d := by
    rw [LinearMap.mem_ker]
    change K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (0, W) = 0
    rw [K_yw_eq_KBMap_add_KWMap, hroot]
    simpa using
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
  refine ⟨⟨x, hxroot⟩, ?_⟩
  rfl

theorem sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_BPair_zeroRoot
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (x : BPairAmbient n a b c d) (A : RootTarget n b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (hcoeff :
      x.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d := by
  rcases BPair_zeroRoot_mem_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc x hroot hcurl with
    ⟨B, hB⟩
  have hBroot :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B = 0 := by
    have hfst := congrArg Prod.fst hB
    have hval := congrArg Subtype.val hfst
    simpa [SquareBMapAmbient, hroot] using hval
  have hBcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
          B 0 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A := by
    have hsnd := congrArg Prod.snd hB
    have hval := congrArg Subtype.val hsnd
    have hval' :
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
            B 0 = x.2.1 := by
      simpa [SquareBMapAmbient, SquareBInclusion, sqdiagCPhaseCoeff] using hval
    exact hval'.trans hcoeff
  exact
    sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_B_source_root_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) B A hBroot hBcoeff

theorem sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_WPair_zeroRoot
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : WPairAmbient n a b c d) (A : RootTarget n b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (hcoeff :
      x.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d := by
  rcases WPair_zeroRoot_mem_range
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hc hd x hroot hcurl with
    ⟨W, hW⟩
  have hWroot :
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W = 0 := by
    have hfst := congrArg Prod.fst hW
    have hval := congrArg Subtype.val hfst
    simpa [SquareWMapAmbient, hroot] using hval
  have hWcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
          0 W =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A := by
    have hsnd := congrArg Prod.snd hW
    have hval := congrArg Subtype.val hsnd
    have hval' :
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
            0 W = x.2.1 := by
      simpa [SquareWMapAmbient, SquareWInclusion, sqdiagCPhaseCoeff] using hval
    exact hval'.trans hcoeff
  exact
    sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_W_source_root_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) W A hWroot hWcoeff

theorem sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_KCAdjointCoeff_zero
    {n a b c d : ℕ} [NeZero n]
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A = 0) :
    A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d := by
  refine
    sqdiagBWAAdjointGraphRootZeroACoeffSpace_mem_of_B_source_root_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      0 A ?_ ?_
  · simpa using
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
  · simpa [hA, sqdiagCPhaseCoeff] using
      (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero

theorem sqdiagAdjointAmbientPairingMatchVertical_witness_of_BPair_zeroRoot
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (x : BPairAmbient n a b c d) (A : RootTarget n b c d)
    (R : RootTarget n b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (hcoeff :
      x.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
        ∃ B : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
            sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) B R =
              sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) A R := by
  have hxrange :
      x ∈ LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    BPair_zeroRoot_mem_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc x hroot hcurl
  have hwzero :
      (0 : WPairAmbient n a b c d) ∈ LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    refine ⟨0, ?_⟩
    exact (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
  let raw : SqdiagAdjointAmbientPairProduct n a b c d :=
    (⟨x, hxrange⟩, ⟨0, hwzero⟩)
  have hpres :
      raw ∈ sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
    apply (sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) raw)).mpr
    constructor
    · rw [sqdiagAdjointAmbientPairAdd_root_apply]
      change x.1.1 + (0 : WPairAmbient n a b c d).1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)
      rw [hroot]
      simp
    · refine ⟨A, ?_⟩
      rw [sqdiagAdjointAmbientPairAdd_coeff_apply]
      change
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          x.2.1 + (0 : WPairAmbient n a b c d).2.1
      rw [hcoeff]
      simp
  let y : SqdiagAdjointAmbientPairPresentation n a b c d := ⟨raw, hpres⟩
  have hyroot :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 := by
    rw [sqdiagAdjointAmbientPairPresentation_root_apply]
    change x.1.1 + (0 : WPairAmbient n a b c d).1.1 = 0
    rw [hroot]
    simp
  have hyvert :
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d :=
    sqdiagAdjointAmbientPairPresentation_mem_vertical_of_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y hyroot
  refine ⟨y, hyvert, A, ?_, rfl⟩
  rw [sqdiagAdjointAmbientPairPresentation_coeff_apply]
  change
    sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) A =
      x.2.1 + (0 : WPairAmbient n a b c d).2.1
  rw [hcoeff]
  simp

theorem sqdiagAdjointAmbientPairingMatchVertical_witness_of_WPair_zeroRoot
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : WPairAmbient n a b c d) (A : RootTarget n b c d)
    (R : RootTarget n b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (hcoeff :
      x.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
        ∃ B : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
            sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) B R =
              sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) A R := by
  have hxrange :
      x ∈ LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    WPair_zeroRoot_mem_range
      (n := n) (a := a) (b := b) (c := c) (d := d) hc hd x hroot hcurl
  have hbzero :
      (0 : BPairAmbient n a b c d) ∈ LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    refine ⟨0, ?_⟩
    exact (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
  let raw : SqdiagAdjointAmbientPairProduct n a b c d :=
    (⟨0, hbzero⟩, ⟨x, hxrange⟩)
  have hpres :
      raw ∈ sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
    apply (sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) raw)).mpr
    constructor
    · rw [sqdiagAdjointAmbientPairAdd_root_apply]
      change (0 : BPairAmbient n a b c d).1.1 + x.1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)
      rw [hroot]
      simp
    · refine ⟨A, ?_⟩
      rw [sqdiagAdjointAmbientPairAdd_coeff_apply]
      change
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A =
          (0 : BPairAmbient n a b c d).2.1 + x.2.1
      rw [hcoeff]
      simp
  let y : SqdiagAdjointAmbientPairPresentation n a b c d := ⟨raw, hpres⟩
  have hyroot :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 := by
    rw [sqdiagAdjointAmbientPairPresentation_root_apply]
    change (0 : BPairAmbient n a b c d).1.1 + x.1.1 = 0
    rw [hroot]
    simp
  have hyvert :
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d :=
    sqdiagAdjointAmbientPairPresentation_mem_vertical_of_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y hyroot
  refine ⟨y, hyvert, A, ?_, rfl⟩
  rw [sqdiagAdjointAmbientPairPresentation_coeff_apply]
  change
    sqdiagKCAdjointCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) A =
      (0 : BPairAmbient n a b c d).2.1 + x.2.1
  rw [hcoeff]
  simp

theorem sqdiagAdjointAmbientPairingMatchVertical_witness_of_pair_root_eq
    {n a b c d : ℕ} [NeZero n]
    (xB : BPairAmbient n a b c d)
    (hxB :
      xB ∈ LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
    (xW : WPairAmbient n a b c d)
    (hxW :
      xW ∈ LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)))
    (A : RootTarget n b c d) (R : RootTarget n b c d)
    (hroot : xB.1.1 = xW.1.1)
    (hcoeff :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        xB.2.1 + xW.2.1) :
    ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
        ∃ B : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
            sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) B R =
              sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) A R := by
  let raw : SqdiagAdjointAmbientPairProduct n a b c d :=
    (⟨xB, hxB⟩, ⟨xW, hxW⟩)
  have hpres :
      raw ∈ sqdiagAdjointAmbientPairPresentationSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagAdjointAmbientPairPresentationSubmodule_mem_iff]
    apply (sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) raw)).mpr
    constructor
    · rw [sqdiagAdjointAmbientPairAdd_root_apply]
      change xB.1.1 + xW.1.1 ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)
      have hsum : xB.1.1 + xW.1.1 = 0 :=
        (add_eq_zero_iff_eq_of_F_module _ _).mpr hroot
      rw [hsum]
      exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).zero_mem
    · refine ⟨A, ?_⟩
      rw [sqdiagAdjointAmbientPairAdd_coeff_apply]
      exact hcoeff
  let y : SqdiagAdjointAmbientPairPresentation n a b c d := ⟨raw, hpres⟩
  have hyroot :
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1).1 = 0 := by
    rw [sqdiagAdjointAmbientPairPresentation_root_apply]
    change xB.1.1 + xW.1.1 = 0
    exact (add_eq_zero_iff_eq_of_F_module _ _).mpr hroot
  have hyvert :
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d :=
    sqdiagAdjointAmbientPairPresentation_mem_vertical_of_root_add_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) y hyroot
  refine ⟨y, hyvert, A, ?_, rfl⟩
  rw [sqdiagAdjointAmbientPairPresentation_coeff_apply]
  exact hcoeff

theorem sqdiagAdjointAmbientPairingMatchVertical_witness_of_ambient_BPair_zeroRoot
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A : RootTarget n b c d) (R : RootTarget n b c d)
    (hroot : x.1.1.1.1.1 = 0)
    (hcoeff :
      x.1.1.1.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
        ∃ B : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
            sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) B R =
              sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) A R :=
  sqdiagAdjointAmbientPairingMatchVertical_witness_of_BPair_zeroRoot
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hb hc x.1.1.1 A R hroot
    (sqdiagAdjointAmbientPairPresentation_BPairCurl_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hb x)
    hcoeff

theorem sqdiagAdjointAmbientPairingMatchVertical_witness_of_ambient_WPair_zeroRoot
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A : RootTarget n b c d) (R : RootTarget n b c d)
    (hroot : x.1.2.1.1.1 = 0)
    (hcoeff :
      x.1.2.1.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    ∃ y : SqdiagAdjointAmbientPairPresentation n a b c d,
      y ∈ sqdiagAdjointAmbientPairPresentationVertical n a b c d ∧
        ∃ B : RootTarget n b c d,
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) B =
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) y.1).2 ∧
            sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) B R =
              sqdiagRootCoeffApply
                (n := n) (b := b) (c := c) (d := d) A R :=
  sqdiagAdjointAmbientPairingMatchVertical_witness_of_WPair_zeroRoot
    (n := n) (a := a) (b := b) (c := c) (d := d)
    hc hd x.1.2.1 A R hroot
    (sqdiagAdjointAmbientPairPresentation_WPairCurl_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hd x)
    hcoeff

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_BPair_zeroRoot_same_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c)
    (x : BPairAmbient n a b c d)
    (A B R : RootTarget n b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0)
    (hcoeff :
      x.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B)
    (hsame :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
      (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) := by
  have hB :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
        (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R) :=
    sqdiagAdjointAmbientPairingMatchVertical_witness_of_BPair_zeroRoot
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb hc x B R hroot hcurl hcoeff
  exact
    sqdiagAdjointAmbientVerticalRootScalarReachable_of_same_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      A B R hsame hB

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_WPair_zeroRoot_same_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d)
    (x : WPairAmbient n a b c d)
    (A B R : RootTarget n b c d)
    (hroot : x.1.1 = 0)
    (hcurl :
      WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd x = 0)
    (hcoeff :
      x.2.1 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B)
    (hsame :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
      (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) := by
  have hB :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
        (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R) :=
    sqdiagAdjointAmbientPairingMatchVertical_witness_of_WPair_zeroRoot
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hc hd x B R hroot hcurl hcoeff
  exact
    sqdiagAdjointAmbientVerticalRootScalarReachable_of_same_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      A B R hsame hB

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_rootZeroACoeffSpace
    {n a b c d : ℕ} [NeZero n]
    (A R : RootTarget n b c d)
    (hA : A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
      (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) := by
  rcases hA with ⟨x, hxA⟩
  let Bsrc : BFun4 n a c d := x.1.1.1.1
  let Wsrc : WFun4 n a b c := x.1.1.1.2
  let xB : BPairAmbient n a b c d :=
    SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) Bsrc
  let xW : WPairAmbient n a b c d :=
    SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) Wsrc
  have hxBrange :
      xB ∈ LinearMap.range
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    ⟨Bsrc, rfl⟩
  have hxWrange :
      xW ∈ LinearMap.range
        (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    ⟨Wsrc, rfl⟩
  have hAeq :
      sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1 = A := by
    simpa [sqdiagBWAAdjointGraphRootZeroAMap] using hxA
  have hxGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1).mp x.1.2
  have hrootZero :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (Bsrc, Wsrc) = 0 := by
    have hxroot :=
      LinearMap.mem_ker.mp x.2
    change
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.1 = 0
      at hxroot
    simpa [Bsrc, Wsrc] using hxroot
  have hroot :
      xB.1.1 = xW.1.1 := by
    have hsum :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) Bsrc +
          KWMap (n := n) (a := a) (b := b) (c := c) (d := d) Wsrc = 0 := by
      simpa [K_yw_eq_KBMap_add_KWMap] using hrootZero
    change
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) Bsrc =
        KWMap (n := n) (a := a) (b := b) (c := c) (d := d) Wsrc
    exact (add_eq_zero_iff_eq_of_F_module _ _).mp hsum
  have hcoeff :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1) =
        xB.2.1 + xW.2.1 := by
    have hphase :
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
            Bsrc Wsrc =
          sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (sqdiagBWAAdjointGraphAMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1) := by
      simpa [Bsrc, Wsrc, sqdiagCPhaseCoeff] using hxGraph.2
    rw [← hphase]
    have hsplit :
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
            Bsrc Wsrc =
          sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
              Bsrc 0 +
            sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
              0 Wsrc := by
      unfold sqdiagCPhaseCoeff
      have hmap :=
        (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_add
          (Bsrc, 0) (0, Wsrc)
      simpa using hmap
    simpa [xB, xW, Bsrc, Wsrc, SquareBMapAmbient, SquareWMapAmbient,
      SquareBInclusion, SquareWInclusion, sqdiagCPhaseCoeff] using hsplit
  have hreach :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
        (sqdiagRootCoeffApply
          (n := n) (b := b) (c := c) (d := d)
          (sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1) R) :=
    sqdiagAdjointAmbientPairingMatchVertical_witness_of_pair_root_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      xB hxBrange xW hxWrange
      (sqdiagBWAAdjointGraphAMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1)
      R hroot hcoeff
  simpa [hAeq] using hreach

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_rootZeroACoeffSpace_scalar_eq
    {n a b c d : ℕ} [NeZero n]
    (A B R : RootTarget n b c d)
    (hB : B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d)
    (hscalar :
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R =
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
      (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) := by
  have hBreach :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
        (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R) :=
    sqdiagAdjointAmbientVerticalRootScalarReachable_of_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d) B R hB
  simpa [hscalar] using hBreach

@[simp]
theorem sqdiagAdjointAmbientPairPresentationSum_root_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  change
    (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x)).1.1.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1
  rw [sqdiagAdjointPairPresentationSum_root_apply]
  exact congrArg Prod.fst
    (sqdiagAdjointAmbientPairProductEquiv_pairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1)

@[simp]
theorem sqdiagAdjointAmbientPairPresentationSum_coeff_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d) :
    (sqdiagAdjointAmbientPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d) x).1.2.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 := by
  change
    (sqdiagAdjointPairPresentationSum
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (sqdiagAdjointAmbientPairEquivPairPresentation
          (n := n) (a := a) (b := b) (c := c) (d := d) x)).1.2.1 =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2
  rw [sqdiagAdjointPairPresentationSum_coeff_apply]
  exact congrArg Prod.snd
    (sqdiagAdjointAmbientPairProductEquiv_pairAdd
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1)

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_reducedRootZeroACoeffScalarMatch
    {n a b c d : ℕ} [NeZero n]
    (hmatch : sqdiagReducedRelationRootZeroACoeffScalarMatch n a b c d)
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1
      (sqdiagRootCoeffApply
        (n := n) (b := b) (c := c) (d := d) A
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1) := by
  let z : SqdiagReducedRelation n a b c d :=
    sqdiagAdjointAmbientPairPresentationSum
      (n := n) (a := a) (b := b) (c := c) (d := d) x
  have hz : z ∈ sqdiagReducedRelationVerticalOrthogonal n a b c d := by
    simpa [z] using
      sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
        (n := n) (a := a) (b := b) (c := c) (d := d) x hx
  have hAz :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        z.1.2.1 := by
    simpa [z] using hA
  rcases hmatch z hz A hAz with ⟨B, hB, hscalar⟩
  have hreach :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d z.1.1.1
        (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A z.1.1.1) :=
    sqdiagAdjointAmbientVerticalRootScalarReachable_of_rootZeroACoeffSpace_scalar_eq
      (n := n) (a := a) (b := b) (c := c) (d := d)
      A B z.1.1.1 hB hscalar
  simpa [z] using hreach

theorem sqdiagAdjointAmbientVerticalRootScalarReachable_of_rootZeroACoeffSpace_same_KCAdjointCoeff
    {n a b c d : ℕ} [NeZero n]
    (A B R : RootTarget n b c d)
    (hB : B ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d)
    (hsame :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) B =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A) :
    sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
      (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R) := by
  have hBreach :
      sqdiagAdjointAmbientVerticalRootScalarReachable n a b c d R
        (sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) B R) :=
    sqdiagAdjointAmbientVerticalRootScalarReachable_of_rootZeroACoeffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d) B R hB
  exact
    sqdiagAdjointAmbientVerticalRootScalarReachable_of_same_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) A B R hsame hBreach

theorem sqdiagAdjointAmbientPairPresentation_sources_CPhaseCoeff_eq_pairCoeff
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (hB :
      SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B =
        x.1.1.1)
    (hW :
      SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W =
        x.1.2.1) :
    sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
      (sqdiagAdjointAmbientPairAdd
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 := by
  have hsplit :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B).2.1 +
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W).2.1 := by
    have hcombined :=
      congrArg Prod.snd
        (SquareCombined_eq_B_add_W
          (n := n) (a := a) (b := b) (c := c) (d := d) B W)
    simpa [SquareCombined, SquareBMap, SquareWMap, SquareBMapAmbient, SquareWMapAmbient,
      sqdiagCPhaseCoeff] using hcombined
  calc
    sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B).2.1 +
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W).2.1 := hsplit
    _ = x.1.1.1.2.1 + x.1.2.1.2.1 := by rw [hB, hW]
    _ =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2 := by
          rw [sqdiagAdjointAmbientPairPresentation_coeff_apply]

set_option synthInstance.maxHeartbeats 200000 in
-- The source extraction moves through nested ambient range subtypes and CPhase
-- coefficient maps; instance search needs a local budget bump.
theorem sqdiagAdjointAmbientPairPresentation_exists_sources_CPhaseLinear_eq_rootCoeffApply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A : RootTarget n b c d) (C : CFun4 n a b d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    ∃ B : BFun4 n a c d, ∃ W : WFun4 n a b c,
      SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B =
          x.1.1.1 ∧
        SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W =
          x.1.2.1 ∧
        sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C =
          sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) := by
  rcases x.1.1.2 with ⟨B, hB⟩
  rcases x.1.2.2 with ⟨W, hW⟩
  refine ⟨B, W, hB, hW, ?_⟩
  refine
    sqdiagCPhaseLinear_eq_rootCoeffApply_KCMap_of_coeff_eq_KCAdjointCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) B W A C ?_
  exact
    (sqdiagAdjointAmbientPairPresentation_sources_CPhaseCoeff_eq_pairCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x B W hB hW).trans
      hA.symm

set_option synthInstance.maxHeartbeats 200000 in
-- Choosing a KC preimage and transporting the CPhase scalar through the ambient
-- presentation keeps the same nested subtype structure as the previous lemma.
theorem sqdiagAdjointAmbientPairPresentation_exists_sources_KC_preimage_CPhaseLinear_eq_targetScalar
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    ∃ B : BFun4 n a c d, ∃ W : WFun4 n a b c, ∃ C : CFun4 n a b d,
      SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B =
          x.1.1.1 ∧
        SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W =
          x.1.2.1 ∧
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∧
        sqdiagCPhaseLinear (n := n) (a := a) (b := b) (c := c) (d := d) B W C =
          sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  have hrootMem :
      (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 ∈
        LinearMap.range
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rw [range_KCMap_eq_ZDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact
      sqdiagAdjointAmbientPairPresentation_root_mem_ZDiff
        (n := n) (a := a) (b := b) (c := c) (d := d) x
  rcases hrootMem with ⟨C, hC⟩
  rcases
    sqdiagAdjointAmbientPairPresentation_exists_sources_CPhaseLinear_eq_rootCoeffApply
      (n := n) (a := a) (b := b) (c := c) (d := d) x A C hA with
    ⟨B, W, hB, hW, hphase⟩
  refine ⟨B, W, C, hB, hW, hC, ?_⟩
  rw [hphase, hC]

set_option synthInstance.maxHeartbeats 300000 in
-- Building a graph representative from ambient sources crosses the graph,
-- adjoint-image, and reduced-relation subtypes, which stresses synthesis.
theorem sqdiagAdjointAmbientPairPresentation_exists_graph_toReduced_eq_sum
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    ∃ g : SqdiagBWAAdjointGraph n a b c d,
      sqdiagBWAAdjointGraphToReducedRelation
          (n := n) (a := a) (b := b) (c := c) (d := d) g =
        sqdiagAdjointAmbientPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∧
      sqdiagBWAAdjointGraphQ
          (n := n) (a := a) (b := b) (c := c) (d := d) g =
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  rcases x.1.1.2 with ⟨B, hB⟩
  rcases x.1.2.2 with ⟨W, hW⟩
  have hcoeff :
      sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d) B W =
        sqdiagKCAdjointCoeff (n := n) (a := a) (b := b) (c := c) (d := d) A :=
    (sqdiagAdjointAmbientPairPresentation_sources_CPhaseCoeff_eq_pairCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) x B W hB hW).trans
      hA.symm
  have hroot :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
    have hBroot :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B =
          x.1.1.1.1.1 := by
      exact congrArg (fun q : BPairAmbient n a b c d => q.1.1) hB
    have hWroot :
        KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
          x.1.2.1.1.1 := by
      exact congrArg (fun q : WPairAmbient n a b c d => q.1.1) hW
    calc
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) =
          KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B +
            KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W := by
            rw [K_yw_eq_KBMap_add_KWMap]
      _ = x.1.1.1.1.1 + x.1.2.1.1.1 := by rw [hBroot, hWroot]
      _ =
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
            rw [sqdiagAdjointAmbientPairPresentation_root_apply]
  let raw : (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d := ((B, W), A)
  have hgraph :
      raw ∈
        sqdiagBWAAdjointGraphSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
    constructor
    · change
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) ∈
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)
      rw [hroot]
      exact
        sqdiagAdjointAmbientPairPresentation_root_mem_ZDiff
          (n := n) (a := a) (b := b) (c := c) (d := d) x
    · simpa [raw] using hcoeff
  let g : SqdiagBWAAdjointGraph n a b c d := ⟨raw, hgraph⟩
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) =
          (sqdiagAdjointAmbientPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x).1.1.1
      rw [sqdiagAdjointAmbientPairPresentationSum_root_apply, hroot]
    · apply Subtype.ext
      change
        (sqdiagBWAAdjointGraphToReducedRelation
            (n := n) (a := a) (b := b) (c := c) (d := d) g).1.2.1 =
          (sqdiagAdjointAmbientPairPresentationSum
            (n := n) (a := a) (b := b) (c := c) (d := d) x).1.2.1
      have hsquare :
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)).2 =
            sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A := by
        simpa [SquareCombined, sqdiagCPhaseCoeff] using hcoeff
      simpa [g, raw, sqdiagBWAAdjointGraphToReducedRelation,
        sqdiagBWAAdjointGraphToAdjointImage, sqdiagAdjointImageEquivReducedRelation,
        sqdiagAdjointAmbientPairPresentationSum_coeff_apply]
        using hsquare.trans hA
  · change
      sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) =
        sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
          (sqdiagAdjointAmbientPairAdd
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1
    rw [hroot]

set_option synthInstance.maxHeartbeats 300000 in
-- The lagrangian lift combines the graph representative with the reduced
-- vertical-orthogonal transport through nested submodules.
theorem sqdiagAdjointAmbientPairPresentation_exists_lagrangian_graph_targetScalar
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagAdjointAmbientPairPresentation n a b c d)
    (hx : x ∈ sqdiagAdjointAmbientPairPresentationVerticalOrthogonal n a b c d)
    (A : RootTarget n b c d)
    (hA :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        (sqdiagAdjointAmbientPairAdd
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).2) :
    ∃ g : SqdiagBWAAdjointGraph n a b c d,
      g ∈ sqdiagBWAAdjointGraphLagrangian n a b c d ∧
        sqdiagBWAAdjointGraphQ
            (n := n) (a := a) (b := b) (c := c) (d := d) g =
          sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A
            (sqdiagAdjointAmbientPairAdd
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 := by
  rcases
    sqdiagAdjointAmbientPairPresentation_exists_graph_toReduced_eq_sum
      (n := n) (a := a) (b := b) (c := c) (d := d) x A hA with
    ⟨g, hred, hQ⟩
  have hsumOrth :
      sqdiagAdjointAmbientPairPresentationSum
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        sqdiagReducedRelationVerticalOrthogonal n a b c d :=
    sqdiagAdjointAmbientPairPresentationSum_mem_reducedVerticalOrthogonal_of_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx
  have hg :
      g ∈ sqdiagBWAAdjointGraphLagrangian n a b c d :=
    sqdiagBWAAdjointGraph_mem_lagrangian_of_toReduced_mem_verticalOrthogonal
      (n := n) (a := a) (b := b) (c := c) (d := d) g (by
        simpa [hred] using hsumOrth)
  exact ⟨g, hg, hQ⟩

theorem sqdiagAdjointAmbientPairingMatchVertical_of_lagrangian_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hQ :
      ∀ g : SqdiagBWAAdjointGraph n a b c d,
        g ∈ sqdiagBWAAdjointGraphLagrangian n a b c d →
          sqdiagBWAAdjointGraphQ
            (n := n) (a := a) (b := b) (c := c) (d := d) g = 0) :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d := by
  refine
    sqdiagAdjointAmbientPairingMatchVertical_of_rootCoeff_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_
  intro x hx A hA
  rcases
    sqdiagAdjointAmbientPairPresentation_exists_lagrangian_graph_targetScalar
      (n := n) (a := a) (b := b) (c := c) (d := d) x hx A hA with
    ⟨g, hg, hscalar⟩
  exact hscalar ▸ hQ g hg

theorem sqdiagAdjointAmbientPairingMatchVertical_iff_lagrangian_Q_zero
    {n a b c d : ℕ} [NeZero n] :
    sqdiagAdjointAmbientPairingMatchVertical n a b c d ↔
      ∀ g : SqdiagBWAAdjointGraph n a b c d,
        g ∈ sqdiagBWAAdjointGraphLagrangian n a b c d →
          sqdiagBWAAdjointGraphQ
            (n := n) (a := a) (b := b) (c := c) (d := d) g = 0 := by
  constructor
  · intro hmatch g hg
    exact
      sqdiagBWAAdjointGraphQ_eq_zero_of_ambientPairPresentation_pairing_match_vertical
        (n := n) (a := a) (b := b) (c := c) (d := d) hmatch g hg
  · exact
      sqdiagAdjointAmbientPairingMatchVertical_of_lagrangian_Q_zero
        (n := n) (a := a) (b := b) (c := c) (d := d)

noncomputable def sqdiagSquareBWIntersectionCoreParamRead
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F] SquareCoreParam n :=
  (SquareCoreAllowedRead (n := n)).comp
    ((SquareBWModelTrace (n := n) (a := a) (c := c)).comp
      (SquareBWIntersectionToModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd))

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamRead_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x =
      SquareCoreAllowedRead (n := n)
        (SquareBWModelTrace (n := n) (a := a) (c := c)
          (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)) :=
  rfl

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamRead_s0_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) (sy sw : I n) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1.1 sy sw =
      ((SquareBWModelTrace (n := n) (a := a) (c := c)
          (SquareBWIntersectionToModel
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1.2 0).1 sy sw :=
  rfl

@[simp]
theorem sqdiagSquareBWIntersectionCoreParamRead_line_apply
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) (t r : I n) :
    (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).2.1 t r =
      corePVal
        (SquareBWModelTrace (n := n) (a := a) (c := c)
          (SquareBWIntersectionToModel
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1.1
        (SquareBWModelTrace (n := n) (a := a) (c := c)
          (SquareBWIntersectionToModel
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1.2
        t r :=
  rfl

theorem sqdiagSquareBWIntersectionCoreParamBuild_read
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    SquareCoreAllowedBuildFun (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x) =
      SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x) := by
  exact
    SquareCoreAllowedBuildFun_read
      (n := n)
      (SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x))

theorem sqdiagSquareBWIntersection_coreBuildAVal_read_eq_trace_root
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) (z sy sw : I n) :
    coreBuildAVal (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).2
        z sy sw =
      ((SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1.1 z).1 sy sw := by
  have h :=
    congrArg
      (fun q : SquareCoreAllowed n => ((q.1.1 z).1 sy sw))
      (sqdiagSquareBWIntersectionCoreParamBuild_read
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)
  simpa using h

theorem sqdiagSquareBWIntersection_coreBuildS_read_eq_trace_compat
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) (t sy sw : I n) :
    (coreBuildS (n := n)
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1
        (sqdiagSquareBWIntersectionCoreParamRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).2
        t).1 sy sw =
      ((SquareBWModelTrace (n := n) (a := a) (c := c)
        (SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)).1.2 t).1 sy sw := by
  have h :=
    congrArg
      (fun q : SquareCoreAllowed n => ((q.1.2 t).1 sy sw))
      (sqdiagSquareBWIntersectionCoreParamBuild_read
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x)
  simpa using h

theorem sqdiagSquareBWIntersectionCoreParamRead_surjective
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Function.Surjective
      (sqdiagSquareBWIntersectionCoreParamRead
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd) := by
  intro p
  rcases SquareBWModelTrace_surjective
      (n := n) (a := a) (c := c) hc
      (SquareCoreAllowedBuildFun (n := n) p) with
    ⟨m, hm⟩
  refine
    ⟨(SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm m, ?_⟩
  have hmodel :
      SquareBWIntersectionToModel
          (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
          ((SquareBWIntersectionEquivModel
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).symm m) =
        m := by
    exact
      (SquareBWIntersectionEquivModel
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).apply_symm_apply m
  rw [sqdiagSquareBWIntersectionCoreParamRead_apply, hmodel, hm]
  exact SquareCoreAllowedRead_buildFun (n := n) p

end

end SquareDiagonal
end Core4loop
