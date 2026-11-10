import Core4loop.CompleteGraph.EvenAllLarge.Coefficients

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.CompleteGraph.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite

private theorem coeffApply_comm
    {ι : Type*} [Fintype ι] (f g : ι → F) :
    coeffApply f g = coeffApply g f := by
  unfold coeffApply
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

private theorem sum_mul_sum_if_eq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : β → F) (g : α → F) (h : α → β) :
    (∑ b : β, f b * ∑ a : α, if h a = b then g a else 0) =
      ∑ a : α, f (h a) * g a := by
  classical
  calc
    (∑ b : β, f b * ∑ a : α, if h a = b then g a else 0) =
        ∑ b : β, ∑ a : α, f b * (if h a = b then g a else 0) := by
      refine Finset.sum_congr rfl ?_
      intro b _
      rw [Finset.mul_sum]
    _ = ∑ a : α, ∑ b : β,
        f b * (if h a = b then g a else 0) := Finset.sum_comm
    _ = ∑ a : α, f (h a) * g a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Finset.sum_eq_single (h a)]
      · simp
      · intro b _ hb
        simp [hb.symm]
      · simp

/-! Literal coefficient functions for the B-test and W-test channels. -/

noncomputable def k4BaseSBLeftCoeff
    {n b c d : Nat} [NeZero n]
    (C : CFun4 n 1 b d) : BFun4 n 1 c d :=
  fun p sy z w =>
    (∑ y : YVec n b,
      if vecSum y = sy then C p y (vecSum z) w else 0) +
    ∑ y : YVec n b,
      if vecSum y + 1 = sy then C p y (vecSum z + 1) w else 0

noncomputable def k4BaseSBRightCoeff
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) : BFun4 n 1 c d :=
  fun p sy z w =>
    (∑ y : YVec n b,
      if vecSum y = sy then
        sigma.1.2 p y z (vecSum w) else 0) +
    ∑ y : YVec n b,
      if vecSum y + 1 = sy then
        sigma.1.2 p y z (vecSum w + 1) else 0

noncomputable def k4BaseSWLeftCoeff
    {n b c d : Nat} [NeZero n]
    (C : CFun4 n 1 b d) : WFun4 n 1 b c :=
  fun p y z sw =>
    (∑ w : WVec n d,
      if vecSum w = sw then C p y (vecSum z) w else 0) +
    ∑ w : WVec n d,
      if vecSum w + 1 = sw then C p y (vecSum z + 1) w else 0

noncomputable def k4BaseSWRightCoeff
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) : WFun4 n 1 b c :=
  fun p y z sw =>
    (∑ w : WVec n d,
      if vecSum w = sw then
        sigma.1.1 p (vecSum y) z w else 0) +
    ∑ w : WVec n d,
      if vecSum w + 1 = sw then
        sigma.1.1 p (vecSum y + 1) z w else 0

def K4SBIndexedEquation
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  ∀ (sy : I n) (z : ZVec n c) (w : WVec n d),
    k4BaseSBLeftCoeff C (zeroVec : PVec n 1) sy z w =
      k4BaseSBRightCoeff sigma (zeroVec : PVec n 1) sy z w

def K4SWIndexedEquation
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) : Prop :=
  ∀ (y : YVec n b) (z : ZVec n c) (sw : I n),
    k4BaseSWLeftCoeff C (zeroVec : PVec n 1) y z sw =
      k4BaseSWRightCoeff sigma (zeroVec : PVec n 1) y z sw

theorem k4Base_SBIndexed_iff_coeff_eq
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    K4SBIndexedEquation sigma C ↔
      k4BaseSBLeftCoeff C = k4BaseSBRightCoeff sigma := by
  constructor
  · intro h
    funext p sy z w
    rw [pVec_one_eq_zeroVec p]
    exact h sy z w
  · intro h sy z w
    exact congrFun (congrFun (congrFun (congrFun h
      (zeroVec : PVec n 1)) sy) z) w

theorem k4Base_SWIndexed_iff_coeff_eq
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    K4SWIndexedEquation sigma C ↔
      k4BaseSWLeftCoeff C = k4BaseSWRightCoeff sigma := by
  constructor
  · intro h
    funext p y z sw
    rw [pVec_one_eq_zeroVec p]
    exact h y z sw
  · intro h y z sw
    exact congrFun (congrFun (congrFun (congrFun h
      (zeroVec : PVec n 1)) y) z) sw

private theorem coeffApply_bFiberCoeff
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d)
    (u v : PVec n 1 → YVec n b → ZVec n c → WVec n d → F) :
    coeffApply
        (bFun4Equiv n 1 c d (fun p sy z w =>
          (∑ y : YVec n b, if vecSum y = sy then u p y z w else 0) +
          ∑ y : YVec n b,
            if vecSum y + 1 = sy then v p y z w else 0))
        (bFun4Equiv n 1 c d B) =
      ∑ p : PVec n 1, ∑ y : YVec n b,
        ∑ z : ZVec n c, ∑ w : WVec n d,
          (B p (vecSum y) z w * u p y z w +
            B p (vecSum y + 1) z w * v p y z w) := by
  classical
  unfold coeffApply bFun4Equiv
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ p : PVec n 1, ∑ sy : I n, ∑ z : ZVec n c, ∑ w : WVec n d,
        B p sy z w *
          ((∑ y : YVec n b, if vecSum y = sy then u p y z w else 0) +
            ∑ y : YVec n b,
              if vecSum y + 1 = sy then v p y z w else 0)) =
      ∑ p : PVec n 1, ∑ z : ZVec n c, ∑ w : WVec n d, ∑ sy : I n,
        B p sy z w *
          ((∑ y : YVec n b, if vecSum y = sy then u p y z w else 0) +
            ∑ y : YVec n b,
              if vecSum y + 1 = sy then v p y z w else 0) := by
        refine Finset.sum_congr rfl ?_
        intro p _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [Finset.sum_comm]
    _ = ∑ p : PVec n 1, ∑ z : ZVec n c, ∑ w : WVec n d,
        ∑ y : YVec n b,
          (B p (vecSum y) z w * u p y z w +
            B p (vecSum y + 1) z w * v p y z w) := by
      refine Finset.sum_congr rfl ?_
      intro p _
      refine Finset.sum_congr rfl ?_
      intro z _
      refine Finset.sum_congr rfl ?_
      intro w _
      calc
        (∑ sy : I n,
            B p sy z w *
              ((∑ y : YVec n b,
                  if vecSum y = sy then u p y z w else 0) +
                ∑ y : YVec n b,
                  if vecSum y + 1 = sy then v p y z w else 0)) =
          (∑ sy : I n, B p sy z w *
            ∑ y : YVec n b,
              if vecSum y = sy then u p y z w else 0) +
          ∑ sy : I n, B p sy z w *
            ∑ y : YVec n b,
              if vecSum y + 1 = sy then v p y z w else 0 := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro sy _
            ring
        _ = (∑ y : YVec n b,
              B p (vecSum y) z w * u p y z w) +
            ∑ y : YVec n b,
              B p (vecSum y + 1) z w * v p y z w := by
          rw [sum_mul_sum_if_eq, sum_mul_sum_if_eq]
        _ = ∑ y : YVec n b,
            (B p (vecSum y) z w * u p y z w +
              B p (vecSum y + 1) z w * v p y z w) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ p : PVec n 1, ∑ y : YVec n b,
        ∑ z : ZVec n c, ∑ w : WVec n d,
          (B p (vecSum y) z w * u p y z w +
            B p (vecSum y + 1) z w * v p y z w) := by
      refine Finset.sum_congr rfl ?_
      intro p _
      calc
        (∑ z : ZVec n c, ∑ w : WVec n d, ∑ y : YVec n b,
            (B p (vecSum y) z w * u p y z w +
              B p (vecSum y + 1) z w * v p y z w)) =
          ∑ z : ZVec n c, ∑ y : YVec n b, ∑ w : WVec n d,
            (B p (vecSum y) z w * u p y z w +
              B p (vecSum y + 1) z w * v p y z w) := by
            refine Finset.sum_congr rfl ?_
            intro z _
            rw [Finset.sum_comm]
        _ = ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
            (B p (vecSum y) z w * u p y z w +
              B p (vecSum y + 1) z w * v p y z w) := by
          rw [Finset.sum_comm]

private theorem sum_PVec_one
    {n : Nat} [NeZero n] (f : PVec n 1 → F) :
    (∑ p : PVec n 1, f p) = f (zeroVec : PVec n 1) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    exact (hp (pVec_one_eq_zeroVec p)).elim
  · simp

theorem k4Base_SB_left_pairing
    {n b c d : Nat} [NeZero n]
    (C : CFun4 n 1 b d) (B : BFun4 n 1 c d) :
    k4BaseCFunDotDual C
        (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          (B, (0 : WFun4 n 1 b c))) =
      coeffApply
        (bFun4Equiv n 1 c d (k4BaseSBLeftCoeff C))
        (bFun4Equiv n 1 c d B) := by
  rw [k4BaseCFunDotDual_apply, coeffApply_comm]
  rw [coeffApply_squareCompat_eq_Q2]
  unfold k4BaseSBLeftCoeff
  rw [coeffApply_bFiberCoeff B
    (fun p y z w => C p y (vecSum z) w)
    (fun p y z w => C p y (vecSum z + 1) w)]
  · unfold Q2 betaB gammaB deltaC etaC xiW zetaW
    simp only [Pi.zero_apply, mul_zero, add_zero]

theorem k4Base_SB_right_pairing
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (B : BFun4 n 1 c d) :
    k4BWSlice B sigma.1.2 =
      coeffApply
        (bFun4Equiv n 1 c d (k4BaseSBRightCoeff sigma))
        (bFun4Equiv n 1 c d B) := by
  unfold k4BaseSBRightCoeff
  rw [coeffApply_bFiberCoeff B
    (fun p y z w => sigma.1.2 p y z (vecSum w))
    (fun p y z w => sigma.1.2 p y z (vecSum w + 1))]
  unfold k4BWSlice betaB gammaB xiW zetaW
  rw [sum_PVec_one]

private theorem coeffApply_eq_forall_iff
    {ι : Type*} [Fintype ι] (c e : ι → F) :
    (∀ f : ι → F, coeffApply c f = coeffApply e f) ↔ c = e := by
  classical
  constructor
  · intro h
    funext i
    have hi := h (Pi.single i (1 : F))
    simpa [coeffApply, Pi.single_apply] using hi
  · rintro rfl
    intro f
    rfl

theorem k4Base_SB_functional_iff_indexed
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    K4SBCoeffEquation sigma C ↔ K4SBIndexedEquation sigma C := by
  rw [k4Base_SBIndexed_iff_coeff_eq]
  constructor
  · intro h
    apply Equiv.injective (bFun4Equiv n 1 c d)
    exact (coeffApply_eq_forall_iff _ _).mp (fun f => by
      let B := (bFun4Equiv n 1 c d).symm f
      have hB := h B
      rw [k4Base_SB_left_pairing, k4Base_SB_right_pairing] at hB
      simpa [B] using hB)
  · intro h B
    rw [k4Base_SB_left_pairing, k4Base_SB_right_pairing, h]

private theorem coeffApply_wFiberCoeff
    {n b c d : Nat} [NeZero n]
    (W : WFun4 n 1 b c)
    (u v : PVec n 1 → YVec n b → ZVec n c → WVec n d → F) :
    coeffApply
        (wFun4Equiv n 1 b c (fun p y z sw =>
          (∑ w : WVec n d, if vecSum w = sw then u p y z w else 0) +
          ∑ w : WVec n d,
            if vecSum w + 1 = sw then v p y z w else 0))
        (wFun4Equiv n 1 b c W) =
      ∑ p : PVec n 1, ∑ y : YVec n b,
        ∑ z : ZVec n c, ∑ w : WVec n d,
          (W p y z (vecSum w) * u p y z w +
            W p y z (vecSum w + 1) * v p y z w) := by
  classical
  unfold coeffApply wFun4Equiv
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro p _
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro z _
  calc
    (∑ sw : I n,
        W p y z sw *
          ((∑ w : WVec n d,
              if vecSum w = sw then u p y z w else 0) +
            ∑ w : WVec n d,
              if vecSum w + 1 = sw then v p y z w else 0)) =
      (∑ sw : I n, W p y z sw *
        ∑ w : WVec n d,
          if vecSum w = sw then u p y z w else 0) +
      ∑ sw : I n, W p y z sw *
        ∑ w : WVec n d,
          if vecSum w + 1 = sw then v p y z w else 0 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro sw _
        ring
    _ = (∑ w : WVec n d,
          W p y z (vecSum w) * u p y z w) +
        ∑ w : WVec n d,
          W p y z (vecSum w + 1) * v p y z w := by
      rw [sum_mul_sum_if_eq, sum_mul_sum_if_eq]
    _ = ∑ w : WVec n d,
        (W p y z (vecSum w) * u p y z w +
          W p y z (vecSum w + 1) * v p y z w) := by
      rw [← Finset.sum_add_distrib]

theorem k4Base_SW_left_pairing
    {n b c d : Nat} [NeZero n]
    (C : CFun4 n 1 b d) (W : WFun4 n 1 b c) :
    k4BaseCFunDotDual C
        (squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          ((0 : BFun4 n 1 c d), W)) =
      coeffApply
        (wFun4Equiv n 1 b c (k4BaseSWLeftCoeff C))
        (wFun4Equiv n 1 b c W) := by
  rw [k4BaseCFunDotDual_apply, coeffApply_comm]
  rw [coeffApply_squareCompat_eq_Q2]
  unfold k4BaseSWLeftCoeff
  rw [coeffApply_wFiberCoeff W
    (fun p y z w => C p y (vecSum z) w)
    (fun p y z w => C p y (vecSum z + 1) w)]
  unfold Q2 betaB gammaB deltaC etaC xiW zetaW
  simp only [Pi.zero_apply, zero_mul, zero_add]
  simp_rw [mul_comm]

theorem k4Base_SW_right_pairing
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (W : WFun4 n 1 b c) :
    k4BWSlice sigma.1.1 W =
      coeffApply
        (wFun4Equiv n 1 b c (k4BaseSWRightCoeff sigma))
        (wFun4Equiv n 1 b c W) := by
  unfold k4BaseSWRightCoeff
  rw [coeffApply_wFiberCoeff W
    (fun p y z w => sigma.1.1 p (vecSum y) z w)
    (fun p y z w => sigma.1.1 p (vecSum y + 1) z w)]
  unfold k4BWSlice betaB gammaB xiW zetaW
  rw [sum_PVec_one]
  simp_rw [mul_comm]

theorem k4Base_SW_functional_iff_indexed
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    K4SWCoeffEquation sigma C ↔ K4SWIndexedEquation sigma C := by
  rw [k4Base_SWIndexed_iff_coeff_eq]
  constructor
  · intro h
    apply Equiv.injective (wFun4Equiv n 1 b c)
    exact (coeffApply_eq_forall_iff _ _).mp (fun f => by
      let W := (wFun4Equiv n 1 b c).symm f
      have hW := h W
      rw [k4Base_SW_left_pairing, k4Base_SW_right_pairing] at hW
      simpa [W] using hW)
  · intro h W
    rw [k4Base_SW_left_pairing, k4Base_SW_right_pairing, h]

theorem k4Base_Sfunctional_iff_indexed
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d) (C : CFun4 n 1 b d) :
    (K4SBCoeffEquation sigma C ∧ K4SWCoeffEquation sigma C) ↔
      (K4SBIndexedEquation sigma C ∧ K4SWIndexedEquation sigma C) := by
  rw [k4Base_SB_functional_iff_indexed,
    k4Base_SW_functional_iff_indexed]

end

end Core4loop.CompleteGraph.EvenP.BaseKKT
