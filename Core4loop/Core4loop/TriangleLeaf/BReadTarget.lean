import Core4loop.TriangleLeaf.CompatibleResidualBReadFiber

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-- Index for the `Cd` part of the B-read target. -/
abbrev LeafBReadCdTargetIndex (n a b : ℕ) [NeZero n] :=
  LeafCdFamilyIndex n b × (PVec n a × NonzeroI n)

/-- Index for the `Cv` part of the B-read target. -/
abbrev LeafBReadCvTargetIndex (n a b d : ℕ) [NeZero n] (hd : 0 < d) :=
  LeafCvFamilyIndex n b d hd
    × {p : PVec n a // p ≠ (zeroVec : PVec n a)}

/-- The finite dual target used to Fourier-expand the two B-read constraints. -/
abbrev LeafBReadTarget
    (n a b c d : ℕ) [NeZero n] (hd : 0 < d) :=
  ((LeafBReadCdTargetIndex n a b → F)
    ×
   (LeafBReadCvTargetIndex n a b d hd → F))

noncomputable instance instFintypeLeafBReadCdTargetIndex
    {n a b : ℕ} [NeZero n] :
    Fintype (LeafBReadCdTargetIndex n a b) := by
  classical
  unfold LeafBReadCdTargetIndex
  infer_instance

noncomputable instance instFintypeLeafBReadCvTargetIndex
    {n a b d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafBReadCvTargetIndex n a b d hd) := by
  classical
  unfold LeafBReadCvTargetIndex
  infer_instance

noncomputable instance instFintypeLeafBReadTarget
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Fintype (LeafBReadTarget n a b c d hd) := by
  classical
  letI : Fintype (LeafBReadCdTargetIndex n a b → F) := Fintype.ofFinite _
  letI : Fintype (LeafBReadCvTargetIndex n a b d hd → F) := Fintype.ofFinite _
  exact Fintype.ofFinite _

/-- Dot pairing between two B-read targets.  The left argument is the coefficient
family and the right argument is the evaluated target family. -/
def leafBReadTargetDot
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U V : LeafBReadTarget n a b c d hd) : F :=
  coeffApply U.1 V.1 + coeffApply U.2 V.2

private theorem coeffApply_add_left
    {ι : Type*} [Fintype ι] (c d f : ι → F) :
    coeffApply (c + d) f = coeffApply c f + coeffApply d f := by
  classical
  unfold coeffApply
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.add_apply, mul_add]

private theorem coeffApply_add_right
    {ι : Type*} [Fintype ι] (c f g : ι → F) :
    coeffApply c (f + g) = coeffApply c f + coeffApply c g := by
  classical
  unfold coeffApply
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.add_apply, add_mul]

private theorem coeffApply_smul_left
    {ι : Type*} [Fintype ι] (r : F) (c f : ι → F) :
    coeffApply (r • c) f = r * coeffApply c f := by
  classical
  unfold coeffApply
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [Pi.smul_apply]
  ring

private theorem coeffApply_zero_right
    {ι : Type*} [Fintype ι] (c : ι → F) :
    coeffApply c 0 = 0 := by
  classical
  simp [coeffApply]

theorem leafBReadTargetDot_add_left
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U V W : LeafBReadTarget n a b c d hd) :
    leafBReadTargetDot hd (U + V) W =
      leafBReadTargetDot hd U W + leafBReadTargetDot hd V W := by
  classical
  change
    coeffApply (U.1 + V.1) W.1 + coeffApply (U.2 + V.2) W.2 =
      (coeffApply U.1 W.1 + coeffApply U.2 W.2)
        + (coeffApply V.1 W.1 + coeffApply V.2 W.2)
  rw [coeffApply_add_left, coeffApply_add_left]
  ring

theorem leafBReadTargetDot_add_right
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U V W : LeafBReadTarget n a b c d hd) :
    leafBReadTargetDot hd U (V + W) =
      leafBReadTargetDot hd U V + leafBReadTargetDot hd U W := by
  classical
  change
    coeffApply U.1 (V.1 + W.1) + coeffApply U.2 (V.2 + W.2) =
      (coeffApply U.1 V.1 + coeffApply U.2 V.2)
        + (coeffApply U.1 W.1 + coeffApply U.2 W.2)
  rw [coeffApply_add_right, coeffApply_add_right]
  ring

theorem leafBReadTargetDot_smul_left
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (r : F) (U V : LeafBReadTarget n a b c d hd) :
    leafBReadTargetDot hd (r • U) V = r * leafBReadTargetDot hd U V := by
  classical
  change
    coeffApply (r • U.1) V.1 + coeffApply (r • U.2) V.2 =
      r * (coeffApply U.1 V.1 + coeffApply U.2 V.2)
  rw [coeffApply_smul_left, coeffApply_smul_left]
  ring

theorem leafBReadTargetDot_zero_right
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd) :
    leafBReadTargetDot hd U 0 = 0 := by
  classical
  change
    coeffApply U.1 (0 : LeafBReadCdTargetIndex n a b → F)
      + coeffApply U.2 (0 : LeafBReadCvTargetIndex n a b d hd → F) = 0
  rw [coeffApply_zero_right, coeffApply_zero_right]
  ring

private theorem coeffApply_forall_left_eq_zero_iff
    {ι : Type*} [Fintype ι] (f : ι → F) :
    (∀ c : ι → F, coeffApply c f = 0) ↔ f = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := h (fun j => if j = i then (1 : F) else 0)
    unfold coeffApply at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hj
      simp [hj]
    · simp
  · intro hf c
    simp [coeffApply, hf]

private theorem coeffApply_zero_left
    {ι : Type*} [Fintype ι] (f : ι → F) :
    coeffApply (0 : ι → F) f = 0 := by
  classical
  simp [coeffApply]

theorem leafBReadTargetDot_eq_zero_forall_left_iff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBReadTarget n a b c d hd) :
    (∀ U : LeafBReadTarget n a b c d hd, leafBReadTargetDot hd U V = 0) ↔
      V = 0 := by
  classical
  constructor
  · intro h
    have h1forall :
        ∀ U1 : LeafBReadCdTargetIndex n a b → F,
          coeffApply U1 V.1 = 0 := by
      intro U1
      have hU := h (U1, 0)
      have hzero := coeffApply_zero_left V.2
      simpa [leafBReadTargetDot, hzero] using hU
    have h2forall :
        ∀ U2 : LeafBReadCvTargetIndex n a b d hd → F,
          coeffApply U2 V.2 = 0 := by
      intro U2
      have hU := h (0, U2)
      have hzero := coeffApply_zero_left V.1
      simpa [leafBReadTargetDot, hzero] using hU
    have h1 : V.1 = 0 :=
      (coeffApply_forall_left_eq_zero_iff V.1).1 h1forall
    have h2 : V.2 = 0 :=
      (coeffApply_forall_left_eq_zero_iff V.2).1 h2forall
    exact Prod.ext h1 h2
  · intro hV U
    subst hV
    exact leafBReadTargetDot_zero_right hd U

/-- The left-linear dot map associated to a fixed target vector. -/
def leafBReadTargetDotLeftLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBReadTarget n a b c d hd) :
    LeafBReadTarget n a b c d hd →ₗ[F] F where
  toFun U := leafBReadTargetDot hd U V
  map_add' U W := leafBReadTargetDot_add_left hd U W V
  map_smul' r U := by
    exact leafBReadTargetDot_smul_left hd r U V

theorem leafBReadTargetDotLeftLinearMap_eq_zero_iff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBReadTarget n a b c d hd) :
    leafBReadTargetDotLeftLinearMap hd V = 0 ↔ V = 0 := by
  classical
  constructor
  · intro hL
    exact (leafBReadTargetDot_eq_zero_forall_left_iff hd V).1
      (by
        intro U
        exact LinearMap.congr_fun hL U)
  · intro hV
    subst hV
    apply LinearMap.ext
    intro U
    exact leafBReadTargetDot_zero_right hd U

theorem sum_leafBReadTargetDot_eq_card_if_zero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBReadTarget n a b c d hd) :
    (∑ U : LeafBReadTarget n a b c d hd,
        bitSign (leafBReadTargetDot hd U V)) =
      if V = 0 then (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) else 0 := by
  classical
  let L := leafBReadTargetDotLeftLinearMap hd V
  have hsum :
      (∑ U : LeafBReadTarget n a b c d hd,
          bitSign (leafBReadTargetDot hd U V)) =
        ∑ U : LeafBReadTarget n a b c d hd, bitSign (L U) := by
    rfl
  rw [hsum, sum_bitSign_linearMap L]
  by_cases hV : V = 0
  · rw [if_pos hV, if_pos]
    exact (leafBReadTargetDotLeftLinearMap_eq_zero_iff hd V).2 hV
  · rw [if_neg hV, if_neg]
    exact fun hL => hV ((leafBReadTargetDotLeftLinearMap_eq_zero_iff hd V).1 hL)

theorem sum_leafBReadTargetDot_add_eq_card_if_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBReadTarget n a b c d hd) :
    (∑ U : LeafBReadTarget n a b c d hd,
        bitSign (leafBReadTargetDot hd U (X + Y))) =
      if X = Y then (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) else 0 := by
  classical
  rw [sum_leafBReadTargetDot_eq_card_if_zero hd (X + Y)]
  by_cases hXY : X = Y
  · have hzero : X + Y = 0 :=
      (add_eq_zero_iff_eq_of_F_module X Y).2 hXY
    rw [if_pos hXY, if_pos hzero]
  · rw [if_neg hXY, if_neg]
    intro hzero
    exact hXY ((add_eq_zero_iff_eq_of_F_module X Y).1 hzero)

theorem sum_leafBReadTargetDot_eq_card_if_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X Y : LeafBReadTarget n a b c d hd) :
    (∑ U : LeafBReadTarget n a b c d hd,
        bitSign (leafBReadTargetDot hd U (X + Y))) =
      if X = Y then (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) else 0 :=
  sum_leafBReadTargetDot_add_eq_card_if_eq hd X Y

theorem leafBReadTarget_card_eq_two_pow_finrank
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) =
      (2 : ℤ) ^ Module.finrank F (LeafBReadTarget n a b c d hd) := by
  classical
  rw [← Nat.card_eq_fintype_card]
  rw [Module.natCard_eq_pow_finrank (K := F)]
  have hF : Nat.card F = 2 := by
    rw [Nat.card_eq_fintype_card]
    simp [F, ZMod.card]
  rw [hF]
  exact
    Int.natCast_pow (2 : ℕ)
      (Module.finrank F (LeafBReadTarget n a b c d hd))

theorem intCast_card_LeafBReadTarget_eq_pow
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    (Fintype.card (LeafBReadTarget n a b c d hd) : ℤ) =
      (2 : ℤ) ^ Module.finrank F (LeafBReadTarget n a b c d hd) :=
  leafBReadTarget_card_eq_two_pow_finrank hd

end

end TriangleLeaf
end Core4loop
