import Core4loop.TriangleLeaf.AfterWResidual
import Core4loop.TriangleLeaf.CorrectedExponent
import Core4loop.TriangleCore.Closed

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

open TriangleCore

noncomputable section

/-!
Triangle-plus-leaf: corrected `d = 1` branch

This module implements the signed `d = 1` TriangleLeaf-to-TriangleCore
source/sign transport.

This file deliberately builds the compatibility guard before using any
closed-form exponent theorem.
-/

/-- Evaluation at the unique coordinate identifies `WVec n 1` with `I n`. -/
def wVecOneEquiv (n : ℕ) : WVec n 1 ≃ I n where
  toFun w := w 0
  invFun s := fun _ => s
  left_inv w := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rfl
  right_inv s := rfl

@[simp]
theorem wVecOneEquiv_apply {n : ℕ} (w : WVec n 1) :
    wVecOneEquiv n w = w 0 := rfl

@[simp]
theorem wVecOneEquiv_symm_apply {n : ℕ} (s : I n) :
    (wVecOneEquiv n).symm s = fun _ => s := rfl

theorem vecSum_wVec_one {n : ℕ} [NeZero n] (w : WVec n 1) :
    vecSum w = wVecOneEquiv n w := by
  simp [vecSum, wVecOneEquiv]

theorem sum_wVec_one_reindex {n : ℕ} [NeZero n] (f : I n → F) :
    (∑ w : WVec n 1, f (vecSum w)) = ∑ s : I n, f s := by
  simpa [vecSum_wVec_one] using
    (Equiv.sum_comp (wVecOneEquiv n) f)

theorem mem_PassiveDiffSpace_one_iff_total_zero
    {n : ℕ} [NeZero n] (f : PassiveRaw n 1) :
    f ∈ PassiveDiffSpace n 1 ↔ (∑ w : WVec n 1, f w) = 0 := by
  constructor
  · rintro ⟨U, rfl⟩
    rw [show
      (∑ w : WVec n 1,
          PassiveDiffEmbed (n := n) (d := 1) U w) =
        ∑ s : I n, U.1 s by
          simpa [PassiveDiffEmbed] using
            (sum_wVec_one_reindex (n := n) U.1)]
    exact LinearMap.mem_ker.mp U.2
  · intro h
    let Uval : I n → F := fun s => f ((wVecOneEquiv n).symm s)
    have hUzero : (∑ s : I n, Uval s) = 0 := by
      calc
        (∑ s : I n, Uval s)
            = ∑ w : WVec n 1, Uval (wVecOneEquiv n w) := by
                symm
                exact Equiv.sum_comp (wVecOneEquiv n) Uval
        _ = ∑ w : WVec n 1, f w := by
              refine Finset.sum_congr rfl ?_
              intro w _
              simp [Uval]
        _ = 0 := h
    let U : ZeroSumProfile n :=
      ⟨Uval, LinearMap.mem_ker.mpr (by
        simpa [sigmaMap] using hUzero)⟩
    refine ⟨U, ?_⟩
    funext w
    simp [PassiveDiffEmbed, U, Uval, vecSum_wVec_one]

theorem mem_WDiffSpace_one_iff_total_zero
    {n b c : ℕ} [NeZero n] (R : RootTarget n b c 1) :
    R ∈ WDiffSpace (n := n) (b := b) (c := c) (d := 1)
      ↔
      ∀ y : YVec n b, ∀ z : ZVec n c,
        (∑ w : WVec n 1, R y z w) = 0 := by
  rw [mem_WDiffSpace_iff_forall_passive]
  constructor
  · intro h y z
    exact (mem_PassiveDiffSpace_one_iff_total_zero
      (fun w : WVec n 1 => R y z w)).1 (h y z)
  · intro h y z
    exact (mem_PassiveDiffSpace_one_iff_total_zero
      (fun w : WVec n 1 => R y z w)).2 (h y z)

theorem triKBMap_leaf_encoding_sum_w
    {n a b c : ℕ} [NeZero n] (ha : 0 < a)
    (B : BFun4 n a c 1) (y : YVec n b) (z : ZVec n c) :
    TriKBMap (n := n) (r := a + 1) (s := b) (t := c)
        ((triBFunLeafEquiv
          (n := n) (a := a) (c := c) (d := 1) ha).symm B) y z
      =
      ∑ w : WVec n 1,
        KBMap (n := n) (a := a) (b := b) (c := c) (d := 1) B y z w := by
  classical
  let e := pvecPassiveEquiv n a 1 ha
  calc
    TriKBMap (n := n) (r := a + 1) (s := b) (t := c)
        ((triBFunLeafEquiv
          (n := n) (a := a) (c := c) (d := 1) ha).symm B) y z
        =
        ∑ x : PVec n a × WVec n 1,
          (B x.1 (vecSum y) z x.2 + B x.1 (vecSum y + 1) z x.2) := by
            simpa [TriKBMap, triBFunLeafEquiv, e] using
              (Equiv.sum_comp e
                (fun x : PVec n a × WVec n 1 =>
                  B x.1 (vecSum y) z x.2
                    + B x.1 (vecSum y + 1) z x.2))
    _ =
        ∑ w : WVec n 1, ∑ p : PVec n a,
          (B p (vecSum y) z w + B p (vecSum y + 1) z w) := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ =
        ∑ w : WVec n 1,
          KBMap (n := n) (a := a) (b := b) (c := c) (d := 1) B y z w := by
            rfl

theorem triKCMap_leaf_encoding_sum_w
    {n a b c : ℕ} [NeZero n] (ha : 0 < a)
    (C : CFun4 n a b 1) (y : YVec n b) (z : ZVec n c) :
    TriKCMap (n := n) (r := a + 1) (s := b) (t := c)
        ((triCFunLeafEquiv
          (n := n) (a := a) (b := b) (d := 1) ha).symm C) y z
      =
      ∑ w : WVec n 1,
        KCMap (n := n) (a := a) (b := b) (c := c) (d := 1) C y z w := by
  classical
  let e := pvecPassiveEquiv n a 1 ha
  calc
    TriKCMap (n := n) (r := a + 1) (s := b) (t := c)
        ((triCFunLeafEquiv
          (n := n) (a := a) (b := b) (d := 1) ha).symm C) y z
        =
        ∑ x : PVec n a × WVec n 1,
          (C x.1 y (vecSum z) x.2 + C x.1 y (vecSum z + 1) x.2) := by
            simpa [TriKCMap, triCFunLeafEquiv, e] using
              (Equiv.sum_comp e
                (fun x : PVec n a × WVec n 1 =>
                  C x.1 y (vecSum z) x.2
                    + C x.1 y (vecSum z + 1) x.2))
    _ =
        ∑ w : WVec n 1, ∑ p : PVec n a,
          (C p y (vecSum z) w + C p y (vecSum z + 1) w) := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ =
        ∑ w : WVec n 1,
          KCMap (n := n) (a := a) (b := b) (c := c) (d := 1) C y z w := by
            rfl

theorem K_yz_leaf_encoding_eq_sum_w
    {n a b c : ℕ} [NeZero n] (ha : 0 < a)
    (B : BFun4 n a c 1) (C : CFun4 n a b 1)
    (y : YVec n b) (z : ZVec n c) :
    K_yz (n := n) (r := a + 1) (s := b) (t := c)
        (((triBFunLeafEquiv
          (n := n) (a := a) (c := c) (d := 1) ha).symm B),
        ((triCFunLeafEquiv
          (n := n) (a := a) (b := b) (d := 1) ha).symm C)) y z
      =
      ∑ w : WVec n 1,
        (KBMap (n := n) (a := a) (b := b) (c := c) (d := 1) B
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := 1) C) y z w := by
  rw [show
      K_yz (n := n) (r := a + 1) (s := b) (t := c)
          (((triBFunLeafEquiv
            (n := n) (a := a) (c := c) (d := 1) ha).symm B),
          ((triCFunLeafEquiv
            (n := n) (a := a) (b := b) (d := 1) ha).symm C)) y z
        =
        TriKBMap (n := n) (r := a + 1) (s := b) (t := c)
            ((triBFunLeafEquiv
              (n := n) (a := a) (c := c) (d := 1) ha).symm B) y z
          +
        TriKCMap (n := n) (r := a + 1) (s := b) (t := c)
            ((triCFunLeafEquiv
              (n := n) (a := a) (b := b) (d := 1) ha).symm C) y z by rfl]
  rw [triKBMap_leaf_encoding_sum_w ha B y z,
    triKCMap_leaf_encoding_sum_w ha C y z,
    ← Finset.sum_add_distrib]
  rfl

theorem leaf_compatible_iff_K_yz_encoding_zero
    {n a b c : ℕ} [NeZero n] (ha : 0 < a)
    (B : BFun4 n a c 1) (C : CFun4 n a b 1) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := 1) B
        + KCMap (n := n) (a := a) (b := b) (c := c) (d := 1) C
      ∈ WDiffSpace (n := n) (b := b) (c := c) (d := 1)
      ↔
    K_yz (n := n) (r := a + 1) (s := b) (t := c)
      (((triBFunLeafEquiv
          (n := n) (a := a) (c := c) (d := 1) ha).symm B),
        ((triCFunLeafEquiv
          (n := n) (a := a) (b := b) (d := 1) ha).symm C)) = 0 := by
  rw [mem_WDiffSpace_one_iff_total_zero]
  constructor
  · intro h
    funext y z
    rw [K_yz_leaf_encoding_eq_sum_w ha B C y z]
    exact h y z
  · intro h y z
    have hpoint := congrFun (congrFun h y) z
    rw [K_yz_leaf_encoding_eq_sum_w ha B C y z] at hpoint
    exact hpoint

/-- Existing field equivalences, oriented from leaf fields to triangle fields. -/
noncomputable def leafPairTriangleEquiv
    {n a b c : ℕ} (ha : 0 < a) :
    (BFun4 n a c 1 × CFun4 n a b 1) ≃
      (TriBFun n (a + 1) c × TriCFun n (a + 1) b) :=
  Equiv.prodCongr
    (triBFunLeafEquiv
      (n := n) (a := a) (c := c) (d := 1) ha).symm
    (triCFunLeafEquiv
      (n := n) (a := a) (b := b) (d := 1) ha).symm

theorem leaf_pair_compatible_iff_triangle_survivor
    {n a b c : ℕ} [NeZero n] (ha : 0 < a)
    (X : BFun4 n a c 1 × CFun4 n a b 1) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := 1) X.1
        + KCMap (n := n) (a := a) (b := b) (c := c) (d := 1) X.2
      ∈ WDiffSpace (n := n) (b := b) (c := c) (d := 1)
      ↔
    K_yz (n := n) (r := a + 1) (s := b) (t := c)
      (leafPairTriangleEquiv ha X) = 0 := by
  simpa [leafPairTriangleEquiv] using
    (leaf_compatible_iff_K_yz_encoding_zero
      (n := n) (a := a) (b := b) (c := c) ha X.1 X.2)

/-- At `d = 1`, compatible leaf `B/C` assignments are exactly the
TriangleCore `A`-survivors after the existing root-coordinate encoding. -/
noncomputable def leafCompatibleBCEquivSurvivingYZ
    {n a b c : ℕ} [NeZero n] (ha : 0 < a) :
    LeafCompatibleBC n a b c 1 ≃
      SurvivingYZ n (a + 1) b c :=
  (leafPairTriangleEquiv
    (n := n) (a := a) (b := b) (c := c) ha).subtypeEquiv
      (leaf_pair_compatible_iff_triangle_survivor
        (n := n) (a := a) (b := b) (c := c) ha)

theorem leafCompatibleBCEquivSurvivingYZ_phase
    {n a b c : ℕ} [NeZero n] (ha : 0 < a)
    (X : LeafCompatibleBC n a b c 1) :
    TriQraw
        ((leafCompatibleBCEquivSurvivingYZ ha X).1.1)
        ((leafCompatibleBCEquivSurvivingYZ ha X).1.2)
      =
      Q1 X.1.1 X.1.2 := by
  simpa [leafCompatibleBCEquivSurvivingYZ, leafPairTriangleEquiv] using
    (TriQraw_leaf_encoding
      (n := n) (a := a) (b := b) (c := c) (d := 1)
      ha X.1.1 X.1.2)

/-- Logical level 6: exact signed-source transport from compatible leaf
assignments to TriangleCore survivors at `d = 1`. -/
theorem leafCompatibleResidualSum_eq_triangle_survivor_sum
    {n a b c : ℕ} [NeZero n] (ha : 0 < a) :
    leafCompatibleResidualSum n a b c 1
      =
      ∑ X : SurvivingYZ n (a + 1) b c,
        bitSign (TriQraw X.1.1 X.1.2) := by
  classical
  let e :=
    leafCompatibleBCEquivSurvivingYZ
      (n := n) (a := a) (b := b) (c := c) ha
  calc
    leafCompatibleResidualSum n a b c 1
        = ∑ X : LeafCompatibleBC n a b c 1,
            bitSign (Q1 X.1.1 X.1.2) :=
          leafCompatibleResidualSum_eq_subtypeSignSum
    _ = ∑ X : LeafCompatibleBC n a b c 1,
          bitSign (TriQraw (e X).1.1 (e X).1.2) := by
            refine Finset.sum_congr rfl ?_
            intro X _
            rw [leafCompatibleBCEquivSurvivingYZ_phase ha X]
    _ = ∑ X : SurvivingYZ n (a + 1) b c,
          bitSign (TriQraw X.1.1 X.1.2) := by
            exact Equiv.sum_comp e
              (fun X : SurvivingYZ n (a + 1) b c =>
                bitSign (TriQraw X.1.1 X.1.2))

/-- Logical level 6: the compatible residual, with its exact TriangleCore
`A`-elimination factor. -/
theorem pow_tail_mul_leafCompatibleResidualSum_eq_DeltaTriangleCore
    {n a b c : ℕ} [NeZero n] (ha : 0 < a) :
    (2 : ℤ) ^ (n ^ (b + c)) *
        leafCompatibleResidualSum n a b c 1
      =
      DeltaTriangleCore (a + 1) b c n := by
  rw [leafCompatibleResidualSum_eq_triangle_survivor_sum ha]
  exact
    (DeltaTriangleCore_survivors
      (n := n) (r := a + 1) (s := b) (t := c)).symm

/-- Logical level 7: whole raw TriangleLeaf `DeltaNF` at `d = 1`, reduced
to the closed TriangleCore source. -/
theorem DeltaNF_triangleLeaf_d_eq_one_eq_triangleCore
    {n a b c : ℕ} [NeZero n] (ha : 0 < a) :
    DeltaNF .triangleLeaf a b c 1 n
      =
      (2 : ℤ) ^ (n ^ (a + b + c)) *
        DeltaTriangleCore (a + 1) b c n := by
  let k : ℕ :=
    Module.finrank F
      (LinearMap.ker
        (KWMap (n := n) (a := a) (b := b) (c := c) (d := 1)))
  have hrank :
      k + (n - 1) * n ^ (b + c) = n ^ (a + b + c) := by
    exact
      finrank_ker_KWMap_add
        (n := n) (a := a) (b := b) (c := c) (d := 1) ha (by omega)
  have hn : 1 ≤ n := one_le_of_neZero (n := n)
  have hexp :
      n ^ (b + c + 1) + k =
        n ^ (a + b + c) + n ^ (b + c) := by
    calc
      n ^ (b + c + 1) + k
          = n ^ (b + c) * n + k := by rw [pow_succ]
      _ = n ^ (b + c) * ((n - 1) + 1) + k := by
            rw [Nat.sub_add_cancel hn]
      _ = k + (n - 1) * n ^ (b + c) + n ^ (b + c) := by ring
      _ = n ^ (a + b + c) + n ^ (b + c) := by rw [hrank]
  calc
    DeltaNF .triangleLeaf a b c 1 n
        =
        (2 : ℤ) ^ (n ^ (b + c + 1)) *
          ((2 : ℤ) ^ k *
            leafCompatibleResidualSum n a b c 1) := by
              simpa [k] using
                (DeltaNF_triangleLeaf_after_WDiff
                  (n := n) (a := a) (b := b) (c := c) (d := 1))
    _ =
        (2 : ℤ) ^ (n ^ (b + c + 1) + k) *
          leafCompatibleResidualSum n a b c 1 := by
            rw [pow_add]
            ring
    _ =
        (2 : ℤ) ^ (n ^ (a + b + c) + n ^ (b + c)) *
          leafCompatibleResidualSum n a b c 1 := by rw [hexp]
    _ =
        (2 : ℤ) ^ (n ^ (a + b + c)) *
          ((2 : ℤ) ^ (n ^ (b + c)) *
            leafCompatibleResidualSum n a b c 1) := by
              rw [pow_add]
              ring
    _ =
        (2 : ℤ) ^ (n ^ (a + b + c)) *
          DeltaTriangleCore (a + 1) b c n := by
            rw [pow_tail_mul_leafCompatibleResidualSum_eq_DeltaTriangleCore ha]

private theorem XtriangleZ_nonneg_positive
    {n r s t : ℕ} [NeZero n]
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    0 ≤ XtriangleZ r s t n := by
  by_cases h : specialBranch r s t n
  · rw [← evenSpecialDeltaExponent_cast_eq_XtriangleZ_of_special
      (n := n) (r := r) (s := s) (t := t) hr hs ht h]
    exact Int.natCast_nonneg _
  · rw [← genericDeltaExponent_cast_eq_XtriangleZ_of_not_special
      (n := n) (r := r) (s := s) (t := t) hr hs ht h]
    exact Int.natCast_nonneg _

/-- Logical level 7: corrected raw `DeltaNF = 2^X` theorem for `d = 1`
and arbitrary positive `a`, `b`, and `c`. -/
theorem DeltaNF_triangleLeaf_eq_pow_X1CorrectedZ_d_eq_one
    {n a b c : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    DeltaNF .triangleLeaf a b c 1 n
      =
      (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c 1 n) := by
  have hnotExceptional : ¬ TriangleLeafExceptional n a b c 1 := by
    intro h
    exact (by omega : ¬(2 ≤ (1 : ℕ))) h.2.2.2.2
  have hcorrected :
      X1CorrectedZ a b c 1 n = X1Z a b c 1 n := by
    unfold X1CorrectedZ
    rw [X1PaperOldZ_eq_current_X1Z]
    rw [correctionZ_nonexceptional hnotExceptional, sub_zero]
  have htriNonneg :
      0 ≤ XtriangleZ (a + 1) b c n :=
    XtriangleZ_nonneg_positive
      (n := n) (r := a + 1) (s := b) (t := c) (by omega) hb hc
  have htoNat :
      Int.toNat (X1CorrectedZ a b c 1 n)
        =
      n ^ (a + b + c) + Int.toNat (XtriangleZ (a + 1) b c n) := by
    rw [hcorrected, X1_d_eq_one_triangle_degenerate]
    rw [Int_toNat_add_of_nonneg
      (show 0 ≤ nPowZ n (a + b + c) by
        unfold nPowZ
        positivity)
      htriNonneg]
    unfold nPowZ
    have hcast :
        (n : ℤ) ^ (a + b + c) = ((n ^ (a + b + c) : ℕ) : ℤ) := by
      norm_cast
    rw [hcast, Int.toNat_natCast]
  calc
    DeltaNF .triangleLeaf a b c 1 n
        =
        (2 : ℤ) ^ (n ^ (a + b + c)) *
          DeltaTriangleCore (a + 1) b c n :=
            DeltaNF_triangleLeaf_d_eq_one_eq_triangleCore ha
    _ =
        (2 : ℤ) ^ (n ^ (a + b + c)) *
          (2 : ℤ) ^ Int.toNat (XtriangleZ (a + 1) b c n) := by
            rw [DeltaTriangleCore_closed (by omega) hb hc]
    _ =
        (2 : ℤ) ^
          (n ^ (a + b + c) + Int.toNat (XtriangleZ (a + 1) b c n)) := by
            rw [← pow_add]
    _ =
        (2 : ℤ) ^ Int.toNat (X1CorrectedZ a b c 1 n) := by
            rw [htoNat]

end

end TriangleLeaf
end Core4loop
