import Core4loop.BDiag
import Core4loop.RootSpaces.Basic
import Core4loop.Square.Rank.Shear

open scoped BigOperators

namespace Core4loop

abbrev BPairAmbient (n a b c d : ℕ) [NeZero n] :=
  YDiffSpace (n := n) (b := b) (c := c) (d := d) ×
    BDiagSpace (n := n) (a := a) (b := b) (d := d)

theorem finrank_BPairAmbient {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) :
    Module.finrank F (BPairAmbient n a b c d) =
      (n - 1) * n ^ (c + d) + (n - 1) * n ^ (a + d) := by
  rw [Module.finrank_prod,
    finrank_YDiffSpace (n := n) (b := b) (c := c) (d := d) hb,
    finrank_BDiagSpace (n := n) (a := a) (b := b) (d := d) ha hb]

noncomputable abbrev PairCurlSpace (n : ℕ) [NeZero n] := MatrixZeroSum n

theorem finrank_PairCurlSpace {n : ℕ} [NeZero n] :
    Module.finrank F (PairCurlSpace n) = (n - 1) ^ 2 := by
  simpa [PairCurlSpace] using finrank_MatrixZeroSum (n := n)

theorem finrank_vec_to_PairCurlSpace {n k : ℕ} [NeZero n] :
    Module.finrank F (Vec n k → PairCurlSpace n) = n ^ k * (n - 1) ^ 2 := by
  calc
    Module.finrank F (Vec n k → PairCurlSpace n)
        = ∑ _ : Vec n k, Module.finrank F (PairCurlSpace n) := by
            simp [Module.finrank_pi_fintype
              (R := F) (M := fun _ : Vec n k => PairCurlSpace n)]
    _ = Fintype.card (Vec n k) * (n - 1) ^ 2 := by
            simp [finrank_PairCurlSpace]
    _ = n ^ k * (n - 1) ^ 2 := by
            rw [card_vec]

theorem finrank_WVec_to_PairCurlSpace {n d : ℕ} [NeZero n] :
    Module.finrank F (WVec n d → PairCurlSpace n) = n ^ d * (n - 1) ^ 2 :=
  finrank_vec_to_PairCurlSpace (n := n) (k := d)

theorem finrank_YVec_to_PairCurlSpace {n b : ℕ} [NeZero n] :
    Module.finrank F (YVec n b → PairCurlSpace n) = n ^ b * (n - 1) ^ 2 :=
  finrank_vec_to_PairCurlSpace (n := n) (k := b)

noncomputable def BRootFiberSum {n b c d : ℕ} [NeZero n] (hb : 0 < b)
    (R : RootTarget n b c d) (sy sz : I n) (w : WVec n d) : F :=
  ∑ z : ZVec n c,
    if vecSum z = sz then R (vecSumRep (n := n) (k := b) hb sy) z w else 0

noncomputable def BCompatPSum {n a b d : ℕ} [NeZero n] (hb : 0 < b)
    (C : CFun4 n a b d) (sy sz : I n) (w : WVec n d) : F :=
  ∑ p : PVec n a, C p (vecSumRep (n := n) (k := b) hb sy) sz w

noncomputable def BPairRawCurl {n a b c d : ℕ} [NeZero n] (hb : 0 < b)
    (x : BPairAmbient n a b c d) (w : WVec n d) : MatrixProfile n :=
  fun sy sz =>
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb x.1.1 sy sz w
      + BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          x.1.1 (sy + 1) (sz - 1) w
      + BCompatPSum (n := n) (a := a) (b := b) (d := d) hb x.2.1 sy sz w
      + BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
          x.2.1 (sy + 1) sz w

lemma sum_if_add_F {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (f g : α → F) :
    (∑ x : α, if p x then f x + g x else 0) =
      (∑ x : α, if p x then f x else 0) + ∑ x : α, if p x then g x else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hx : p x <;> simp [hx]

lemma sum_if_mul_F {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (r : F) (f : α → F) :
    (∑ x : α, if p x then r * f x else 0) =
      r * ∑ x : α, if p x then f x else 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases hx : p x <;> simp [hx]

set_option linter.flexible false in
noncomputable def BPairRawCurlMap {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    BPairAmbient n a b c d →ₗ[F] (WVec n d → MatrixProfile n) where
  toFun x := BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb x
  map_add' x y := by
    funext w sy sz
    unfold BPairRawCurl BRootFiberSum BCompatPSum
    simp [Finset.sum_add_distrib]
    rw [sum_if_add_F, sum_if_add_F]
    abel
  map_smul' r x := by
    funext w sy sz
    unfold BPairRawCurl BRootFiberSum BCompatPSum
    simp [smul_eq_mul]
    rw [sum_if_mul_F, sum_if_mul_F, ← Finset.mul_sum, ← Finset.mul_sum]
    ring

def zmodSubLeftEquiv {n : ℕ} [NeZero n] (t : I n) : I n ≃ I n where
  toFun s := t - s
  invFun s := t - s
  left_inv s := by
    simp [sub_eq_add_neg]
  right_inv s := by
    simp [sub_eq_add_neg]

lemma lineZeroSum_sum_coord {n : ℕ} [NeZero n] (L : LineZeroSum n) (t : I n) :
    (∑ sy : I n, L.1 sy t) = 0 := by
  have hsum : sigmaMapM (n := n) (Profile n) L.1 = 0 :=
    LinearMap.mem_ker.mp L.2
  change (∑ sy : I n, L.1 sy) = 0 at hsum
  simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun hsum t

lemma BRootFiberSum_YDiff_col_zero {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) (w : WVec n d) (sz : I n) :
    (∑ sy : I n,
      BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb x.1.1 sy sz w) = 0 := by
  classical
  rcases x.1.2 with ⟨U, hU⟩
  rw [← hU]
  unfold BRootFiberSum YDiffEmbed
  change
    (∑ sy : I n, ∑ z : ZVec n c,
      if vecSum z = sz then
        (U z w).1 (vecSum (vecSumRep (n := n) (k := b) hb sy))
      else 0) = 0
  calc
    (∑ sy : I n, ∑ z : ZVec n c,
        if vecSum z = sz then (U z w).1 (vecSum (vecSumRep (n := n) (k := b) hb sy))
        else 0)
        =
      ∑ sy : I n, ∑ z : ZVec n c,
        if vecSum z = sz then (U z w).1 sy else 0
        := by
          refine Finset.sum_congr rfl ?_
          intro sy _
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [vecSum_vecSumRep (n := n) (k := b) hb sy]
    _ = ∑ z : ZVec n c, ∑ sy : I n,
            if vecSum z = sz then (U z w).1 sy else 0 := by
            rw [Finset.sum_comm]
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro z _
            by_cases hz : vecSum z = sz
            · have hterm :
                  (∑ sy : I n, if vecSum z = sz then (U z w).1 sy else 0) =
                    ∑ sy : I n, (U z w).1 sy := by
                refine Finset.sum_congr rfl ?_
                intro sy _
                rw [if_pos hz]
              rw [hterm]
              have hzero : sigmaMap (n := n) (U z w).1 = 0 :=
                LinearMap.mem_ker.mp (U z w).2
              change (∑ sy : I n, (U z w).1 sy) = 0 at hzero
              exact hzero
            · apply Finset.sum_eq_zero
              intro sy _
              rw [if_neg hz]

lemma BRootFiberSum_YDiff_col_shift_zero {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) (w : WVec n d) (sz : I n) :
    (∑ sy : I n,
      BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
        x.1.1 (sy + 1) (sz - 1) w) = 0 := by
  classical
  have hshift :
      (∑ sy : I n,
        BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          x.1.1 (sy + 1) (sz - 1) w)
        =
      ∑ sy : I n,
        BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          x.1.1 sy (sz - 1) w := by
    simpa using
      ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n))
        (fun sy : I n =>
          BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
            x.1.1 sy (sz - 1) w))
  rw [hshift]
  exact BRootFiberSum_YDiff_col_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hb x w (sz - 1)

lemma BCompatPSum_col_shift {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (C : CFun4 n a b d) (w : WVec n d) (sz : I n) :
    (∑ sy : I n, BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        C (sy + 1) sz w)
      =
    ∑ sy : I n, BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        C sy sz w := by
  simpa using
    ((Equiv.addRight (1 : I n)).sum_comp (Finset.univ : Finset (I n))
      (fun sy : I n =>
        BCompatPSum (n := n) (a := a) (b := b) (d := d) hb C sy sz w))

lemma BPairRawCurl_col_zero {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) (w : WVec n d) (sz : I n) :
    (∑ sy : I n,
      BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x w sy sz) = 0 := by
  classical
  unfold BPairRawCurl
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [BRootFiberSum_YDiff_col_zero (n := n) (a := a) (b := b) (c := c) (d := d)
    hb x w sz]
  rw [BRootFiberSum_YDiff_col_shift_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hb x w sz]
  rw [BCompatPSum_col_shift (n := n) (a := a) (b := b) (d := d) hb x.2.1 w sz]
  simpa [add_assoc] using
    F_add_self (∑ sy : I n,
      BCompatPSum (n := n) (a := a) (b := b) (d := d) hb x.2.1 sy sz w)

lemma BRootFiberSum_diag_cancel {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) (w : WVec n d) (t : I n) :
    (∑ sz : I n,
      BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb x.1.1 (t - sz) sz w)
      +
    (∑ sz : I n,
      BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
        x.1.1 (t - sz + 1) (sz - 1) w) = 0 := by
  classical
  let f : I n → F := fun sz =>
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb x.1.1 (t - sz) sz w
  have hshift :
      (∑ sz : I n,
        BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          x.1.1 (t - sz + 1) (sz - 1) w)
        = ∑ sz : I n, f sz := by
    calc
      (∑ sz : I n,
        BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
          x.1.1 (t - sz + 1) (sz - 1) w)
          = ∑ sz : I n, f (sz - 1) := by
              refine Finset.sum_congr rfl ?_
              intro sz _
              unfold f
              have hcoord : t - (sz - 1) = t - sz + 1 := by abel
              rw [hcoord]
      _ = ∑ sz : I n, f sz := by
              simpa [sub_eq_add_neg] using
                ((Equiv.addRight (-(1 : I n))).sum_comp
                  (Finset.univ : Finset (I n)) f)
  rw [hshift]
  exact F_add_self _

lemma BCompatPSum_BDiag_diag_zero {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) (w : WVec n d) (t : I n) :
    (∑ sz : I n,
      BCompatPSum (n := n) (a := a) (b := b) (d := d) hb x.2.1 (t - sz) sz w) = 0 := by
  classical
  rcases x.2.2 with ⟨V, hV⟩
  rw [← hV]
  unfold BCompatPSum BDiagEmbed
  change
    (∑ sz : I n, ∑ p : PVec n a,
      (V p w).1 (vecSum (vecSumRep (n := n) (k := b) hb (t - sz)))
        (vecSum (vecSumRep (n := n) (k := b) hb (t - sz)) + sz)) = 0
  calc
    (∑ sz : I n, ∑ p : PVec n a,
      (V p w).1 (vecSum (vecSumRep (n := n) (k := b) hb (t - sz)))
        (vecSum (vecSumRep (n := n) (k := b) hb (t - sz)) + sz))
        = ∑ sz : I n, ∑ p : PVec n a, (V p w).1 (t - sz) t := by
            refine Finset.sum_congr rfl ?_
            intro sz _
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [vecSum_vecSumRep (n := n) (k := b) hb (t - sz)]
            have hcoord : t - sz + sz = t := by abel
            rw [hcoord]
    _ = ∑ p : PVec n a, ∑ sz : I n, (V p w).1 (t - sz) t := by
            rw [Finset.sum_comm]
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro p _
            have hshift :
                (∑ sz : I n, (V p w).1 (t - sz) t) =
                  ∑ sy : I n, (V p w).1 sy t := by
              simpa using
                ((zmodSubLeftEquiv (n := n) t).sum_comp
                  (fun sy : I n => (V p w).1 sy t))
            rw [hshift]
            exact lineZeroSum_sum_coord (V p w) t

lemma BCompatPSum_BDiag_diag_shift_zero {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) (w : WVec n d) (t : I n) :
    (∑ sz : I n,
      BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        x.2.1 (t - sz + 1) sz w) = 0 := by
  classical
  rcases x.2.2 with ⟨V, hV⟩
  rw [← hV]
  unfold BCompatPSum BDiagEmbed
  change
    (∑ sz : I n, ∑ p : PVec n a,
      (V p w).1 (vecSum (vecSumRep (n := n) (k := b) hb (t - sz + 1)))
        (vecSum (vecSumRep (n := n) (k := b) hb (t - sz + 1)) + sz)) = 0
  calc
    (∑ sz : I n, ∑ p : PVec n a,
      (V p w).1 (vecSum (vecSumRep (n := n) (k := b) hb (t - sz + 1)))
        (vecSum (vecSumRep (n := n) (k := b) hb (t - sz + 1)) + sz))
        = ∑ sz : I n, ∑ p : PVec n a, (V p w).1 (t + 1 - sz) (t + 1) := by
            refine Finset.sum_congr rfl ?_
            intro sz _
            refine Finset.sum_congr rfl ?_
            intro p _
            rw [vecSum_vecSumRep (n := n) (k := b) hb (t - sz + 1)]
            have hfirst : t - sz + 1 = t + 1 - sz := by abel
            have hcoord : (t + 1 - sz) + sz = t + 1 := by abel
            rw [hfirst, hcoord]
    _ = ∑ p : PVec n a, ∑ sz : I n, (V p w).1 (t + 1 - sz) (t + 1) := by
            rw [Finset.sum_comm]
    _ = 0 := by
            apply Finset.sum_eq_zero
            intro p _
            have hshift :
                (∑ sz : I n, (V p w).1 (t + 1 - sz) (t + 1)) =
                  ∑ sy : I n, (V p w).1 sy (t + 1) := by
              simpa using
                ((zmodSubLeftEquiv (n := n) (t + 1)).sum_comp
                  (fun sy : I n => (V p w).1 sy (t + 1)))
            rw [hshift]
            exact lineZeroSum_sum_coord (V p w) (t + 1)

lemma BPairRawCurl_diag_zero {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) (w : WVec n d) (t : I n) :
    (∑ sz : I n,
      BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x w (t - sz) sz) = 0 := by
  classical
  unfold BPairRawCurl
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hroot := BRootFiberSum_diag_cancel
    (n := n) (a := a) (b := b) (c := c) (d := d) hb x w t
  rw [BCompatPSum_BDiag_diag_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hb x w t]
  rw [BCompatPSum_BDiag_diag_shift_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) hb x w t]
  simpa [add_assoc] using hroot

noncomputable def BPairCurl {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) : WVec n d → PairCurlSpace n :=
  fun w =>
    ⟨shearDiagVal (n := n)
      (BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb x w),
      shearDiagVal_mem_MatrixZeroSum
        (BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb x w)
        (BPairRawCurl_col_zero (n := n) (a := a) (b := b) (c := c) (d := d) hb x w)
        (BPairRawCurl_diag_zero (n := n) (a := a) (b := b) (c := c) (d := d) hb x w)⟩

noncomputable def BPairCurlMap {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    BPairAmbient n a b c d →ₗ[F] (WVec n d → PairCurlSpace n) where
  toFun x := BPairCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb x
  map_add' x y := by
    funext w
    apply Subtype.ext
    funext sz t
    unfold BPairCurl shearDiagVal
    have hraw :=
      congrFun (congrFun (congrFun
        ((BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb).map_add x y)
        w) (t - sz)) sz
    exact hraw
  map_smul' r x := by
    funext w
    apply Subtype.ext
    funext sz t
    unfold BPairCurl shearDiagVal
    have hraw :=
      congrFun (congrFun (congrFun
        ((BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb).map_smul r x)
        w) (t - sz)) sz
    exact hraw

lemma BPairCurl_eq_zero_iff_raw {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : BPairAmbient n a b c d) :
    BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0 ↔
      BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb x = 0 := by
  constructor
  · intro h
    funext w sy sz
    have hw := congrFun h w
    have hv := congrArg Subtype.val hw
    have hpoint := congrFun (congrFun hv sz) (sy + sz)
    change
      (BPairCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb x w).1 sz (sy + sz) =
        0 at hpoint
    unfold BPairCurl shearDiagVal at hpoint
    change
      BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d)
        hb x w (sy + sz - sz) sz = 0 at hpoint
    have hcoord : sy + sz - sz = sy := by abel
    rw [hcoord] at hpoint
    exact hpoint
  · intro h
    funext w
    apply Subtype.ext
    funext sz t
    change (BPairCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb x w).1 sz t = 0
    unfold BPairCurl shearDiagVal
    exact congrFun (congrFun (congrFun h w) (t - sz)) sz

theorem ker_BPairCurlMap_eq_ker_raw {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.ker (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) =
      LinearMap.ker (BPairRawCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    exact (BPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d) hb x).1
      (LinearMap.mem_ker.mp hx)
  · intro hx
    apply LinearMap.mem_ker.mpr
    exact (BPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d) hb x).2
      (LinearMap.mem_ker.mp hx)

end Core4loop
