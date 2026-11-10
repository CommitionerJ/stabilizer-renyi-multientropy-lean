import Core4loop.TriangleLeaf.Exponent
import Core4loop.Gauss.DeltaAfterA
import Core4loop.RootSpaces.KRange
import Core4loop.NormalFormDims

open scoped BigOperators

namespace Core4loop

private lemma sum_if_mul_eq_mul_subtype_tleaf {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (c : ℤ) (f : α → ℤ) :
    (∑ x : α, if p x then c * f x else 0) =
      c * ∑ x : {x // p x}, f x.1 := by
  classical
  calc
    (∑ x : α, if p x then c * f x else 0)
        = ∑ x ∈ (Finset.univ : Finset α) with p x, c * f x := by
            rw [Finset.sum_filter]
    _ = ∑ x : {x // p x}, c * f x.1 := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset α)) (p := p)
                (f := fun x => c * f x)).symm
    _ = c * ∑ x : {x // p x}, f x.1 := by
            rw [Finset.mul_sum]

private lemma sum_if_const_eq_mul_card_subtype {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (c : ℤ) :
    (∑ x : α, if p x then c else 0) =
      c * (Nat.card {x // p x} : ℤ) := by
  calc
    (∑ x : α, if p x then c else 0)
        = ∑ x : α, if p x then c * (1 : ℤ) else 0 := by
            simp
    _ = c * ∑ x : {x // p x}, (1 : ℤ) := by
            exact sum_if_mul_eq_mul_subtype_tleaf p c (fun _ => (1 : ℤ))
    _ = c * (Nat.card {x // p x} : ℤ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rw [Nat.card_eq_fintype_card]
            simp

private lemma F_eq_add_of_add_add_eq_zero {x y z : F}
    (h : x + y + z = 0) :
    z = x + y := by
  calc
    z = z + 0 := by simp
    _ = z + (x + y + z) := by rw [h]
    _ = (x + y) + (z + z) := by ring
    _ = x + y := by rw [F_add_self, add_zero]

private lemma F_add_add_eq_zero_of_eq_add {x y z : F}
    (h : z = x + y) :
    x + y + z = 0 := by
  calc
    x + y + z = x + y + (x + y) := by rw [h]
    _ = (x + x) + (y + y) := by ring
    _ = 0 := by rw [F_add_self, F_add_self]; simp

theorem K_yzw_eq_KBMap_add_KCMap_add_KWMap {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W)
      =
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W := by
  funext y z w
  change
    (∑ p : PVec n a, (dyB B p y z w + dzC C p y z w + dwW W p y z w))
      =
      (∑ p : PVec n a, dyB B p y z w)
        + (∑ p : PVec n a, dzC C p y z w)
        + (∑ p : PVec n a, dwW W p y z w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem K_yzw_eq_zero_iff_KWMap_eq_target {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
      ↔
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
        =
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C := by
  constructor
  · intro h
    have h0 :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
          + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
            = 0 := by
      simpa [K_yzw_eq_KBMap_add_KCMap_add_KWMap
        (n := n) (a := a) (b := b) (c := c) (d := d) B C W] using h
    funext y z w
    have hpoint := congrFun (congrFun (congrFun h0 y) z) w
    simp only [Pi.add_apply, Pi.zero_apply] at hpoint
    exact F_eq_add_of_add_add_eq_zero hpoint
  · intro h
    rw [K_yzw_eq_KBMap_add_KCMap_add_KWMap
      (n := n) (a := a) (b := b) (c := c) (d := d) B C W]
    funext y z w
    have hpoint := congrFun (congrFun (congrFun h y) z) w
    simp only [Pi.add_apply] at hpoint ⊢
    exact F_add_add_eq_zero_of_eq_add hpoint

noncomputable def linearMapFiberEquivKer {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) {target : W} (htarget : target ∈ LinearMap.range L) :
    {x : V // L x = target} ≃ LinearMap.ker L where
  toFun x :=
    ⟨x.1 - Classical.choose htarget, by
      rw [LinearMap.mem_ker]
      rw [map_sub, x.2, Classical.choose_spec htarget]
      simp⟩
  invFun x :=
    ⟨x.1 + Classical.choose htarget, by
      rw [map_add, LinearMap.mem_ker.mp x.2, Classical.choose_spec htarget]
      simp⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

theorem finrank_range_KWMap {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      =
      (n - 1) * n ^ (b + c) := by
  rw [range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact finrank_WDiffSpace (n := n) (b := b) (c := c) (d := d) hd

theorem finrank_ker_KWMap_add {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      + (n - 1) * n ^ (b + c)
      =
      n ^ (a + b + c) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [finrank_range_KWMap (n := n) (a := a) (b := b) (c := c) (d := d) hd,
    finrank_WFun4 (n := n) (a := a) (b := b) (c := c) ha] at h
  omega

theorem intCast_finrank_ker_KWMap_eq {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    (Module.finrank F
        (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ)
      =
      nPowZ n (a + b + c) - mZ n * nPowZ n (b + c) := by
  have h :=
    finrank_ker_KWMap_add (n := n) (a := a) (b := b) (c := c) (d := d) ha hd
  have hZ :
      (Module.finrank F
          (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) : ℤ)
        + ((n - 1) * n ^ (b + c) : ℕ)
        =
        (n ^ (a + b + c) : ℕ) := by
    exact_mod_cast h
  simp only [Nat.cast_mul, Nat.cast_pow] at hZ
  have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    have hn : 1 ≤ n := one_le_of_neZero
    omega
  unfold nPowZ mZ
  rw [hpred] at hZ
  ring_nf at hZ ⊢
  linarith

set_option synthInstance.maxHeartbeats 200000 in
-- The kernel is a finite function-space submodule; instance search is deep here.
theorem natCard_ker_KWMap {n a b c d : ℕ} [NeZero n] :
    Nat.card
        (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
      =
      2 ^ Module.finrank F
        (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

theorem triangleLeaf_sum_over_W_by_range {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (q : ℤ) :
    (∑ W : WFun4 n a b c,
      if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
      then q
      else 0)
      =
      if
        ∃ W : WFun4 n a b c,
          KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
            KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
              + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
      then
        (2 : ℤ) ^ Module.finrank F
          (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
          * q
      else 0 := by
  classical
  let target : RootTarget n b c d :=
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
      + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
  let L : WFun4 n a b c →ₗ[F] RootTarget n b c d :=
    KWMap (n := n) (a := a) (b := b) (c := c) (d := d)
  have hsum_eq :
      (∑ W : WFun4 n a b c,
        if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
        then q
        else 0)
        =
        ∑ W : WFun4 n a b c, if L W = target then q else 0 := by
    refine Finset.sum_congr rfl ?_
    intro W _
    by_cases hK :
        K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
    · have hL : L W = target :=
        (K_yzw_eq_zero_iff_KWMap_eq_target
          (n := n) (a := a) (b := b) (c := c) (d := d) B C W).1 hK
      simp [hK, hL]
    · have hL : ¬ L W = target := by
        intro hLW
        exact hK ((K_yzw_eq_zero_iff_KWMap_eq_target
          (n := n) (a := a) (b := b) (c := c) (d := d) B C W).2 hLW)
      simp [hK, hL]
  rw [hsum_eq]
  by_cases htarget : ∃ W : WFun4 n a b c, L W = target
  · rw [if_pos htarget]
    have htargetRange : target ∈ LinearMap.range L := htarget
    calc
      (∑ W : WFun4 n a b c, if L W = target then q else 0)
          = q * (Nat.card {W : WFun4 n a b c // L W = target} : ℤ) := by
              exact sum_if_const_eq_mul_card_subtype (fun W => L W = target) q
      _ = q * (Nat.card (LinearMap.ker L) : ℤ) := by
              rw [Nat.card_congr (linearMapFiberEquivKer L htargetRange)]
      _ = q * (2 ^ Module.finrank F (LinearMap.ker L) : ℕ) := by
              rw [natCard_ker_KWMap (n := n) (a := a) (b := b) (c := c) (d := d)]
      _ = (2 : ℤ) ^ Module.finrank F (LinearMap.ker L) * q := by
              norm_num
              ring
  · rw [if_neg htarget]
    refine Finset.sum_eq_zero ?_
    intro W _
    have hne : ¬ L W = target := by
      intro hW
      exact htarget ⟨W, hW⟩
    simp [hne]

theorem triangleLeaf_W_compatible_iff_mem_WDiffSpace {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) :
    (∃ W : WFun4 n a b c,
      KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
          + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C)
      ↔
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
          ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  constructor
  · intro h
    rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact h
  · intro h
    rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)] at h
    exact h

theorem DeltaNF_triangleLeaf_after_W {n a b c d : ℕ} [NeZero n] :
    DeltaNF .triangleLeaf a b c d n =
      (2 : ℤ) ^ (n ^ (b + c + d)) *
        ∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
          if
            ∃ W : WFun4 n a b c,
              KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
                KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                  + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
          then
            (2 : ℤ) ^ Module.finrank F
              (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
              * bitSign (Q1 B C)
          else 0 := by
  classical
  rw [DeltaNF_triangleLeaf_afterA]
  let scale : ℤ := (2 : ℤ) ^ (n ^ (b + c + d))
  let kerScale : ℤ :=
    (2 : ℤ) ^ Module.finrank F
      (LinearMap.ker (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
  calc
    (∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d, ∑ W : WFun4 n a b c,
      if K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) (B, C, W) = 0
      then scale * bitSign (Q1 B C)
      else 0)
        =
        ∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
          if
            ∃ W : WFun4 n a b c,
              KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
                KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                  + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
          then kerScale * (scale * bitSign (Q1 B C))
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro B _
            refine Finset.sum_congr rfl ?_
            intro C _
            simpa [kerScale] using
              triangleLeaf_sum_over_W_by_range
                (n := n) (a := a) (b := b) (c := c) (d := d)
                B C (scale * bitSign (Q1 B C))
    _ =
        scale *
          ∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
            if
              ∃ W : WFun4 n a b c,
                KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
                  KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                    + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
            then kerScale * bitSign (Q1 B C)
            else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro B _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro C _
            by_cases h :
                ∃ W : WFun4 n a b c,
                  KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
                    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                      + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
            · simp [h, mul_assoc, mul_comm, mul_left_comm]
            · simp [h]
    _ =
        (2 : ℤ) ^ (n ^ (b + c + d)) *
          ∑ B : BFun4 n a c d, ∑ C : CFun4 n a b d,
            if
              ∃ W : WFun4 n a b c,
                KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
                  KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                    + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
            then
              (2 : ℤ) ^ Module.finrank F
                (LinearMap.ker
                  (KWMap (n := n) (a := a) (b := b) (c := c) (d := d)))
                * bitSign (Q1 B C)
            else 0 := by
            rfl

end Core4loop
