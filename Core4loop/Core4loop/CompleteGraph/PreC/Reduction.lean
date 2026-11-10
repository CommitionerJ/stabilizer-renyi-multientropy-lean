import Core4loop.LinearSignSum
import Core4loop.Square.Linear

open scoped BigOperators

namespace Core4loop

attribute [local instance] Fintype.ofFinite

noncomputable def k4BWPhaseClean {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c) : F :=
  ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    (betaB B p y z w * xiW W p y z w
      + gammaB B p y z w * zetaW W p y z w)

private theorem k4_Q4_eq_Q3_add_BW_clean {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) :
    Q4 B C W = Q3 B C W + k4BWPhaseClean B W := by
  classical
  unfold Q4 Q3 Q2 k4BWPhaseClean
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro w _
  ring

noncomputable def k4CPhaseCoeffClean {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d) (W : WFun4 n a b c) :
    CFun4 n a b d →ₗ[F] F where
  toFun C :=
    coeffApplyA
        (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) A
      + coeffApply
          (cFun4Equiv n a b d
            (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
          (cFun4Equiv n a b d C)
  map_add' C C' := by
    classical
    have hKC :
        aFun4Equiv n b c d
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) (C + C')) =
          aFun4Equiv n b c d
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) +
            aFun4Equiv n b c d
              (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C') := by
      rw [(KCMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_add]
      funext i
      rcases i with ⟨y, z, w⟩
      rfl
    have hC :
        cFun4Equiv n a b d (C + C') =
          cFun4Equiv n a b d C + cFun4Equiv n a b d C' := by
      funext i
      rcases i with ⟨p, y, sz, w⟩
      rfl
    have hleft {i : Type} [Fintype i] (u v f : i → F) :
        coeffApply (u + v) f = coeffApply u f + coeffApply v f := by
      unfold coeffApply
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Pi.add_apply]
      ring
    have hright {i : Type} [Fintype i] (u f g : i → F) :
        coeffApply u (f + g) = coeffApply u f + coeffApply u g := by
      unfold coeffApply
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Pi.add_apply]
      ring
    unfold coeffApplyA
    change
      coeffApply
          (aFun4Equiv n b c d
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) (C + C')))
          (aFun4Equiv n b c d A)
        + coeffApply
            (cFun4Equiv n a b d
              (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
            (cFun4Equiv n a b d (C + C')) = _
    rw [hKC, hC]
    calc
      _ =
          (coeffApply
              (aFun4Equiv n b c d
                (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
              (aFun4Equiv n b c d A) +
            coeffApply
              (aFun4Equiv n b c d
                (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C'))
              (aFun4Equiv n b c d A)) +
          (coeffApply
              (cFun4Equiv n a b d
                (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
              (cFun4Equiv n a b d C) +
            coeffApply
              (cFun4Equiv n a b d
                (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
              (cFun4Equiv n a b d C')) := by
            congr 1
            · exact hleft _ _ _
            · exact hright _ _ _
      _ = _ := by ring
  map_smul' r C := by
    classical
    have hKC :
        aFun4Equiv n b c d
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) (r • C)) =
          r • aFun4Equiv n b c d
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) := by
      rw [(KCMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul]
      funext i
      rcases i with ⟨y, z, w⟩
      rfl
    have hC : cFun4Equiv n a b d (r • C) = r • cFun4Equiv n a b d C := by
      funext i
      rcases i with ⟨p, y, sz, w⟩
      rfl
    have hleft {i : Type} [Fintype i] (u f : i → F) (s : F) :
        coeffApply (s • u) f = s * coeffApply u f := by
      unfold coeffApply
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    have hright {i : Type} [Fintype i] (u f : i → F) (s : F) :
        coeffApply u (s • f) = s * coeffApply u f := by
      unfold coeffApply
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    unfold coeffApplyA
    change
      coeffApply
          (aFun4Equiv n b c d
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) (r • C)))
          (aFun4Equiv n b c d A)
        + coeffApply
            (cFun4Equiv n a b d
              (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
            (cFun4Equiv n a b d (r • C)) = _
    rw [hKC, hC]
    calc
      _ = r * coeffApply
              (aFun4Equiv n b c d
                (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
              (aFun4Equiv n b c d A) +
          r * coeffApply
              (cFun4Equiv n a b d
                (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
              (cFun4Equiv n a b d C) := by
            congr 1
            · exact hleft _ _ r
            · exact hright _ _ r
      _ = _ := by
        change
          r * coeffApply
                (aFun4Equiv n b c d
                  (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
                (aFun4Equiv n b c d A) +
              r * coeffApply
                (cFun4Equiv n a b d
                  (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
                (cFun4Equiv n a b d C) =
            r *
              (coeffApply
                  (aFun4Equiv n b c d
                    (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
                  (aFun4Equiv n b c d A) +
                coeffApply
                  (cFun4Equiv n a b d
                    (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
                  (cFun4Equiv n a b d C))
        ring

noncomputable def k4PreCMap {n a b c d : ℕ} [NeZero n] :
    (AFun4 n b c d × BFun4 n a c d × WFun4 n a b c) →ₗ[F]
      (CFun4 n a b d →ₗ[F] F) where
  toFun x := k4CPhaseCoeffClean x.1 x.2.1 x.2.2
  map_add' x x' := by
    classical
    apply LinearMap.ext
    intro C
    have hA :
        aFun4Equiv n b c d (x.1 + x'.1) =
          aFun4Equiv n b c d x.1 + aFun4Equiv n b c d x'.1 := by
      funext i
      rcases i with ⟨y, z, w⟩
      rfl
    have hBW :
        cFun4Equiv n a b d
            (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
              (x.2.1 + x'.2.1, x.2.2 + x'.2.2)) =
          cFun4Equiv n a b d
              (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2) +
            cFun4Equiv n a b d
              (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x'.2) := by
      have hs :
          squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
              (x.2.1 + x'.2.1, x.2.2 + x'.2.2) =
            squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2 +
              squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x'.2 := by
        simpa only [Prod.fst_add, Prod.snd_add] using
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.2 x'.2
      rw [hs]
      funext i
      rcases i with ⟨p, y, sz, w⟩
      rfl
    have hleft {i : Type} [Fintype i] (u v f : i → F) :
        coeffApply (u + v) f = coeffApply u f + coeffApply v f := by
      unfold coeffApply
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Pi.add_apply]
      ring
    have hright {i : Type} [Fintype i] (u f g : i → F) :
        coeffApply u (f + g) = coeffApply u f + coeffApply u g := by
      unfold coeffApply
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      simp only [Pi.add_apply]
      ring
    unfold k4CPhaseCoeffClean coeffApplyA
    change
      coeffApply
          (aFun4Equiv n b c d
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
          (aFun4Equiv n b c d (x.1 + x'.1))
        + coeffApply
            (cFun4Equiv n a b d
              (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
                (x.2.1 + x'.2.1, x.2.2 + x'.2.2)))
            (cFun4Equiv n a b d C) = _
    rw [hA, hBW]
    calc
      _ =
          (coeffApply
              (aFun4Equiv n b c d
                (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
              (aFun4Equiv n b c d x.1) +
            coeffApply
              (aFun4Equiv n b c d
                (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
              (aFun4Equiv n b c d x'.1)) +
          (coeffApply
              (cFun4Equiv n a b d
                (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2))
              (cFun4Equiv n a b d C) +
            coeffApply
              (cFun4Equiv n a b d
                (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x'.2))
              (cFun4Equiv n a b d C)) := by
            congr 1
            · exact hright _ _ _
            · exact hleft _ _ _
      _ = _ := by
        change
          _ =
            (coeffApply
                (aFun4Equiv n b c d
                  (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
                (aFun4Equiv n b c d x.1) +
              coeffApply
                (cFun4Equiv n a b d
                  (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2))
                (cFun4Equiv n a b d C)) +
            (coeffApply
                (aFun4Equiv n b c d
                  (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
                (aFun4Equiv n b c d x'.1) +
              coeffApply
                (cFun4Equiv n a b d
                  (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x'.2))
                (cFun4Equiv n a b d C))
        ring
  map_smul' r x := by
    classical
    apply LinearMap.ext
    intro C
    have hA : aFun4Equiv n b c d (r • x.1) = r • aFun4Equiv n b c d x.1 := by
      funext i
      rcases i with ⟨y, z, w⟩
      rfl
    have hBW :
        cFun4Equiv n a b d
            (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
              (r • x.2.1, r • x.2.2)) =
          r • cFun4Equiv n a b d
            (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2) := by
      have hs :
          squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
              (r • x.2.1, r • x.2.2) =
            r • squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2 := by
        simpa only [Prod.smul_fst, Prod.smul_snd] using
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.2
      rw [hs]
      funext i
      rcases i with ⟨p, y, sz, w⟩
      rfl
    have hleft {i : Type} [Fintype i] (u f : i → F) (s : F) :
        coeffApply (s • u) f = s * coeffApply u f := by
      unfold coeffApply
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    have hright {i : Type} [Fintype i] (u f : i → F) (s : F) :
        coeffApply u (s • f) = s * coeffApply u f := by
      unfold coeffApply
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    unfold k4CPhaseCoeffClean coeffApplyA
    change
      coeffApply
          (aFun4Equiv n b c d
            (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
          (aFun4Equiv n b c d (r • x.1))
        + coeffApply
            (cFun4Equiv n a b d
              (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
                (r • x.2.1, r • x.2.2)))
            (cFun4Equiv n a b d C) = _
    rw [hA, hBW]
    calc
      _ = r * coeffApply
              (aFun4Equiv n b c d
                (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
              (aFun4Equiv n b c d x.1) +
          r * coeffApply
              (cFun4Equiv n a b d
                (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2))
              (cFun4Equiv n a b d C) := by
            congr 1
            · exact hright _ _ r
            · exact hleft _ _ r
      _ = _ := by
        change
          r * coeffApply
                (aFun4Equiv n b c d
                  (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
                (aFun4Equiv n b c d x.1) +
              r * coeffApply
                (cFun4Equiv n a b d
                  (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2))
                (cFun4Equiv n a b d C) =
            r *
              (coeffApply
                  (aFun4Equiv n b c d
                    (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C))
                  (aFun4Equiv n b c d x.1) +
                coeffApply
                  (cFun4Equiv n a b d
                    (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.2))
                  (cFun4Equiv n a b d C))
        ring

noncomputable abbrev K4PreCSource (n a b c d : ℕ) [NeZero n] :=
  LinearMap.ker (k4PreCMap (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def k4PreCQ {n a b c d : ℕ} [NeZero n]
    (x : K4PreCSource n a b c d) : F :=
  coeffApplyA
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2.1
        + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2.2)
      x.1.1
    + k4BWPhaseClean x.1.2.1 x.1.2.2

private theorem k4PreC_phase_split {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (C : CFun4 n a b d) (W : WFun4 n a b c) :
    phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d) =
      k4CPhaseCoeffClean A B W C
        + (coeffApplyA
            (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
              + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) A
          + k4BWPhaseClean B W) := by
  rw [phaseExponent_complete_split, k4_Q4_eq_Q3_add_BW_clean]
  unfold Q3
  rw [← coeffApply_squareCompat_eq_Q2 (B := B) (C := C) (W := W)]
  unfold k4CPhaseCoeffClean
  simp [coeffApplyA, coeffApply, aFun4Equiv, K_yzw, K_yzw_fun,
    KBMap, KCMap, KWMap, Finset.sum_add_distrib]
  simp_rw [mul_add]
  repeat' rw [Finset.sum_add_distrib]
  ring

private theorem k4_sum_C_eq_kernel_indicator {n a b c d : ℕ} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d) (W : WFun4 n a b c) :
    (∑ C : CFun4 n a b d,
      bitSign (phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n a b c d))) =
      if k4PreCMap (n := n) (a := a) (b := b) (c := c) (d := d) (A, B, W) = 0
      then (Fintype.card (CFun4 n a b d) : ℤ) *
        bitSign
          (coeffApplyA
              (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) A
            + k4BWPhaseClean B W)
      else 0 := by
  classical
  calc
    (∑ C : CFun4 n a b d,
        bitSign (phaseExponentNF .complete
          ({ A := A, B := B, C := C, W := W } : NF4 n a b c d))) =
      ∑ C : CFun4 n a b d,
        bitSign
          (k4CPhaseCoeffClean A B W C
            + (coeffApplyA
                (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                  + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) A
              + k4BWPhaseClean B W)) := by
        refine Finset.sum_congr rfl ?_
        intro C _
        rw [k4PreC_phase_split]
    _ = if k4CPhaseCoeffClean A B W = 0
        then (Fintype.card (CFun4 n a b d) : ℤ) *
          bitSign
            (coeffApplyA
                (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
                  + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) A
              + k4BWPhaseClean B W)
        else 0 :=
      sum_bitSign_linearMap_add_const
        (k4CPhaseCoeffClean A B W)
        (coeffApplyA
            (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
              + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W) A
          + k4BWPhaseClean B W)
    _ = _ := by rfl

theorem DeltaNF_complete_eq_preC_kernel_sum
    {n a b c d : ℕ} [NeZero n] :
    DeltaNF .complete a b c d n =
      (Fintype.card (CFun4 n a b d) : ℤ) *
        ∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x) := by
  classical
  rw [DeltaNF_eq_sum_components]
  let scale : ℤ := Fintype.card (CFun4 n a b d)
  let p : AFun4 n b c d × BFun4 n a c d × WFun4 n a b c → Prop :=
    fun x => x ∈ K4PreCSource n a b c d
  let f : AFun4 n b c d × BFun4 n a c d × WFun4 n a b c → ℤ :=
    fun x =>
      bitSign
        (coeffApplyA
            (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1
              + KWMap (n := n) (a := a) (b := b) (c := c) (d := d) x.2.2)
            x.1
          + k4BWPhaseClean x.2.1 x.2.2)
  have hreorder :
      (∑ A : AFun4 n b c d,
        ∑ B : BFun4 n a c d,
          ∑ C : CFun4 n a b d,
            ∑ W : WFun4 n a b c,
              bitSign (phaseExponentNF .complete
                ({ A := A, B := B, C := C, W := W } : NF4 n a b c d))) =
        ∑ x : AFun4 n b c d × BFun4 n a c d × WFun4 n a b c,
          if p x then scale * f x else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro A _
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro B _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro W _
    simpa [p, f, scale, K4PreCSource, LinearMap.mem_ker] using
      k4_sum_C_eq_kernel_indicator
        (n := n) (a := a) (b := b) (c := c) (d := d) A B W
  rw [hreorder, sum_if_mul_eq_mul_subtype p scale f]
  simp only [p, f, scale, K4PreCSource, k4PreCQ]
  congr 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    rfl


end Core4loop
