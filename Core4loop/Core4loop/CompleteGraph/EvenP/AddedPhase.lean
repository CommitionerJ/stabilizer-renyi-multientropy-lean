import Core4loop.CompleteGraph.DirectWitt.AddedBWPhase

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop

attribute [local instance] Fintype.ofFinite

private theorem k2_sum_eq_at_point_add_tail
    {S V : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)] [AddCommMonoid V]
    (f : S → V) :
    (∑ s, f s) = f s0 + ∑ t : PointedTail S s0, f t.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset S)) (p := fun s : S => s = s0) f).symm
  calc
    (∑ s, f s) =
        (∑ s ∈ (Finset.univ : Finset S) with s = s0, f s) +
          ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
            simpa using hpart
    _ = f s0 + ∑ s ∈ (Finset.univ : Finset S) with s ≠ s0, f s := by
          congr 1
          rw [Finset.sum_eq_single s0]
          · intro s hs hne
            exact (hne (Finset.mem_filter.mp hs).2).elim
          · simp
    _ = f s0 + ∑ t : PointedTail S s0, f t.1 := by
          congr 1
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset S)) (p := fun s : S => s ≠ s0)
              (f := f)).symm

private theorem k2_sum_tail_const_of_card_even
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S)) (x : F) :
    (∑ _ : PointedTail S s0, x) = x := by
  have hall : (∑ _ : S, x) = 0 := by
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul F]
    rcases heven with ⟨k, hk⟩
    rw [hk]
    push_cast
    rw [show (k : F) + (k : F) = 0 by exact F_add_self _, zero_smul]
  rw [k2_sum_eq_at_point_add_tail s0 (fun _ : S => x)] at hall
  exact
    ((add_eq_zero_iff_eq_of_F_module
      x (∑ _ : PointedTail S s0, x)).mp hall).symm

private noncomputable def k2BWSliceLeftAddHom
    {n b c d : Nat} [NeZero n]
    (W : WFun4 n 1 b c) :
    BFun4 n 1 c d →+ F where
  toFun B := k4BWSlice B W
  map_zero' := k4BWSlice_zero_left W
  map_add' B₁ B₂ := k4BWSlice_add_left B₁ B₂ W

private noncomputable def k2BWSliceRightAddHom
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) :
    WFun4 n 1 b c →+ F where
  toFun W := k4BWSlice B W
  map_zero' := k4BWSlice_zero_right B
  map_add' W₁ W₂ := k4BWSlice_add_right B W₁ W₂

theorem k4BWPhaseClean_evenP_pointed
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    k4BWPhaseClean B W =
      k4BWSlice
        (SquareDiagonal.EvenP.diamondEvenPBSigma B)
        (SquareDiagonal.EvenP.diamondEvenPWSigma W)
      + k4BWSlice
          (SquareDiagonal.EvenP.diamondEvenPBSigma B)
          (SquareDiagonal.EvenP.diamondEvenPWK W)
      + k4BWSlice
          (SquareDiagonal.EvenP.diamondEvenPBK B)
          (SquareDiagonal.EvenP.diamondEvenPWSigma W)
      + ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
          k4BWSlice
            (SquareDiagonal.EvenP.diamondEvenPBTail B t)
            (SquareDiagonal.EvenP.diamondEvenPWTail W t) := by
  classical
  let s0 : PVec n a := zeroVec
  let sigmaB := SquareDiagonal.EvenP.diamondEvenPBSigma B
  let sigmaW := SquareDiagonal.EvenP.diamondEvenPWSigma W
  let KB := SquareDiagonal.EvenP.diamondEvenPBK B
  let KW := SquareDiagonal.EvenP.diamondEvenPWK W
  let U := SquareDiagonal.EvenP.diamondEvenPBTail B
  let V := SquareDiagonal.EvenP.diamondEvenPWTail W
  let slice :=
    fun p : PVec n a =>
      SquareDiagonal.EvenP.diamondEvenPBWCurryEquiv (B, W) p
  have hbaseB : (slice s0).1 = sigmaB + KB := by
    funext q sy z w
    rw [SquareDiagonal.EvenP.pVec_one_eq_zeroVec q]
    change B s0 sy z w =
      (∑ p : PVec n a, B p sy z w) +
        ∑ t : PointedTail (PVec n a) s0, B t.1 sy z w
    rw [k2_sum_eq_at_point_add_tail s0]
    simp only [add_assoc, F_add_self, add_zero]
  have hbaseW : (slice s0).2 = sigmaW + KW := by
    funext q y z sw
    rw [SquareDiagonal.EvenP.pVec_one_eq_zeroVec q]
    change W s0 y z sw =
      (∑ p : PVec n a, W p y z sw) +
        ∑ t : PointedTail (PVec n a) s0, W t.1 y z sw
    rw [k2_sum_eq_at_point_add_tail s0]
    simp only [add_assoc, F_add_self, add_zero]
  have htailB :
      ∀ t : PointedTail (PVec n a) s0, (slice t.1).1 = U t + KB := by
    intro t
    funext q sy z w
    rw [SquareDiagonal.EvenP.pVec_one_eq_zeroVec q]
    change B t.1 sy z w =
      (B t.1 sy z w + KB 0 sy z w) + KB 0 sy z w
    simp only [add_assoc, F_add_self, add_zero]
  have htailW :
      ∀ t : PointedTail (PVec n a) s0, (slice t.1).2 = V t + KW := by
    intro t
    funext q y z sw
    rw [SquareDiagonal.EvenP.pVec_one_eq_zeroVec q]
    change W t.1 y z sw =
      (W t.1 y z sw + KW 0 y z sw) + KW 0 y z sw
    simp only [add_assoc, F_add_self, add_zero]
  have hTailPair :
      (∑ t : PointedTail (PVec n a) s0, (U t, V t)) = 0 := by
    have hmem :=
      (SquareDiagonal.EvenP.diamondEvenPBWPointedEquiv hn ha2 (B, W)).2.2
    exact LinearMap.mem_ker.mp hmem
  have hTailB : (∑ t : PointedTail (PVec n a) s0, U t) = 0 := by
    calc
      _ =
          (AddMonoidHom.fst (BFun4 n 1 c d) (WFun4 n 1 b c))
            (∑ t : PointedTail (PVec n a) s0, (U t, V t)) := by
              exact
                (map_sum
                  (AddMonoidHom.fst (BFun4 n 1 c d) (WFun4 n 1 b c))
                  (fun t : PointedTail (PVec n a) s0 => (U t, V t))
                  Finset.univ).symm
      _ = 0 := by rw [hTailPair]; rfl
  have hTailW : (∑ t : PointedTail (PVec n a) s0, V t) = 0 := by
    calc
      _ =
          (AddMonoidHom.snd (BFun4 n 1 c d) (WFun4 n 1 b c))
            (∑ t : PointedTail (PVec n a) s0, (U t, V t)) := by
              exact
                (map_sum
                  (AddMonoidHom.snd (BFun4 n 1 c d) (WFun4 n 1 b c))
                  (fun t : PointedTail (PVec n a) s0 => (U t, V t))
                  Finset.univ).symm
      _ = 0 := by rw [hTailPair]; rfl
  rw [k4BWPhaseClean_eq_sum_slices]
  change (∑ p : PVec n a, k4BWSlice (slice p).1 (slice p).2) = _
  rw [k2_sum_eq_at_point_add_tail s0]
  rw [hbaseB, hbaseW]
  rw [k4BWSlice_add_left, k4BWSlice_add_right,
    k4BWSlice_add_right]
  simp_rw [htailB, htailW, k4BWSlice_add_left,
    k4BWSlice_add_right]
  repeat' rw [Finset.sum_add_distrib]
  have hMixedB :
      (∑ t : PointedTail (PVec n a) s0, k4BWSlice (U t) KW) = 0 := by
    calc
      _ = k4BWSlice (∑ t, U t) KW := by
        exact
          (map_sum (k2BWSliceLeftAddHom KW) U Finset.univ).symm
      _ = 0 := by rw [hTailB]; exact k4BWSlice_zero_left KW
  have hMixedW :
      (∑ t : PointedTail (PVec n a) s0, k4BWSlice KB (V t)) = 0 := by
    calc
      _ = k4BWSlice KB (∑ t, V t) := by
        exact
          (map_sum (k2BWSliceRightAddHom KB) V Finset.univ).symm
      _ = 0 := by rw [hTailW]; exact k4BWSlice_zero_right KB
  rw [hMixedB, hMixedW,
    k2_sum_tail_const_of_card_even s0
      (SquareDiagonal.EvenP.even_card_PVec hn ha2)]
  let target :=
    k4BWSlice sigmaB sigmaW
      + k4BWSlice sigmaB KW
      + k4BWSlice KB sigmaW
      + ∑ t : PointedTail (PVec n a) s0, k4BWSlice (U t) (V t)
  calc
    _ = target + (k4BWSlice KB KW + k4BWSlice KB KW) := by
      dsimp only [target]
      abel
    _ = target := by rw [F_add_self, add_zero]
    _ = _ := rfl

theorem k4PreCQ_evenP_pointed
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (x : K4PreCSource n a b c d) :
    k4PreCQ x =
      coeffApplyA
        (KBMap
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (SquareDiagonal.EvenP.diamondEvenPBSigma x.1.2.1)
          + KWMap
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              (SquareDiagonal.EvenP.diamondEvenPWSigma x.1.2.2))
        x.1.1
      + k4BWSlice
          (SquareDiagonal.EvenP.diamondEvenPBSigma x.1.2.1)
          (SquareDiagonal.EvenP.diamondEvenPWSigma x.1.2.2)
      + k4BWSlice
          (SquareDiagonal.EvenP.diamondEvenPBSigma x.1.2.1)
          (SquareDiagonal.EvenP.diamondEvenPWK x.1.2.2)
      + k4BWSlice
          (SquareDiagonal.EvenP.diamondEvenPBK x.1.2.1)
          (SquareDiagonal.EvenP.diamondEvenPWSigma x.1.2.2)
      + ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
          k4BWSlice
            (SquareDiagonal.EvenP.diamondEvenPBTail x.1.2.1 t)
            (SquareDiagonal.EvenP.diamondEvenPWTail x.1.2.2 t) := by
  rw [k4PreCQ,
    SquareDiagonal.EvenP.KBMap_eq_KBMap_sigma,
    SquareDiagonal.EvenP.KWMap_eq_KWMap_sigma,
    k4BWPhaseClean_evenP_pointed hn ha2]
  abel

end Core4loop
