import Core4loop.SquareDiagonal.PreC.Reduction
import Core4loop.ZeroSumSpaces.PointedAugConstNormalForm

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

abbrev DiamondEvenPBWSlice (n b c d : Nat) :=
  BFun4 n 1 c d × WFun4 n 1 b c

noncomputable def diamondEvenPAConstraint
    {n a b c d : Nat} [NeZero n] :
    AFun4 n b c d →ₗ[F] CFun4 n a b d where
  toFun A := fun _p y sz w =>
    (∑ z : ZVec n c, if vecSum z = sz then A y z w else 0) +
      ∑ z : ZVec n c, if vecSum z + 1 = sz then A y z w else 0
  map_add' A A' := by
    funext p y sz w
    simp only [Pi.add_apply]
    calc
      _ =
          ((∑ z : ZVec n c, if vecSum z = sz then A y z w else 0) +
            ∑ z : ZVec n c, if vecSum z = sz then A' y z w else 0) +
          ((∑ z : ZVec n c, if vecSum z + 1 = sz then A y z w else 0) +
            ∑ z : ZVec n c, if vecSum z + 1 = sz then A' y z w else 0) := by
        congr 1
        · rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : vecSum z = sz <;> simp [h]
        · rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : vecSum z + 1 = sz <;> simp [h]
      _ = _ := by abel
  map_smul' r A := by
    funext p y sz w
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      _ =
          r * (∑ z : ZVec n c, if vecSum z = sz then A y z w else 0) +
            r * ∑ z : ZVec n c, if vecSum z + 1 = sz then A y z w else 0 := by
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : vecSum z = sz <;> simp [h]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          by_cases h : vecSum z + 1 = sz <;> simp [h]
      _ = _ := by ring

theorem coeffApply_diamondEvenPAConstraint_eq_coeffApplyA_KCMap
    {n a b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) (C : CFun4 n a b d) :
    coeffApply
        (cFun4Equiv n a b d
          (diamondEvenPAConstraint
            (n := n) (a := a) (b := b) (c := c) (d := d) A))
        (cFun4Equiv n a b d C)
      =
    coeffApplyA
      (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) A := by
  unfold coeffApply coeffApplyA diamondEvenPAConstraint
    KCMap dzC deltaC etaC cFun4Equiv aFun4Equiv
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ p : PVec n a, ∑ y : YVec n b, ∑ x : I n, ∑ w : WVec n d,
        C p y x w *
          ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
            + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0))
        =
      ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
        refine Finset.sum_congr rfl ?_
        intro p _
        refine Finset.sum_congr rfl ?_
        intro y _
        calc
          (∑ x : I n, ∑ w : WVec n d,
              C p y x w *
                ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                  + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0))
              =
            ∑ w : WVec n d, ∑ x : I n,
              C p y x w *
                ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                  + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0) := by
              exact Finset.sum_comm
          _ =
            ∑ w : WVec n d, ∑ z : ZVec n c,
              (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
              refine Finset.sum_congr rfl ?_
              intro w _
              calc
                (∑ x : I n,
                  C p y x w *
                    ((∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                      + ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0))
                    =
                  (∑ x : I n,
                    C p y x w *
                      ∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                    +
                  ∑ x : I n,
                    C p y x w *
                      ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0 := by
                    rw [← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl ?_
                    intro x _
                    ring
                _ =
                  (∑ z : ZVec n c, C p y (vecSum z) w * A y z w)
                    +
                  ∑ z : ZVec n c, C p y (vecSum z + 1) w * A y z w := by
                    congr 1
                    · calc
                        (∑ x : I n,
                          C p y x w *
                            ∑ z : ZVec n c, if vecSum z = x then A y z w else 0)
                          =
                          ∑ x : I n, ∑ z : ZVec n c,
                            C p y x w * (if vecSum z = x then A y z w else 0) := by
                            refine Finset.sum_congr rfl ?_
                            intro x _
                            rw [Finset.mul_sum]
                        _ =
                          ∑ z : ZVec n c, ∑ x : I n,
                            C p y x w * (if vecSum z = x then A y z w else 0) := by
                            exact Finset.sum_comm
                        _ = ∑ z : ZVec n c, C p y (vecSum z) w * A y z w := by
                            refine Finset.sum_congr rfl ?_
                            intro z _
                            rw [Finset.sum_eq_single (vecSum z)]
                            · simp
                            · intro x _ hx
                              simp [hx.symm]
                            · simp
                    · calc
                        (∑ x : I n,
                          C p y x w *
                            ∑ z : ZVec n c, if vecSum z + 1 = x then A y z w else 0)
                          =
                          ∑ x : I n, ∑ z : ZVec n c,
                            C p y x w * (if vecSum z + 1 = x then A y z w else 0) := by
                            refine Finset.sum_congr rfl ?_
                            intro x _
                            rw [Finset.mul_sum]
                        _ =
                          ∑ z : ZVec n c, ∑ x : I n,
                            C p y x w * (if vecSum z + 1 = x then A y z w else 0) := by
                            exact Finset.sum_comm
                        _ = ∑ z : ZVec n c, C p y (vecSum z + 1) w * A y z w := by
                            refine Finset.sum_congr rfl ?_
                            intro z _
                            rw [Finset.sum_eq_single (vecSum z + 1)]
                            · simp
                            · intro x _ hx
                              simp [hx.symm]
                            · simp
                _ =
                  ∑ z : ZVec n c,
                    (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
                    rw [← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl ?_
                    intro z _
                    ring
          _ =
            ∑ z : ZVec n c, ∑ w : WVec n d,
              (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
              exact Finset.sum_comm
    _ =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d, ∑ p : PVec n a,
        (C p y (vecSum z) w + C p y (vecSum z + 1) w) * A y z w := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro y _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [Finset.sum_comm]
    _ =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        A y z w *
          ∑ p : PVec n a, (C p y (vecSum z) w + C p y (vecSum z + 1) w) := by
        refine Finset.sum_congr rfl ?_
        intro y _
        refine Finset.sum_congr rfl ?_
        intro z _
        refine Finset.sum_congr rfl ?_
        intro w _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro p _
        ring
    _ = _ := by
      unfold coeffApply
      simp_rw [Fintype.sum_prod_type]
      rfl

private theorem coeffApply_forall_eq_zero_iff
    {ι : Type*} [Fintype ι] (c : ι → F) :
    (∀ f : ι → F, coeffApply c f = 0) ↔ c = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi := h (fun j => if j = i then (1 : F) else 0)
    unfold coeffApply at hi
    rw [Finset.sum_eq_single i] at hi
    · simpa using hi
    · intro j _ hji
      simp [hji]
    · simp
  · intro hc f
    simp [coeffApply, hc]

theorem diamondPreCMap_eq_zero_iff_constraint
    {n a b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (A, B, W) = 0 ↔
      diamondEvenPAConstraint
          (n := n) (a := a) (b := b) (c := c) (d := d) A =
        squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (B, W) := by
  constructor
  · intro hmap
    have hcoeff :
        cFun4Equiv n a b d
            (diamondEvenPAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A) +
          cFun4Equiv n a b d
            (squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)) = 0 := by
      apply (coeffApply_forall_eq_zero_iff _).mp
      intro f
      rcases (cFun4Equiv n a b d).surjective f with ⟨C, rfl⟩
      have happ :=
        congrArg
          (fun L : CFun4 n a b d →ₗ[F] F => L C)
          hmap
      calc
        coeffApply
            (cFun4Equiv n a b d
                (diamondEvenPAConstraint
                  (n := n) (a := a) (b := b) (c := c) (d := d) A) +
              cFun4Equiv n a b d
                (squareCompat
                  (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
            (cFun4Equiv n a b d C)
          =
            coeffApply
                (cFun4Equiv n a b d
                  (diamondEvenPAConstraint
                    (n := n) (a := a) (b := b) (c := c) (d := d) A))
                (cFun4Equiv n a b d C) +
              coeffApply
                (cFun4Equiv n a b d
                  (squareCompat
                    (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
                (cFun4Equiv n a b d C) := by
                  unfold coeffApply
                  rw [← Finset.sum_add_distrib]
                  refine Finset.sum_congr rfl ?_
                  intro i _
                  simp only [Pi.add_apply]
                  ring
        _ =
            coeffApplyA
                (KCMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) C) A +
              coeffApply
                (cFun4Equiv n a b d
                  (squareCompat
                    (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
                (cFun4Equiv n a b d C) := by
                  rw [coeffApply_diamondEvenPAConstraint_eq_coeffApplyA_KCMap]
        _ = diamondCPhaseCoeffClean A B W C := rfl
        _ = 0 := by
          simpa [diamondPreCMap] using happ
    have hsum :
        diamondEvenPAConstraint
              (n := n) (a := a) (b := b) (c := c) (d := d) A +
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d) (B, W) =
          0 := by
      apply (cFun4Equiv n a b d).injective
      simpa [cFun4Equiv] using hcoeff
    exact (add_eq_zero_iff_eq_of_F_module _ _).mp hsum
  · intro hconstraint
    apply LinearMap.ext
    intro C
    change
      coeffApplyA
          (KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C) A +
        coeffApply
            (cFun4Equiv n a b d
              (squareCompat
                (n := n) (a := a) (b := b) (c := c) (d := d) (B, W)))
            (cFun4Equiv n a b d C) =
          0
    rw [← coeffApply_diamondEvenPAConstraint_eq_coeffApplyA_KCMap]
    rw [hconstraint]
    exact F_add_self _

theorem pVec_one_eq_zeroVec
    {n : Nat} (p : PVec n 1) :
    p = (zeroVec : PVec n 1) := by
  funext i
  exact Fin.elim0 i

noncomputable def diamondEvenPBWCurryEquiv
    {n a b c d : Nat} [NeZero n] :
    (BFun4 n a c d × WFun4 n a b c) ≃ₗ[F]
      (PVec n a → DiamondEvenPBWSlice n b c d) where
  toFun x := fun p =>
    (fun _q sy z w => x.1 p sy z w,
      fun _q y z sw => x.2 p y z sw)
  invFun f :=
    (fun p sy z w => (f p).1 (zeroVec : PVec n 1) sy z w,
      fun p y z sw => (f p).2 (zeroVec : PVec n 1) y z sw)
  left_inv x := by
    apply Prod.ext <;> rfl
  right_inv f := by
    funext p
    apply Prod.ext
    · funext q sy z w
      rw [pVec_one_eq_zeroVec q]
    · funext q y z sw
      rw [pVec_one_eq_zeroVec q]
  map_add' x x' := by
    funext p
    apply Prod.ext <;> rfl
  map_smul' r x := by
    funext p
    apply Prod.ext <;> rfl

theorem even_card_PVec
    {n a : Nat} [NeZero n] (hn : Even n) (ha2 : 2 ≤ a) :
    Even (Fintype.card (PVec n a)) := by
  rw [card_vec]
  exact Even.pow_of_ne_zero hn (Nat.sub_ne_zero_of_lt ha2)

noncomputable def diamondEvenPBSigma
    {n a c d : Nat} [NeZero n] :
    BFun4 n a c d →ₗ[F] BFun4 n 1 c d where
  toFun B := fun _q sy z w => ∑ p : PVec n a, B p sy z w
  map_add' B B' := by
    funext q sy z w
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r B := by
    funext q sy z w
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]

noncomputable def diamondEvenPBK
    {n a c d : Nat} [NeZero n] :
    BFun4 n a c d →ₗ[F] BFun4 n 1 c d where
  toFun B := fun _q sy z w =>
    ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
      B t.1 sy z w
  map_add' B B' := by
    funext q sy z w
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r B := by
    funext q sy z w
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]

noncomputable def diamondEvenPBTail
    {n a c d : Nat} [NeZero n] :
    BFun4 n a c d →ₗ[F]
      PointedTail (PVec n a) (zeroVec : PVec n a) →
        BFun4 n 1 c d where
  toFun B := fun t _q sy z w =>
    B t.1 sy z w +
      diamondEvenPBK (n := n) (a := a) (c := c) (d := d)
        B (zeroVec : PVec n 1) sy z w
  map_add' B B' := by
    funext t q sy z w
    change
      (B + B') t.1 sy z w + diamondEvenPBK (B + B') 0 sy z w =
        (B t.1 sy z w + diamondEvenPBK B 0 sy z w) +
          (B' t.1 sy z w + diamondEvenPBK B' 0 sy z w)
    rw [(diamondEvenPBK
      (n := n) (a := a) (c := c) (d := d)).map_add]
    simp only [Pi.add_apply]
    abel
  map_smul' r B := by
    funext t q sy z w
    change
      r * B t.1 sy z w + diamondEvenPBK (r • B) 0 sy z w =
        r * (B t.1 sy z w + diamondEvenPBK B 0 sy z w)
    rw [(diamondEvenPBK
      (n := n) (a := a) (c := c) (d := d)).map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

noncomputable def diamondEvenPWSigma
    {n a b c : Nat} [NeZero n] :
    WFun4 n a b c →ₗ[F] WFun4 n 1 b c where
  toFun W := fun _q y z sw => ∑ p : PVec n a, W p y z sw
  map_add' W W' := by
    funext q y z sw
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r W := by
    funext q y z sw
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]

noncomputable def diamondEvenPWK
    {n a b c : Nat} [NeZero n] :
    WFun4 n a b c →ₗ[F] WFun4 n 1 b c where
  toFun W := fun _q y z sw =>
    ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
      W t.1 y z sw
  map_add' W W' := by
    funext q y z sw
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r W := by
    funext q y z sw
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]

noncomputable def diamondEvenPWTail
    {n a b c : Nat} [NeZero n] :
    WFun4 n a b c →ₗ[F]
      PointedTail (PVec n a) (zeroVec : PVec n a) →
        WFun4 n 1 b c where
  toFun W := fun t _q y z sw =>
    W t.1 y z sw +
      diamondEvenPWK (n := n) (a := a) (b := b) (c := c)
        W (zeroVec : PVec n 1) y z sw
  map_add' W W' := by
    funext t q y z sw
    change
      (W + W') t.1 y z sw + diamondEvenPWK (W + W') 0 y z sw =
        (W t.1 y z sw + diamondEvenPWK W 0 y z sw) +
          (W' t.1 y z sw + diamondEvenPWK W' 0 y z sw)
    rw [(diamondEvenPWK
      (n := n) (a := a) (b := b) (c := c)).map_add]
    simp only [Pi.add_apply]
    abel
  map_smul' r W := by
    funext t q y z sw
    change
      r * W t.1 y z sw + diamondEvenPWK (r • W) 0 y z sw =
        r * (W t.1 y z sw + diamondEvenPWK W 0 y z sw)
    rw [(diamondEvenPWK
      (n := n) (a := a) (b := b) (c := c)).map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

noncomputable def diamondEvenPTailSum
    {n a b c d : Nat} [NeZero n] :
    (PointedTail (PVec n a) (zeroVec : PVec n a) →
      DiamondEvenPBWSlice n b c d) →ₗ[F]
        DiamondEvenPBWSlice n b c d where
  toFun f := ∑ t, f t
  map_add' f g := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]

noncomputable abbrev DiamondEvenPBWTailZero
    (n a b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (diamondEvenPTailSum (n := n) (a := a) (b := b) (c := c) (d := d))

private theorem cast_card_eq_zero_of_even
    {m : Nat} (hm : Even m) : (m : F) = 0 := by
  rcases hm with ⟨k, hk⟩
  rw [hk]
  push_cast
  exact F_add_self _

private theorem sum_eq_at_point_add_tail
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
          exact congrArg (fun v => f s0 + v) (by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset S)) (p := fun s : S => s ≠ s0)
                (f := f)).symm)

private theorem sum_tail_const_of_even
    {S : Type*} [Fintype S] (s0 : S)
    [Fintype (PointedTail S s0)]
    (heven : Even (Fintype.card S)) (x : F) :
    (∑ _ : PointedTail S s0, x) = x := by
  have hall : (∑ _ : S, x) = 0 := by
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul F,
      cast_card_eq_zero_of_even heven, zero_smul]
  rw [sum_eq_at_point_add_tail s0 (fun _ : S => x)] at hall
  exact
    ((add_eq_zero_iff_eq_of_F_module x
      (∑ _ : PointedTail S s0, x)).mp hall).symm

private noncomputable def diamondEvenPBWPointedRead
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    (BFun4 n a c d × WFun4 n a b c) →ₗ[F]
      (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d where
  toFun x :=
    (((diamondEvenPBSigma x.1, diamondEvenPWSigma x.2),
      (diamondEvenPBK x.1, diamondEvenPWK x.2)),
      ⟨fun t => (diamondEvenPBTail x.1 t, diamondEvenPWTail x.2 t), by
        have hB :
            (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              diamondEvenPBTail x.1 t) = 0 := by
          funext q sy z w
          simp only [Finset.sum_apply, diamondEvenPBTail,
            LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
          change
            (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
                (x.1 t.1 sy z w +
                  ∑ u : PointedTail (PVec n a) (zeroVec : PVec n a),
                    x.1 u.1 sy z w)) = 0
          rw [Finset.sum_add_distrib,
            sum_tail_const_of_even (zeroVec : PVec n a)
              (even_card_PVec hn ha2)]
          exact F_add_self _
        have hW :
            (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              diamondEvenPWTail x.2 t) = 0 := by
          funext q y z sw
          simp only [Finset.sum_apply, diamondEvenPWTail,
            LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
          change
            (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
                (x.2 t.1 y z sw +
                  ∑ u : PointedTail (PVec n a) (zeroVec : PVec n a),
                    x.2 u.1 y z sw)) = 0
          rw [Finset.sum_add_distrib,
            sum_tail_const_of_even (zeroVec : PVec n a)
              (even_card_PVec hn ha2)]
          exact F_add_self _
        apply LinearMap.mem_ker.mpr
        change
          (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
            (diamondEvenPBTail x.1 t, diamondEvenPWTail x.2 t)) = 0
        have hprojB :=
          map_sum
            (AddMonoidHom.fst (BFun4 n 1 c d) (WFun4 n 1 b c))
            (fun t : PointedTail (PVec n a) (zeroVec : PVec n a) =>
              (diamondEvenPBTail x.1 t, diamondEvenPWTail x.2 t))
            Finset.univ
        have hprojW :=
          map_sum
            (AddMonoidHom.snd (BFun4 n 1 c d) (WFun4 n 1 b c))
            (fun t : PointedTail (PVec n a) (zeroVec : PVec n a) =>
              (diamondEvenPBTail x.1 t, diamondEvenPWTail x.2 t))
            Finset.univ
        apply Prod.ext
        · exact hprojB.trans hB
        · exact hprojW.trans hW⟩)
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact (diamondEvenPBSigma
            (n := n) (a := a) (c := c) (d := d)).map_add x.1 y.1
        · exact (diamondEvenPWSigma
            (n := n) (a := a) (b := b) (c := c)).map_add x.2 y.2
      · apply Prod.ext
        · exact (diamondEvenPBK
            (n := n) (a := a) (c := c) (d := d)).map_add x.1 y.1
        · exact (diamondEvenPWK
            (n := n) (a := a) (b := b) (c := c)).map_add x.2 y.2
    · apply Subtype.ext
      funext t
      apply Prod.ext
      · exact congrFun
          ((diamondEvenPBTail
            (n := n) (a := a) (c := c) (d := d)).map_add x.1 y.1) t
      · exact congrFun
          ((diamondEvenPWTail
            (n := n) (a := a) (b := b) (c := c)).map_add x.2 y.2) t
  map_smul' r x := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · exact (diamondEvenPBSigma
            (n := n) (a := a) (c := c) (d := d)).map_smul r x.1
        · exact (diamondEvenPWSigma
            (n := n) (a := a) (b := b) (c := c)).map_smul r x.2
      · apply Prod.ext
        · exact (diamondEvenPBK
            (n := n) (a := a) (c := c) (d := d)).map_smul r x.1
        · exact (diamondEvenPWK
            (n := n) (a := a) (b := b) (c := c)).map_smul r x.2
    · apply Subtype.ext
      funext t
      apply Prod.ext
      · exact congrFun
          ((diamondEvenPBTail
            (n := n) (a := a) (c := c) (d := d)).map_smul r x.1) t
      · exact congrFun
          ((diamondEvenPWTail
            (n := n) (a := a) (b := b) (c := c)).map_smul r x.2) t

private noncomputable def diamondEvenPBWPointedBuild
    {n a b c d : Nat} [NeZero n] :
    ((DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d) →ₗ[F]
      (BFun4 n a c d × WFun4 n a b c) where
  toFun x :=
    (fun p sy z w =>
      if hp : p = (zeroVec : PVec n a) then
        x.1.1.1 (zeroVec : PVec n 1) sy z w +
          x.1.2.1 (zeroVec : PVec n 1) sy z w
      else
        (x.2.1 ⟨p, hp⟩).1 (zeroVec : PVec n 1) sy z w +
          x.1.2.1 (zeroVec : PVec n 1) sy z w,
    fun p y z sw =>
      if hp : p = (zeroVec : PVec n a) then
        x.1.1.2 (zeroVec : PVec n 1) y z sw +
          x.1.2.2 (zeroVec : PVec n 1) y z sw
      else
        (x.2.1 ⟨p, hp⟩).2 (zeroVec : PVec n 1) y z sw +
          x.1.2.2 (zeroVec : PVec n 1) y z sw)
  map_add' x y := by
    apply Prod.ext
    · funext p sy z w
      by_cases hp : p = (zeroVec : PVec n a)
      · simp [hp]
        abel
      · simp [hp]
        abel
    · funext p yy z sw
      by_cases hp : p = (zeroVec : PVec n a)
      · simp [hp]
        abel
      · simp [hp]
        abel
  map_smul' r x := by
    apply Prod.ext
    · funext p sy z w
      by_cases hp : p = (zeroVec : PVec n a)
      · simp [hp, mul_add]
      · simp [hp, mul_add]
    · funext p y z sw
      by_cases hp : p = (zeroVec : PVec n a)
      · simp [hp, mul_add]
      · simp [hp, mul_add]

@[simp] private theorem diamondEvenPBWPointedBuild_B_zero
    {n a b c d : Nat} [NeZero n]
    (x : (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d)
    (sy : I n) (z : ZVec n c) (w : WVec n d) :
    (diamondEvenPBWPointedBuild x).1
        (zeroVec : PVec n a) sy z w =
      x.1.1.1 (zeroVec : PVec n 1) sy z w +
        x.1.2.1 (zeroVec : PVec n 1) sy z w := by
  simp [diamondEvenPBWPointedBuild]

@[simp] private theorem diamondEvenPBWPointedBuild_W_zero
    {n a b c d : Nat} [NeZero n]
    (x : (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d)
    (y : YVec n b) (z : ZVec n c) (sw : I n) :
    (diamondEvenPBWPointedBuild x).2
        (zeroVec : PVec n a) y z sw =
      x.1.1.2 (zeroVec : PVec n 1) y z sw +
        x.1.2.2 (zeroVec : PVec n 1) y z sw := by
  simp [diamondEvenPBWPointedBuild]

@[simp] private theorem diamondEvenPBWPointedBuild_B_tail
    {n a b c d : Nat} [NeZero n]
    (x : (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d)
    (t : PointedTail (PVec n a) (zeroVec : PVec n a))
    (sy : I n) (z : ZVec n c) (w : WVec n d) :
    (diamondEvenPBWPointedBuild x).1 t.1 sy z w =
      (x.2.1 t).1 (zeroVec : PVec n 1) sy z w +
        x.1.2.1 (zeroVec : PVec n 1) sy z w := by
  simp [diamondEvenPBWPointedBuild, t.2]

@[simp] private theorem diamondEvenPBWPointedBuild_W_tail
    {n a b c d : Nat} [NeZero n]
    (x : (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d)
    (t : PointedTail (PVec n a) (zeroVec : PVec n a))
    (y : YVec n b) (z : ZVec n c) (sw : I n) :
    (diamondEvenPBWPointedBuild x).2 t.1 y z sw =
      (x.2.1 t).2 (zeroVec : PVec n 1) y z sw +
        x.1.2.2 (zeroVec : PVec n 1) y z sw := by
  simp [diamondEvenPBWPointedBuild, t.2]

private theorem diamondEvenPBWPointedBuild_read
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (x : BFun4 n a c d × WFun4 n a b c) :
    diamondEvenPBWPointedBuild
      (diamondEvenPBWPointedRead hn ha2 x) = x := by
  apply Prod.ext
  · funext p sy z w
    by_cases hp : p = (zeroVec : PVec n a)
    · subst p
      rw [diamondEvenPBWPointedBuild_B_zero]
      change
        (∑ p : PVec n a, x.1 p sy z w) +
            (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              x.1 t.1 sy z w) =
          x.1 (zeroVec : PVec n a) sy z w
      rw [sum_eq_at_point_add_tail]
      rw [add_assoc, F_add_self, add_zero]
    · let t : PointedTail (PVec n a) (zeroVec : PVec n a) := ⟨p, hp⟩
      change
        (diamondEvenPBWPointedBuild
          (diamondEvenPBWPointedRead hn ha2 x)).1 t.1 sy z w =
            x.1 p sy z w
      rw [diamondEvenPBWPointedBuild_B_tail]
      change
        (x.1 p sy z w +
            ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              x.1 t.1 sy z w) +
          (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
            x.1 t.1 sy z w) = x.1 p sy z w
      rw [add_assoc, F_add_self, add_zero]
  · funext p y z sw
    by_cases hp : p = (zeroVec : PVec n a)
    · subst p
      rw [diamondEvenPBWPointedBuild_W_zero]
      change
        (∑ p : PVec n a, x.2 p y z sw) +
            (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              x.2 t.1 y z sw) =
          x.2 (zeroVec : PVec n a) y z sw
      rw [sum_eq_at_point_add_tail]
      rw [add_assoc, F_add_self, add_zero]
    · let t : PointedTail (PVec n a) (zeroVec : PVec n a) := ⟨p, hp⟩
      change
        (diamondEvenPBWPointedBuild
          (diamondEvenPBWPointedRead hn ha2 x)).2 t.1 y z sw =
            x.2 p y z sw
      rw [diamondEvenPBWPointedBuild_W_tail]
      change
        (x.2 p y z sw +
            ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              x.2 t.1 y z sw) +
          (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
            x.2 t.1 y z sw) = x.2 p y z sw
      rw [add_assoc, F_add_self, add_zero]

private theorem diamondEvenPBWPointedRead_build
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (x : (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d) :
    diamondEvenPBWPointedRead hn ha2
        (diamondEvenPBWPointedBuild x) = x := by
  have htail := LinearMap.mem_ker.mp x.2.2
  change (∑ t, x.2.1 t) = 0 at htail
  have hprojB :=
    map_sum
      (AddMonoidHom.fst (BFun4 n 1 c d) (WFun4 n 1 b c))
      (fun t => x.2.1 t) Finset.univ
  have hprojW :=
    map_sum
      (AddMonoidHom.snd (BFun4 n 1 c d) (WFun4 n 1 b c))
      (fun t => x.2.1 t) Finset.univ
  have htailBfun :
      (∑ t, (x.2.1 t).1) = (0 : BFun4 n 1 c d) := by
    calc
      (∑ t, (x.2.1 t).1) =
          (AddMonoidHom.fst (BFun4 n 1 c d) (WFun4 n 1 b c))
            (∑ t, x.2.1 t) := hprojB.symm
      _ = 0 := by rw [htail]; rfl
  have htailWfun :
      (∑ t, (x.2.1 t).2) = (0 : WFun4 n 1 b c) := by
    calc
      (∑ t, (x.2.1 t).2) =
          (AddMonoidHom.snd (BFun4 n 1 c d) (WFun4 n 1 b c))
            (∑ t, x.2.1 t) := hprojW.symm
      _ = 0 := by rw [htail]; rfl
  have htailB :
      ∀ q sy z w, (∑ t, (x.2.1 t).1 q sy z w) = 0 := by
    intro q sy z w
    have h := congrFun (congrFun (congrFun (congrFun htailBfun q) sy) z) w
    simpa only [Finset.sum_apply, Pi.zero_apply] using h
  have htailW :
      ∀ q y z sw, (∑ t, (x.2.1 t).2 q y z sw) = 0 := by
    intro q y z sw
    have h := congrFun (congrFun (congrFun (congrFun htailWfun q) y) z) sw
    simpa only [Finset.sum_apply, Pi.zero_apply] using h
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · funext q sy z w
        rw [pVec_one_eq_zeroVec q]
        change
          (∑ p : PVec n a,
            (diamondEvenPBWPointedBuild x).1 p sy z w) =
              x.1.1.1 0 sy z w
        rw [sum_eq_at_point_add_tail (zeroVec : PVec n a)]
        rw [diamondEvenPBWPointedBuild_B_zero]
        simp_rw [diamondEvenPBWPointedBuild_B_tail]
        change
          ((x.1.1.1 0 sy z w + x.1.2.1 0 sy z w) +
              ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
                ((x.2.1 t).1 0 sy z w + x.1.2.1 0 sy z w)) =
            x.1.1.1 0 sy z w
        rw [Finset.sum_add_distrib, htailB,
          sum_tail_const_of_even (zeroVec : PVec n a)
            (even_card_PVec hn ha2)]
        simp only [zero_add, add_assoc, F_add_self, add_zero]
      · funext q y z sw
        rw [pVec_one_eq_zeroVec q]
        change
          (∑ p : PVec n a,
            (diamondEvenPBWPointedBuild x).2 p y z sw) =
              x.1.1.2 0 y z sw
        rw [sum_eq_at_point_add_tail (zeroVec : PVec n a)]
        rw [diamondEvenPBWPointedBuild_W_zero]
        simp_rw [diamondEvenPBWPointedBuild_W_tail]
        change
          ((x.1.1.2 0 y z sw + x.1.2.2 0 y z sw) +
              ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
                ((x.2.1 t).2 0 y z sw + x.1.2.2 0 y z sw)) =
            x.1.1.2 0 y z sw
        rw [Finset.sum_add_distrib, htailW,
          sum_tail_const_of_even (zeroVec : PVec n a)
            (even_card_PVec hn ha2)]
        simp only [zero_add, add_assoc, F_add_self, add_zero]
    · apply Prod.ext
      · funext q sy z w
        rw [pVec_one_eq_zeroVec q]
        change
          (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
            (diamondEvenPBWPointedBuild x).1 t.1 sy z w) =
              x.1.2.1 0 sy z w
        simp_rw [diamondEvenPBWPointedBuild_B_tail]
        change
          (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              ((x.2.1 t).1 0 sy z w + x.1.2.1 0 sy z w)) =
            x.1.2.1 0 sy z w
        rw [Finset.sum_add_distrib, htailB,
          sum_tail_const_of_even (zeroVec : PVec n a)
            (even_card_PVec hn ha2)]
        simp
      · funext q y z sw
        rw [pVec_one_eq_zeroVec q]
        change
          (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
            (diamondEvenPBWPointedBuild x).2 t.1 y z sw) =
              x.1.2.2 0 y z sw
        simp_rw [diamondEvenPBWPointedBuild_W_tail]
        change
          (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
              ((x.2.1 t).2 0 y z sw + x.1.2.2 0 y z sw)) =
            x.1.2.2 0 y z sw
        rw [Finset.sum_add_distrib, htailW,
          sum_tail_const_of_even (zeroVec : PVec n a)
            (even_card_PVec hn ha2)]
        simp
  · apply Subtype.ext
    funext t
    apply Prod.ext
    · funext q sy z w
      rw [pVec_one_eq_zeroVec q]
      change
        (diamondEvenPBWPointedBuild x).1 t.1 sy z w +
            (∑ u : PointedTail (PVec n a) (zeroVec : PVec n a),
              (diamondEvenPBWPointedBuild x).1 u.1 sy z w) =
          (x.2.1 t).1 0 sy z w
      rw [diamondEvenPBWPointedBuild_B_tail]
      simp_rw [diamondEvenPBWPointedBuild_B_tail]
      change
        ((x.2.1 t).1 0 sy z w + x.1.2.1 0 sy z w) +
            (∑ u : PointedTail (PVec n a) (zeroVec : PVec n a),
              ((x.2.1 u).1 0 sy z w + x.1.2.1 0 sy z w)) =
          (x.2.1 t).1 0 sy z w
      rw [Finset.sum_add_distrib, htailB,
        sum_tail_const_of_even (zeroVec : PVec n a)
          (even_card_PVec hn ha2)]
      simp only [zero_add, add_assoc, F_add_self, add_zero]
    · funext q y z sw
      rw [pVec_one_eq_zeroVec q]
      change
        (diamondEvenPBWPointedBuild x).2 t.1 y z sw +
            (∑ u : PointedTail (PVec n a) (zeroVec : PVec n a),
              (diamondEvenPBWPointedBuild x).2 u.1 y z sw) =
          (x.2.1 t).2 0 y z sw
      rw [diamondEvenPBWPointedBuild_W_tail]
      simp_rw [diamondEvenPBWPointedBuild_W_tail]
      change
        ((x.2.1 t).2 0 y z sw + x.1.2.2 0 y z sw) +
            (∑ u : PointedTail (PVec n a) (zeroVec : PVec n a),
              ((x.2.1 u).2 0 y z sw + x.1.2.2 0 y z sw)) =
          (x.2.1 t).2 0 y z sw
      rw [Finset.sum_add_distrib, htailW,
        sum_tail_const_of_even (zeroVec : PVec n a)
          (even_card_PVec hn ha2)]
      simp only [zero_add, add_assoc, F_add_self, add_zero]

set_option maxHeartbeats 800000 in
-- Elaborating both explicit inverse laws needs more than the default budget.
noncomputable def diamondEvenPBWPointedEquiv
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    (BFun4 n a c d × WFun4 n a b c) ≃ₗ[F]
      (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d where
  toFun := diamondEvenPBWPointedRead hn ha2
  invFun := diamondEvenPBWPointedBuild
  left_inv := diamondEvenPBWPointedBuild_read hn ha2
  right_inv := diamondEvenPBWPointedRead_build hn ha2
  map_add' := (diamondEvenPBWPointedRead hn ha2).map_add
  map_smul' := (diamondEvenPBWPointedRead hn ha2).map_smul

@[simp] theorem diamondEvenPBWPointedEquiv_apply_sigma
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    (diamondEvenPBWPointedEquiv hn ha2 (B, W)).1.1 =
      (diamondEvenPBSigma B, diamondEvenPWSigma W) := rfl

@[simp] theorem diamondEvenPBWPointedEquiv_apply_K
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (B : BFun4 n a c d) (W : WFun4 n a b c) :
    (diamondEvenPBWPointedEquiv hn ha2 (B, W)).1.2 =
      (diamondEvenPBK B, diamondEvenPWK W) := rfl

@[simp] theorem diamondEvenPBWPointedEquiv_apply_tail
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (t : PointedTail (PVec n a) (zeroVec : PVec n a)) :
    (diamondEvenPBWPointedEquiv hn ha2 (B, W)).2.1 t =
      (diamondEvenPBTail B t, diamondEvenPWTail W t) := rfl

private noncomputable def diamondEvenPBWSliceAt
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (p : PVec n a) : DiamondEvenPBWSlice n b c d :=
  (fun _q sy z w => B p sy z w,
    fun _q y z sw => W p y z sw)

private theorem squareCompat_sliceAt_apply
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (p : PVec n a) (q : PVec n 1)
    (y : YVec n b) (sz : I n) (w : WVec n d) :
    squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)
        (diamondEvenPBWSliceAt B W p) q y sz w =
      squareCompat
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (B, W) p y sz w := by
  rfl

private theorem prod_fst_fintype_sum
    {ι α β : Type*} [Fintype ι]
    [AddCommMonoid α] [AddCommMonoid β] (f : ι → α × β) :
    (∑ i, f i).1 = ∑ i, (f i).1 := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      simp [hi, hs]

private theorem prod_snd_fintype_sum
    {ι α β : Type*} [Fintype ι]
    [AddCommMonoid α] [AddCommMonoid β] (f : ι → α × β) :
    (∑ i, f i).2 = ∑ i, (f i).2 := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      simp [hi, hs]

theorem squareCompat_sigma_apply
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (q : PVec n 1) (y : YVec n b) (sz : I n) (w : WVec n d) :
    squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)
        (diamondEvenPBSigma B, diamondEvenPWSigma W) q y sz w =
      ∑ p : PVec n a,
        squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (B, W) p y sz w := by
  have hpair :
      (diamondEvenPBSigma B, diamondEvenPWSigma W) =
        ∑ p : PVec n a, diamondEvenPBWSliceAt B W p := by
    apply Prod.ext
    · funext q sy z w
      rw [prod_fst_fintype_sum]
      simp [diamondEvenPBSigma, diamondEvenPBWSliceAt]
    · funext q yy z sw
      rw [prod_snd_fintype_sum]
      simp [diamondEvenPWSigma, diamondEvenPBWSliceAt]
  rw [hpair]
  have hsum :=
    map_sum
      (squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)).toAddMonoidHom
      (fun p : PVec n a => diamondEvenPBWSliceAt B W p)
      Finset.univ
  have happ := congrFun (congrFun (congrFun (congrFun hsum q) y) sz) w
  calc
    _ =
        ∑ p : PVec n a,
          squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBWSliceAt B W p) q y sz w := by
              simpa only [Finset.sum_apply] using happ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      exact squareCompat_sliceAt_apply B W p q y sz w

theorem squareCompat_K_apply
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (q : PVec n 1) (y : YVec n b) (sz : I n) (w : WVec n d) :
    squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)
        (diamondEvenPBK B, diamondEvenPWK W) q y sz w =
      ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
        squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (B, W) t.1 y sz w := by
  have hpair :
      (diamondEvenPBK B, diamondEvenPWK W) =
        ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
          diamondEvenPBWSliceAt B W t.1 := by
    apply Prod.ext
    · funext q sy z w
      rw [prod_fst_fintype_sum]
      simp [diamondEvenPBK, diamondEvenPBWSliceAt]
    · funext q yy z sw
      rw [prod_snd_fintype_sum]
      simp [diamondEvenPWK, diamondEvenPBWSliceAt]
  rw [hpair]
  have hsum :=
    map_sum
      (squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)).toAddMonoidHom
      (fun t : PointedTail (PVec n a) (zeroVec : PVec n a) =>
        diamondEvenPBWSliceAt B W t.1)
      Finset.univ
  have happ := congrFun (congrFun (congrFun (congrFun hsum q) y) sz) w
  calc
    _ =
        ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
          squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBWSliceAt B W t.1) q y sz w := by
              simpa only [Finset.sum_apply] using happ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      exact squareCompat_sliceAt_apply B W t.1 q y sz w

theorem squareCompat_tail_apply
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (t : PointedTail (PVec n a) (zeroVec : PVec n a))
    (q : PVec n 1) (y : YVec n b) (sz : I n) (w : WVec n d) :
    squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)
        (diamondEvenPBTail B t, diamondEvenPWTail W t) q y sz w =
      squareCompat
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (B, W) t.1 y sz w +
        squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          (diamondEvenPBK B, diamondEvenPWK W) q y sz w := by
  have happ :=
    congrArg
      (fun C : CFun4 n 1 b d => C q y sz w)
      ((squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d)).map_add
          (diamondEvenPBWSliceAt B W t.1)
          (diamondEvenPBK B, diamondEvenPWK W))
  calc
    _ =
        squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBWSliceAt B W t.1) q y sz w +
          squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBK B, diamondEvenPWK W) q y sz w := by
              simpa only [diamondEvenPBTail, diamondEvenPWTail,
                Pi.add_apply] using happ
    _ = _ := by rw [squareCompat_sliceAt_apply]

theorem KBMap_eq_KBMap_sigma
    {n a b c d : Nat} [NeZero n]
    (B : BFun4 n a c d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B =
      KBMap (n := n) (a := 1) (b := b) (c := c) (d := d)
        (diamondEvenPBSigma
          (n := n) (a := a) (c := c) (d := d) B) := by
  funext y z w
  unfold KBMap dyB betaB gammaB diamondEvenPBSigma
  change
    (∑ p : PVec n a,
        (B p (vecSum y) z w + B p (vecSum y + 1) z w)) =
      ∑ q : PVec n 1,
        ((∑ p : PVec n a, B p (vecSum y) z w) +
          ∑ p : PVec n a, B p (vecSum y + 1) z w)
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · rw [Finset.sum_add_distrib]
  · intro q _ hq
    exact (hq (pVec_one_eq_zeroVec q)).elim
  · simp

theorem KWMap_eq_KWMap_sigma
    {n a b c d : Nat} [NeZero n]
    (W : WFun4 n a b c) :
    KWMap (n := n) (a := a) (b := b) (c := c) (d := d) W =
      KWMap (n := n) (a := 1) (b := b) (c := c) (d := d)
        (diamondEvenPWSigma
          (n := n) (a := a) (b := b) (c := c) W) := by
  funext y z w
  unfold KWMap dwW xiW zetaW diamondEvenPWSigma
  change
    (∑ p : PVec n a,
        (W p y z (vecSum w) + W p y z (vecSum w + 1))) =
      ∑ q : PVec n 1,
        ((∑ p : PVec n a, W p y z (vecSum w)) +
          ∑ p : PVec n a, W p y z (vecSum w + 1))
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · rw [Finset.sum_add_distrib]
  · intro q _ hq
    exact (hq (pVec_one_eq_zeroVec q)).elim
  · simp

theorem diamondEvenPAConstraint_apply_singleton
    {n a b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) (p : PVec n a) (q : PVec n 1)
    (y : YVec n b) (sz : I n) (w : WVec n d) :
    diamondEvenPAConstraint
        (n := n) (a := a) (b := b) (c := c) (d := d) A p y sz w =
      diamondEvenPAConstraint
        (n := n) (a := 1) (b := b) (c := c) (d := d) A q y sz w := by
  rfl

theorem diamondEvenP_source_equations_iff
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (A : AFun4 n b c d) (B : BFun4 n a c d)
    (W : WFun4 n a b c) :
    diamondPreCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (A, B, W) = 0 ↔
      squareCompat
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          (diamondEvenPBSigma
              (n := n) (a := a) (c := c) (d := d) B,
            diamondEvenPWSigma
              (n := n) (a := a) (b := b) (c := c) W) = 0 ∧
        diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d) A =
          squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBK
                (n := n) (a := a) (c := c) (d := d) B,
              diamondEvenPWK
                (n := n) (a := a) (b := b) (c := c) W) ∧
        ∀ t : PointedTail (PVec n a) (zeroVec : PVec n a),
          squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              (diamondEvenPBTail
                  (n := n) (a := a) (c := c) (d := d) B t,
                diamondEvenPWTail
                  (n := n) (a := a) (b := b) (c := c) W t) = 0 := by
  constructor
  · intro hsource
    have hconstraint :=
      (diamondPreCMap_eq_zero_iff_constraint
        (n := n) (a := a) (b := b) (c := c) (d := d) A B W).mp hsource
    have hSigma :
        squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBSigma B, diamondEvenPWSigma W) = 0 := by
      funext q y sz w
      rw [squareCompat_sigma_apply]
      calc
        (∑ p : PVec n a,
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (B, W) p y sz w)
            =
          ∑ _p : PVec n a,
            diamondEvenPAConstraint
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              A q y sz w := by
                apply Finset.sum_congr rfl
                intro p _
                have hp :=
                  congrFun
                    (congrFun
                      (congrFun (congrFun hconstraint p) y) sz) w
                calc
                  _ =
                      diamondEvenPAConstraint
                        (n := n) (a := a) (b := b) (c := c) (d := d)
                        A p y sz w := hp.symm
                  _ = _ :=
                    diamondEvenPAConstraint_apply_singleton A p q y sz w
        _ = 0 := by
          rw [Finset.sum_const, Finset.card_univ,
            ← Nat.cast_smul_eq_nsmul F,
            cast_card_eq_zero_of_even (even_card_PVec hn ha2), zero_smul]
    have hK :
        diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d) A =
          squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBK B, diamondEvenPWK W) := by
      funext q y sz w
      calc
        diamondEvenPAConstraint
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              A q y sz w
            =
          ∑ _t : PointedTail (PVec n a) (zeroVec : PVec n a),
            diamondEvenPAConstraint
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              A q y sz w :=
                (sum_tail_const_of_even
                  (zeroVec : PVec n a) (even_card_PVec hn ha2) _).symm
        _ =
          ∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
            squareCompat
              (n := n) (a := a) (b := b) (c := c) (d := d)
              (B, W) t.1 y sz w := by
                apply Finset.sum_congr rfl
                intro t _
                have ht :=
                  congrFun
                    (congrFun
                      (congrFun (congrFun hconstraint t.1) y) sz) w
                calc
                  _ =
                      diamondEvenPAConstraint
                        (n := n) (a := a) (b := b) (c := c) (d := d)
                        A t.1 y sz w :=
                          (diamondEvenPAConstraint_apply_singleton
                            A t.1 q y sz w).symm
                  _ = _ := ht
        _ =
          squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBK B, diamondEvenPWK W) q y sz w :=
              (squareCompat_K_apply B W q y sz w).symm
    have hTail :
        ∀ t : PointedTail (PVec n a) (zeroVec : PVec n a),
          squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              (diamondEvenPBTail B t, diamondEvenPWTail W t) = 0 := by
      intro t
      funext q y sz w
      rw [squareCompat_tail_apply]
      have ht :=
        congrFun
          (congrFun
            (congrFun (congrFun hconstraint t.1) y) sz) w
      have hk :=
        congrFun (congrFun (congrFun (congrFun hK q) y) sz) w
      rw [← ht, diamondEvenPAConstraint_apply_singleton A t.1 q y sz w,
        ← hk]
      exact F_add_self _
    exact ⟨hSigma, hK, hTail⟩
  · rintro ⟨hSigma, hK, hTail⟩
    apply
      (diamondPreCMap_eq_zero_iff_constraint
        (n := n) (a := a) (b := b) (c := c) (d := d) A B W).mpr
    funext p y sz w
    have hSigmaPoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hSigma (zeroVec : PVec n 1)) y) sz) w
    have hKPoint :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hK (zeroVec : PVec n 1)) y) sz) w
    have hsumAll :
        (∑ p' : PVec n a,
          squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (B, W) p' y sz w) = 0 := by
      rw [← squareCompat_sigma_apply B W
        (zeroVec : PVec n 1) y sz w]
      exact hSigmaPoint
    have hsumTail :
        (∑ t : PointedTail (PVec n a) (zeroVec : PVec n a),
          squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (B, W) t.1 y sz w) =
          diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            A (zeroVec : PVec n 1) y sz w := by
      calc
        _ =
          squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBK B, diamondEvenPWK W)
            (zeroVec : PVec n 1) y sz w :=
              (squareCompat_K_apply B W
                (zeroVec : PVec n 1) y sz w).symm
        _ = _ := hKPoint.symm
    by_cases hp : p = (zeroVec : PVec n a)
    · subst p
      rw [sum_eq_at_point_add_tail (zeroVec : PVec n a)] at hsumAll
      rw [hsumTail] at hsumAll
      have hlocal :=
        (add_eq_zero_iff_eq_of_F_module
          (squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (B, W) (zeroVec : PVec n a) y sz w)
          (diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            A (zeroVec : PVec n 1) y sz w)).mp hsumAll
      calc
        _ =
          diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            A (zeroVec : PVec n 1) y sz w :=
              diamondEvenPAConstraint_apply_singleton
                A (zeroVec : PVec n a) (zeroVec : PVec n 1) y sz w
        _ = _ := hlocal.symm
    · let t : PointedTail (PVec n a) (zeroVec : PVec n a) := ⟨p, hp⟩
      have hTailPoint :=
        congrFun
          (congrFun
            (congrFun
              (congrFun (hTail t) (zeroVec : PVec n 1)) y) sz) w
      rw [squareCompat_tail_apply] at hTailPoint
      rw [← hKPoint] at hTailPoint
      have hlocal :=
        (add_eq_zero_iff_eq_of_F_module
          (squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (B, W) p y sz w)
          (diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            A (zeroVec : PVec n 1) y sz w)).mp hTailPoint
      calc
        _ =
          diamondEvenPAConstraint
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            A (zeroVec : PVec n 1) y sz w :=
              diamondEvenPAConstraint_apply_singleton
                A p (zeroVec : PVec n 1) y sz w
        _ = _ := hlocal.symm

set_option linter.unusedVariables false in
theorem diamondEvenP_q_reads_sigma_only
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (x : DiamondPreCSource n a b c d) :
    diamondPreCQ x =
      coeffApplyA
        (KBMap
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPBSigma
              (n := n) (a := a) (c := c) (d := d)
              x.1.2.1) +
          KWMap
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            (diamondEvenPWSigma
              (n := n) (a := a) (b := b) (c := c)
              x.1.2.2))
        x.1.1 := by
  rw [diamondPreCQ, KBMap_eq_KBMap_sigma, KWMap_eq_KWMap_sigma]

noncomputable def fintypeSumLinearMap
    {S V : Type*} [Fintype S] [AddCommMonoid V] [Module F V] :
    (S → V) →ₗ[F] V where
  toFun f := ∑ s, f s
  map_add' f g := by
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]

theorem fintypeSumLinearMap_surjective
    {S V : Type*} [Fintype S] [Nonempty S]
    [AddCommGroup V] [Module F V] :
    Function.Surjective
      (fintypeSumLinearMap (S := S) (V := V)) := by
  classical
  intro v
  let ⟨s0⟩ := ‹Nonempty S›
  refine ⟨Pi.single s0 v, ?_⟩
  simp [fintypeSumLinearMap]

theorem finrank_ker_fintype_sum
    {S V : Type*} [Fintype S] [Nonempty S]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] :
    Module.finrank F
        (LinearMap.ker (fintypeSumLinearMap (S := S) (V := V))) +
      Module.finrank F V =
        Fintype.card S * Module.finrank F V := by
  let L := fintypeSumLinearMap (S := S) (V := V)
  have hrange : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr
      (fintypeSumLinearMap_surjective (S := S) (V := V))
  have h := LinearMap.finrank_range_add_finrank_ker L
  rw [hrange, finrank_top] at h
  change
      Module.finrank F V +
          Module.finrank F
            (LinearMap.ker (fintypeSumLinearMap (S := S) (V := V))) =
        Module.finrank F (S → V) at h
  rw [Module.finrank_pi_fintype] at h
  simpa [add_comm] using h

end

end Core4loop.SquareDiagonal.EvenP
