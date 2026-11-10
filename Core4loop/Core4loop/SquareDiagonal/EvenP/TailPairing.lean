import Core4loop.SquareDiagonal.EvenP.CrossProjection
import Core4loop.SquareDiagonal.EvenP.PointedValueNormalForm

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

abbrev DiamondEvenAxisTailIndex (n k : Nat) :=
  PointedTail (PVec n k) (zeroVec : PVec n k)

noncomputable abbrev DiamondEvenAxisTailZero
    (n k : Nat) [NeZero n] :=
  PointedValueTailZero
    (PVec n k) F (zeroVec : PVec n k)

noncomputable abbrev DiamondEvenAxisValueTailZero
    (n k : Nat) [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :=
  PointedValueTailZero
    (PVec n k) V (zeroVec : PVec n k)

theorem diamondEvenAxisTailIndex_eq_diamondEvenPTailIndex
    {n k : Nat} [NeZero n] :
    DiamondEvenAxisTailIndex n k = DiamondEvenPTailIndex n k := rfl

theorem diamondEvenAxisTailIndex_nonempty
    {n k : Nat} [NeZero n]
    (hn : Even n) (hk2 : 2 ≤ k) :
    Nonempty (DiamondEvenAxisTailIndex n k) := by
  exact diamondEvenPTailIndex_nonempty hn hk2

private theorem card_diamondEvenAxisTailIndex
    {n k : Nat} [NeZero n] :
    Fintype.card (DiamondEvenAxisTailIndex n k) =
      n ^ (k - 1) - 1 := by
  have htailNatCard :
      Nat.card
          (PointedTail (PVec n k) (zeroVec : PVec n k)) =
        Nat.card (PVec n k) - 1 := by
    simpa only [← Nat.card_eq_fintype_card] using
      (card_pointedTail (zeroVec : PVec n k))
  calc
    Fintype.card (DiamondEvenAxisTailIndex n k) =
        Nat.card (DiamondEvenAxisTailIndex n k) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (PVec n k) - 1 := by
      simpa only [DiamondEvenAxisTailIndex] using htailNatCard
    _ = Fintype.card (PVec n k) - 1 := by
      rw [Nat.card_eq_fintype_card]
    _ = n ^ (k - 1) - 1 := by
      rw [card_vec]

theorem odd_card_diamondEvenAxisTailIndex
    {n k : Nat} [NeZero n]
    (hn : Even n) (hk2 : 2 ≤ k) :
    Odd (Fintype.card (DiamondEvenAxisTailIndex n k)) := by
  rw [card_diamondEvenAxisTailIndex]
  have heven : Even (n ^ (k - 1)) :=
    Even.pow_of_ne_zero hn (Nat.sub_ne_zero_of_lt hk2)
  rcases heven with ⟨m, hm⟩
  have hpowpos : 0 < n ^ (k - 1) :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne n)) _
  refine ⟨m - 1, ?_⟩
  omega

theorem finrank_diamondEvenAxisValueTailZero_add
    {n k : Nat} [NeZero n]
    (_hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k)
    (V : Type*) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Module.finrank F
        (DiamondEvenAxisValueTailZero n k V)
      + Module.finrank F V
      =
    (n ^ (k - 1) - 1) * Module.finrank F V := by
  letI : Nonempty (DiamondEvenAxisTailIndex n k) :=
    diamondEvenPTailIndex_nonempty hn hk2
  have h :=
    finrank_ker_fintype_sum
      (S := DiamondEvenAxisTailIndex n k) (V := V)
  change
    Module.finrank F (DiamondEvenAxisValueTailZero n k V) +
        Module.finrank F V =
      Fintype.card (DiamondEvenAxisTailIndex n k) *
        Module.finrank F V at h
  rw [card_diamondEvenAxisTailIndex] at h
  exact h

theorem finrank_diamondEvenAxisTailZero_add_two
    {n k : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k) :
    Module.finrank F (DiamondEvenAxisTailZero n k) + 2 =
      n ^ (k - 1) := by
  have h :=
    finrank_diamondEvenAxisValueTailZero_add
      (n := n) (k := k) hn2 hn hk2 F
  change
    Module.finrank F (DiamondEvenAxisTailZero n k) +
        Module.finrank F F =
      (n ^ (k - 1) - 1) * Module.finrank F F at h
  simp only [Module.finrank_self, mul_one] at h
  have hpow : 2 ≤ n ^ (k - 1) := by
    have hkpos : 0 < k - 1 := by omega
    exact hn2.trans (Nat.le_pow hkpos)
  omega

theorem finrank_diamondEvenAxisTailZero
    {n k : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k) :
    Module.finrank F (DiamondEvenAxisTailZero n k) =
      n ^ (k - 1) - 2 := by
  have h :=
    finrank_diamondEvenAxisTailZero_add_two
      (n := n) (k := k) hn2 hn hk2
  omega

noncomputable def diamondTailAmplify
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V) :
    DiamondEvenAxisValueTailZero n k U →ₗ[F]
      Module.Dual F (DiamondEvenAxisValueTailZero n k V) :=
  LinearMap.mk₂ F
    (fun u v => ∑ t, f (u.1 t) (v.1 t))
    (by
      intro u u' v
      simp only [Submodule.coe_add, Pi.add_apply, map_add,
        LinearMap.add_apply, Finset.sum_add_distrib])
    (by
      intro r u v
      simp only [SetLike.val_smul, Pi.smul_apply, map_smul,
        LinearMap.smul_apply, Finset.smul_sum])
    (by
      intro u v v'
      simp only [Submodule.coe_add, Pi.add_apply, map_add,
        Finset.sum_add_distrib])
    (by
      intro r u v
      simp only [SetLike.val_smul, Pi.smul_apply, map_smul,
        Finset.smul_sum])

@[simp] theorem diamondTailAmplify_apply
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V)
    (u : DiamondEvenAxisValueTailZero n k U)
    (v : DiamondEvenAxisValueTailZero n k V) :
    diamondTailAmplify f u v =
      ∑ t, f (u.1 t) (v.1 t) :=
  rfl

private theorem cast_card_eq_one_of_odd
    {m : Nat} (hm : Odd m) : (m : F) = 1 := by
  rcases hm with ⟨q, hq⟩
  rw [hq]
  push_cast
  rw [show (2 : F) = 0 by decide]
  simp

private theorem sum_const_of_odd
    {T W : Type*} [Fintype T]
    [AddCommGroup W] [Module F W]
    (hodd : Odd (Fintype.card T)) (w : W) :
    (∑ _ : T, w) = w := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul F,
    cast_card_eq_one_of_odd hodd, one_smul]

theorem diamondTailAmplify_eq_zero_iff
    {n k : Nat} [NeZero n]
    (_hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k)
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V)
    (u : DiamondEvenAxisValueTailZero n k U) :
    diamondTailAmplify (n := n) (k := k) f u = 0 ↔
      ∀ t, f (u.1 t) = 0 := by
  classical
  constructor
  · intro hz
    rcases diamondEvenAxisTailIndex_nonempty hn hk2 with ⟨t0⟩
    have hconst :
        ∀ t : DiamondEvenAxisTailIndex n k,
          f (u.1 t) = f (u.1 t0) := by
      intro t
      by_cases ht : t = t0
      · exact congrArg (fun q => f (u.1 q)) ht
      · apply LinearMap.ext
        intro v
        let testFun : DiamondEvenAxisTailIndex n k → V :=
          fun q => if q = t then v else if q = t0 then v else 0
        have htestFun :
            testFun =
              fun q =>
                (if t = q then v else 0) +
                  (if t0 = q then v else 0) := by
          funext q
          by_cases hqt : q = t
          · subst q
            simp [testFun, Ne.symm ht]
          · by_cases hqt0 : q = t0
            · subst q
              simp [testFun, hqt, ht]
            · simp [testFun, hqt, hqt0, Ne.symm hqt, Ne.symm hqt0]
        let test : DiamondEvenAxisValueTailZero n k V :=
          ⟨testFun, by
            apply LinearMap.mem_ker.mpr
            change (∑ q, testFun q) = 0
            rw [htestFun, Finset.sum_add_distrib]
            simp only [Fintype.sum_ite_eq]
            exact (add_eq_zero_iff_eq_of_F_module v v).2 rfl⟩
        have hpair :=
          congrArg
            (fun phi :
              Module.Dual F (DiamondEvenAxisValueTailZero n k V) =>
                phi test)
            hz
        change (∑ q, f (u.1 q) (testFun q)) = 0 at hpair
        rw [htestFun] at hpair
        simp_rw [map_add] at hpair
        rw [Finset.sum_add_distrib] at hpair
        simp only [apply_ite, map_zero, Fintype.sum_ite_eq] at hpair
        have hadd := congrArg
          (fun z : F => z + f (u.1 t0) v) hpair
        simpa [add_assoc, F_add_self] using hadd
    have hsumF :
        (∑ t : DiamondEvenAxisTailIndex n k, f (u.1 t)) = 0 := by
      calc
        (∑ t : DiamondEvenAxisTailIndex n k, f (u.1 t)) =
            f (∑ t : DiamondEvenAxisTailIndex n k, u.1 t) := by
              rw [map_sum]
        _ = f 0 := by rw [pointedValueTailZero_sum u]
        _ = 0 := map_zero f
    intro t
    calc
      f (u.1 t) =
          ∑ _q : DiamondEvenAxisTailIndex n k, f (u.1 t) :=
        (sum_const_of_odd
          (odd_card_diamondEvenAxisTailIndex hn hk2)
          (f (u.1 t))).symm
      _ = ∑ q : DiamondEvenAxisTailIndex n k, f (u.1 q) := by
        apply Finset.sum_congr rfl
        intro q _
        exact (hconst t).trans (hconst q).symm
      _ = 0 := hsumF
  · intro hall
    apply LinearMap.ext
    intro v
    rw [diamondTailAmplify_apply]
    apply Finset.sum_eq_zero
    intro t _
    rw [hall t]
    rfl

noncomputable def diamondTailAmplifyKernelEquiv
    {n k : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k)
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V) :
    LinearMap.ker
        (diamondTailAmplify (n := n) (k := k) f)
      ≃ₗ[F]
    DiamondEvenAxisValueTailZero n k (LinearMap.ker f) where
  toFun x :=
    ⟨fun t =>
      ⟨x.1.1 t,
        (diamondTailAmplify_eq_zero_iff hn2 hn hk2 f x.1).mp x.2 t⟩,
      by
        apply LinearMap.mem_ker.mpr
        change
          (∑ t : DiamondEvenAxisTailIndex n k,
            (⟨x.1.1 t,
              (diamondTailAmplify_eq_zero_iff
                hn2 hn hk2 f x.1).mp x.2 t⟩ :
              LinearMap.ker f)) = 0
        apply Subtype.ext
        simpa only [Submodule.coe_sum] using
          pointedValueTailZero_sum x.1⟩
  invFun y :=
    ⟨⟨fun t => (y.1 t).1, by
        apply LinearMap.mem_ker.mpr
        have hy := pointedValueTailZero_sum y
        simpa only [Submodule.coe_sum] using
          congrArg Subtype.val hy⟩,
      (diamondTailAmplify_eq_zero_iff hn2 hn hk2 f _).mpr
        (fun t => (y.1 t).2)⟩
  map_add' x y := by
    apply Subtype.ext
    funext t
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    funext t
    apply Subtype.ext
    rfl
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    funext t
    apply Subtype.ext
    rfl

noncomputable abbrev diamondScalarDot :
    F →ₗ[F] Module.Dual F F :=
  pointedValueScalarDot

noncomputable def diamondTailZeroDot
    {n k : Nat} [NeZero n] :
    DiamondEvenAxisTailZero n k →ₗ[F]
      Module.Dual F (DiamondEvenAxisTailZero n k) :=
  diamondTailAmplify (n := n) (k := k) diamondScalarDot

theorem diamondTailZeroDot_injective
    {n k : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k) :
    Function.Injective (diamondTailZeroDot (n := n) (k := k)) := by
  rw [← LinearMap.ker_eq_bot]
  ext x
  constructor
  · intro hx
    simp only [Submodule.mem_bot]
    apply Subtype.ext
    funext t
    have hcomponents :=
      (diamondTailAmplify_eq_zero_iff
        hn2 hn hk2 diamondScalarDot x).mp hx
    have ht := congrArg
      (fun phi : Module.Dual F F => phi 1) (hcomponents t)
    change x.1 t * 1 = 0 at ht
    simpa using ht
  · intro hx
    rw [Submodule.mem_bot] at hx
    subst x
    exact LinearMap.mem_ker.mpr (map_zero _)

noncomputable def diamondTailZeroDotEquiv
    {n k : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k) :
    DiamondEvenAxisTailZero n k ≃ₗ[F]
      Module.Dual F (DiamondEvenAxisTailZero n k) := by
  let f := diamondTailZeroDot (n := n) (k := k)
  have hinj : Function.Injective f :=
    diamondTailZeroDot_injective hn2 hn hk2
  have hfin :
      Module.finrank F (DiamondEvenAxisTailZero n k) =
        Module.finrank F
          (Module.Dual F (DiamondEvenAxisTailZero n k)) :=
    Subspace.dual_finrank_eq.symm
  exact LinearEquiv.ofBijective f
    ⟨hinj,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
        hinj⟩

private theorem finrank_diamondEvenAxisValueTailZero_mul
    {n k : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k)
    (V : Type*) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Module.finrank F (DiamondEvenAxisValueTailZero n k V) =
      Module.finrank F (DiamondEvenAxisTailZero n k) *
        Module.finrank F V := by
  have hV :=
    finrank_diamondEvenAxisValueTailZero_add
      (n := n) (k := k) hn2 hn hk2 V
  have hH :=
    finrank_diamondEvenAxisTailZero_add_two
      (n := n) (k := k) hn2 hn hk2
  have hsub :
      n ^ (k - 1) - 1 =
        Module.finrank F (DiamondEvenAxisTailZero n k) + 1 := by
    omega
  rw [hsub, Nat.add_mul, one_mul] at hV
  exact Nat.add_right_cancel hV

theorem finrank_range_diamondTailAmplify
    {n k : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n) (hk2 : 2 ≤ k)
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V) :
    Module.finrank F
        (LinearMap.range
          (diamondTailAmplify (n := n) (k := k) f))
      =
    Module.finrank F (DiamondEvenAxisTailZero n k) *
      Module.finrank F (LinearMap.range f) := by
  let hker :=
    diamondTailAmplifyKernelEquiv
      (n := n) (k := k) hn2 hn hk2 f
  have hamp :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondTailAmplify (n := n) (k := k) f)
  have hkerFin := LinearEquiv.finrank_eq hker
  have hdom :=
    finrank_diamondEvenAxisValueTailZero_mul
      (n := n) (k := k) hn2 hn hk2 U
  have hkerDom :=
    finrank_diamondEvenAxisValueTailZero_mul
      (n := n) (k := k) hn2 hn hk2 (LinearMap.ker f)
  rw [hkerFin, hdom, hkerDom] at hamp
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hscaled := congrArg
    (fun q : Nat =>
      Module.finrank F (DiamondEvenAxisTailZero n k) * q) hf
  change
    Module.finrank F (DiamondEvenAxisTailZero n k) *
          (Module.finrank F (LinearMap.range f) +
            Module.finrank F (LinearMap.ker f)) =
      Module.finrank F (DiamondEvenAxisTailZero n k) *
        Module.finrank F U at hscaled
  rw [Nat.mul_add] at hscaled
  omega

noncomputable abbrev DiamondMixedTailZero
    (n k l : Nat) [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V] :=
  DiamondEvenAxisValueTailZero n k
    (DiamondEvenAxisValueTailZero n l V)

noncomputable def diamondMixedTailAmplify
    {n k l : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V) :
    DiamondMixedTailZero n k l U →ₗ[F]
      Module.Dual F (DiamondMixedTailZero n k l V) :=
  diamondTailAmplify
    (n := n) (k := k)
    (U := DiamondEvenAxisValueTailZero n l U)
    (V := DiamondEvenAxisValueTailZero n l V)
    (diamondTailAmplify (n := n) (k := l) f)

theorem finrank_range_diamondMixedTailAmplify
    {n k l : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hk2 : 2 ≤ k) (hl2 : 2 ≤ l)
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V]
    (f : U →ₗ[F] Module.Dual F V) :
    Module.finrank F
        (LinearMap.range
          (diamondMixedTailAmplify
            (n := n) (k := k) (l := l) f))
      =
    Module.finrank F (DiamondEvenAxisTailZero n k) *
      Module.finrank F (DiamondEvenAxisTailZero n l) *
      Module.finrank F (LinearMap.range f) := by
  change
    Module.finrank F
        (LinearMap.range
          (diamondTailAmplify
            (n := n) (k := k)
            (U := DiamondEvenAxisValueTailZero n l U)
            (V := DiamondEvenAxisValueTailZero n l V)
            (diamondTailAmplify (n := n) (k := l) f))) =
      Module.finrank F (DiamondEvenAxisTailZero n k) *
        Module.finrank F (DiamondEvenAxisTailZero n l) *
          Module.finrank F (LinearMap.range f)
  rw [finrank_range_diamondTailAmplify
      (n := n) (k := k) hn2 hn hk2
      (diamondTailAmplify (n := n) (k := l) f)]
  rw [finrank_range_diamondTailAmplify
      (n := n) (k := l) hn2 hn hl2 f]
  simp only [Nat.mul_assoc]

noncomputable def diamondCrossProd
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommGroup U₁] [Module F U₁]
    [AddCommGroup U₂] [Module F U₂]
    [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂) :
    (U₁ × U₂) →ₗ[F] Module.Dual F (V₁ × V₂) :=
  (Module.dualProdDualEquivDual F V₁ V₂).toLinearMap.comp
    (f.prodMap g)

private def diamondSubmoduleProdEquiv
    {M N : Type*}
    [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N]
    (p : Submodule F M) (q : Submodule F N) :
    p.prod q ≃ₗ[F] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def diamondCrossProdRangeEquiv
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommGroup U₁] [Module F U₁]
    [AddCommGroup U₂] [Module F U₂]
    [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂) :
  LinearMap.range (diamondCrossProd f g) ≃ₗ[F]
    LinearMap.range f × LinearMap.range g := by
  let E := Module.dualProdDualEquivDual F V₁ V₂
  have hmap :
      (LinearMap.range (f.prodMap g)).map E.toLinearMap =
        LinearMap.range (diamondCrossProd f g) := by
    simpa only [diamondCrossProd, E] using
      (LinearMap.range_comp (f.prodMap g) E.toLinearMap).symm
  exact
    ((E.ofSubmodules
        (LinearMap.range (f.prodMap g))
        (LinearMap.range (diamondCrossProd f g))
        hmap).symm).trans
      ((LinearEquiv.ofEq _ _
        (LinearMap.range_prodMap f g)).trans
        (diamondSubmoduleProdEquiv
          (LinearMap.range f) (LinearMap.range g)))

theorem finrank_range_diamondCrossProd
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommGroup U₁] [Module F U₁] [FiniteDimensional F U₁]
    [AddCommGroup U₂] [Module F U₂] [FiniteDimensional F U₂]
    [AddCommGroup V₁] [Module F V₁]
    [AddCommGroup V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂) :
    Module.finrank F (LinearMap.range (diamondCrossProd f g)) =
      Module.finrank F (LinearMap.range f) +
        Module.finrank F (LinearMap.range g) := by
  calc
    Module.finrank F (LinearMap.range (diamondCrossProd f g)) =
        Module.finrank F
          (LinearMap.range f × LinearMap.range g) :=
      LinearEquiv.finrank_eq (diamondCrossProdRangeEquiv f g)
    _ = Module.finrank F (LinearMap.range f) +
          Module.finrank F (LinearMap.range g) :=
      Module.finrank_prod

end

end Core4loop.SquareDiagonal.EvenP
