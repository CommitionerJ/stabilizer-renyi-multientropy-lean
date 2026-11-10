import Core4loop.SquareDiagonal.DirectWitt.OddConstrainedQZero
import Core4loop.SquareDiagonal.DirectWitt.OddFamilyCross
import Core4loop.SquareDiagonal.EvenP.TailPrototypeBlocks

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.SquareDiagonal.DirectWitt

open Core4loop
open Core4loop.SquareDiagonal.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite

noncomputable local instance prototypeCyclicCubeFintype
    {n : Nat} [NeZero n] : Fintype (CyclicCube n) :=
  Fintype.ofFinite _

private theorem card_diamondOddAxisTail
    {n k : Nat} [NeZero n] :
    Fintype.card (DiamondOddAxisTail n k) =
      n ^ (k - 1) - 1 := by
  have htailNatCard :
      Nat.card
          (PointedTail (PVec n k) (zeroVec : PVec n k)) =
        Nat.card (PVec n k) - 1 := by
    simpa only [← Nat.card_eq_fintype_card] using
      (card_pointedTail (zeroVec : PVec n k))
  calc
    Fintype.card (DiamondOddAxisTail n k) =
        Nat.card (DiamondOddAxisTail n k) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (PVec n k) - 1 := by
      simpa only [DiamondOddAxisTail] using htailNatCard
    _ = Fintype.card (PVec n k) - 1 := by
      rw [Nat.card_eq_fintype_card]
    _ = n ^ (k - 1) - 1 := by
      rw [card_vec]

private noncomputable def diamondOddAxisTailJEquiv
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    (hn : Odd n) :
    (DiamondOddAxisTail n k → V) ≃ₗ[F]
      (DiamondOddAxisTail n k → V) where
  toLinearMap := diamondOddAxisTailJ V
  invFun := diamondOddAxisTailJ V
  left_inv := diamondOddAxisTailJ_sq_apply V hn
  right_inv := diamondOddAxisTailJ_sq_apply V hn

private noncomputable def diamondOddTensorTailJLinear
    {S T V : Type*} [Fintype S] [Fintype T]
    (s0 : S) (t0 : T)
    [AddCommGroup V] [Module F V] :
    (PointedTail S s0 → PointedTail T t0 → V) →ₗ[F]
      (PointedTail S s0 → PointedTail T t0 → V) where
  toFun f := diamondOddTensorTailJ s0 t0 f
  map_add' f g := by
    funext s t
    simp only [diamondOddTensorTailJ_apply, Pi.add_apply,
      Finset.sum_add_distrib]
    abel
  map_smul' r f := by
    funext s t
    simp only [diamondOddTensorTailJ_apply, Pi.smul_apply,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

private noncomputable def diamondOddTensorTailJEquiv
    {S T V : Type*} [Fintype S] [Fintype T]
    (s0 : S) (t0 : T)
    [AddCommGroup V] [Module F V]
    (hS : Odd (Fintype.card S))
    (hT : Odd (Fintype.card T)) :
    (PointedTail S s0 → PointedTail T t0 → V) ≃ₗ[F]
      (PointedTail S s0 → PointedTail T t0 → V) where
  toLinearMap := diamondOddTensorTailJLinear s0 t0
  invFun := diamondOddTensorTailJ s0 t0
  left_inv := diamondOddTensorTailJ_sq_apply s0 t0 hS hT
  right_inv := diamondOddTensorTailJ_sq_apply s0 t0 hS hT

private theorem cubeDot_comm_local
    {n : Nat} [NeZero n] (x y : CyclicCube n) :
    cubeDot x y = cubeDot y x := by
  unfold cubeDot
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_comm]

noncomputable def diamondOddSSTSCross
    {n c : Nat} [NeZero n] (hn : Odd n) :
    (DiamondOddAxisTail n c →
        DiamondEOOOLeftAmbient n) →ₗ[F]
      Module.Dual F
        (DiamondOddAxisTail n c → CyclicCube n) :=
  (diamondOddFamilyCross
      (T := DiamondOddAxisTail n c)
      (diamondTailFreeStarCross (n := n))).comp
    (diamondOddAxisTailJEquiv
      (DiamondEOOOLeftAmbient n) hn).toLinearMap

@[simp] theorem diamondOddSSTSCross_apply
    {n c : Nat} [NeZero n] (hn : Odd n)
    (u : DiamondOddAxisTail n c →
      DiamondEOOOLeftAmbient n)
    (A : DiamondOddAxisTail n c → CyclicCube n) :
    diamondOddSSTSCross hn u A =
      ∑ zt, diamondTailFreeStarCross
        (diamondOddAxisTailJ
          (DiamondEOOOLeftAmbient n) u zt)
        (A zt) :=
  rfl

private theorem diamondOddAxisTailJ_fst
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (u : DiamondOddAxisTail n k → U × V)
    (t : DiamondOddAxisTail n k) :
    (diamondOddAxisTailJ (U × V) u t).1 =
      diamondOddAxisTailJ U (fun s => (u s).1) t := by
  simp only [diamondOddAxisTailJ_apply, Prod.fst_add]
  change
    (u t).1 + (LinearMap.fst F U V) (∑ v, u v) =
      (u t).1 + ∑ s, (LinearMap.fst F U V) (u s)
  rw [map_sum]

private theorem diamondOddAxisTailJ_snd
    {n k : Nat} [NeZero n]
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (u : DiamondOddAxisTail n k → U × V)
    (t : DiamondOddAxisTail n k) :
    (diamondOddAxisTailJ (U × V) u t).2 =
      diamondOddAxisTailJ V (fun s => (u s).2) t := by
  simp only [diamondOddAxisTailJ_apply, Prod.snd_add]
  change
    (u t).2 + (LinearMap.snd F U V) (∑ v, u v) =
      (u t).2 + ∑ s, (LinearMap.snd F U V) (u s)
  rw [map_sum]

theorem diamondOddPointedPhaseSSTS_eq_cross
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (v : DiamondOddPointedAmbient n a b c d) :
    diamondOddPointedPhaseSSTS v =
      diamondOddSSTSCross hn
        (fun zt =>
          (v.2.1 diamondOddChannelS
              (diamondOddChannelT zt) diamondOddChannelS,
            v.2.2 diamondOddChannelS diamondOddChannelS
              (diamondOddChannelT zt)))
        (fun zt =>
          v.1 diamondOddChannelS
            (diamondOddChannelT zt) diamondOddChannelS) := by
  rw [diamondOddSSTSCross_apply]
  apply Finset.sum_congr rfl
  intro zt _
  rw [cubeDot_comm_local]
  change
    cubeDot
      (cubeDiffI
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' =>
              v.2.1 diamondOddChannelS
                (diamondOddChannelT zt')
                diamondOddChannelS) zt) +
        cubeDiffK
          (diamondOddAxisTailJ (CyclicCube n)
            (fun zt' =>
              v.2.2 diamondOddChannelS diamondOddChannelS
                (diamondOddChannelT zt')) zt))
      _ =
    cubeDot
      (cubeDiffI
          (diamondOddAxisTailJ
            (DiamondEOOOLeftAmbient n)
            (fun zt' =>
              (v.2.1 diamondOddChannelS
                  (diamondOddChannelT zt')
                  diamondOddChannelS,
                v.2.2 diamondOddChannelS diamondOddChannelS
                  (diamondOddChannelT zt'))) zt).1 +
        cubeDiffK
          (diamondOddAxisTailJ
            (DiamondEOOOLeftAmbient n)
            (fun zt' =>
              (v.2.1 diamondOddChannelS
                  (diamondOddChannelT zt')
                  diamondOddChannelS,
                v.2.2 diamondOddChannelS diamondOddChannelS
                  (diamondOddChannelT zt'))) zt).2)
      _
  rw [diamondOddAxisTailJ_fst, diamondOddAxisTailJ_snd]

theorem rank_diamondOddSSTSCross
    {n c : Nat} [NeZero n] (hn : Odd n) :
    Module.finrank F
        (LinearMap.range
          (diamondOddSSTSCross (c := c) hn)) =
      (n ^ (c - 1) - 1) *
        (n * (n - 1) * (n + 1)) := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondOddSSTSCross (c := c) hn)) =
        Module.finrank F
          (LinearMap.range
            (diamondOddFamilyCross
              (T := DiamondOddAxisTail n c)
              (diamondTailFreeStarCross (n := n)))) := by
      rw [diamondOddSSTSCross,
        LinearMap.range_comp_of_range_eq_top _
          (LinearEquiv.range
            (diamondOddAxisTailJEquiv
              (DiamondEOOOLeftAmbient n) hn))]
    _ = Fintype.card (DiamondOddAxisTail n c) *
          Module.finrank F
            (LinearMap.range
              (diamondTailFreeStarCross (n := n))) :=
      finrank_range_diamondOddFamilyCross
        (diamondTailFreeStarCross (n := n))
    _ = (n ^ (c - 1) - 1) *
          (n * (n - 1) * (n + 1)) := by
      rw [card_diamondOddAxisTail,
        rank_diamondTailFreeStarCross]

noncomputable def diamondOddSSTTCross
    {n c d : Nat} [NeZero n] (hn : Odd n) :
    (DiamondOddAxisTail n c →
        DiamondOddAxisTail n d → CyclicCube n) →ₗ[F]
      Module.Dual F
        (DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n) :=
  (diamondOddFamilyCross
      (T := DiamondOddAxisTail n c)
      (diamondOddFamilyCross
        (T := DiamondOddAxisTail n d)
        (diamondTailSingleICross (n := n)))).comp
    (diamondOddTensorTailJEquiv
      (zeroVec : PVec n c) (zeroVec : PVec n d)
      (odd_card_PVec hn) (odd_card_PVec hn)).toLinearMap

@[simp] theorem diamondOddSSTTCross_apply
    {n c d : Nat} [NeZero n] (hn : Odd n)
    (B A : DiamondOddAxisTail n c →
      DiamondOddAxisTail n d → CyclicCube n) :
    diamondOddSSTTCross hn B A =
      ∑ zt, ∑ wt,
        diamondTailSingleICross
          (diamondOddTensorTailJ
            (zeroVec : PVec n c) (zeroVec : PVec n d)
            B zt wt)
          (A zt wt) :=
  rfl

theorem diamondOddPointedPhaseSSTT_eq_cross
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (v : DiamondOddPointedAmbient n a b c d) :
    diamondOddPointedPhaseSSTT v =
      diamondOddSSTTCross hn
        (fun zt wt =>
          v.2.1 diamondOddChannelS
            (diamondOddChannelT zt)
            (diamondOddChannelT wt))
        (fun zt wt =>
          v.1 diamondOddChannelS
            (diamondOddChannelT zt)
            (diamondOddChannelT wt)) := by
  rw [diamondOddSSTTCross_apply]
  apply Finset.sum_congr rfl
  intro zt _
  apply Finset.sum_congr rfl
  intro wt _
  rw [cubeDot_comm_local]
  rfl

theorem rank_diamondOddSSTTCross
    {n c d : Nat} [NeZero n] (hn : Odd n) :
    Module.finrank F
        (LinearMap.range
          (diamondOddSSTTCross (c := c) (d := d) hn)) =
      (n ^ (c - 1) - 1) *
        (n ^ (d - 1) - 1) *
          (n ^ 2 * (n - 1)) := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondOddSSTTCross (c := c) (d := d) hn)) =
        Module.finrank F
          (LinearMap.range
            (diamondOddFamilyCross
              (T := DiamondOddAxisTail n c)
              (diamondOddFamilyCross
                (T := DiamondOddAxisTail n d)
                (diamondTailSingleICross (n := n))))) := by
      rw [diamondOddSSTTCross,
        LinearMap.range_comp_of_range_eq_top _
          (LinearEquiv.range
            (diamondOddTensorTailJEquiv
              (zeroVec : PVec n c) (zeroVec : PVec n d)
              (odd_card_PVec hn) (odd_card_PVec hn)))]
    _ = Fintype.card (DiamondOddAxisTail n c) *
          (Fintype.card (DiamondOddAxisTail n d) *
            Module.finrank F
              (LinearMap.range
                (diamondTailSingleICross (n := n)))) := by
      rw [finrank_range_diamondOddFamilyCross,
        finrank_range_diamondOddFamilyCross]
    _ = (n ^ (c - 1) - 1) *
          (n ^ (d - 1) - 1) *
            (n ^ 2 * (n - 1)) := by
      rw [card_diamondOddAxisTail,
        card_diamondOddAxisTail,
        rank_diamondTailSingleICross]
      ring

noncomputable def diamondOddSTTSCross
    {n b c : Nat} [NeZero n] (hn : Odd n) :
    (DiamondOddAxisTail n b →
        DiamondOddAxisTail n c → CyclicCube n) →ₗ[F]
      Module.Dual F
        (DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n) :=
  (diamondOddFamilyCross
      (T := DiamondOddAxisTail n b)
      (diamondOddFamilyCross
        (T := DiamondOddAxisTail n c)
        (diamondTailSingleKCross (n := n)))).comp
    (diamondOddTensorTailJEquiv
      (zeroVec : PVec n b) (zeroVec : PVec n c)
      (odd_card_PVec hn) (odd_card_PVec hn)).toLinearMap

@[simp] theorem diamondOddSTTSCross_apply
    {n b c : Nat} [NeZero n] (hn : Odd n)
    (W A : DiamondOddAxisTail n b →
      DiamondOddAxisTail n c → CyclicCube n) :
    diamondOddSTTSCross hn W A =
      ∑ yt, ∑ zt,
        diamondTailSingleKCross
          (diamondOddTensorTailJ
            (zeroVec : PVec n b) (zeroVec : PVec n c)
            W yt zt)
          (A yt zt) :=
  rfl

theorem diamondOddPointedPhaseSTTS_eq_cross
    {n a b c d : Nat} [NeZero n] (hn : Odd n)
    (v : DiamondOddPointedAmbient n a b c d) :
    diamondOddPointedPhaseSTTS v =
      diamondOddSTTSCross hn
        (fun yt zt =>
          v.2.2 diamondOddChannelS
            (diamondOddChannelT yt)
            (diamondOddChannelT zt))
        (fun yt zt =>
          v.1 (diamondOddChannelT yt)
            (diamondOddChannelT zt)
            diamondOddChannelS) := by
  rw [diamondOddSTTSCross_apply]
  apply Finset.sum_congr rfl
  intro yt _
  apply Finset.sum_congr rfl
  intro zt _
  rw [cubeDot_comm_local]
  rfl

theorem rank_diamondOddSTTSCross
    {n b c : Nat} [NeZero n] (hn : Odd n) :
    Module.finrank F
        (LinearMap.range
          (diamondOddSTTSCross (b := b) (c := c) hn)) =
      (n ^ (b - 1) - 1) *
        (n ^ (c - 1) - 1) *
          (n ^ 2 * (n - 1)) := by
  calc
    Module.finrank F
        (LinearMap.range
          (diamondOddSTTSCross (b := b) (c := c) hn)) =
        Module.finrank F
          (LinearMap.range
            (diamondOddFamilyCross
              (T := DiamondOddAxisTail n b)
              (diamondOddFamilyCross
                (T := DiamondOddAxisTail n c)
                (diamondTailSingleKCross (n := n))))) := by
      rw [diamondOddSTTSCross,
        LinearMap.range_comp_of_range_eq_top _
          (LinearEquiv.range
            (diamondOddTensorTailJEquiv
              (zeroVec : PVec n b) (zeroVec : PVec n c)
              (odd_card_PVec hn) (odd_card_PVec hn)))]
    _ = Fintype.card (DiamondOddAxisTail n b) *
          (Fintype.card (DiamondOddAxisTail n c) *
            Module.finrank F
              (LinearMap.range
                (diamondTailSingleKCross (n := n)))) := by
      rw [finrank_range_diamondOddFamilyCross,
        finrank_range_diamondOddFamilyCross]
    _ = (n ^ (b - 1) - 1) *
          (n ^ (c - 1) - 1) *
            (n ^ 2 * (n - 1)) := by
      rw [card_diamondOddAxisTail,
        card_diamondOddAxisTail,
        rank_diamondTailSingleKCross]
      ring

/-! ## Generic full cross-polar and its true two-sided radical -/

private noncomputable def diamondOddCrossPolar
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    (U × V) →ₗ[F] Module.Dual F (U × V) where
  toFun x :=
    { toFun := fun y => L x.1 y.2 + L y.1 x.2
      map_add' := by
        intro y z
        simp only [Prod.fst_add, Prod.snd_add, map_add,
          LinearMap.add_apply]
        abel
      map_smul' := by
        intro r y
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
          RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp only [Prod.fst_add, Prod.snd_add, map_add,
      LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    abel
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring

@[simp] private theorem diamondOddCrossPolar_apply
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V)
    (x y : U × V) :
    diamondOddCrossPolar L x y =
      L x.1 y.2 + L y.1 x.2 :=
  rfl

private theorem diamondOddCrossPolar_eq_quadratic_polar
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V)
    (x y : U × V) :
    diamondOddCrossPolar L x y =
      L (x + y).1 (x + y).2 +
        L x.1 x.2 + L y.1 y.2 := by
  simp only [Prod.fst_add, Prod.snd_add, map_add,
    LinearMap.add_apply, diamondOddCrossPolar_apply]
  ring_nf
  rw [show (2 : F) = 0 by decide]
  simp

private theorem diamondOddCrossPolar_mem_ker_iff
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V)
    (x : U × V) :
    x ∈ LinearMap.ker (diamondOddCrossPolar L) ↔
      x.1 ∈ LinearMap.ker L ∧
        x.2 ∈ LinearMap.ker L.flip := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    constructor
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro v
      have hpoint :=
        LinearMap.congr_fun hx (0, v)
      simpa [diamondOddCrossPolar_apply] using hpoint
    · rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro u
      have hpoint :=
        LinearMap.congr_fun hx (u, 0)
      simpa [diamondOddCrossPolar_apply] using hpoint
  · rintro ⟨hu, hv⟩
    apply LinearMap.ext
    intro y
    rw [diamondOddCrossPolar_apply]
    have hu0 := LinearMap.mem_ker.mp hu
    have hv0 := LinearMap.mem_ker.mp hv
    rw [LinearMap.congr_fun hu0 y.2]
    change 0 + L.flip x.2 y.1 = 0
    rw [LinearMap.congr_fun hv0 y.1]
    simp

private theorem ker_diamondOddCrossPolar
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    LinearMap.ker (diamondOddCrossPolar L) =
      (LinearMap.ker L).prod (LinearMap.ker L.flip) := by
  ext x
  change
    x ∈ LinearMap.ker (diamondOddCrossPolar L) ↔
      x.1 ∈ LinearMap.ker L ∧
        x.2 ∈ LinearMap.ker L.flip
  exact diamondOddCrossPolar_mem_ker_iff L x

private theorem finrank_range_flip_eq
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F (LinearMap.range L.flip) =
      Module.finrank F (LinearMap.range L) := by
  change
    Module.finrank F
        (LinearMap.range
          (L.dualMap.comp
            (Module.evalEquiv F V).toLinearMap)) =
      Module.finrank F (LinearMap.range L)
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (Module.evalEquiv F V))]
  exact
    LinearMap.finrank_range_dualMap_eq_finrank_range L

private noncomputable def diamondOddCrossPolarKerEquiv
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (L : U →ₗ[F] Module.Dual F V) :
    LinearMap.ker (diamondOddCrossPolar L) ≃ₗ[F]
      LinearMap.ker L × LinearMap.ker L.flip where
  toFun x :=
    (⟨x.1.1,
        (diamondOddCrossPolar_mem_ker_iff L x.1).mp x.2 |>.1⟩,
      ⟨x.1.2,
        (diamondOddCrossPolar_mem_ker_iff L x.1).mp x.2 |>.2⟩)
  invFun x := ⟨(x.1.1, x.2.1),
    (diamondOddCrossPolar_mem_ker_iff
      L (x.1.1, x.2.1)).mpr ⟨x.1.2, x.2.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    ext <;> rfl
  map_add' x y := rfl
  map_smul' r x := rfl

private theorem finrank_ker_diamondOddCrossPolar
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F
        (LinearMap.ker (diamondOddCrossPolar L)) =
      Module.finrank F (LinearMap.ker L) +
        Module.finrank F (LinearMap.ker L.flip) := by
  rw [LinearEquiv.finrank_eq
      (diamondOddCrossPolarKerEquiv L),
    Module.finrank_prod]

private theorem finrank_range_diamondOddCrossPolar
    {U V : Type*}
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (L : U →ₗ[F] Module.Dual F V) :
    Module.finrank F
        (LinearMap.range (diamondOddCrossPolar L)) =
      2 * Module.finrank F (LinearMap.range L) := by
  have hpolar :=
    LinearMap.finrank_range_add_finrank_ker
      (diamondOddCrossPolar L)
  have hleft :=
    LinearMap.finrank_range_add_finrank_ker L
  have hright :=
    LinearMap.finrank_range_add_finrank_ker L.flip
  rw [finrank_ker_diamondOddCrossPolar,
    Module.finrank_prod] at hpolar
  rw [finrank_range_flip_eq L] at hright
  omega

noncomputable def diamondOddSSTSPolar
    {n c : Nat} [NeZero n] (hn : Odd n) :
    ((DiamondOddAxisTail n c →
          DiamondEOOOLeftAmbient n) ×
        (DiamondOddAxisTail n c → CyclicCube n)) →ₗ[F]
      Module.Dual F
        ((DiamondOddAxisTail n c →
            DiamondEOOOLeftAmbient n) ×
          (DiamondOddAxisTail n c → CyclicCube n)) :=
  diamondOddCrossPolar (diamondOddSSTSCross hn)

theorem diamondOddSSTSPolar_eq_quadratic_polar
    {n c : Nat} [NeZero n] (hn : Odd n)
    (x y :
      (DiamondOddAxisTail n c →
          DiamondEOOOLeftAmbient n) ×
        (DiamondOddAxisTail n c → CyclicCube n)) :
    diamondOddSSTSPolar hn x y =
      diamondOddSSTSCross hn (x + y).1 (x + y).2 +
        diamondOddSSTSCross hn x.1 x.2 +
        diamondOddSSTSCross hn y.1 y.2 :=
  diamondOddCrossPolar_eq_quadratic_polar
    (diamondOddSSTSCross hn) x y

theorem diamondOddSSTSPolar_mem_ker_iff
    {n c : Nat} [NeZero n] (hn : Odd n)
    (x :
      (DiamondOddAxisTail n c →
          DiamondEOOOLeftAmbient n) ×
        (DiamondOddAxisTail n c → CyclicCube n)) :
    x ∈ LinearMap.ker (diamondOddSSTSPolar hn) ↔
      x.1 ∈ LinearMap.ker (diamondOddSSTSCross hn) ∧
        x.2 ∈ LinearMap.ker
          (diamondOddSSTSCross hn).flip :=
  diamondOddCrossPolar_mem_ker_iff
    (diamondOddSSTSCross hn) x

noncomputable def diamondOddSSTTPolar
    {n c d : Nat} [NeZero n] (hn : Odd n) :
    ((DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n) ×
        (DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n)) →ₗ[F]
      Module.Dual F
        ((DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → CyclicCube n) ×
          (DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → CyclicCube n)) :=
  diamondOddCrossPolar (diamondOddSSTTCross hn)

theorem diamondOddSSTTPolar_eq_quadratic_polar
    {n c d : Nat} [NeZero n] (hn : Odd n)
    (x y :
      (DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n) ×
        (DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n)) :
    diamondOddSSTTPolar hn x y =
      diamondOddSSTTCross hn (x + y).1 (x + y).2 +
        diamondOddSSTTCross hn x.1 x.2 +
        diamondOddSSTTCross hn y.1 y.2 :=
  diamondOddCrossPolar_eq_quadratic_polar
    (diamondOddSSTTCross hn) x y

theorem diamondOddSSTTPolar_mem_ker_iff
    {n c d : Nat} [NeZero n] (hn : Odd n)
    (x :
      (DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n) ×
        (DiamondOddAxisTail n c →
          DiamondOddAxisTail n d → CyclicCube n)) :
    x ∈ LinearMap.ker (diamondOddSSTTPolar hn) ↔
      x.1 ∈ LinearMap.ker (diamondOddSSTTCross hn) ∧
        x.2 ∈ LinearMap.ker
          (diamondOddSSTTCross hn).flip :=
  diamondOddCrossPolar_mem_ker_iff
    (diamondOddSSTTCross hn) x

noncomputable def diamondOddSTTSPolar
    {n b c : Nat} [NeZero n] (hn : Odd n) :
    ((DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n) ×
        (DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n)) →ₗ[F]
      Module.Dual F
        ((DiamondOddAxisTail n b →
            DiamondOddAxisTail n c → CyclicCube n) ×
          (DiamondOddAxisTail n b →
            DiamondOddAxisTail n c → CyclicCube n)) :=
  diamondOddCrossPolar (diamondOddSTTSCross hn)

theorem diamondOddSTTSPolar_eq_quadratic_polar
    {n b c : Nat} [NeZero n] (hn : Odd n)
    (x y :
      (DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n) ×
        (DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n)) :
    diamondOddSTTSPolar hn x y =
      diamondOddSTTSCross hn (x + y).1 (x + y).2 +
        diamondOddSTTSCross hn x.1 x.2 +
        diamondOddSTTSCross hn y.1 y.2 :=
  diamondOddCrossPolar_eq_quadratic_polar
    (diamondOddSTTSCross hn) x y

theorem diamondOddSTTSPolar_mem_ker_iff
    {n b c : Nat} [NeZero n] (hn : Odd n)
    (x :
      (DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n) ×
        (DiamondOddAxisTail n b →
          DiamondOddAxisTail n c → CyclicCube n)) :
    x ∈ LinearMap.ker (diamondOddSTTSPolar hn) ↔
      x.1 ∈ LinearMap.ker (diamondOddSTTSCross hn) ∧
        x.2 ∈ LinearMap.ker
          (diamondOddSTTSCross hn).flip :=
  diamondOddCrossPolar_mem_ker_iff
    (diamondOddSTTSCross hn) x

/-! ## Closed positive signed sums -/

private theorem finrank_cyclicCube_local
    {n : Nat} [NeZero n] :
    Module.finrank F (CyclicCube n) = n ^ 3 := by
  simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
    pow_succ, mul_assoc]

private theorem finrank_diamondEOOOLeftAmbient
    {n : Nat} [NeZero n] :
    Module.finrank F (DiamondEOOOLeftAmbient n) =
      2 * n ^ 3 := by
  rw [Module.finrank_prod, finrank_cyclicCube_local]
  ring

private theorem finrank_diamondOddAxisTailPi
    {n k : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Module.finrank F (DiamondOddAxisTail n k → V) =
      (n ^ (k - 1) - 1) * Module.finrank F V := by
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ,
    Nat.nsmul_eq_mul, card_diamondOddAxisTail]

private theorem finrank_diamondOddTensorTailPi
    {n k l : Nat} [NeZero n]
    (V : Type*) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] :
    Module.finrank F
        (DiamondOddAxisTail n k →
          DiamondOddAxisTail n l → V) =
      (n ^ (k - 1) - 1) *
        (n ^ (l - 1) - 1) *
          Module.finrank F V := by
  rw [finrank_diamondOddAxisTailPi,
    finrank_diamondOddAxisTailPi]
  ring

private theorem sum_bitSign_cross_eq_closed_pow
    {U V : Type*}
    [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (L : U →ₗ[F] Module.Dual F V)
    (e : Nat)
    (htotal :
      Module.finrank F (LinearMap.range L) + e =
        Module.finrank F U + Module.finrank F V) :
    (∑ z : U × V, bitSign (L z.1 z.2)) =
      (2 : Int) ^ e := by
  calc
    (∑ z : U × V, bitSign (L z.1 z.2)) =
        (2 : Int) ^
          (Module.finrank F (LinearMap.ker L) +
            Module.finrank F V) :=
      sum_bitSign_bilinear_eq_pow L
    _ = (2 : Int) ^ e := by
      congr 1
      have hnull :=
        LinearMap.finrank_range_add_finrank_ker L
      omega

theorem sum_bitSign_diamondOddSSTSCross_eq_pow
    {n c : Nat} [NeZero n] (hn : Odd n) :
    (∑ z :
        (DiamondOddAxisTail n c →
            DiamondEOOOLeftAmbient n) ×
          (DiamondOddAxisTail n c → CyclicCube n),
        bitSign (diamondOddSSTSCross hn z.1 z.2)) =
      (2 : Int) ^
        ((n ^ (c - 1) - 1) *
          (2 * n ^ 3 + n)) := by
  apply sum_bitSign_cross_eq_closed_pow
  rw [rank_diamondOddSSTSCross,
    finrank_diamondOddAxisTailPi,
    finrank_diamondEOOOLeftAmbient,
    finrank_diamondOddAxisTailPi,
    finrank_cyclicCube_local]
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
  ring

theorem sum_bitSign_diamondOddSSTTCross_eq_pow
    {n c d : Nat} [NeZero n] (hn : Odd n) :
    (∑ z :
        (DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → CyclicCube n) ×
          (DiamondOddAxisTail n c →
            DiamondOddAxisTail n d → CyclicCube n),
        bitSign (diamondOddSSTTCross hn z.1 z.2)) =
      (2 : Int) ^
        ((n ^ (c - 1) - 1) *
          (n ^ (d - 1) - 1) *
            (n ^ 3 + n ^ 2)) := by
  apply sum_bitSign_cross_eq_closed_pow
  rw [rank_diamondOddSSTTCross,
    finrank_diamondOddTensorTailPi,
    finrank_cyclicCube_local]
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
  ring

theorem sum_bitSign_diamondOddSTTSCross_eq_pow
    {n b c : Nat} [NeZero n] (hn : Odd n) :
    (∑ z :
        (DiamondOddAxisTail n b →
            DiamondOddAxisTail n c → CyclicCube n) ×
          (DiamondOddAxisTail n b →
            DiamondOddAxisTail n c → CyclicCube n),
        bitSign (diamondOddSTTSCross hn z.1 z.2)) =
      (2 : Int) ^
        ((n ^ (b - 1) - 1) *
          (n ^ (c - 1) - 1) *
            (n ^ 3 + n ^ 2)) := by
  apply sum_bitSign_cross_eq_closed_pow
  rw [rank_diamondOddSTTSCross,
    finrank_diamondOddTensorTailPi,
    finrank_cyclicCube_local]
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
  ring

end

end Core4loop.SquareDiagonal.DirectWitt
