import Core4loop.CompleteGraph.Odd.FreeCross.DiagonalOrbit

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.Odd

open Core4loop
open Core4loop.CompleteGraph.CubeCompat
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

/-- The two pointed-tail families in the K4 odd `TSTS` free cross. -/
abbrev K4OddTSTSFamily
    (n a c : Nat) [NeZero n] :=
  DiamondOddAxisTail n a →
    DiamondOddAxisTail n c → CyclicCube n

private theorem card_k4OddAxisTail
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

private theorem k4CubeKappa_eq_diagonalDiff
    {n : Nat} [NeZero n] (B W : CyclicCube n) :
    k4CubeKappa B W =
      EEOEInternal.cubeDotDual (k4DiagonalDiff W) B := by
  unfold k4CubeKappa EEOEInternal.cubeDotDual cubeDot
  change
    (∑ q : I n × I n × I n,
      (B q.1 q.2.1 q.2.2 * W q.1 q.2.1 q.2.2
        + B (q.1 + 1) q.2.1 q.2.2 *
            W q.1 q.2.1 (q.2.2 + 1))) =
      ∑ q : I n × I n × I n,
        (W q.1 q.2.1 q.2.2 +
            W (q.1 - 1) q.2.1 (q.2.2 + 1)) *
          B q.1 q.2.1 q.2.2
  rw [Finset.sum_add_distrib]
  simp only [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro q _
    ring
  · let e : (I n × I n × I n) ≃ (I n × I n × I n) :=
      Equiv.prodCongr (Equiv.addRight (1 : I n))
        (Equiv.refl (I n × I n))
    apply Fintype.sum_equiv e
    intro q
    change
      B (q.1 + 1) q.2.1 q.2.2 *
          W q.1 q.2.1 (q.2.2 + 1) =
        W ((q.1 + 1) - 1) q.2.1 (q.2.2 + 1) *
          B (q.1 + 1) q.2.1 q.2.2
    rw [add_sub_cancel_right]
    ring

private noncomputable def k4DiagonalWCross
    {n : Nat} [NeZero n] :
    CyclicCube n →ₗ[F] Module.Dual F (CyclicCube n) :=
  EEOEInternal.cubeDotDual.comp k4DiagonalDiff

private noncomputable def k4CubeDotPostcompRangeEquiv
    {n : Nat} [NeZero n]
    {U : Type*} [AddCommGroup U] [Module F U]
    (f : U →ₗ[F] CyclicCube n) :
    LinearMap.range (EEOEInternal.cubeDotDual.comp f) ≃ₗ[F]
      LinearMap.range f := by
  let E := EEOEInternal.cubeDotEquiv (n := n)
  have hmap :
      (LinearMap.range f).map E.toLinearMap =
        LinearMap.range (EEOEInternal.cubeDotDual.comp f) := by
    simpa only [E] using
      (LinearMap.range_comp f E.toLinearMap).symm
  exact
    (E.ofSubmodules
      (LinearMap.range f)
      (LinearMap.range (EEOEInternal.cubeDotDual.comp f))
      hmap).symm

private theorem finrank_range_k4DiagonalWCross
    {n : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range (k4DiagonalWCross (n := n))) =
      n ^ 2 * (n - 1) := by
  calc
    Module.finrank F
        (LinearMap.range (k4DiagonalWCross (n := n))) =
        Module.finrank F
          (LinearMap.range (k4DiagonalDiff (n := n))) :=
      LinearEquiv.finrank_eq
        (k4CubeDotPostcompRangeEquiv
          (k4DiagonalDiff (n := n)))
    _ = n ^ 2 * (n - 1) :=
      finrank_range_k4DiagonalDiff

private noncomputable def k4OddTensorTailJLinear
    {n a c : Nat} [NeZero n] :
    K4OddTSTSFamily n a c →ₗ[F] K4OddTSTSFamily n a c where
  toFun W :=
    diamondOddTensorTailJ
      (zeroVec : PVec n a) (zeroVec : PVec n c) W
  map_add' W V := by
    funext pt zt
    simp only [diamondOddTensorTailJ_apply, Pi.add_apply,
      Finset.sum_add_distrib]
    abel
  map_smul' r W := by
    funext pt zt
    simp only [diamondOddTensorTailJ_apply, Pi.smul_apply,
      ← Finset.smul_sum, smul_add, RingHom.id_apply]

private noncomputable def k4OddTensorTailJEquiv
    {n a c : Nat} [NeZero n] (hn : Odd n) :
    K4OddTSTSFamily n a c ≃ₗ[F] K4OddTSTSFamily n a c where
  toLinearMap := k4OddTensorTailJLinear
  invFun :=
    diamondOddTensorTailJ
      (zeroVec : PVec n a) (zeroVec : PVec n c)
  left_inv :=
    diamondOddTensorTailJ_sq_apply
      (zeroVec : PVec n a) (zeroVec : PVec n c)
      (odd_card_PVec hn) (odd_card_PVec hn)
  right_inv :=
    diamondOddTensorTailJ_sq_apply
      (zeroVec : PVec n a) (zeroVec : PVec n c)
      (odd_card_PVec hn) (odd_card_PVec hn)

/-- Reverse orientation used internally: `W` is the source and `B` is dual. -/
private noncomputable def k4OddTSTSReverseCross
    {n a c : Nat} [NeZero n] (hn : Odd n) :
    K4OddTSTSFamily n a c →ₗ[F]
      Module.Dual F (K4OddTSTSFamily n a c) :=
  (diamondOddFamilyCross
      (T := DiamondOddAxisTail n a)
      (diamondOddFamilyCross
        (T := DiamondOddAxisTail n c)
        (k4DiagonalWCross (n := n)))).comp
    (k4OddTensorTailJEquiv hn).toLinearMap

private theorem k4OddTSTSReverseCross_apply
    {n a c : Nat} [NeZero n] (hn : Odd n)
    (W B : K4OddTSTSFamily n a c) :
    k4OddTSTSReverseCross hn W B =
      ∑ pt : DiamondOddAxisTail n a,
        ∑ zt : DiamondOddAxisTail n c,
          EEOEInternal.cubeDotDual
            (k4DiagonalDiff
              (diamondOddTensorTailJ
                (zeroVec : PVec n a)
                (zeroVec : PVec n c) W pt zt))
            (B pt zt) :=
  rfl

private theorem rank_k4OddTSTSReverseCross
    {n a c : Nat} [NeZero n] (hn : Odd n) :
    Module.finrank F
        (LinearMap.range
          (k4OddTSTSReverseCross (a := a) (c := c) hn)) =
      (n ^ (a - 1) - 1) *
        (n ^ (c - 1) - 1) *
          (n ^ 2 * (n - 1)) := by
  calc
    Module.finrank F
        (LinearMap.range
          (k4OddTSTSReverseCross (a := a) (c := c) hn)) =
        Module.finrank F
          (LinearMap.range
            (diamondOddFamilyCross
              (T := DiamondOddAxisTail n a)
              (diamondOddFamilyCross
                (T := DiamondOddAxisTail n c)
                (k4DiagonalWCross (n := n))))) := by
      rw [k4OddTSTSReverseCross,
        LinearMap.range_comp_of_range_eq_top _
          (LinearEquiv.range (k4OddTensorTailJEquiv hn))]
    _ = Fintype.card (DiamondOddAxisTail n a) *
          (Fintype.card (DiamondOddAxisTail n c) *
            Module.finrank F
              (LinearMap.range (k4DiagonalWCross (n := n)))) := by
      rw [finrank_range_diamondOddFamilyCross,
        finrank_range_diamondOddFamilyCross]
    _ = (n ^ (a - 1) - 1) *
          (n ^ (c - 1) - 1) *
            (n ^ 2 * (n - 1)) := by
      rw [card_k4OddAxisTail, card_k4OddAxisTail,
        finrank_range_k4DiagonalWCross]
      ring

private theorem finrank_k4CyclicCube
    {n : Nat} [NeZero n] :
    Module.finrank F (CyclicCube n) = n ^ 3 := by
  simp [CyclicCube, Module.finrank_pi_fintype, I, ZMod.card,
    pow_succ, mul_assoc]

private theorem finrank_k4OddTSTSFamily
    {n a c : Nat} [NeZero n] :
    Module.finrank F (K4OddTSTSFamily n a c) =
      (n ^ (a - 1) - 1) *
        (n ^ (c - 1) - 1) * n ^ 3 := by
  change
    Module.finrank F
        (DiamondOddAxisTail n a →
          DiamondOddAxisTail n c → CyclicCube n) = _
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    card_k4OddAxisTail, finrank_k4CyclicCube]
  ring

private theorem sum_bitSign_k4Cross_eq_closed_pow
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

private theorem sum_bitSign_k4ReverseCross_eq_pow
    {n a c : Nat} [NeZero n] (hn : Odd n) :
    (∑ z :
        K4OddTSTSFamily n a c × K4OddTSTSFamily n a c,
      bitSign (k4OddTSTSReverseCross hn z.1 z.2)) =
      (2 : Int) ^
        ((n ^ (a - 1) - 1) *
          (n ^ (c - 1) - 1) *
            (n ^ 3 + n ^ 2)) := by
  apply sum_bitSign_k4Cross_eq_closed_pow
  rw [rank_k4OddTSTSReverseCross,
    finrank_k4OddTSTSFamily]
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp only [Nat.succ_eq_add_one, Nat.succ_sub_one]
  ring

/-- The positive K4 odd `TSTS` free-cross sum, in literal `B × W` order
with the actual two-axis pointed-tail involution on `W`. -/
theorem sum_bitSign_k4OddTSTS_eq_pow
    {n a c : Nat} [NeZero n] (hn : Odd n) :
    (∑ z : K4OddTSTSFamily n a c ×
          K4OddTSTSFamily n a c,
      bitSign
        (∑ pt : DiamondOddAxisTail n a,
          ∑ zt : DiamondOddAxisTail n c,
            k4CubeKappa (z.1 pt zt)
              (diamondOddTensorTailJ
                (zeroVec : PVec n a)
                (zeroVec : PVec n c)
                z.2 pt zt))) =
      (2 : Int) ^
        ((n ^ (a - 1) - 1) *
          (n ^ (c - 1) - 1) *
            (n ^ 3 + n ^ 2)) := by
  calc
    (∑ z : K4OddTSTSFamily n a c ×
          K4OddTSTSFamily n a c,
      bitSign
        (∑ pt : DiamondOddAxisTail n a,
          ∑ zt : DiamondOddAxisTail n c,
            k4CubeKappa (z.1 pt zt)
              (diamondOddTensorTailJ
                (zeroVec : PVec n a)
                (zeroVec : PVec n c)
                z.2 pt zt))) =
        ∑ z : K4OddTSTSFamily n a c ×
            K4OddTSTSFamily n a c,
          bitSign (k4OddTSTSReverseCross hn z.1 z.2) := by
      let e :
          (K4OddTSTSFamily n a c × K4OddTSTSFamily n a c) ≃
            (K4OddTSTSFamily n a c × K4OddTSTSFamily n a c) :=
        Equiv.prodComm _ _
      apply Fintype.sum_equiv e
      intro z
      change
        bitSign
            (∑ pt : DiamondOddAxisTail n a,
              ∑ zt : DiamondOddAxisTail n c,
                k4CubeKappa (z.1 pt zt)
                  (diamondOddTensorTailJ
                    (zeroVec : PVec n a)
                    (zeroVec : PVec n c)
                    z.2 pt zt)) =
          bitSign (k4OddTSTSReverseCross hn z.2 z.1)
      congr 1
      rw [k4OddTSTSReverseCross_apply]
      apply Finset.sum_congr rfl
      intro pt _
      apply Finset.sum_congr rfl
      intro zt _
      exact k4CubeKappa_eq_diagonalDiff _ _
    _ = (2 : Int) ^
        ((n ^ (a - 1) - 1) *
          (n ^ (c - 1) - 1) *
            (n ^ 3 + n ^ 2)) :=
      sum_bitSign_k4ReverseCross_eq_pow hn

end

end Core4loop.CompleteGraph.Odd
