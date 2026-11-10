import Core4loop.CompleteGraph.EvenP.TailWitt.SignedSum
import Core4loop.CompleteGraph.EvenAllLarge.BaseQZero
import Core4loop.CompleteGraph.EvenAllLarge.BaseRank
import Core4loop.SquareDiagonal.DirectWitt.BilinearSignSum

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.DirectWitt
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.TailWitt

noncomputable section

attribute [local instance] Fintype.ofFinite

private local instance
    {n b c d : Nat} [NeZero n] :
    Fintype (K4EvenPLeft n b c d) :=
  Fintype.ofFinite _

private local instance
    {n b c d : Nat} [NeZero n] :
    Fintype (K4EvenPBaseRight n b c d) :=
  Fintype.ofFinite _

private local instance
    {n b c d : Nat} [NeZero n] :
    Fintype (K4EvenPBase n b c d) :=
  inferInstance

private theorem sum_bitSign_bilinear_add_left_eq_pow_of_zero_on_ker
    {U V : Type*}
    [AddCommGroup U] [Module F U] [Fintype U]
    [AddCommGroup V] [Module F V] [Fintype V]
    (L : U →ₗ[F] Module.Dual F V)
    (g : U → F)
    (hg : ∀ u, u ∈ LinearMap.ker L → g u = 0) :
    (∑ z : U × V, bitSign (g z.1 + L z.1 z.2)) =
      (2 : Int) ^
        (Module.finrank F (LinearMap.ker L) +
          Module.finrank F V) := by
  calc
    (∑ z : U × V, bitSign (g z.1 + L z.1 z.2)) =
        ∑ z : U × V, bitSign (L z.1 z.2) := by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro u _
      change
        (∑ v : V, bitSign (g u + L u v)) =
          ∑ v : V, bitSign (L u v)
      have hadd (v : V) :
          bitSign (g u + L u v) = bitSign (L u v + g u) := by
        rw [add_comm]
      simp_rw [hadd]
      rw [sum_bitSign_linearMap_add_const, sum_bitSign_linearMap]
      by_cases hu : L u = 0
      · have hgu : g u = 0 := hg u (LinearMap.mem_ker.mpr hu)
        simp only [hu, if_pos, hgu, bitSign_zero, mul_one]
      · simp [hu]
    _ = _ := sum_bitSign_bilinear_eq_pow L

private theorem sum_bitSign_k4EvenPBaseQ_eq_pow
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (∑ x : K4EvenPBase n b c d, bitSign (k4EvenPBaseQ x)) =
      (2 : Int) ^
        (Module.finrank F
            (LinearMap.ker
              (k4EvenPBaseCross
                (n := n) (b := b) (c := c) (d := d))) +
          Module.finrank F (K4EvenPBaseRight n b c d)) := by
  exact sum_bitSign_bilinear_add_left_eq_pow_of_zero_on_ker
    (L := k4EvenPBaseCross)
    (g := fun sigma : K4EvenPLeft n b c d => k4EvenPSliceQ sigma.1)
    (hg := by
      intro sigma hsigma
      exact k4EvenPBase_qzero_on_ker hn2 hb hc hd sigma hsigma)

def k4EvenAllLargeHalfRankNat
    (n a b c d : Nat) : Nat :=
  (2 * (n * (n - 1) * (n ^ c - 2 * (n - 1))) +
    ((n - 1) * (3 * n ^ 2 - 4 * n + 6) +
    ((n ^ (b - 1) - 2) * (2 * n * (n - 1)) +
    ((n ^ (d - 1) - 2) * (2 * n * (n - 1)) +
    ((n ^ (c - 1) - 2) * ((n - 1) * (n ^ 2 + 3 * n)) +
    ((n ^ (b - 1) - 2) * (n ^ (c - 1) - 2) *
        (n ^ 2 * (n - 1)) +
    ((n ^ (c - 1) - 2) * (n ^ (d - 1) - 2) *
        (n ^ 2 * (n - 1)) + (0 + 0)))))))) +
  (n ^ (a - 1) - 2) *
    (n * (n - 1) * (n ^ c - 2 * (n - 1)))

noncomputable def k4EvenAllLargeResidualExponent
    {n a b c d : Nat} [NeZero n] : Nat :=
  (Module.finrank F
      (LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d))) +
    Module.finrank F (K4EvenPBaseRight n b c d)) +
  ((n ^ (a - 1) - 2) *
      Module.finrank F
        (LinearMap.ker
          (k4EvenPGPolar
            (n := n) (b := b) (c := c) (d := d))) +
    (n ^ (a - 1) - 2) *
      (n * (n - 1) * (n ^ c - 2 * (n - 1))))

private theorem card_k4EvenPTailCoordinateIndex
    {n a : Nat} [NeZero n]
    (t0 : K4EvenPTailIndex n a) :
    Fintype.card (PointedTail (K4EvenPTailIndex n a) t0) =
      n ^ (a - 1) - 2 := by
  have houter :
      Fintype.card (K4EvenPTailIndex n a) = n ^ (a - 1) - 1 := by
    have hnat :
        Nat.card (PointedTail (PVec n a) (zeroVec : PVec n a)) =
          Nat.card (PVec n a) - 1 := by
      simpa only [← Nat.card_eq_fintype_card] using
        card_pointedTail (zeroVec : PVec n a)
    calc
      Fintype.card (K4EvenPTailIndex n a) =
          Nat.card (K4EvenPTailIndex n a) :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card (PVec n a) - 1 := by
        simpa only [K4EvenPTailIndex] using hnat
      _ = Fintype.card (PVec n a) - 1 := by
        rw [Nat.card_eq_fintype_card]
      _ = n ^ (a - 1) - 1 := by
        rw [card_vec]
  have hinner :
      Fintype.card (PointedTail (K4EvenPTailIndex n a) t0) =
        Fintype.card (K4EvenPTailIndex n a) - 1 := by
    simpa only [← Nat.card_eq_fintype_card] using card_pointedTail t0
  rw [hinner, houter]
  omega

private theorem sum_bitSign_k4EvenPTailQ_eq_pow_exact
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (t0 : K4EvenPTailIndex n a) :
    (∑ U : K4EvenPTail n a b c d, bitSign (k4EvenPTailQ U)) =
      (2 : Int) ^
        ((n ^ (a - 1) - 2) *
            Module.finrank F
              (LinearMap.ker
                (k4EvenPGPolar
                  (n := n) (b := b) (c := c) (d := d))) +
          (n ^ (a - 1) - 2) *
            (n * (n - 1) * (n ^ c - 2 * (n - 1)))) := by
  rw [sum_bitSign_k4EvenPTailQ_eq_radical_add_half_range hn ha2 t0]
  rw [finrank_k4EvenPTailCoordinateRadical hn ha2 t0,
    finrank_range_k4EvenPTailCoordinateGram hn ha2 t0]
  have hcard := card_k4EvenPTailCoordinateIndex t0
  have hG := finrank_range_k4EvenPGPolar hn2 hn hb2 hc2 hd2
  simp only [hcard]
  rw [hG]
  have hdiv :
      ((n ^ (a - 1) - 2) *
          (2 * (n * (n - 1) * (n ^ c - 2 * (n - 1))))) / 2 =
        (n ^ (a - 1) - 2) *
          (n * (n - 1) * (n ^ c - 2 * (n - 1))) := by
    rw [show
      (n ^ (a - 1) - 2) *
          (2 * (n * (n - 1) * (n ^ c - 2 * (n - 1)))) =
        2 * ((n ^ (a - 1) - 2) *
          (n * (n - 1) * (n ^ c - 2 * (n - 1)))) by ring]
    exact Nat.mul_div_cancel_left _ (by omega)
  rw [hdiv]

private theorem source_sum_transport
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
      ∑ z : K4EvenPBase n b c d × K4EvenPTail n a b c d,
        bitSign (k4EvenPBaseQ z.1 + k4EvenPTailQ z.2) := by
  let E := k4EvenAllLargeSourceEquiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  calc
    (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
        ∑ z : K4EvenPBase n b c d × K4EvenPTail n a b c d,
          bitSign (k4PreCQ (E.symm z)) := by
            exact (E.symm.sum_comp
              (fun x : K4PreCSource n a b c d =>
                bitSign (k4PreCQ x))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [k4PreCQ_eq_base_add_tail hn ha2]
      simp only [E, LinearEquiv.apply_symm_apply]

theorem sum_bitSign_k4PreCQ_eq_pow_even_all_large
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (t0 : K4EvenPTailIndex n a) :
    (∑ x : K4PreCSource n a b c d, bitSign (k4PreCQ x)) =
      (2 : Int) ^
        k4EvenAllLargeResidualExponent
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
  rw [source_sum_transport hn ha2]
  rw [Fintype.sum_prod_type]
  simp_rw [bitSign_add]
  calc
    (∑ x : K4EvenPBase n b c d,
        ∑ y : K4EvenPTail n a b c d,
          bitSign (k4EvenPBaseQ x) * bitSign (k4EvenPTailQ y)) =
        (∑ x : K4EvenPBase n b c d, bitSign (k4EvenPBaseQ x)) *
          ∑ y : K4EvenPTail n a b c d, bitSign (k4EvenPTailQ y) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_bitSign_k4EvenPBaseQ_eq_pow
        hn2 (by omega) (by omega) (by omega)]
      rw [sum_bitSign_k4EvenPTailQ_eq_pow_exact
        hn2 hn ha2 hb2 hc2 hd2 t0]
      rw [← pow_add]
      rfl

private noncomputable def structuralResidualExponent
    (n a b c d : Nat) [NeZero n] : Nat :=
  Module.finrank F
      (LinearMap.ker
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d))) +
    Module.finrank F (K4EvenPBaseRight n b c d) +
    ((Fintype.card (K4EvenPTailIndex n a) - 1) *
      Module.finrank F
        (LinearMap.ker
          (k4EvenPGPolar
            (n := n) (b := b) (c := c) (d := d))) +
      ((Fintype.card (K4EvenPTailIndex n a) - 1) *
        Module.finrank F
          (LinearMap.range
            (k4EvenPGPolar
              (n := n) (b := b) (c := c) (d := d)))) / 2)

private noncomputable def structuralHalfRank
    (n a b c d : Nat) [NeZero n] : Nat :=
  Module.finrank F
      (LinearMap.range
        (k4EvenPBaseCross
          (n := n) (b := b) (c := c) (d := d))) +
    ((Fintype.card (K4EvenPTailIndex n a) - 1) *
      Module.finrank F
        (LinearMap.range
          (k4EvenPGPolar
            (n := n) (b := b) (c := c) (d := d)))) / 2

set_option synthInstance.maxHeartbeats 4000000 in
-- The product-source finrank normalization requires large nested module-instance synthesis.
set_option maxHeartbeats 30000000 in
-- The product-source finrank normalization requires large nested module-instance synthesis.
private theorem structural_exponent_add_halfRank_eq_source
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    structuralResidualExponent n a b c d +
        structuralHalfRank n a b c d =
      Module.finrank F (K4PreCSource n a b c d) := by
  have hpos : 0 < Fintype.card (K4EvenPTailIndex n a) :=
    (k4EvenPTailIndex_card_odd hn ha2).pos
  rcases Fintype.card_pos_iff.mp hpos with ⟨t0⟩
  let m := Fintype.card (K4EvenPTailIndex n a) - 1
  let L := K4EvenPLeft n b c d
  let B := k4EvenPBaseCross (n := n) (b := b) (c := c) (d := d)
  let G := k4EvenPGPolar (n := n) (b := b) (c := c) (d := d)
  have hm : Even m := by
    rcases k4EvenPTailIndex_card_odd hn ha2 with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp only [m, hk]
    omega
  have hB := LinearMap.finrank_range_add_finrank_ker B
  have hG := LinearMap.finrank_range_add_finrank_ker G
  change
    Module.finrank F (LinearMap.range B) +
        Module.finrank F (LinearMap.ker B) =
      Module.finrank F L at hB
  change
    Module.finrank F (LinearMap.range G) +
        Module.finrank F (LinearMap.ker G) =
      Module.finrank F L at hG
  simp only [L] at hB hG
  have hGscaled := congrArg (fun q : Nat => m * q) hG
  dsimp only at hGscaled
  rw [Nat.mul_add] at hGscaled
  have htail := LinearEquiv.finrank_eq
    (k4EvenPTailCoordinates
      (n := n) (a := a) (b := b) (c := c) (d := d) t0)
  have hcard :
      Fintype.card (PointedTail (K4EvenPTailIndex n a) t0) = m := by
    simpa only [m, ← Nat.card_eq_fintype_card] using card_pointedTail t0
  have htail' :
      Module.finrank F (K4EvenPTail n a b c d) =
        m * Module.finrank F (K4EvenPLeft n b c d) := by
    rw [htail, Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    norm_num
  have hsource := LinearEquiv.finrank_eq
    (k4EvenAllLargeSourceEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2)
  have hsource' :
      Module.finrank F (K4PreCSource n a b c d) =
        (Module.finrank F (K4EvenPLeft n b c d) +
          Module.finrank F (K4EvenPBaseRight n b c d)) +
        Module.finrank F (K4EvenPTail n a b c d) := by
    simpa only [Module.finrank_prod] using hsource
  rw [htail'] at hsource'
  clear hsource
  rcases hm with ⟨k, hk⟩
  have hhalf :
      (m * Module.finrank F (LinearMap.range G)) / 2 +
          (m * Module.finrank F (LinearMap.range G)) / 2 =
        m * Module.finrank F (LinearMap.range G) := by
    rw [hk]
    have hdiv :
        ((k + k) * Module.finrank F (LinearMap.range G)) / 2 =
          k * Module.finrank F (LinearMap.range G) := by
      rw [show
        (k + k) * Module.finrank F (LinearMap.range G) =
          2 * (k * Module.finrank F (LinearMap.range G)) by ring]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [hdiv]
    ring
  unfold structuralResidualExponent structuralHalfRank
  change
    Module.finrank F (LinearMap.ker B) +
          Module.finrank F (K4EvenPBaseRight n b c d) +
          (m * Module.finrank F (LinearMap.ker G) +
            m * Module.finrank F (LinearMap.range G) / 2) +
        (Module.finrank F (LinearMap.range B) +
          m * Module.finrank F (LinearMap.range G) / 2) =
      Module.finrank F (K4PreCSource n a b c d)
  omega

theorem k4EvenAllLargeResidualExponent_add_halfRank_eq_source
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (t0 : K4EvenPTailIndex n a) :
    k4EvenAllLargeResidualExponent
          (n := n) (a := a) (b := b) (c := c) (d := d) +
        k4EvenAllLargeHalfRankNat n a b c d =
      Module.finrank F (K4PreCSource n a b c d) := by
  have hstruct := structural_exponent_add_halfRank_eq_source
    (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  have hpointed :
      Fintype.card (PointedTail (K4EvenPTailIndex n a) t0) =
        Fintype.card (K4EvenPTailIndex n a) - 1 := by
    simpa only [← Nat.card_eq_fintype_card] using card_pointedTail t0
  have hM :
      Fintype.card (K4EvenPTailIndex n a) - 1 =
        n ^ (a - 1) - 2 := by
    rw [← hpointed]
    exact card_k4EvenPTailCoordinateIndex t0
  have hG := finrank_range_k4EvenPGPolar hn2 hn hb2 hc2 hd2
  have htailHalf :
      ((Fintype.card (K4EvenPTailIndex n a) - 1) *
          Module.finrank F
            (LinearMap.range
              (k4EvenPGPolar
                (n := n) (b := b) (c := c) (d := d)))) / 2 =
        (n ^ (a - 1) - 2) *
          (n * (n - 1) * (n ^ c - 2 * (n - 1))) := by
    rw [hM, hG]
    rw [show
      (n ^ (a - 1) - 2) *
          (2 * (n * (n - 1) * (n ^ c - 2 * (n - 1)))) =
        2 * ((n ^ (a - 1) - 2) *
          (n * (n - 1) * (n ^ c - 2 * (n - 1)))) by ring]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hExp :
      structuralResidualExponent n a b c d =
        k4EvenAllLargeResidualExponent
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    unfold structuralResidualExponent k4EvenAllLargeResidualExponent
    rw [htailHalf, hM]
  have hHalf :
      structuralHalfRank n a b c d =
        k4EvenAllLargeHalfRankNat n a b c d := by
    unfold structuralHalfRank k4EvenAllLargeHalfRankNat
    rw [htailHalf]
    rw [finrank_range_k4EvenPBaseCross_addition_first
      hn2 hn hb2 hc2 hd2]
  rw [hExp, hHalf] at hstruct
  exact hstruct

end

end Core4loop.CompleteGraph.EvenP
