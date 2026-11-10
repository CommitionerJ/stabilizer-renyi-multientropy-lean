import Core4loop.PhaseAfterA
import Core4loop.SquareDiagonal.SingletonLC.Kernel

open scoped BigOperators

namespace Core4loop.SquareDiagonal.SingletonLC

noncomputable section

private def shiftYPlus {n b : Nat} [NeZero n] (hb : 0 < b) :
    YVec n b ≃ YVec n b :=
  shiftVecEquiv (⟨0, hb⟩ : Fin b) (1 : I n)

private def shiftZPlus {n c : Nat} [NeZero n] (hc : 0 < c) :
    ZVec n c ≃ ZVec n c :=
  shiftVecEquiv (⟨0, hc⟩ : Fin c) (1 : I n)

private def shiftWPlus {n d : Nat} [NeZero n] (hd : 0 < d) :
    WVec n d ≃ WVec n d :=
  shiftVecEquiv (⟨0, hd⟩ : Fin d) (1 : I n)

private theorem betaB_shiftYPlus
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (B : BFun4 n 1 c d)
    (p : PVec n 1) (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    betaB B p (shiftYPlus hb y) z w = gammaB B p y z w := by
  simp only [betaB, gammaB]
  change
    B p (vecSum (shiftVec y (⟨0, hb⟩ : Fin b) (1 : I n))) z w =
      B p (vecSum y + 1) z w
  rw [vecSum_shiftVec]

private theorem deltaC_shiftZPlus
    {n b c d : Nat} [NeZero n]
    (hc : 0 < c) (C : CFun4 n 1 b d)
    (p : PVec n 1) (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    deltaC C p y (shiftZPlus hc z) w = etaC C p y z w := by
  simp only [deltaC, etaC]
  change
    C p y (vecSum (shiftVec z (⟨0, hc⟩ : Fin c) (1 : I n))) w =
      C p y (vecSum z + 1) w
  rw [vecSum_shiftVec]

private theorem xiW_shiftWPlus
    {n b c d : Nat} [NeZero n]
    (hd : 0 < d) (W : WFun4 n 1 b c)
    (p : PVec n 1) (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    xiW W p y z (shiftWPlus hd w) = zetaW W p y z w := by
  simp only [xiW, zetaW]
  change
    W p y z (vecSum (shiftVec w (⟨0, hd⟩ : Fin d) (1 : I n))) =
      W p y z (vecSum w + 1)
  rw [vecSum_shiftVec]

theorem sum_beta_bitNat_eq_sum_gamma_bitNat
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (B : BFun4 n 1 c d) :
    (∑ p : PVec n 1, ∑ y : YVec n b,
      ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (betaB B p y z w)) =
      ∑ p : PVec n 1, ∑ y : YVec n b,
        ∑ z : ZVec n c, ∑ w : WVec n d,
          bitToNat (gammaB B p y z w) := by
  simp_rw [← betaB_shiftYPlus hb B]
  apply Finset.sum_congr rfl
  intro p _
  exact ((shiftYPlus hb).sum_comp
    (fun y : YVec n b =>
      ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (betaB B p y z w))).symm

theorem sum_delta_bitNat_eq_sum_eta_bitNat
    {n b c d : Nat} [NeZero n]
    (hc : 0 < c) (C : CFun4 n 1 b d) :
    (∑ p : PVec n 1, ∑ y : YVec n b,
      ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (deltaC C p y z w)) =
      ∑ p : PVec n 1, ∑ y : YVec n b,
        ∑ z : ZVec n c, ∑ w : WVec n d,
          bitToNat (etaC C p y z w) := by
  simp_rw [← deltaC_shiftZPlus hc C]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro y _
  exact ((shiftZPlus hc).sum_comp
    (fun z : ZVec n c =>
      ∑ w : WVec n d, bitToNat (deltaC C p y z w))).symm

theorem sum_xi_bitNat_eq_sum_zeta_bitNat
    {n b c d : Nat} [NeZero n]
    (hd : 0 < d) (W : WFun4 n 1 b c) :
    (∑ p : PVec n 1, ∑ y : YVec n b,
      ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (xiW W p y z w)) =
      ∑ p : PVec n 1, ∑ y : YVec n b,
        ∑ z : ZVec n c, ∑ w : WVec n d,
          bitToNat (zetaW W p y z w) := by
  simp_rw [← xiW_shiftWPlus hd W]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  exact ((shiftWPlus hd).sum_comp
    (fun w : WVec n d => bitToNat (xiW W p y z w))).symm

end

end Core4loop.SquareDiagonal.SingletonLC
