import Core4loop.Exponents

open scoped BigOperators

namespace Core4loop

noncomputable def betaB {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  B p (vecSum y) z w

noncomputable def gammaB {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  B p (vecSum y + 1) z w

noncomputable def deltaC {n a b c d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  C p y (vecSum z) w

noncomputable def etaC {n a b c d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  C p y (vecSum z + 1) w

noncomputable def xiW {n a b c d : ℕ} [NeZero n]
    (W : WFun4 n a b c) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  W p y z (vecSum w)

noncomputable def zetaW {n a b c d : ℕ} [NeZero n]
    (W : WFun4 n a b c) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  W p y z (vecSum w + 1)

noncomputable def dyB {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  betaB B p y z w + gammaB B p y z w

noncomputable def dzC {n a b c d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  deltaC C p y z w + etaC C p y z w

noncomputable def dwW {n a b c d : ℕ} [NeZero n]
    (W : WFun4 n a b c) (p : PVec n a)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  xiW W p y z w + zetaW W p y z w

abbrev RootTarget (n b c d : ℕ) :=
  YVec n b → ZVec n c → WVec n d → F

noncomputable def K_yzw_fun {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  ∑ p : PVec n a, (dyB B p y z w + dzC C p y z w + dwW W p y z w)

noncomputable def K_yw_fun {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (W : WFun4 n a b c)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  ∑ p : PVec n a, (dyB B p y z w + dwW W p y z w)

noncomputable def K_yzw {n a b c d : ℕ} [NeZero n] :
    (BFun4 n a c d × CFun4 n a b d × WFun4 n a b c)
      →ₗ[F] RootTarget n b c d where
  toFun x := fun y z w => K_yzw_fun x.1 x.2.1 x.2.2 y z w
  map_add' x x' := by
    funext y z w
    unfold K_yzw_fun dyB dzC dwW betaB gammaB deltaC etaC xiW zetaW
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  map_smul' r x := by
    funext y z w
    unfold K_yzw_fun dyB dzC dwW betaB gammaB deltaC etaC xiW zetaW
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring

noncomputable def K_yw {n a b c d : ℕ} [NeZero n] :
    (BFun4 n a c d × WFun4 n a b c) →ₗ[F] RootTarget n b c d where
  toFun x := fun y z w => K_yw_fun x.1 x.2 y z w
  map_add' x x' := by
    funext y z w
    unfold K_yw_fun dyB dwW betaB gammaB xiW zetaW
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring
  map_smul' r x := by
    funext y z w
    unfold K_yw_fun dyB dwW betaB gammaB xiW zetaW
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro p _
    ring

noncomputable def Q1 {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) : F :=
  ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    (
    betaB B p y z w * deltaC C p y z w
    + gammaB B p y z w * etaC C p y z w)

noncomputable def Q2 {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) : F :=
  ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    (
    betaB B p y z w * deltaC C p y z w
    + gammaB B p y z w * etaC C p y z w
    + deltaC C p y z w * xiW W p y z w
    + etaC C p y z w * zetaW W p y z w)

noncomputable def Q3 {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) : F :=
  Q2 B C W

noncomputable def Q4 {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) (W : WFun4 n a b c) : F :=
  ∑ p : PVec n a, ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
    (
    betaB B p y z w * deltaC C p y z w
    + gammaB B p y z w * etaC C p y z w
    + betaB B p y z w * xiW W p y z w
    + gammaB B p y z w * zetaW W p y z w
    + deltaC C p y z w * xiW W p y z w
    + etaC C p y z w * zetaW W p y z w)

abbrev Surviving_yzw (n a b c d : ℕ) [NeZero n] :=
  { x : BFun4 n a c d × CFun4 n a b d × WFun4 n a b c //
      K_yzw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 }

abbrev Surviving_yw (n a b c d : ℕ) [NeZero n] :=
  { x : BFun4 n a c d × WFun4 n a b c //
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 }

end Core4loop
