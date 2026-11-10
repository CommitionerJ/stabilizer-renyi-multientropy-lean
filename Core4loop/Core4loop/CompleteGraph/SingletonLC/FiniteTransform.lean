import Core4loop.SquareDiagonal.SingletonLC.ShiftBalance

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace Core4loop.CompleteGraph.SingletonLC

noncomputable section

open Core4loop

private abbrev bitToNat := SquareDiagonal.SingletonLC.bitToNat
private abbrev lcKernel := SquareDiagonal.SingletonLC.lcKernel

private def cSign (x : F) : Complex :=
  (-1 : Complex) ^ bitToNat x

@[simp] private theorem cSign_zero : cSign 0 = 1 := by
  simp [cSign, bitToNat]

private theorem cSign_eq_cast_bitSign (x : F) :
    cSign x = ((bitSign x : Int) : Complex) := by
  fin_cases x <;>
    norm_num [cSign, SquareDiagonal.SingletonLC.bitToNat, bitSign]

private theorem cSign_add (x y : F) :
    cSign (x + y) = cSign x * cSign y := by
  rw [cSign_eq_cast_bitSign, cSign_eq_cast_bitSign,
    cSign_eq_cast_bitSign, bitSign_add]
  norm_num

private theorem cSign_sum
    {U : Type*} [Fintype U] (f : U → F) :
    cSign (∑ u : U, f u) = ∏ u : U, cSign (f u) := by
  classical
  induction (Finset.univ : Finset U) using Finset.induction_on with
  | empty => simp
  | @insert u s hu ih =>
      rw [Finset.sum_insert hu, Finset.prod_insert hu, cSign_add, ih]

private theorem orthogonality_product
    {U : Type*} [Fintype U] [DecidableEq U]
    (Xket Xbra : U → F) :
    (∑ Y : U → F,
      ∏ u : U,
        lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) =
      if Xket = Xbra then 1 else 0 := by
  have hfactor :
      (∑ Y : U → F,
        ∏ u : U,
          lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) =
        ∏ u : U, ∑ y : F,
          lcKernel y (Xket u) * star (lcKernel y (Xbra u)) := by
    exact (Fintype.prod_sum
      (fun u : U => fun y : F =>
        lcKernel y (Xket u) * star (lcKernel y (Xbra u)))).symm
  rw [hfactor]
  simp_rw [SquareDiagonal.SingletonLC.lcKernel_orthogonality]
  by_cases h : Xket = Xbra
  · subst Xbra
    simp
  · have hne : ∃ u, Xket u ≠ Xbra u := by
      simpa [funext_iff] using h
    rcases hne with ⟨u, hu⟩
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    simp [hu]

private theorem rootDiagonal_sum_eq_lcExpandedSum
    {U : Type*} [Fintype U] [DecidableEq U]
    (Ffun : (U → F) → (U → F) → Complex) :
    (∑ A : U → F, Ffun A A) =
      ∑ Y : U → F, ∑ Xket : U → F, ∑ Xbra : U → F,
        (∏ u : U,
          lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) *
          Ffun Xket Xbra := by
  classical
  symm
  calc
    (∑ Y : U → F, ∑ Xket : U → F, ∑ Xbra : U → F,
        (∏ u : U,
          lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) *
          Ffun Xket Xbra)
        = ∑ Xket : U → F, ∑ Xbra : U → F, ∑ Y : U → F,
            (∏ u : U,
              lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) *
              Ffun Xket Xbra := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro Xket _
            rw [Finset.sum_comm]
    _ = ∑ Xket : U → F, ∑ Xbra : U → F,
          (∑ Y : U → F,
            ∏ u : U,
              lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) *
            Ffun Xket Xbra := by
          simp_rw [Finset.sum_mul]
    _ = ∑ Xket : U → F, ∑ Xbra : U → F,
          (if Xket = Xbra then 1 else 0) * Ffun Xket Xbra := by
          simp_rw [orthogonality_product]
    _ = ∑ A : U → F, Ffun A A := by simp

private theorem exp_neg_mul_exp_pos :
    Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
        Complex.exp (((Real.pi : Complex) * Complex.I) / 4) = 1 := by
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 1
  ring_nf

private theorem local_ket_transform
    (b c t y : F) :
    (-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t) *
        (∑ x : F, lcKernel y x *
          cSign (x * (b + c + t) + b * c + b * t + c * t)) =
      Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
        cSign (y * (b + c + t)) := by
  have hsplit :
      (∑ x : F, lcKernel y x *
        cSign (x * (b + c + t) + b * c + b * t + c * t)) =
      cSign (b * c + b * t + c * t) *
        (∑ x : F, lcKernel y x *
          (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by
    calc
      (∑ x : F, lcKernel y x *
        cSign (x * (b + c + t) + b * c + b * t + c * t))
          = ∑ x : F, cSign (b * c + b * t + c * t) *
              (lcKernel y x *
                (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [show x * (b + c + t) + b * c + b * t + c * t =
                x * (b + c + t) + (b * c + b * t + c * t) by ring]
              rw [cSign_add]
              simp only [cSign]
              ring
      _ = cSign (b * c + b * t + c * t) *
          (∑ x : F, lcKernel y x *
            (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by
          rw [Finset.mul_sum]
  rw [hsplit]
  calc
    (-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t) *
        (cSign (b * c + b * t + c * t) *
          ∑ x : F, lcKernel y x *
            (-1 : Complex) ^ bitToNat (x * (b + c + t)))
        = cSign (b * c + b * t + c * t) *
            (((-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t)) *
              ∑ x : F, lcKernel y x *
                (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by ring
    _ = cSign (b * c + b * t + c * t) *
          (Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
            (-1 : Complex) ^ bitToNat
              (y * (b + c + t) + b * c + b * t + c * t)) := by
          rw [SquareDiagonal.SingletonLC.lcKernel_ket_identity]
    _ = Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
          (cSign (b * c + b * t + c * t) *
            cSign (y * (b + c + t) + b * c + b * t + c * t)) := by
          simp only [cSign]
          ring
    _ = Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
          cSign (y * (b + c + t)) := by
          congr 1
          rw [← cSign_add]
          congr 1
          ring_nf
          simp [show (2 : F) = 0 by rfl]

private theorem local_bra_transform
    (g e z y : F) :
    Complex.I ^ (bitToNat g + bitToNat e + bitToNat z) *
        (∑ x : F, star (lcKernel y x) *
          cSign (x * (g + e + z) + g * e + g * z + e * z)) =
      Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
        cSign (y * (g + e + z)) := by
  have hsplit :
      (∑ x : F, star (lcKernel y x) *
        cSign (x * (g + e + z) + g * e + g * z + e * z)) =
      cSign (g * e + g * z + e * z) *
        (∑ x : F, star (lcKernel y x) *
          (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by
    calc
      (∑ x : F, star (lcKernel y x) *
        cSign (x * (g + e + z) + g * e + g * z + e * z))
          = ∑ x : F, cSign (g * e + g * z + e * z) *
              (star (lcKernel y x) *
                (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [show x * (g + e + z) + g * e + g * z + e * z =
                x * (g + e + z) + (g * e + g * z + e * z) by ring]
              rw [cSign_add]
              simp only [cSign]
              ring
      _ = cSign (g * e + g * z + e * z) *
          (∑ x : F, star (lcKernel y x) *
            (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by
          rw [Finset.mul_sum]
  rw [hsplit]
  calc
    Complex.I ^ (bitToNat g + bitToNat e + bitToNat z) *
        (cSign (g * e + g * z + e * z) *
          ∑ x : F, star (lcKernel y x) *
            (-1 : Complex) ^ bitToNat (x * (g + e + z)))
        = cSign (g * e + g * z + e * z) *
            ((Complex.I ^ (bitToNat g + bitToNat e + bitToNat z)) *
              ∑ x : F, star (lcKernel y x) *
                (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by ring
    _ = cSign (g * e + g * z + e * z) *
          (Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
            (-1 : Complex) ^ bitToNat
              (y * (g + e + z) + g * e + g * z + e * z)) := by
          rw [SquareDiagonal.SingletonLC.lcKernel_bra_identity]
    _ = Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
          (cSign (g * e + g * z + e * z) *
            cSign (y * (g + e + z) + g * e + g * z + e * z)) := by
          simp only [cSign]
          ring
    _ = Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
          cSign (y * (g + e + z)) := by
          congr 1
          rw [← cSign_add]
          congr 1
          ring_nf
          simp [show (2 : F) = 0 by rfl]

private theorem local_combined_transform
    (b c t g e z y : F) :
    (((-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t)) *
        (∑ x : F, lcKernel y x *
          cSign (x * (b + c + t) + b * c + b * t + c * t))) *
      ((Complex.I ^ (bitToNat g + bitToNat e + bitToNat z)) *
        (∑ x : F, star (lcKernel y x) *
          cSign (x * (g + e + z) + g * e + g * z + e * z))) =
      cSign
        (y * (b + g + c + e + t + z)) := by
  rw [local_ket_transform, local_bra_transform]
  rw [mul_mul_mul_comm, exp_neg_mul_exp_pos, one_mul]
  rw [← cSign_add]
  congr 1
  ring

private def completeLocal
    (b c t g e z xket xbra : F) : F :=
  xket * (b + c + t) + b * c + b * t + c * t +
  (xbra * (g + e + z) + g * e + g * z + e * z)

private def starRootLocal
    (b c t g e z y : F) : F :=
  y * (b + g + c + e + t + z)

private theorem fixedNeighbors_finiteTransform
    {U : Type*} [Fintype U] [DecidableEq U]
    (b c t g e z : U → F)
    (hcount :
      (∑ u : U,
        (bitToNat (b u) + bitToNat (c u) + bitToNat (t u))) =
      ∑ u : U,
        (bitToNat (g u) + bitToNat (e u) + bitToNat (z u))) :
    (∑ A : U → F,
      cSign (∑ u : U,
        completeLocal (b u) (c u) (t u) (g u) (e u) (z u) (A u) (A u))) =
    ∑ Y : U → F,
      cSign (∑ u : U,
        starRootLocal (b u) (c u) (t u) (g u) (e u) (z u) (Y u)) := by
  classical
  rw [rootDiagonal_sum_eq_lcExpandedSum
    (Ffun := fun Xket Xbra =>
      cSign (∑ u : U,
        completeLocal (b u) (c u) (t u) (g u) (e u) (z u)
          (Xket u) (Xbra u)))]
  -- Convert the global sign to sitewise factors and separate ket/bra root sums.
  simp_rw [cSign_sum]
  have hphase :
      (∏ u : U,
          (-Complex.I) ^
            (bitToNat (b u) + bitToNat (c u) + bitToNat (t u))) *
        (∏ u : U,
          Complex.I ^
            (bitToNat (g u) + bitToNat (e u) + bitToNat (z u))) = 1 := by
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
    rw [hcount]
    rw [← mul_pow]
    norm_num [Complex.I_sq]
  -- Reorder both function-space sums, factor them coordinatewise, and insert
  -- the globally trivial neighbor phase.
  apply Finset.sum_congr rfl
  intro Y _
  have hintegrand (Xket Xbra : U → F) :
      (∏ u : U,
          lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) *
          (∏ u : U,
            cSign (completeLocal
              (b u) (c u) (t u) (g u) (e u) (z u)
              (Xket u) (Xbra u))) =
        ∏ u : U,
          (lcKernel (Y u) (Xket u) *
            cSign
              (Xket u * (b u + c u + t u) +
                b u * c u + b u * t u + c u * t u)) *
          (star (lcKernel (Y u) (Xbra u)) *
            cSign
              (Xbra u * (g u + e u + z u) +
                g u * e u + g u * z u + e u * z u)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro u _
    unfold completeLocal
    rw [cSign_add]
    ring
  rw [show
    (∑ Xket : U → F, ∑ Xbra : U → F,
      (∏ u : U,
          lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) *
          ∏ u : U,
            cSign (completeLocal
              (b u) (c u) (t u) (g u) (e u) (z u)
              (Xket u) (Xbra u))) =
      ∑ Xket : U → F, ∑ Xbra : U → F,
        ∏ u : U,
          (lcKernel (Y u) (Xket u) *
            cSign
              (Xket u * (b u + c u + t u) +
                b u * c u + b u * t u + c u * t u)) *
          (star (lcKernel (Y u) (Xbra u)) *
            cSign
              (Xbra u * (g u + e u + z u) +
                g u * e u + g u * z u + e u * z u)) by
    apply Finset.sum_congr rfl
    intro Xket _
    apply Finset.sum_congr rfl
    intro Xbra _
    exact hintegrand Xket Xbra]
  let ketFactor : U → F → Complex := fun u x =>
    lcKernel (Y u) x *
      cSign (x * (b u + c u + t u) +
        b u * c u + b u * t u + c u * t u)
  let braFactor : U → F → Complex := fun u x =>
    star (lcKernel (Y u) x) *
      cSign (x * (g u + e u + z u) +
        g u * e u + g u * z u + e u * z u)
  change
    (∑ Xket : U → F, ∑ Xbra : U → F,
      ∏ u : U, ketFactor u (Xket u) * braFactor u (Xbra u)) =
    ∏ u : U,
      cSign (starRootLocal
        (b u) (c u) (t u) (g u) (e u) (z u) (Y u))
  have hseparate :
      (∑ Xket : U → F, ∑ Xbra : U → F,
        ∏ u : U, ketFactor u (Xket u) * braFactor u (Xbra u)) =
      (∑ Xket : U → F, ∏ u : U, ketFactor u (Xket u)) *
        (∑ Xbra : U → F, ∏ u : U, braFactor u (Xbra u)) := by
    calc
      (∑ Xket : U → F, ∑ Xbra : U → F,
        ∏ u : U, ketFactor u (Xket u) * braFactor u (Xbra u))
          = ∑ Xket : U → F, ∑ Xbra : U → F,
              (∏ u : U, ketFactor u (Xket u)) *
                (∏ u : U, braFactor u (Xbra u)) := by
              simp_rw [Finset.prod_mul_distrib]
      _ = (∑ Xket : U → F, ∏ u : U, ketFactor u (Xket u)) *
          (∑ Xbra : U → F, ∏ u : U, braFactor u (Xbra u)) := by
            rw [Finset.sum_mul_sum]
  rw [hseparate]
  have hket :
      (∑ Xket : U → F, ∏ u : U, ketFactor u (Xket u)) =
        ∏ u : U, ∑ x : F, ketFactor u x := by
    exact (Fintype.prod_sum ketFactor).symm
  have hbra :
      (∑ Xbra : U → F, ∏ u : U, braFactor u (Xbra u)) =
        ∏ u : U, ∑ x : F, braFactor u x := by
    exact (Fintype.prod_sum braFactor).symm
  rw [hket, hbra]
  calc
    (∏ u : U, ∑ x : F, ketFactor u x) *
        (∏ u : U, ∑ x : F, braFactor u x)
        = ((∏ u : U,
              (-Complex.I) ^
                (bitToNat (b u) + bitToNat (c u) + bitToNat (t u))) *
            (∏ u : U,
              Complex.I ^
                (bitToNat (g u) + bitToNat (e u) + bitToNat (z u)))) *
          ((∏ u : U, ∑ x : F, ketFactor u x) *
            (∏ u : U, ∑ x : F, braFactor u x)) := by
              rw [hphase, one_mul]
    _ = (∏ u : U,
            ((-Complex.I) ^
              (bitToNat (b u) + bitToNat (c u) + bitToNat (t u))) *
              (∑ x : F, ketFactor u x)) *
          (∏ u : U,
            (Complex.I ^
              (bitToNat (g u) + bitToNat (e u) + bitToNat (z u))) *
              (∑ x : F, braFactor u x)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          ring
    _ = ∏ u : U,
          (((-Complex.I) ^
            (bitToNat (b u) + bitToNat (c u) + bitToNat (t u))) *
              (∑ x : F, ketFactor u x)) *
            ((Complex.I ^
              (bitToNat (g u) + bitToNat (e u) + bitToNat (z u))) *
              (∑ x : F, braFactor u x)) := by
          symm
          exact Finset.prod_mul_distrib
    _ = ∏ u : U,
          cSign (starRootLocal
            (b u) (c u) (t u) (g u) (e u) (z u) (Y u)) := by
          apply Finset.prod_congr rfl
          intro u _
          exact local_combined_transform
            (b u) (c u) (t u) (g u) (e u) (z u) (Y u)

private theorem sum_PVec_one
    {n : Nat} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : PVec n 1 → M) :
    (∑ p : PVec n 1, f p) = f (zeroVec : PVec n 1) := by
  classical
  rw [Finset.sum_eq_single (zeroVec : PVec n 1)]
  · intro p _ hp
    have hsub : p = (zeroVec : PVec n 1) := by
      funext i
      exact Fin.elim0 i
    exact (hp hsub).elim
  · simp

private theorem fixed_neighbor_count
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d)
    (W : WFun4 n 1 b c) :
    (∑ u : YVec n b × ZVec n c × WVec n d,
      (bitToNat (betaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2) +
        bitToNat (deltaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2) +
        bitToNat (xiW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2))) =
      ∑ u : YVec n b × ZVec n c × WVec n d,
        (bitToNat (gammaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2) +
          bitToNat (etaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2) +
          bitToNat (zetaW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)) := by
  have hB :
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (betaB B (zeroVec : PVec n 1) y z w)) =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (gammaB B (zeroVec : PVec n 1) y z w) := by
    calc
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (betaB B (zeroVec : PVec n 1) y z w))
          = ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
              ∑ w : WVec n d, bitToNat (betaB B p y z w) := by
              symm
              exact sum_PVec_one _
      _ = ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
              ∑ w : WVec n d, bitToNat (gammaB B p y z w) :=
            SquareDiagonal.SingletonLC.sum_beta_bitNat_eq_sum_gamma_bitNat hb B
      _ = ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
              bitToNat (gammaB B (zeroVec : PVec n 1) y z w) :=
            sum_PVec_one _
  have hC :
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (deltaC C (zeroVec : PVec n 1) y z w)) =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (etaC C (zeroVec : PVec n 1) y z w) := by
    calc
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (deltaC C (zeroVec : PVec n 1) y z w))
          = ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
              ∑ w : WVec n d, bitToNat (deltaC C p y z w) := by
              symm
              exact sum_PVec_one _
      _ = ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
              ∑ w : WVec n d, bitToNat (etaC C p y z w) :=
            SquareDiagonal.SingletonLC.sum_delta_bitNat_eq_sum_eta_bitNat hc C
      _ = ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
              bitToNat (etaC C (zeroVec : PVec n 1) y z w) :=
            sum_PVec_one _
  have hW :
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (xiW W (zeroVec : PVec n 1) y z w)) =
      ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (zetaW W (zeroVec : PVec n 1) y z w) := by
    calc
      (∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
        bitToNat (xiW W (zeroVec : PVec n 1) y z w))
          = ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
              ∑ w : WVec n d, bitToNat (xiW W p y z w) := by
              symm
              exact sum_PVec_one _
      _ = ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
              ∑ w : WVec n d, bitToNat (zetaW W p y z w) :=
            SquareDiagonal.SingletonLC.sum_xi_bitNat_eq_sum_zeta_bitNat hd W
      _ = ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
              bitToNat (zetaW W (zeroVec : PVec n 1) y z w) :=
            sum_PVec_one _
  simp only [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  omega

/-- The literal two-copy phase for the three-leaf star target. -/
noncomputable def starLocalPhase
    {n b c d : Nat} [NeZero n]
    (nf : NF4 n 1 b c d) (p : PVec n 1)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) : F :=
  alphaOf nf p y z w *
    (betaOf nf p y z w + gammaOf nf p y z w +
      deltaOf nf p y z w + etaOf nf p y z w +
      xiOf nf p y z w + zetaOf nf p y z w)

/-- The global phase exponent for the three-leaf star target. -/
noncomputable def starPhaseExponentNF
    {n b c d : Nat} [NeZero n]
    (nf : NF4 n 1 b c d) : F :=
  ∑ p : PVec n 1, ∑ y : YVec n b, ∑ z : ZVec n c,
    ∑ w : WVec n d, starLocalPhase nf p y z w

/-- Raw finite-assignment signed sum for the three-leaf star target. -/
noncomputable def StarDeltaNF
    (n b c d : Nat) [NeZero n] : Int :=
  ∑ nf : NF4 n 1 b c d, bitSign (starPhaseExponentNF nf)

private theorem complete_phase_as_completeLocal
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d)
    (W : WFun4 n 1 b c)
    (X : (YVec n b × ZVec n c × WVec n d) → F) :
    phaseExponentNF .complete
        ({ A := (aFun4Equiv n b c d).symm X, B := B, C := C, W := W } :
          NF4 n 1 b c d) =
      ∑ u : YVec n b × ZVec n c × WVec n d,
        completeLocal
          (betaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (deltaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (xiW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (gammaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (etaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (zetaW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (X u) (X u) := by
  unfold phaseExponentNF
  rw [sum_PVec_one]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  rw [localPhase_complete_expanded]
  unfold alphaOf betaOf gammaOf deltaOf etaOf xiOf zetaOf
  unfold betaB gammaB deltaC etaC xiW zetaW
  unfold completeLocal
  change
    X (y, z, w) *
          (B (zeroVec : PVec n 1) (vecSum y) z w +
            B (zeroVec : PVec n 1) (vecSum y + 1) z w +
            C (zeroVec : PVec n 1) y (vecSum z) w +
            C (zeroVec : PVec n 1) y (vecSum z + 1) w +
            W (zeroVec : PVec n 1) y z (vecSum w) +
            W (zeroVec : PVec n 1) y z (vecSum w + 1)) +
        B (zeroVec : PVec n 1) (vecSum y) z w *
            C (zeroVec : PVec n 1) y (vecSum z) w +
        B (zeroVec : PVec n 1) (vecSum y + 1) z w *
            C (zeroVec : PVec n 1) y (vecSum z + 1) w +
        B (zeroVec : PVec n 1) (vecSum y) z w *
            W (zeroVec : PVec n 1) y z (vecSum w) +
        B (zeroVec : PVec n 1) (vecSum y + 1) z w *
            W (zeroVec : PVec n 1) y z (vecSum w + 1) +
        C (zeroVec : PVec n 1) y (vecSum z) w *
            W (zeroVec : PVec n 1) y z (vecSum w) +
        C (zeroVec : PVec n 1) y (vecSum z + 1) w *
            W (zeroVec : PVec n 1) y z (vecSum w + 1) =
      completeLocal
        (B (zeroVec : PVec n 1) (vecSum y) z w)
        (C (zeroVec : PVec n 1) y (vecSum z) w)
        (W (zeroVec : PVec n 1) y z (vecSum w))
        (B (zeroVec : PVec n 1) (vecSum y + 1) z w)
        (C (zeroVec : PVec n 1) y (vecSum z + 1) w)
        (W (zeroVec : PVec n 1) y z (vecSum w + 1))
        (X (y, z, w)) (X (y, z, w))
  unfold completeLocal
  ring

private theorem star_phase_as_starRootLocal
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d)
    (W : WFun4 n 1 b c)
    (X : (YVec n b × ZVec n c × WVec n d) → F) :
    starPhaseExponentNF
        ({ A := (aFun4Equiv n b c d).symm X,
           B := B, C := C, W := W } : NF4 n 1 b c d) =
      ∑ u : YVec n b × ZVec n c × WVec n d,
        starRootLocal
          (betaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (deltaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (xiW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (gammaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (etaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (zetaW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (X u) := by
  unfold starPhaseExponentNF
  rw [sum_PVec_one]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  unfold starLocalPhase
  unfold alphaOf betaOf gammaOf deltaOf etaOf xiOf zetaOf
  unfold betaB gammaB deltaC etaC xiW zetaW
  change
    X (y, z, w) *
          (B (zeroVec : PVec n 1) (vecSum y) z w +
            B (zeroVec : PVec n 1) (vecSum y + 1) z w +
            C (zeroVec : PVec n 1) y (vecSum z) w +
            C (zeroVec : PVec n 1) y (vecSum z + 1) w +
            W (zeroVec : PVec n 1) y z (vecSum w) +
            W (zeroVec : PVec n 1) y z (vecSum w + 1)) =
      starRootLocal
        (B (zeroVec : PVec n 1) (vecSum y) z w)
        (C (zeroVec : PVec n 1) y (vecSum z) w)
        (W (zeroVec : PVec n 1) y z (vecSum w))
        (B (zeroVec : PVec n 1) (vecSum y + 1) z w)
        (C (zeroVec : PVec n 1) y (vecSum z + 1) w)
        (W (zeroVec : PVec n 1) y z (vecSum w + 1))
        (X (y, z, w))
  unfold starRootLocal
  ring

private theorem fixed_fields_finite_transform
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d)
    (W : WFun4 n 1 b c) :
    (∑ A : AFun4 n b c d,
      cSign (phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d))) =
      ∑ A : AFun4 n b c d,
        cSign (starPhaseExponentNF
          ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d)) := by
  let U := YVec n b × ZVec n c × WVec n d
  let eA := aFun4Equiv n b c d
  let bK : U → F := fun u =>
    betaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2
  let cK : U → F := fun u =>
    deltaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2
  let tK : U → F := fun u =>
    xiW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2
  let gB : U → F := fun u =>
    gammaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2
  let eB : U → F := fun u =>
    etaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2
  let zB : U → F := fun u =>
    zetaW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2
  have hcount :
      (∑ u : U,
        (bitToNat (bK u) + bitToNat (cK u) + bitToNat (tK u))) =
      ∑ u : U,
        (bitToNat (gB u) + bitToNat (eB u) + bitToNat (zB u)) := by
    exact fixed_neighbor_count hb hc hd B C W
  have htransform :
      (∑ X : U → F,
        cSign (∑ u : U,
          completeLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u) (X u))) =
      ∑ X : U → F,
        cSign (∑ u : U,
          starRootLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u)) :=
    fixedNeighbors_finiteTransform bK cK tK gB eB zB hcount
  have hcomplete (X : U → F) :
      phaseExponentNF .complete
          ({ A := eA.symm X, B := B, C := C, W := W } :
            NF4 n 1 b c d) =
        ∑ u : U,
          completeLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u) (X u) := by
    exact complete_phase_as_completeLocal B C W X
  have hstar (X : U → F) :
      starPhaseExponentNF
          ({ A := eA.symm X, B := B, C := C, W := W } :
            NF4 n 1 b c d) =
        ∑ u : U,
          starRootLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u) := by
    exact star_phase_as_starRootLocal B C W X
  calc
    (∑ A : AFun4 n b c d,
      cSign (phaseExponentNF .complete
        ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d)))
        = ∑ X : U → F,
            cSign (phaseExponentNF .complete
              ({ A := eA.symm X, B := B, C := C, W := W } :
                NF4 n 1 b c d)) := by
            exact Fintype.sum_equiv eA
              (fun A : AFun4 n b c d =>
                cSign (phaseExponentNF .complete
                  ({ A := A, B := B, C := C, W := W } :
                    NF4 n 1 b c d)))
              (fun X : U → F =>
                cSign (phaseExponentNF .complete
                  ({ A := eA.symm X, B := B, C := C, W := W } :
                    NF4 n 1 b c d)))
              (fun A => by simp [eA])
    _ = ∑ X : U → F,
          cSign (∑ u : U,
            completeLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
              (X u) (X u)) := by
          apply Finset.sum_congr rfl
          intro X _
          rw [hcomplete]
    _ = ∑ X : U → F,
          cSign (∑ u : U,
            starRootLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
              (X u)) := htransform
    _ = ∑ X : U → F,
          cSign (starPhaseExponentNF
            ({ A := eA.symm X, B := B, C := C, W := W } :
              NF4 n 1 b c d)) := by
          apply Finset.sum_congr rfl
          intro X _
          rw [hstar]
    _ = ∑ A : AFun4 n b c d,
        cSign (starPhaseExponentNF
          ({ A := A, B := B, C := C, W := W } :
            NF4 n 1 b c d)) := by
          symm
          exact Fintype.sum_equiv eA
            (fun A : AFun4 n b c d =>
              cSign (starPhaseExponentNF
                ({ A := A, B := B, C := C, W := W } :
                  NF4 n 1 b c d)))
            (fun X : U → F =>
              cSign (starPhaseExponentNF
                ({ A := eA.symm X, B := B, C := C, W := W } :
                  NF4 n 1 b c d)))
            (fun A => by simp [eA])

private theorem sum_nf4_complex_components
    {n a b c d : Nat} [NeZero n]
    (f : NF4 n a b c d → Complex) :
    (∑ nf : NF4 n a b c d, f nf) =
      ∑ A : AFun4 n b c d,
        ∑ B : BFun4 n a c d,
          ∑ C : CFun4 n a b d,
            ∑ W : WFun4 n a b c,
              f ({ A := A, B := B, C := C, W := W } :
                NF4 n a b c d) := by
  let e := nf4EquivProd n a b c d
  calc
    (∑ nf : NF4 n a b c d, f nf) =
        ∑ x : AFun4 n b c d × BFun4 n a c d ×
            CFun4 n a b d × WFun4 n a b c,
          f (e.symm x) := by
            exact Fintype.sum_equiv e f (fun x => f (e.symm x))
              (fun nf => by simp [e])
    _ = ∑ A : AFun4 n b c d,
        ∑ B : BFun4 n a c d,
          ∑ C : CFun4 n a b d,
            ∑ W : WFun4 n a b c,
              f ({ A := A, B := B, C := C, W := W } :
                NF4 n a b c d) := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro A _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro B _
          rw [Fintype.sum_prod_type]
          rfl

/-- For a singleton A root, the literal complete source is related to the
three-leaf star source by the normalized root-diagonal finite transform. -/
theorem DeltaNF_complete_eq_StarDeltaNF_of_a_eq_one
    {n a b c d : Nat} [NeZero n]
    (hn2 : 2 <= n) (ha1 : a = 1)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .complete a b c d n =
      StarDeltaNF n b c d := by
  subst a
  have hn2_used : 2 <= n := hn2
  clear hn2_used
  apply @Int.cast_injective Complex _ _
  unfold DeltaNF StarDeltaNF
  rw [Int.cast_sum, Int.cast_sum]
  simp_rw [← cSign_eq_cast_bitSign]
  calc
    (∑ nf : NF4 n 1 b c d,
      cSign (phaseExponentNF .complete nf))
        = ∑ A : AFun4 n b c d,
            ∑ B : BFun4 n 1 c d,
              ∑ C : CFun4 n 1 b d,
                ∑ W : WFun4 n 1 b c,
                  cSign (phaseExponentNF .complete
                    ({ A := A, B := B, C := C, W := W } :
                      NF4 n 1 b c d)) := by
            rw [sum_nf4_complex_components]
    _ = ∑ B : BFun4 n 1 c d,
          ∑ C : CFun4 n 1 b d,
            ∑ W : WFun4 n 1 b c,
              ∑ A : AFun4 n b c d,
                cSign (phaseExponentNF .complete
                  ({ A := A, B := B, C := C, W := W } :
                    NF4 n 1 b c d)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro B _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro C _
          rw [Finset.sum_comm]
    _ = ∑ B : BFun4 n 1 c d,
          ∑ C : CFun4 n 1 b d,
            ∑ W : WFun4 n 1 b c,
              ∑ A : AFun4 n b c d,
                cSign (starPhaseExponentNF
                  ({ A := A, B := B, C := C, W := W } :
                    NF4 n 1 b c d)) := by
          apply Finset.sum_congr rfl
          intro B _
          apply Finset.sum_congr rfl
          intro C _
          apply Finset.sum_congr rfl
          intro W _
          exact fixed_fields_finite_transform hb hc hd B C W
    _ = ∑ A : AFun4 n b c d,
          ∑ B : BFun4 n 1 c d,
            ∑ C : CFun4 n 1 b d,
              ∑ W : WFun4 n 1 b c,
                cSign (starPhaseExponentNF
                  ({ A := A, B := B, C := C, W := W } :
                    NF4 n 1 b c d)) := by
          calc
            (∑ B : BFun4 n 1 c d,
              ∑ C : CFun4 n 1 b d,
                ∑ W : WFun4 n 1 b c,
                  ∑ A : AFun4 n b c d,
                    cSign (starPhaseExponentNF
                      ({ A := A, B := B, C := C, W := W } :
                        NF4 n 1 b c d)))
                = ∑ B : BFun4 n 1 c d,
                    ∑ C : CFun4 n 1 b d,
                      ∑ A : AFun4 n b c d,
                        ∑ W : WFun4 n 1 b c,
                          cSign (starPhaseExponentNF
                            ({ A := A, B := B, C := C, W := W } :
                              NF4 n 1 b c d)) := by
                    apply Finset.sum_congr rfl
                    intro B _
                    apply Finset.sum_congr rfl
                    intro C _
                    rw [Finset.sum_comm]
            _ = ∑ B : BFun4 n 1 c d,
                  ∑ A : AFun4 n b c d,
                    ∑ C : CFun4 n 1 b d,
                      ∑ W : WFun4 n 1 b c,
                        cSign (starPhaseExponentNF
                          ({ A := A, B := B, C := C, W := W } :
                            NF4 n 1 b c d)) := by
                  apply Finset.sum_congr rfl
                  intro B _
                  rw [Finset.sum_comm]
            _ = ∑ A : AFun4 n b c d,
                  ∑ B : BFun4 n 1 c d,
                    ∑ C : CFun4 n 1 b d,
                      ∑ W : WFun4 n 1 b c,
                        cSign (starPhaseExponentNF
                          ({ A := A, B := B, C := C, W := W } :
                            NF4 n 1 b c d)) := by
                  rw [Finset.sum_comm]
    _ = ∑ nf : NF4 n 1 b c d,
          cSign (starPhaseExponentNF nf) := by
          symm
          rw [sum_nf4_complex_components]


end

end Core4loop.CompleteGraph.SingletonLC
