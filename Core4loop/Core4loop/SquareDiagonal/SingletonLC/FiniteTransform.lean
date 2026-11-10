import Core4loop.SquareDiagonal.SingletonLC.ShiftBalance

open scoped BigOperators

namespace Core4loop.SquareDiagonal.SingletonLC

noncomputable section

private def cSign (x : F) : Complex :=
  (-1 : Complex) ^ bitToNat x

@[simp] private theorem cSign_zero : cSign 0 = 1 := by
  simp [cSign, bitToNat]

private theorem cSign_eq_cast_bitSign (x : F) :
    cSign x = ((bitSign x : Int) : Complex) := by
  fin_cases x <;> norm_num [cSign, bitToNat, bitSign]

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
  simp_rw [lcKernel_orthogonality]
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
  ring

private theorem local_ket_transform
    (b c t y : F) :
    (-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t) *
        (∑ x : F, lcKernel y x *
          cSign (x * (b + c + t) + b * c + c * t)) =
      Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
        cSign (y * (b + c + t) + b * t) := by
  have hsplit :
      (∑ x : F, lcKernel y x *
        cSign (x * (b + c + t) + b * c + c * t)) =
      cSign (b * c + c * t) *
        (∑ x : F, lcKernel y x *
          (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by
    calc
      (∑ x : F, lcKernel y x *
        cSign (x * (b + c + t) + b * c + c * t))
          = ∑ x : F, cSign (b * c + c * t) *
              (lcKernel y x *
                (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [show x * (b + c + t) + b * c + c * t =
                x * (b + c + t) + (b * c + c * t) by ring]
              rw [cSign_add]
              simp only [cSign]
              ring
      _ = cSign (b * c + c * t) *
          (∑ x : F, lcKernel y x *
            (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by
          rw [Finset.mul_sum]
  rw [hsplit]
  calc
    (-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t) *
        (cSign (b * c + c * t) *
          ∑ x : F, lcKernel y x *
            (-1 : Complex) ^ bitToNat (x * (b + c + t)))
        = cSign (b * c + c * t) *
            (((-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t)) *
              ∑ x : F, lcKernel y x *
                (-1 : Complex) ^ bitToNat (x * (b + c + t))) := by ring
    _ = cSign (b * c + c * t) *
          (Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
            (-1 : Complex) ^ bitToNat
              (y * (b + c + t) + b * c + b * t + c * t)) := by
          rw [lcKernel_ket_identity]
    _ = Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
          (cSign (b * c + c * t) *
            cSign (y * (b + c + t) + b * c + b * t + c * t)) := by
          simp only [cSign]
          ring
    _ = Complex.exp (-((Real.pi : Complex) * Complex.I) / 4) *
          cSign (y * (b + c + t) + b * t) := by
          congr 1
          rw [← cSign_add]
          congr 1
          fin_cases b <;> fin_cases c <;> fin_cases t <;> fin_cases y <;> decide

private theorem local_bra_transform
    (g e z y : F) :
    Complex.I ^ (bitToNat g + bitToNat e + bitToNat z) *
        (∑ x : F, star (lcKernel y x) *
          cSign (x * (g + e + z) + g * e + e * z)) =
      Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
        cSign (y * (g + e + z) + g * z) := by
  have hsplit :
      (∑ x : F, star (lcKernel y x) *
        cSign (x * (g + e + z) + g * e + e * z)) =
      cSign (g * e + e * z) *
        (∑ x : F, star (lcKernel y x) *
          (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by
    calc
      (∑ x : F, star (lcKernel y x) *
        cSign (x * (g + e + z) + g * e + e * z))
          = ∑ x : F, cSign (g * e + e * z) *
              (star (lcKernel y x) *
                (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [show x * (g + e + z) + g * e + e * z =
                x * (g + e + z) + (g * e + e * z) by ring]
              rw [cSign_add]
              simp only [cSign]
              ring
      _ = cSign (g * e + e * z) *
          (∑ x : F, star (lcKernel y x) *
            (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by
          rw [Finset.mul_sum]
  rw [hsplit]
  calc
    Complex.I ^ (bitToNat g + bitToNat e + bitToNat z) *
        (cSign (g * e + e * z) *
          ∑ x : F, star (lcKernel y x) *
            (-1 : Complex) ^ bitToNat (x * (g + e + z)))
        = cSign (g * e + e * z) *
            ((Complex.I ^ (bitToNat g + bitToNat e + bitToNat z)) *
              ∑ x : F, star (lcKernel y x) *
                (-1 : Complex) ^ bitToNat (x * (g + e + z))) := by ring
    _ = cSign (g * e + e * z) *
          (Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
            (-1 : Complex) ^ bitToNat
              (y * (g + e + z) + g * e + g * z + e * z)) := by
          rw [lcKernel_bra_identity]
    _ = Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
          (cSign (g * e + e * z) *
            cSign (y * (g + e + z) + g * e + g * z + e * z)) := by
          simp only [cSign]
          ring
    _ = Complex.exp (((Real.pi : Complex) * Complex.I) / 4) *
          cSign (y * (g + e + z) + g * z) := by
          congr 1
          rw [← cSign_add]
          congr 1
          fin_cases g <;> fin_cases e <;> fin_cases z <;> fin_cases y <;> decide

private theorem local_combined_transform
    (b c t g e z y : F) :
    (((-Complex.I) ^ (bitToNat b + bitToNat c + bitToNat t)) *
        (∑ x : F, lcKernel y x *
          cSign (x * (b + c + t) + b * c + c * t))) *
      ((Complex.I ^ (bitToNat g + bitToNat e + bitToNat z)) *
        (∑ x : F, star (lcKernel y x) *
          cSign (x * (g + e + z) + g * e + e * z))) =
      cSign
        (y * (b + g + c + e + t + z) + b * t + g * z) := by
  rw [local_ket_transform, local_bra_transform]
  rw [mul_mul_mul_comm, exp_neg_mul_exp_pos, one_mul]
  rw [← cSign_add]
  congr 1
  ring

private def diamondLocal
    (b c t g e z xket xbra : F) : F :=
  xket * (b + c + t) + b * c + c * t +
  (xbra * (g + e + z) + g * e + e * z)

private def triangleLocal
    (b c t g e z y : F) : F :=
  y * (b + g + c + e + t + z) + b * t + g * z

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
        diamondLocal (b u) (c u) (t u) (g u) (e u) (z u) (A u) (A u))) =
    ∑ Y : U → F,
      cSign (∑ u : U,
        triangleLocal (b u) (c u) (t u) (g u) (e u) (z u) (Y u)) := by
  classical
  rw [rootDiagonal_sum_eq_lcExpandedSum
    (Ffun := fun Xket Xbra =>
      cSign (∑ u : U,
        diamondLocal (b u) (c u) (t u) (g u) (e u) (z u)
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
            cSign (diamondLocal
              (b u) (c u) (t u) (g u) (e u) (z u)
              (Xket u) (Xbra u))) =
        ∏ u : U,
          (lcKernel (Y u) (Xket u) *
            cSign
              (Xket u * (b u + c u + t u) +
                b u * c u + c u * t u)) *
          (star (lcKernel (Y u) (Xbra u)) *
            cSign
              (Xbra u * (g u + e u + z u) +
                g u * e u + e u * z u)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro u _
    unfold diamondLocal
    rw [cSign_add]
    ring
  rw [show
    (∑ Xket : U → F, ∑ Xbra : U → F,
      (∏ u : U,
          lcKernel (Y u) (Xket u) * star (lcKernel (Y u) (Xbra u))) *
          ∏ u : U,
            cSign (diamondLocal
              (b u) (c u) (t u) (g u) (e u) (z u)
              (Xket u) (Xbra u))) =
      ∑ Xket : U → F, ∑ Xbra : U → F,
        ∏ u : U,
          (lcKernel (Y u) (Xket u) *
            cSign
              (Xket u * (b u + c u + t u) +
                b u * c u + c u * t u)) *
          (star (lcKernel (Y u) (Xbra u)) *
            cSign
              (Xbra u * (g u + e u + z u) +
                g u * e u + e u * z u)) by
    apply Finset.sum_congr rfl
    intro Xket _
    apply Finset.sum_congr rfl
    intro Xbra _
    exact hintegrand Xket Xbra]
  let ketFactor : U → F → Complex := fun u x =>
    lcKernel (Y u) x *
      cSign (x * (b u + c u + t u) + b u * c u + c u * t u)
  let braFactor : U → F → Complex := fun u x =>
    star (lcKernel (Y u) x) *
      cSign (x * (g u + e u + z u) + g u * e u + e u * z u)
  change
    (∑ Xket : U → F, ∑ Xbra : U → F,
      ∏ u : U, ketFactor u (Xket u) * braFactor u (Xbra u)) =
    ∏ u : U,
      cSign (triangleLocal
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
          cSign (triangleLocal
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

private def singletonSwapCW
    {n b c d : Nat}
    (nf : NF4 n 1 b c d) : NF4 n 1 b d c where
  A := fun y w z => nf.A y z w
  B := fun p sy w z => nf.B p sy z w
  C := fun p y sw z => nf.W p y z sw
  W := fun p y w sz => nf.C p y sz w

private noncomputable def singletonSwapCWEquiv
    (n b c d : Nat) :
    NF4 n 1 b c d ≃ NF4 n 1 b d c where
  toFun := singletonSwapCW
  invFun := singletonSwapCW
  left_inv nf := by
    cases nf
    rfl
  right_inv nf := by
    cases nf
    rfl

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
            sum_beta_bitNat_eq_sum_gamma_bitNat hb B
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
            sum_delta_bitNat_eq_sum_eta_bitNat hc C
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
            sum_xi_bitNat_eq_sum_zeta_bitNat hd W
      _ = ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
              bitToNat (zetaW W (zeroVec : PVec n 1) y z w) :=
            sum_PVec_one _
  simp only [Fintype.sum_prod_type]
  simp_rw [Finset.sum_add_distrib]
  omega

private theorem square_phase_as_diamondLocal
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d)
    (W : WFun4 n 1 b c)
    (X : (YVec n b × ZVec n c × WVec n d) → F) :
    phaseExponentNF .squareDiagonal
        ({ A := (aFun4Equiv n b c d).symm X, B := B, C := C, W := W } :
          NF4 n 1 b c d) =
      ∑ u : YVec n b × ZVec n c × WVec n d,
        diamondLocal
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
  rw [localPhase_squareDiagonal_expanded]
  unfold alphaOf betaOf gammaOf deltaOf etaOf xiOf zetaOf
  unfold betaB gammaB deltaC etaC xiW zetaW
  unfold diamondLocal
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
        C (zeroVec : PVec n 1) y (vecSum z) w *
            W (zeroVec : PVec n 1) y z (vecSum w) +
        C (zeroVec : PVec n 1) y (vecSum z + 1) w *
            W (zeroVec : PVec n 1) y z (vecSum w + 1) =
      diamondLocal
        (B (zeroVec : PVec n 1) (vecSum y) z w)
        (C (zeroVec : PVec n 1) y (vecSum z) w)
        (W (zeroVec : PVec n 1) y z (vecSum w))
        (B (zeroVec : PVec n 1) (vecSum y + 1) z w)
        (C (zeroVec : PVec n 1) y (vecSum z + 1) w)
        (W (zeroVec : PVec n 1) y z (vecSum w + 1))
        (X (y, z, w)) (X (y, z, w))
  unfold diamondLocal
  ring

private theorem triangle_phase_after_swap_as_triangleLocal
    {n b c d : Nat} [NeZero n]
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d)
    (W : WFun4 n 1 b c)
    (X : (YVec n b × ZVec n c × WVec n d) → F) :
    phaseExponentNF .triangleLeaf
        (singletonSwapCW
          ({ A := (aFun4Equiv n b c d).symm X,
             B := B, C := C, W := W } : NF4 n 1 b c d)) =
      ∑ u : YVec n b × ZVec n c × WVec n d,
        triangleLocal
          (betaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (deltaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (xiW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (gammaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (etaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (zetaW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (X u) := by
  unfold phaseExponentNF
  rw [sum_PVec_one]
  have hprod :
      (∑ u : YVec n b × ZVec n c × WVec n d,
        triangleLocal
          (betaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (deltaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (xiW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (gammaB B (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (etaC C (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (zetaW W (zeroVec : PVec n 1) u.1 u.2.1 u.2.2)
          (X u)) =
        ∑ y : YVec n b, ∑ z : ZVec n c, ∑ w : WVec n d,
          triangleLocal
            (betaB B (zeroVec : PVec n 1) y z w)
            (deltaC C (zeroVec : PVec n 1) y z w)
            (xiW W (zeroVec : PVec n 1) y z w)
            (gammaB B (zeroVec : PVec n 1) y z w)
            (etaC C (zeroVec : PVec n 1) y z w)
            (zetaW W (zeroVec : PVec n 1) y z w)
            (X (y, z, w)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    rw [Fintype.sum_prod_type]
  rw [hprod]
  -- The target coordinate order is `(y, old-w, old-z)`.  Swap the two
  -- innermost sums to compare with the old `(y, old-z, old-w)` order.
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  rw [localPhase_triangleLeaf_expanded]
  unfold singletonSwapCW
  unfold alphaOf betaOf gammaOf deltaOf etaOf xiOf zetaOf
  unfold betaB gammaB deltaC etaC xiW zetaW
  unfold triangleLocal
  change
    X (y, z, w) *
          (B (zeroVec : PVec n 1) (vecSum y) z w +
            B (zeroVec : PVec n 1) (vecSum y + 1) z w +
            W (zeroVec : PVec n 1) y z (vecSum w) +
            W (zeroVec : PVec n 1) y z (vecSum w + 1) +
            C (zeroVec : PVec n 1) y (vecSum z) w +
            C (zeroVec : PVec n 1) y (vecSum z + 1) w) +
        B (zeroVec : PVec n 1) (vecSum y) z w *
            W (zeroVec : PVec n 1) y z (vecSum w) +
        B (zeroVec : PVec n 1) (vecSum y + 1) z w *
            W (zeroVec : PVec n 1) y z (vecSum w + 1) =
      triangleLocal
        (B (zeroVec : PVec n 1) (vecSum y) z w)
        (C (zeroVec : PVec n 1) y (vecSum z) w)
        (W (zeroVec : PVec n 1) y z (vecSum w))
        (B (zeroVec : PVec n 1) (vecSum y + 1) z w)
        (C (zeroVec : PVec n 1) y (vecSum z + 1) w)
        (W (zeroVec : PVec n 1) y z (vecSum w + 1))
        (X (y, z, w))
  unfold triangleLocal
  ring

private theorem fixed_fields_finite_transform
    {n b c d : Nat} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (B : BFun4 n 1 c d) (C : CFun4 n 1 b d)
    (W : WFun4 n 1 b c) :
    (∑ A : AFun4 n b c d,
      cSign (phaseExponentNF .squareDiagonal
        ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d))) =
      ∑ A : AFun4 n b c d,
        cSign (phaseExponentNF .triangleLeaf
          (singletonSwapCW
            ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d))) := by
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
          diamondLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u) (X u))) =
      ∑ X : U → F,
        cSign (∑ u : U,
          triangleLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u)) :=
    fixedNeighbors_finiteTransform bK cK tK gB eB zB hcount
  have hsq (X : U → F) :
      phaseExponentNF .squareDiagonal
          ({ A := eA.symm X, B := B, C := C, W := W } :
            NF4 n 1 b c d) =
        ∑ u : U,
          diamondLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u) (X u) := by
    exact square_phase_as_diamondLocal B C W X
  have htl (X : U → F) :
      phaseExponentNF .triangleLeaf
          (singletonSwapCW
            ({ A := eA.symm X, B := B, C := C, W := W } :
              NF4 n 1 b c d)) =
        ∑ u : U,
          triangleLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
            (X u) := by
    exact triangle_phase_after_swap_as_triangleLocal B C W X
  calc
    (∑ A : AFun4 n b c d,
      cSign (phaseExponentNF .squareDiagonal
        ({ A := A, B := B, C := C, W := W } : NF4 n 1 b c d)))
        = ∑ X : U → F,
            cSign (phaseExponentNF .squareDiagonal
              ({ A := eA.symm X, B := B, C := C, W := W } :
                NF4 n 1 b c d)) := by
            exact Fintype.sum_equiv eA
              (fun A : AFun4 n b c d =>
                cSign (phaseExponentNF .squareDiagonal
                  ({ A := A, B := B, C := C, W := W } :
                    NF4 n 1 b c d)))
              (fun X : U → F =>
                cSign (phaseExponentNF .squareDiagonal
                  ({ A := eA.symm X, B := B, C := C, W := W } :
                    NF4 n 1 b c d)))
              (fun A => by simp [eA])
    _ = ∑ X : U → F,
          cSign (∑ u : U,
            diamondLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
              (X u) (X u)) := by
          apply Finset.sum_congr rfl
          intro X _
          rw [hsq]
    _ = ∑ X : U → F,
          cSign (∑ u : U,
            triangleLocal (bK u) (cK u) (tK u) (gB u) (eB u) (zB u)
              (X u)) := htransform
    _ = ∑ X : U → F,
          cSign (phaseExponentNF .triangleLeaf
            (singletonSwapCW
              ({ A := eA.symm X, B := B, C := C, W := W } :
                NF4 n 1 b c d))) := by
          apply Finset.sum_congr rfl
          intro X _
          rw [htl]
    _ = ∑ A : AFun4 n b c d,
        cSign (phaseExponentNF .triangleLeaf
          (singletonSwapCW
            ({ A := A, B := B, C := C, W := W } :
              NF4 n 1 b c d))) := by
          symm
          exact Fintype.sum_equiv eA
            (fun A : AFun4 n b c d =>
              cSign (phaseExponentNF .triangleLeaf
                (singletonSwapCW
                  ({ A := A, B := B, C := C, W := W } :
                    NF4 n 1 b c d))))
            (fun X : U → F =>
              cSign (phaseExponentNF .triangleLeaf
                (singletonSwapCW
                  ({ A := eA.symm X, B := B, C := C, W := W } :
                    NF4 n 1 b c d))))
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

theorem DeltaNF_squareDiagonal_eq_triangleLeaf_of_a_eq_one
    {n a b c d : Nat} [NeZero n]
    (_hn2 : 2 <= n) (ha1 : a = 1)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    DeltaNF .squareDiagonal a b c d n =
      DeltaNF .triangleLeaf a b d c n := by
  subst a
  apply @Int.cast_injective Complex _ _
  unfold DeltaNF
  rw [Int.cast_sum, Int.cast_sum]
  simp_rw [← cSign_eq_cast_bitSign]
  calc
    (∑ nf : NF4 n 1 b c d,
      cSign (phaseExponentNF .squareDiagonal nf))
        = ∑ A : AFun4 n b c d,
            ∑ B : BFun4 n 1 c d,
              ∑ C : CFun4 n 1 b d,
                ∑ W : WFun4 n 1 b c,
                  cSign (phaseExponentNF .squareDiagonal
                    ({ A := A, B := B, C := C, W := W } :
                      NF4 n 1 b c d)) := by
            rw [sum_nf4_complex_components]
    _ = ∑ B : BFun4 n 1 c d,
          ∑ C : CFun4 n 1 b d,
            ∑ W : WFun4 n 1 b c,
              ∑ A : AFun4 n b c d,
                cSign (phaseExponentNF .squareDiagonal
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
                cSign (phaseExponentNF .triangleLeaf
                  (singletonSwapCW
                    ({ A := A, B := B, C := C, W := W } :
                      NF4 n 1 b c d))) := by
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
                cSign (phaseExponentNF .triangleLeaf
                  (singletonSwapCW
                    ({ A := A, B := B, C := C, W := W } :
                      NF4 n 1 b c d))) := by
          calc
            (∑ B : BFun4 n 1 c d,
              ∑ C : CFun4 n 1 b d,
                ∑ W : WFun4 n 1 b c,
                  ∑ A : AFun4 n b c d,
                    cSign (phaseExponentNF .triangleLeaf
                      (singletonSwapCW
                        ({ A := A, B := B, C := C, W := W } :
                          NF4 n 1 b c d))))
                = ∑ B : BFun4 n 1 c d,
                    ∑ C : CFun4 n 1 b d,
                      ∑ A : AFun4 n b c d,
                        ∑ W : WFun4 n 1 b c,
                          cSign (phaseExponentNF .triangleLeaf
                            (singletonSwapCW
                              ({ A := A, B := B, C := C, W := W } :
                                NF4 n 1 b c d))) := by
                    apply Finset.sum_congr rfl
                    intro B _
                    apply Finset.sum_congr rfl
                    intro C _
                    rw [Finset.sum_comm]
            _ = ∑ B : BFun4 n 1 c d,
                  ∑ A : AFun4 n b c d,
                    ∑ C : CFun4 n 1 b d,
                      ∑ W : WFun4 n 1 b c,
                        cSign (phaseExponentNF .triangleLeaf
                          (singletonSwapCW
                            ({ A := A, B := B, C := C, W := W } :
                              NF4 n 1 b c d))) := by
                  apply Finset.sum_congr rfl
                  intro B _
                  rw [Finset.sum_comm]
            _ = ∑ A : AFun4 n b c d,
                  ∑ B : BFun4 n 1 c d,
                    ∑ C : CFun4 n 1 b d,
                      ∑ W : WFun4 n 1 b c,
                        cSign (phaseExponentNF .triangleLeaf
                          (singletonSwapCW
                            ({ A := A, B := B, C := C, W := W } :
                              NF4 n 1 b c d))) := by
                  rw [Finset.sum_comm]
    _ = ∑ nf : NF4 n 1 b c d,
          cSign (phaseExponentNF .triangleLeaf (singletonSwapCW nf)) := by
          symm
          rw [sum_nf4_complex_components]
    _ = ∑ nf : NF4 n 1 b d c,
          cSign (phaseExponentNF .triangleLeaf nf) := by
          exact Fintype.sum_equiv (singletonSwapCWEquiv n b c d)
            (fun nf : NF4 n 1 b c d =>
              cSign (phaseExponentNF .triangleLeaf (singletonSwapCW nf)))
            (fun nf : NF4 n 1 b d c =>
              cSign (phaseExponentNF .triangleLeaf nf))
            (fun _ => rfl)


end

end Core4loop.SquareDiagonal.SingletonLC
