import No16.Symplectic

open scoped BigOperators

namespace No16

/-!
The odd-case factorization and final odd formula for `Delta16` will live here.
-/

def bSlice {n : ℕ} (B : BFun n) (t p q' : I n) : Profile n :=
  fun a => B a t p q'

def cSlice {n : ℕ} (C : CFun n) (v w r : I n) : Profile n :=
  fun a => C a v w r

noncomputable def oddHeadB {n : ℕ} [NeZero n] (B : BFun n) : BCoef n :=
  fun t p q' => sigma (bSlice B t p q')

noncomputable def oddHeadC {n : ℕ} [NeZero n] (C : CFun n) : CCoef n :=
  fun v w r => sigma (cSlice C v w r)

noncomputable def oddTailB {n : ℕ} [NeZero n] (B : BFun n) : BFun n :=
  fun a t p q' => B a t p q' + oddHeadB B t p q'

noncomputable def oddTailC {n : ℕ} [NeZero n] (C : CFun n) : CFun n :=
  fun a v w r => C a v w r + oddHeadC C v w r

noncomputable def oddVisibleB {n : ℕ} [NeZero n] (B : BFun n) : BFun n :=
  tensorB (oneProfile (n := n)) (oddHeadB B)

noncomputable def oddVisibleC {n : ℕ} [NeZero n] (C : CFun n) : CFun n :=
  tensorC (oneProfile (n := n)) (oddHeadC C)

def oddBuildB {n : ℕ} [NeZero n] (b : BCoef n) (R : BFun n) : BFun n :=
  tensorB (oneProfile (n := n)) b + R

def oddBuildC {n : ℕ} [NeZero n] (c : CCoef n) (R : CFun n) : CFun n :=
  tensorC (oneProfile (n := n)) c + R

lemma oddHeadB_eq_sigma_slice {n : ℕ} [NeZero n] (B : BFun n) (t p q' : I n) :
    oddHeadB B t p q' = sigma (bSlice B t p q') := rfl

lemma oddHeadC_eq_sigma_slice {n : ℕ} [NeZero n] (C : CFun n) (v w r : I n) :
    oddHeadC C v w r = sigma (cSlice C v w r) := rfl

lemma oddVisibleB_apply {n : ℕ} [NeZero n] (B : BFun n) (a t p q' : I n) :
    oddVisibleB B a t p q' = oddHeadB B t p q' := by
  simp [oddVisibleB, tensorB, oneProfile]

lemma oddVisibleC_apply {n : ℕ} [NeZero n] (C : CFun n) (a v w r : I n) :
    oddVisibleC C a v w r = oddHeadC C v w r := by
  simp [oddVisibleC, tensorC, oneProfile]

lemma sigma_const_odd {n : ℕ} [NeZero n] (hn : Odd n) (c : F) :
    sigma (fun _ : I n => c) = c := by
  fin_cases c
  · change sigma (0 : Profile n) = 0
    simp [sigma]
  · simpa [oneProfile] using sigma_oneProfile_odd (n := n) hn

lemma sum_pair_add_eq_of_odd {n : ℕ} [NeZero n] (hn : Odd n) (g : I n → F) :
    ∑ v : I n, ∑ w : I n, g (v + w) = ∑ t : I n, g t := by
  calc
    ∑ v : I n, ∑ w : I n, g (v + w) = ∑ v : I n, ∑ t : I n, g t := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      simpa using sum_reindex_addLeft (n := n) (a := v) (f := g)
    _ = sigma (fun _ : I n => ∑ t : I n, g t) := by
      rfl
    _ = ∑ t : I n, g t := by
      simpa [sigma] using sigma_const_odd (n := n) hn (∑ t : I n, g t)

lemma sum_pair_add_h_eq_colSum_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (h : HFun n) (s : I n) :
    ∑ v : I n, ∑ w : I n, h (v + w) s = colSum h s := by
  simpa [colSum] using sum_pair_add_eq_of_odd (n := n) hn (fun t => h t s)

lemma sum_pair_add_h_eq_rowSum_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (h : HFun n) (t : I n) :
    ∑ p : I n, ∑ q' : I n, h t (p + q') = rowSum h t := by
  simpa [rowSum] using sum_pair_add_eq_of_odd (n := n) hn (fun s => h t s)

lemma sum_const_I_odd {n : ℕ} [NeZero n] (hn : Odd n) (c : F) :
    ∑ a : I n, c = c := by
  change sigma (fun _ : I n => c) = c
  exact sigma_const_odd (n := n) hn c

lemma sum_mul_prefix_nat_symm (n : ℕ) (f g : ℕ → F) :
    (Finset.sum (Finset.range n) (fun s => f s * Finset.sum (Finset.range s) g)) +
      (Finset.sum (Finset.range n) (fun s => g s * Finset.sum (Finset.range s) f)) =
        (Finset.sum (Finset.range n) f) * (Finset.sum (Finset.range n) g) +
          Finset.sum (Finset.range n) (fun s => f s * g s) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let A : F := Finset.sum (Finset.range n) (fun s => f s * Finset.sum (Finset.range s) g)
      let B : F := Finset.sum (Finset.range n) (fun s => g s * Finset.sum (Finset.range s) f)
      let Fsum : F := Finset.sum (Finset.range n) f
      let Gsum : F := Finset.sum (Finset.range n) g
      let D : F := Finset.sum (Finset.range n) (fun s => f s * g s)
      have hih : A + B = Fsum * Gsum + D := by
        simpa [A, B, Fsum, Gsum, D] using ih
      calc
        (Finset.sum (Finset.range (n + 1)) (fun s => f s * Finset.sum (Finset.range s) g)) +
            (Finset.sum (Finset.range (n + 1)) (fun s => g s * Finset.sum (Finset.range s) f))
            = f n * Gsum + (g n * Fsum + (A + B)) := by
                simp [A, B, Fsum, Gsum, Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]
        _ = f n * Gsum + (g n * Fsum + (Fsum * Gsum + D)) := by rw [hih]
        _ = (Fsum + f n) * (Gsum + g n) + (D + f n * g n) := by
              calc
                f n * Gsum + (g n * Fsum + (Fsum * Gsum + D))
                    = 0 + (f n * Gsum + (g n * Fsum + (Fsum * Gsum + D))) := by simp
                _ = (f n * g n + f n * g n) + (f n * Gsum + (g n * Fsum + (Fsum * Gsum + D))) := by
                      rw [F_add_self]
                _ = f n * g n + (f n * g n + (f n * Gsum + (g n * Fsum + (Fsum * Gsum + D)))) := by
                      ac_rfl
                _ = (Fsum + f n) * (Gsum + g n) + (D + f n * g n) := by
                      simp [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, add_assoc,
                        add_left_comm, add_comm, F_add_self]
        _ = (Finset.sum (Finset.range (n + 1)) f) * (Finset.sum (Finset.range (n + 1)) g) +
              Finset.sum (Finset.range (n + 1)) (fun s => f s * g s) := by
              simp [Fsum, Gsum, D, Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]

def bConst {n : ℕ} [NeZero n] (u : UVFun n) : BCoef n :=
  fun _ p q' => u p q'

def cConst {n : ℕ} [NeZero n] (v : UVFun n) : CCoef n :=
  fun x y _ => v x y

noncomputable def bPref {n : ℕ} [NeZero n] (h : HFun n) : BCoef n :=
  buildB h 0

noncomputable def cPref {n : ℕ} [NeZero n] (h : HFun n) : CCoef n :=
  buildC h 0

lemma bPref_add {n : ℕ} [NeZero n] (h k : HFun n) :
    bPref (h + k) = bPref h + bPref k := by
  funext t p q'
  simp [bPref, buildB, prefixT, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma cPref_add {n : ℕ} [NeZero n] (h k : HFun n) :
    cPref (h + k) = cPref h + cPref k := by
  funext t p q'
  simp [cPref, buildC, prefixR, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma buildB_eq_bConst_add_bPref {n : ℕ} [NeZero n] (h : HFun n) (u : UVFun n) :
    buildB h u = bConst u + bPref h := by
  funext t p q'
  simp [bConst, bPref, buildB, add_assoc, add_left_comm, add_comm]

lemma buildC_eq_cConst_add_cPref {n : ℕ} [NeZero n] (h : HFun n) (v : UVFun n) :
    buildC h v = cConst v + cPref h := by
  funext x y r
  simp [cConst, cPref, buildC, add_assoc, add_left_comm, add_comm]

lemma q_bConst_cConst_eq_zero {n : ℕ} [NeZero n]
    (u v : UVFun n) :
    q (bConst u) (cConst v) = 0 := by
  rw [q_eq_qLeft_add_qRight]
  have hsame : qLeft (bConst u) (cConst v) = qRight (bConst u) (cConst v) := by
    unfold qLeft qRight bConst cConst
    simp [add_assoc, add_left_comm, add_comm]
  rw [hsame]
  simp [F_add_self]

set_option maxHeartbeats 800000 in
-- This proof reorders four nested finite sums before applying the odd pair-collapse lemmas.
lemma q_bConst_cPref_eq_zero_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    {h : HFun n} (hh : h ∈ HSpace (n := n)) (u : UVFun n) :
    q (bConst u) (cPref h) = 0 := by
  unfold q bConst cPref buildC
  simp only [Pi.zero_apply, add_zero]
  have hmain :
      (∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
        u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1))) = 0 := by
    have hswap :
      ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
        u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1))
        =
      ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ w : I n,
        u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
      calc
        ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
            u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1))
          = ∑ v : I n, ∑ p : I n, ∑ w : I n, ∑ q' : I n,
              u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro v hv
                rw [Finset.sum_comm]
        _ = ∑ p : I n, ∑ v : I n, ∑ w : I n, ∑ q' : I n,
              u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
                rw [Finset.sum_comm]
        _ = ∑ p : I n, ∑ v : I n, ∑ q' : I n, ∑ w : I n,
              u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                refine Finset.sum_congr rfl ?_
                intro v hv
                rw [Finset.sum_comm]
        _ = ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ w : I n,
              u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                rw [Finset.sum_comm]
    have hfactor :
      ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ w : I n,
        u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1))
        =
      ∑ p : I n, ∑ q' : I n,
        u p q' * ∑ v : I n, ∑ w : I n,
          (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      calc
        ∑ v : I n, ∑ w : I n,
            u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1))
          = ∑ v : I n,
              u p q' * ∑ w : I n,
                (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
                  refine Finset.sum_congr rfl ?_
                  intro v hv
                  rw [← Finset.mul_sum]
        _ = u p q' * ∑ v : I n, ∑ w : I n,
              (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := by
                rw [← Finset.mul_sum]
    calc
      ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
          u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1))
        = ∑ p : I n, ∑ q' : I n, ∑ v : I n, ∑ w : I n,
            u p q' * (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := hswap
      _ = ∑ p : I n, ∑ q' : I n,
            u p q' * ∑ v : I n, ∑ w : I n,
              (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) := hfactor
      _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro p hp
            refine Finset.sum_eq_zero ?_
            intro q' hq'
            have hvw :
                ∑ v : I n, ∑ w : I n,
                  (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1)) = 0 := by
              calc
                ∑ v : I n, ∑ w : I n,
                    (prefixR h (v + w) (p + q') + prefixR h (v + w) (p + q' + 1))
                  = ∑ v : I n, ∑ w : I n, h (v + w) (p + q') := by
                      refine Finset.sum_congr rfl ?_
                      intro v hv
                      refine Finset.sum_congr rfl ?_
                      intro w hw
                      rw [prefixR_pair_eq_of_mem_HSpace hh (v + w) (p + q')]
                _ = colSum h (p + q') := by
                      exact sum_pair_add_h_eq_colSum_of_odd (n := n) hn h (p + q')
                _ = 0 := colSum_eq_zero_of_mem_HSpace hh (p + q')
            rw [hvw]
            simp
  simpa [mul_add] using hmain

lemma q_bPref_cConst_eq_zero_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    {h : HFun n} (hh : h ∈ HSpace (n := n)) (vfun : UVFun n) :
    q (bPref h) (cConst vfun) = 0 := by
  unfold q bPref cConst buildB
  simp only [Pi.zero_apply, add_zero]
  have hmain :
      (∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
        (prefixT h (v + w) (p + q') + prefixT h (v + w + 1) (p + q')) * vfun v w) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro v hv
    refine Finset.sum_eq_zero ?_
    intro w hw
    have hpq :
        ∑ p : I n, ∑ q' : I n,
          (prefixT h (v + w) (p + q') + prefixT h (v + w + 1) (p + q')) * vfun v w = 0 := by
      calc
        ∑ p : I n, ∑ q' : I n,
            (prefixT h (v + w) (p + q') + prefixT h (v + w + 1) (p + q')) * vfun v w
          = (∑ p : I n,
              (∑ q' : I n,
                (prefixT h (v + w) (p + q') + prefixT h (v + w + 1) (p + q'))) * vfun v w) := by
                refine Finset.sum_congr rfl ?_
                intro p hp
                rw [← Finset.sum_mul]
        _ = (∑ p : I n, ∑ q' : I n,
              (prefixT h (v + w) (p + q') + prefixT h (v + w + 1) (p + q'))) * vfun v w := by
                rw [← Finset.sum_mul]
        _ = rowSum h (v + w) * vfun v w := by
              congr 1
              calc
                ∑ p : I n, ∑ q' : I n,
                    (prefixT h (v + w) (p + q') + prefixT h (v + w + 1) (p + q'))
                  = ∑ p : I n, ∑ q' : I n, h (v + w) (p + q') := by
                      refine Finset.sum_congr rfl ?_
                      intro p hp
                      refine Finset.sum_congr rfl ?_
                      intro q' hq'
                      rw [prefixT_pair_eq_of_mem_HSpace hh (v + w) (p + q')]
                _ = rowSum h (v + w) := by
                      exact sum_pair_add_h_eq_rowSum_of_odd (n := n) hn h (v + w)
        _ = 0 := by
              rw [rowSum_eq_zero_of_mem_HSpace hh (v + w)]
              simp
    exact hpq
  simpa [add_mul] using hmain

lemma bPair_add_left {n : ℕ} [NeZero n] (b₁ b₂ b : BCoef n) :
    bPair (b₁ + b₂) b = bPair b₁ b + bPair b₂ b := by
  unfold bPair
  simp [add_mul, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma cPair_add_right {n : ℕ} [NeZero n] (c c₁ c₂ : CCoef n) :
    cPair c (c₁ + c₂) = cPair c c₁ + cPair c c₂ := by
  unfold cPair
  simp [mul_add, Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm]

lemma q_add_left {n : ℕ} [NeZero n] (b₁ b₂ : BCoef n) (c : CCoef n) :
    q (b₁ + b₂) c = q b₁ c + q b₂ c := by
  rw [q_eq_bPair_T, q_eq_bPair_T, q_eq_bPair_T]
  rw [bPair_add_left]

lemma q_add_right {n : ℕ} [NeZero n] (b : BCoef n) (c₁ c₂ : CCoef n) :
    q b (c₁ + c₂) = q b c₁ + q b c₂ := by
  rw [q_eq_cPair_Tadj, q_eq_cPair_Tadj, q_eq_cPair_Tadj]
  rw [cPair_add_right]

lemma q_bPref_add_left {n : ℕ} [NeZero n] (h₁ h₂ k : HFun n) :
    q (bPref (h₁ + h₂)) (cPref k) = q (bPref h₁) (cPref k) + q (bPref h₂) (cPref k) := by
  rw [bPref_add, q_add_left]

lemma q_bPref_add_right {n : ℕ} [NeZero n] (h k₁ k₂ : HFun n) :
    q (bPref h) (cPref (k₁ + k₂)) = q (bPref h) (cPref k₁) + q (bPref h) (cPref k₂) := by
  rw [cPref_add, q_add_right]

lemma q_build_eq_q_bPref_cPref_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    {h : HFun n} (hh : h ∈ HSpace (n := n)) (u v : UVFun n) :
    q (buildB h u) (buildC h v) = q (bPref h) (cPref h) := by
  rw [buildB_eq_bConst_add_bPref, buildC_eq_cConst_add_cPref]
  rw [q_add_left]
  rw [q_add_right, q_add_right]
  rw [q_bConst_cConst_eq_zero, q_bConst_cPref_eq_zero_of_odd (hn := hn) hh]
  rw [q_bPref_cConst_eq_zero_of_odd (hn := hn) hh]
  ac_rfl

set_option maxHeartbeats 800000 in
-- Reordering the four finite sums and normalizing the cyclic prefix identities is expensive here.
lemma q_bPref_cPref_formula_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    {h : HFun n} (hh : h ∈ HSpace (n := n)) :
    q (bPref h) (cPref h) =
      ∑ t : I n, ∑ s : I n, h t s * (prefixT h t s + prefixR h t s + 1) := by
  let E : I n → I n → F := fun t s =>
    prefixT h t s * prefixR h t s +
      prefixT h (t + 1) s * prefixR h t (s + 1)
  have hcollapse_pq :
      ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, E (v + w) (p + q') =
        ∑ v : I n, ∑ w : I n, ∑ s : I n, E (v + w) s := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    refine Finset.sum_congr rfl ?_
    intro w hw
    simpa using sum_pair_add_eq_of_odd (n := n) hn (fun s => E (v + w) s)
  have hcollapse_vw :
      ∑ v : I n, ∑ w : I n, ∑ s : I n, E (v + w) s =
        ∑ t : I n, ∑ s : I n, E t s := by
    calc
      ∑ v : I n, ∑ w : I n, ∑ s : I n, E (v + w) s
        = ∑ v : I n, ∑ s : I n, ∑ w : I n, E (v + w) s := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            rw [Finset.sum_comm]
      _ = ∑ s : I n, ∑ v : I n, ∑ w : I n, E (v + w) s := by
            rw [Finset.sum_comm]
      _ = ∑ s : I n, ∑ t : I n, E t s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simpa using sum_pair_add_eq_of_odd (n := n) hn (fun t => E t s)
      _ = ∑ t : I n, ∑ s : I n, E t s := by
            rw [Finset.sum_comm]
  have hPt :
      ∀ t s : I n, prefixT h (t + 1) s = prefixT h t s + h t s := by
    intro t s
    have hp := prefixT_pair_eq_of_mem_HSpace hh t s
    apply add_left_cancel (a := prefixT h t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hp
  have hQs :
      ∀ t s : I n, prefixR h t (s + 1) = prefixR h t s + h t s := by
    intro t s
    have hq := prefixR_pair_eq_of_mem_HSpace hh t s
    apply add_left_cancel (a := prefixR h t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hq
  unfold q bPref cPref buildB buildC
  simp only [Pi.zero_apply, add_zero, zero_add]
  change ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, E (v + w) (p + q') =
    ∑ t : I n, ∑ s : I n, h t s * (prefixT h t s + prefixR h t s + 1)
  rw [hcollapse_pq, hcollapse_vw]
  refine Finset.sum_congr rfl ?_
  intro t ht
  refine Finset.sum_congr rfl ?_
  intro s hs
  change
    prefixT h t s * prefixR h t s + prefixT h (t + 1) s * prefixR h t (s + 1) =
      h t s * (prefixT h t s + prefixR h t s + 1)
  rw [hPt t s, hQs t s]
  simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm, F_add_self]
  have hsqF : ∀ x : F, x * x = x := by
    intro x
    fin_cases x <;> native_decide
  have hsq : h t s * h t s = h t s := by
    exact hsqF (h t s)
  rw [hsq, mul_comm (prefixT h t s) (h t s)]

set_option maxHeartbeats 800000 in
-- Same finite-sum normalization as the diagonal formula, but with separate left/right profile data.
lemma q_bPref_cPref_formula_mixed_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    {h k : HFun n} (hh : h ∈ HSpace (n := n)) (hk : k ∈ HSpace (n := n)) :
    q (bPref h) (cPref k) =
      ∑ t : I n, ∑ s : I n,
        ((h t s * prefixR k t s) + (prefixT h t s * k t s) + (h t s * k t s)) := by
  let E : I n → I n → F := fun t s =>
    prefixT h t s * prefixR k t s +
      prefixT h (t + 1) s * prefixR k t (s + 1)
  have hcollapse_pq :
      ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, E (v + w) (p + q') =
        ∑ v : I n, ∑ w : I n, ∑ s : I n, E (v + w) s := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    refine Finset.sum_congr rfl ?_
    intro w hw
    simpa using sum_pair_add_eq_of_odd (n := n) hn (fun s => E (v + w) s)
  have hcollapse_vw :
      ∑ v : I n, ∑ w : I n, ∑ s : I n, E (v + w) s =
        ∑ t : I n, ∑ s : I n, E t s := by
    calc
      ∑ v : I n, ∑ w : I n, ∑ s : I n, E (v + w) s
        = ∑ v : I n, ∑ s : I n, ∑ w : I n, E (v + w) s := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            rw [Finset.sum_comm]
      _ = ∑ s : I n, ∑ v : I n, ∑ w : I n, E (v + w) s := by
            rw [Finset.sum_comm]
      _ = ∑ s : I n, ∑ t : I n, E t s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simpa using sum_pair_add_eq_of_odd (n := n) hn (fun t => E t s)
      _ = ∑ t : I n, ∑ s : I n, E t s := by
            rw [Finset.sum_comm]
  have hPt :
      ∀ t s : I n, prefixT h (t + 1) s = prefixT h t s + h t s := by
    intro t s
    have hp := prefixT_pair_eq_of_mem_HSpace hh t s
    apply add_left_cancel (a := prefixT h t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hp
  have hQs :
      ∀ t s : I n, prefixR k t (s + 1) = prefixR k t s + k t s := by
    intro t s
    have hq := prefixR_pair_eq_of_mem_HSpace hk t s
    apply add_left_cancel (a := prefixR k t s)
    simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hq
  unfold q bPref cPref buildB buildC
  simp only [Pi.zero_apply, add_zero, zero_add]
  change ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, E (v + w) (p + q') =
    Finset.sum Finset.univ
      (fun t : I n =>
        Finset.sum Finset.univ
          (fun s : I n => (h t s * prefixR k t s) + (prefixT h t s * k t s) + (h t s * k t s)))
  rw [hcollapse_pq, hcollapse_vw]
  refine Finset.sum_congr rfl ?_
  intro t ht
  refine Finset.sum_congr rfl ?_
  intro s hs
  change
    prefixT h t s * prefixR k t s + prefixT h (t + 1) s * prefixR k t (s + 1) =
      (h t s * prefixR k t s) + (prefixT h t s * k t s) + (h t s * k t s)
  rw [hPt t s, hQs t s]
  simp [mul_add, add_mul, add_assoc, add_left_comm, add_comm, F_add_self]

abbrev OddRectIndex (n : ℕ) [NeZero n] := INonzero n × INonzero n

noncomputable def oddRectVec {n : ℕ} [NeZero n] (i : OddRectIndex n) : HSpace (n := n) :=
  ⟨rect i.1.1 i.2.1, rect_mem_HSpace i.1.1 i.2.1⟩

lemma rect_apply_oddRectIndex {n : ℕ} [NeZero n] (i j : OddRectIndex n) :
    rect i.1.1 i.2.1 j.1.1 j.2.1 = if j = i then 1 else 0 := by
  rw [rect_apply_nonzero_nonzero i.1.2 i.2.2 j.1.2 j.2.2]
  by_cases h : j = i
  · simp [h]
  · have hneq : ¬ (j.1.1 = i.1.1 ∧ j.2.1 = i.2.1) := by
      intro hji
      apply h
      rcases i with ⟨⟨i1, hi1⟩, ⟨i2, hi2⟩⟩
      rcases j with ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩
      cases hji with
      | intro h1 h2 =>
          simp only at h1 h2
          subst h1
          subst h2
          rfl
    simp [h, hneq]

lemma linearIndependent_oddRectVec {n : ℕ} [NeZero n] :
    LinearIndependent F (oddRectVec (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro l hl i
  have hEval :=
    congrFun (congrFun (congrArg Subtype.val hl) i.1.1) i.2.1
  simpa [oddRectVec, rect_apply_oddRectIndex] using hEval

lemma card_oddRectIndex {n : ℕ} [NeZero n] :
    Fintype.card (OddRectIndex n) = (n - 1) ^ 2 := by
  simp [OddRectIndex, card_INonzero, pow_two]

lemma span_oddRectVec_eq_top {n : ℕ} [NeZero n] :
    Submodule.span F (Set.range (oddRectVec (n := n))) = ⊤ := by
  have hspanfin :
      Fintype.card (OddRectIndex n) =
        Module.finrank F (Submodule.span F (Set.range (oddRectVec (n := n)))) :=
    linearIndependent_iff_card_eq_finrank_span.mp (linearIndependent_oddRectVec (n := n))
  have hcard :
      Fintype.card (OddRectIndex n) = Module.finrank F (HSpace (n := n)) := by
    rw [card_oddRectIndex, finrank_HSpace (n := n)]
  exact Submodule.eq_top_of_finrank_eq (hspanfin.symm.trans hcard)

lemma top_le_span_oddRectVec {n : ℕ} [NeZero n] :
    ⊤ ≤ Submodule.span F (Set.range (oddRectVec (n := n))) := by
  simpa [span_oddRectVec_eq_top (n := n)]

noncomputable def oddRectBasis {n : ℕ} [NeZero n] :
    Module.Basis (OddRectIndex n) F (HSpace (n := n)) :=
  Module.Basis.mk (linearIndependent_oddRectVec (n := n)) (top_le_span_oddRectVec (n := n))

@[simp] lemma oddRectBasis_apply {n : ℕ} [NeZero n] (i : OddRectIndex n) :
    oddRectBasis (n := n) i = oddRectVec (n := n) i := by
  simpa [oddRectBasis]

lemma rect_row_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (ht0 : t ≠ 0) (hta : t ≠ a) :
    rect a b t s = 0 := by
  unfold rect pointH
  by_cases hs0 : s = 0 <;> by_cases hsb : s = b <;>
    simp [ht0, hta, hs0, hsb]

lemma rect_row_zero_eq {n : ℕ} [NeZero n] {a b s : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b 0 s = if s = 0 then 1 else if s = b then 1 else 0 := by
  unfold rect pointH
  by_cases hs0 : s = 0
  · subst hs0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
    simp [pointH, h0a, h0b, ha]
  · by_cases hsb : s = b
    · subst hsb
      have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
      simp [pointH, h0a, hb]
    · simp [hs0, hsb, ha, hb]

lemma rect_row_a_eq {n : ℕ} [NeZero n] {a b s : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b a s = if s = 0 then 1 else if s = b then 1 else 0 := by
  unfold rect pointH
  by_cases hs0 : s = 0
  · subst hs0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
    simpa [pointH, h0a, h0b, ha, hb]
  · by_cases hsb : s = b
    · subst hsb
      simp [pointH, ha, hb]
    · simp [hs0, hsb, ha, hb]

lemma rect_col_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (hs0 : s ≠ 0) (hsb : s ≠ b) :
    rect a b t s = 0 := by
  unfold rect pointH
  by_cases ht0 : t = 0 <;> by_cases hta : t = a <;>
    simp [hs0, hsb, ht0, hta]

lemma rect_col_zero_eq {n : ℕ} [NeZero n] {a b t : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b t 0 = if t = 0 then 1 else if t = a then 1 else 0 := by
  unfold rect pointH
  by_cases ht0 : t = 0
  · subst ht0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
    simp [pointH, h0a, h0b, ha]
  · by_cases hta : t = a
    · subst hta
      have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
      simp [pointH, ha, h0b]
    · simp [ht0, hta, ha, hb]

lemma rect_col_b_eq {n : ℕ} [NeZero n] {a b t : I n} (ha : a ≠ 0) (hb : b ≠ 0) :
    rect a b t b = if t = 0 then 1 else if t = a then 1 else 0 := by
  unfold rect pointH
  by_cases ht0 : t = 0
  · subst ht0
    have h0a : (0 : I n) ≠ a := by simpa [eq_comm] using ha
    simp [pointH, h0a, ha, hb]
  · by_cases hta : t = a
    · subst hta
      have h0b : (0 : I n) ≠ b := by simpa [eq_comm] using hb
      simp [pointH, h0b, ha, hb]
    · simp [ht0, hta, ha, hb]

lemma prefixT_rect_a_zero_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) a 0 = 1 := by
  unfold prefixT
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_zero_eq (a := a) (b := b) ha hb, hb]
  · intro i hi hi0
    have hit0 : ((i : ℕ) : I n) ≠ 0 := by
      have hi_lt : i < n := Nat.lt_trans (Finset.mem_range.mp hi) (ZMod.val_lt a)
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt hi_lt
      intro h
      have : i = 0 := by
        simpa [hiv] using congrArg ZMod.val h
      exact hi0 this
    have hita : ((i : ℕ) : I n) ≠ a := by
      intro hia
      have hi_lt : i < a.val := Finset.mem_range.mp hi
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt a))
      have hav : a.val = i := by
        rw [← hiv]
        exact congrArg ZMod.val hia.symm
      have : ¬ i < a.val := by omega
      exact this (by simpa [hav] using hi_lt)
    simp [rect_row_other_eq_zero (s := (0 : I n)) hit0 hita]
  · have : a ≠ 0 := ha
    simp [this]

lemma prefixR_rect_zero_b_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) 0 b = 1 := by
  unfold prefixR
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_zero_eq (a := a) (b := b) ha hb]
  · intro j hj hj0
    have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
      have hj_lt : j < n := Nat.lt_trans (Finset.mem_range.mp hj) (ZMod.val_lt b)
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt hj_lt
      intro h
      have : j = 0 := by
        simpa [hjv] using congrArg ZMod.val h
      exact hj0 this
    have hjsb : ((j : ℕ) : I n) ≠ b := by
      intro hjb
      have hj_lt : j < b.val := Finset.mem_range.mp hj
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt b))
      have hbv : b.val = j := by
        rw [← hjv]
        exact congrArg ZMod.val hjb.symm
      have : ¬ j < b.val := by omega
      exact this (by simpa [hbv] using hj_lt)
    simp [rect_row_zero_eq (a := a) (b := b) ha hb, hjs0, hjsb]
  · simp [hb]

lemma prefixT_rect_a_b_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) a b = 1 := by
  unfold prefixT
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_zero_eq (a := a) (b := b) ha hb, hb]
  · intro i hi hi0
    have hit0 : ((i : ℕ) : I n) ≠ 0 := by
      have hi_lt : i < n := Nat.lt_trans (Finset.mem_range.mp hi) (ZMod.val_lt a)
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt hi_lt
      intro h
      have : i = 0 := by
        simpa [hiv] using congrArg ZMod.val h
      exact hi0 this
    have hita : ((i : ℕ) : I n) ≠ a := by
      intro hia
      have hi_lt : i < a.val := Finset.mem_range.mp hi
      have hiv : (((i : ℕ) : I n)).val = i := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt a))
      have hav : a.val = i := by
        rw [← hiv]
        exact congrArg ZMod.val hia.symm
      have : ¬ i < a.val := by omega
      exact this (by simpa [hav] using hi_lt)
    simp [rect_row_other_eq_zero (s := b) hit0 hita]
  · simp [ha]

lemma prefixT_rect_t_zero_eq_indicator {n : ℕ} [NeZero n] {a b t : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) t 0 = if t = 0 then 0 else if t.val ≤ a.val then 1 else 0 := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [prefixT_zero]
  · unfold prefixT
    by_cases hta : t.val ≤ a.val
    · have htpos : 0 < t.val := Nat.pos_of_ne_zero (by
          intro h
          have htzero : ((t.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val t)
          have htz : t = 0 := by
            simpa using ((ZMod.natCast_zmod_val t).symm.trans htzero)
          exact ht0 htz)
      rw [Finset.sum_eq_single 0]
      · simp [rect_row_zero_eq (a := a) (b := b) ha hb, ht0, hta]
      · intro i hi hi0
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hi_lt : i < t.val := Finset.mem_range.mp hi
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_lt_t : i < t.val := Finset.mem_range.mp hi
          have hi_lt_a : i < a.val := lt_of_lt_of_le hi_lt_t hta
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          have : ¬ i < a.val := by omega
          exact this (by simpa [hav] using hi_lt_a)
        simp [rect_row_other_eq_zero (s := (0 : I n)) hit0 hita]
      · simp [htpos]
    · have hat : a.val < t.val := lt_of_not_ge hta
      have h0mem : (0 : ℕ) ∈ Finset.range t.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hat)
      have ha0 : a.val ≠ 0 := by
        intro hav
        have hazero : ((a.val : ℕ) : I n) = 0 := by
          simpa [hav] using (ZMod.natCast_zmod_val a)
        have hza : a = 0 := by
          simpa using ((ZMod.natCast_zmod_val a).symm.trans hazero)
        exact ha hza
      have hamem : a.val ∈ (Finset.range t.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact ha0
        · exact Finset.mem_range.mpr hat
      have hrest :
          Finset.sum (((Finset.range t.val).erase 0).erase a.val)
            (fun i => rect a b (i : I n) 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hi0 : i ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).1
        have hi_lt_t : i < t.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).2)
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita' : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_ne_a : i ≠ a.val := by simpa using (Finset.mem_erase.mp hi).1
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          exact hi_ne_a hav.symm
        simp [rect_row_other_eq_zero (s := (0 : I n)) hit0 hita']
      have hsum0 := (Finset.sum_erase_add (Finset.range t.val) (fun i => rect a b (i : I n) 0) h0mem).symm
      have hsuma := (Finset.sum_erase_add ((Finset.range t.val).erase 0) (fun i => rect a b (i : I n) 0) hamem).symm
      rw [hsum0, hsuma]
      have ha_lt_n : a.val < n := ZMod.val_lt a
      simp [hrest, rect_row_a_eq (a := a) (b := b) ha hb, rect_row_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt ha_lt_n, ha, hb, ht0, hat, add_assoc, F_add_self]

lemma prefixT_rect_t_b_eq_indicator {n : ℕ} [NeZero n] {a b t : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixT (rect a b) t b = if t = 0 then 0 else if t.val ≤ a.val then 1 else 0 := by
  by_cases ht0 : t = 0
  · subst ht0
    simp [prefixT_zero]
  · unfold prefixT
    by_cases hta : t.val ≤ a.val
    · have htpos : 0 < t.val := Nat.pos_of_ne_zero (by
          intro h
          have htzero : ((t.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val t)
          have htz : t = 0 := by
            simpa using ((ZMod.natCast_zmod_val t).symm.trans htzero)
          exact ht0 htz)
      rw [Finset.sum_eq_single 0]
      · simp [rect_row_zero_eq (a := a) (b := b) ha hb, ht0, hta]
      · intro i hi hi0
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hi_lt : i < t.val := Finset.mem_range.mp hi
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_lt_t : i < t.val := Finset.mem_range.mp hi
          have hi_lt_a : i < a.val := lt_of_lt_of_le hi_lt_t hta
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          have : ¬ i < a.val := by omega
          exact this (by simpa [hav] using hi_lt_a)
        simp [rect_row_other_eq_zero (s := b) hit0 hita]
      · simp [htpos]
    · have hat : a.val < t.val := lt_of_not_ge hta
      have h0mem : (0 : ℕ) ∈ Finset.range t.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hat)
      have ha0 : a.val ≠ 0 := by
        intro hav
        have hazero : ((a.val : ℕ) : I n) = 0 := by
          simpa [hav] using (ZMod.natCast_zmod_val a)
        have hza : a = 0 := by
          simpa using ((ZMod.natCast_zmod_val a).symm.trans hazero)
        exact ha hza
      have hamem : a.val ∈ (Finset.range t.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact ha0
        · exact Finset.mem_range.mpr hat
      have hrest :
          Finset.sum (((Finset.range t.val).erase 0).erase a.val)
            (fun i => rect a b (i : I n) b) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hi0 : i ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).1
        have hi_lt_t : i < t.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hi).2)).2)
        have hit0 : ((i : ℕ) : I n) ≠ 0 := by
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          intro h
          have : i = 0 := by simpa [hiv] using congrArg ZMod.val h
          exact hi0 this
        have hita' : ((i : ℕ) : I n) ≠ a := by
          intro hia
          have hi_ne_a : i ≠ a.val := by simpa using (Finset.mem_erase.mp hi).1
          have hiv : (((i : ℕ) : I n)).val = i := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hi_lt_t (ZMod.val_lt t))
          have hav : a.val = i := by
            rw [← hiv]
            exact congrArg ZMod.val hia.symm
          exact hi_ne_a hav.symm
        simp [rect_row_other_eq_zero (s := b) hit0 hita']
      have hsum0 := (Finset.sum_erase_add (Finset.range t.val) (fun i => rect a b (i : I n) b) h0mem).symm
      have hsuma := (Finset.sum_erase_add ((Finset.range t.val).erase 0) (fun i => rect a b (i : I n) b) hamem).symm
      rw [hsum0, hsuma]
      have ha_lt_n : a.val < n := ZMod.val_lt a
      simp [hrest, rect_row_a_eq (a := a) (b := b) ha hb, rect_row_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt ha_lt_n, ha, hb, ht0, hat, add_assoc, F_add_self]

lemma prefixR_rect_a_b_eq_one {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) a b = 1 := by
  unfold prefixR
  rw [Finset.sum_eq_single 0]
  · simp [rect_row_a_eq (a := a) ha hb, hb]
  · intro j hj hj0
    have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
      have hj_lt : j < n := Nat.lt_trans (Finset.mem_range.mp hj) (ZMod.val_lt b)
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt hj_lt
      intro h
      have : j = 0 := by
        simpa [hjv] using congrArg ZMod.val h
      exact hj0 this
    have hjsb : ((j : ℕ) : I n) ≠ b := by
      intro hjb
      have hj_lt : j < b.val := Finset.mem_range.mp hj
      have hjv : (((j : ℕ) : I n)).val = j := by
        exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt b))
      have hbv : b.val = j := by
        rw [← hjv]
        exact congrArg ZMod.val hjb.symm
      have : ¬ j < b.val := by omega
      exact this (by simpa [hbv] using hj_lt)
    simp [rect_row_a_eq (a := a) ha hb, hjs0, hjsb]
  · simp [hb]

lemma prefixR_rect_zero_s_eq_indicator {n : ℕ} [NeZero n] {a b s : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) 0 s = if s = 0 then 0 else if s.val ≤ b.val then 1 else 0 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [prefixR_zero]
  · unfold prefixR
    by_cases hsb : s.val ≤ b.val
    · have hspos : 0 < s.val := Nat.pos_of_ne_zero (by
          intro h
          have hszero : ((s.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val s)
          have hzs : s = 0 := by
            simpa using ((ZMod.natCast_zmod_val s).symm.trans hszero)
          exact hs0 hzs)
      rw [Finset.sum_eq_single 0]
      · simp [rect_col_zero_eq (a := a) (b := b) ha hb, hs0, hsb]
      · intro j hj hj0
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hj_lt : j < s.val := Finset.mem_range.mp hj
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_lt_s : j < s.val := Finset.mem_range.mp hj
          have hj_lt_b : j < b.val := lt_of_lt_of_le hj_lt_s hsb
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          have : ¬ j < b.val := by omega
          exact this (by simpa [hbv] using hj_lt_b)
        simp [rect_col_other_eq_zero (t := (0 : I n)) hjs0 hjsb]
      · simp [hspos]
    · have hbs : b.val < s.val := lt_of_not_ge hsb
      have h0mem : (0 : ℕ) ∈ Finset.range s.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hbs)
      have hb0 : b.val ≠ 0 := by
        intro hv
        have hbzero : ((b.val : ℕ) : I n) = 0 := by
          simpa [hv] using (ZMod.natCast_zmod_val b)
        have hzb : b = 0 := by
          simpa using ((ZMod.natCast_zmod_val b).symm.trans hbzero)
        exact hb hzb
      have hbmem : b.val ∈ (Finset.range s.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact hb0
        · exact Finset.mem_range.mpr hbs
      have hrest :
          Finset.sum (((Finset.range s.val).erase 0).erase b.val)
            (fun j => rect a b 0 (j : I n)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hj0 : j ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).1
        have hj_lt_s : j < s.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).2)
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_ne_b : j ≠ b.val := by simpa using (Finset.mem_erase.mp hj).1
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          exact hj_ne_b hbv.symm
        simp [rect_col_other_eq_zero (t := (0 : I n)) hjs0 hjsb]
      have hsum0 := (Finset.sum_erase_add (Finset.range s.val) (fun j => rect a b 0 (j : I n)) h0mem).symm
      have hsumb := (Finset.sum_erase_add ((Finset.range s.val).erase 0) (fun j => rect a b 0 (j : I n)) hbmem).symm
      rw [hsum0, hsumb]
      have hb_lt_n : b.val < n := ZMod.val_lt b
      simp [hrest, rect_col_b_eq (a := a) (b := b) ha hb, rect_col_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt hb_lt_n, ha, hb, hs0, hbs, add_assoc, F_add_self]

lemma prefixR_rect_a_s_eq_indicator {n : ℕ} [NeZero n] {a b s : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    prefixR (rect a b) a s = if s = 0 then 0 else if s.val ≤ b.val then 1 else 0 := by
  by_cases hs0 : s = 0
  · subst hs0
    simp [prefixR_zero]
  · unfold prefixR
    by_cases hsb : s.val ≤ b.val
    · have hspos : 0 < s.val := Nat.pos_of_ne_zero (by
          intro h
          have hszero : ((s.val : ℕ) : I n) = 0 := by
            simpa [h] using (ZMod.natCast_zmod_val s)
          have hzs : s = 0 := by
            simpa using ((ZMod.natCast_zmod_val s).symm.trans hszero)
          exact hs0 hzs)
      rw [Finset.sum_eq_single 0]
      · simp [rect_col_zero_eq (a := a) (b := b) ha hb, hs0, hsb]
      · intro j hj hj0
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hj_lt : j < s.val := Finset.mem_range.mp hj
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_lt_s : j < s.val := Finset.mem_range.mp hj
          have hj_lt_b : j < b.val := lt_of_lt_of_le hj_lt_s hsb
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          have : ¬ j < b.val := by omega
          exact this (by simpa [hbv] using hj_lt_b)
        simp [rect_col_other_eq_zero (t := a) hjs0 hjsb]
      · simp [hspos]
    · have hbs : b.val < s.val := lt_of_not_ge hsb
      have h0mem : (0 : ℕ) ∈ Finset.range s.val := Finset.mem_range.mpr (Nat.zero_lt_of_lt hbs)
      have hb0 : b.val ≠ 0 := by
        intro hv
        have hbzero : ((b.val : ℕ) : I n) = 0 := by
          simpa [hv] using (ZMod.natCast_zmod_val b)
        have hzb : b = 0 := by
          simpa using ((ZMod.natCast_zmod_val b).symm.trans hbzero)
        exact hb hzb
      have hbmem : b.val ∈ (Finset.range s.val).erase 0 := by
        refine Finset.mem_erase.mpr ?_
        constructor
        · exact hb0
        · exact Finset.mem_range.mpr hbs
      have hrest :
          Finset.sum (((Finset.range s.val).erase 0).erase b.val)
            (fun j => rect a b a (j : I n)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hj0 : j ≠ 0 := by simpa using (Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).1
        have hj_lt_s : j < s.val := by
          exact Finset.mem_range.mp ((Finset.mem_erase.mp ((Finset.mem_erase.mp hj).2)).2)
        have hjs0 : ((j : ℕ) : I n) ≠ 0 := by
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          intro h
          have : j = 0 := by simpa [hjv] using congrArg ZMod.val h
          exact hj0 this
        have hjsb : ((j : ℕ) : I n) ≠ b := by
          intro hjb
          have hj_ne_b : j ≠ b.val := by simpa using (Finset.mem_erase.mp hj).1
          have hjv : (((j : ℕ) : I n)).val = j := by
            exact ZMod.val_natCast_of_lt (Nat.lt_trans hj_lt_s (ZMod.val_lt s))
          have hbv : b.val = j := by
            rw [← hjv]
            exact congrArg ZMod.val hjb.symm
          exact hj_ne_b hbv.symm
        simp [rect_col_other_eq_zero (t := a) hjs0 hjsb]
      have hsum0 := (Finset.sum_erase_add (Finset.range s.val) (fun j => rect a b a (j : I n)) h0mem).symm
      have hsumb := (Finset.sum_erase_add ((Finset.range s.val).erase 0) (fun j => rect a b a (j : I n)) hbmem).symm
      rw [hsum0, hsumb]
      have hb_lt_n : b.val < n := ZMod.val_lt b
      simp [hrest, rect_col_b_eq (a := a) (b := b) ha hb, rect_col_zero_eq (a := a) (b := b) ha hb,
        ZMod.val_natCast_of_lt hb_lt_n, ha, hb, hs0, hbs, add_assoc, F_add_self]

lemma prefixR_rect_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (ht0 : t ≠ 0) (hta : t ≠ a) :
    prefixR (rect a b) t s = 0 := by
  unfold prefixR
  refine Finset.sum_eq_zero ?_
  intro j hj
  simp [rect_row_other_eq_zero (s := ((j : ℕ) : I n)) ht0 hta]

lemma prefixT_rect_t_other_eq_zero {n : ℕ} [NeZero n] {a b t s : I n}
    (hs0 : s ≠ 0) (hsb : s ≠ b) :
    prefixT (rect a b) t s = 0 := by
  unfold prefixT
  refine Finset.sum_eq_zero ?_
  intro i hi
  simp [rect_col_other_eq_zero (t := ((i : ℕ) : I n)) hs0 hsb]

lemma sum_rect_row_zero_mul_eq {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (g : I n → F) :
    ∑ s : I n, rect a b 0 s * g s = g 0 + g b := by
  have h0mem : (0 : I n) ∈ Finset.univ := by simp
  have hbmem : b ∈ Finset.univ.erase (0 : I n) := by simp [hb]
  have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun x => rect a b 0 x * g x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hsin : s ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp hs).2
    have hs0 : s ≠ 0 := by simpa using (Finset.mem_erase.mp hsin).1
    have hsb : s ≠ b := by simpa using (Finset.mem_erase.mp hs).1
    simp [rect_row_zero_eq (a := a) (b := b) ha hb, hs0, hsb]
  calc
    ∑ s : I n, rect a b 0 s * g s
        = Finset.sum (Finset.univ.erase (0 : I n)) (fun s => rect a b 0 s * g s) +
            rect a b 0 0 * g 0 := by
              simpa using (Finset.sum_erase_add Finset.univ (fun s => rect a b 0 s * g s) h0mem).symm
    _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun s => rect a b 0 s * g s) +
          rect a b 0 b * g b) + rect a b 0 0 * g 0 := by
            simpa [add_assoc] using congrArg (fun x => x + rect a b 0 0 * g 0)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun s => rect a b 0 s * g s) hbmem).symm)
    _ = 0 + rect a b 0 b * g b + rect a b 0 0 * g 0 := by simp [hrest]
    _ = g 0 + g b := by
          simp [rect_row_zero_eq (a := a) (b := b) ha hb, hb, add_assoc, add_left_comm, add_comm]

lemma sum_rect_row_a_mul_eq {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (g : I n → F) :
    ∑ s : I n, rect a b a s * g s = g 0 + g b := by
  have h0mem : (0 : I n) ∈ Finset.univ := by simp
  have hbmem : b ∈ Finset.univ.erase (0 : I n) := by simp [hb]
  have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun x => rect a b a x * g x) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hsin : s ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp hs).2
    have hs0 : s ≠ 0 := by simpa using (Finset.mem_erase.mp hsin).1
    have hsb : s ≠ b := by simpa using (Finset.mem_erase.mp hs).1
    simp [rect_row_a_eq (a := a) ha hb, hs0, hsb]
  calc
    ∑ s : I n, rect a b a s * g s
        = Finset.sum (Finset.univ.erase (0 : I n)) (fun s => rect a b a s * g s) +
            rect a b a 0 * g 0 := by
              simpa using (Finset.sum_erase_add Finset.univ (fun s => rect a b a s * g s) h0mem).symm
    _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun s => rect a b a s * g s) +
          rect a b a b * g b) + rect a b a 0 * g 0 := by
            simpa [add_assoc] using congrArg (fun x => x + rect a b a 0 * g 0)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun s => rect a b a s * g s) hbmem).symm)
    _ = 0 + rect a b a b * g b + rect a b a 0 * g 0 := by simp [hrest]
    _ = g 0 + g b := by
          simp [rect_row_a_eq (a := a) ha hb, hb, add_assoc, add_left_comm, add_comm]

lemma sum_rect_row_other_mul_eq_zero {n : ℕ} [NeZero n] {a b t : I n}
    (ht0 : t ≠ 0) (hta : t ≠ a) (g : I n → F) :
    ∑ s : I n, rect a b t s * g s = 0 := by
  refine Finset.sum_eq_zero ?_
  intro s hs
  simp [rect_row_other_eq_zero (s := s) ht0 hta]

lemma sum_rect_mul_eq_corners {n : ℕ} [NeZero n] {a b : I n}
    (ha : a ≠ 0) (hb : b ≠ 0) (g : I n → I n → F) :
    ∑ t : I n, ∑ s : I n, rect a b t s * g t s = g 0 0 + g 0 b + g a 0 + g a b := by
  have h0mem : (0 : I n) ∈ Finset.univ := by simp
  have hamem : a ∈ Finset.univ.erase (0 : I n) := by simp [ha]
  have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase a) (fun x => ∑ s : I n, rect a b x s * g x s) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have htin : t ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp ht).2
    have ht0 : t ≠ 0 := by simpa using (Finset.mem_erase.mp htin).1
    have hta : t ≠ a := by simpa using (Finset.mem_erase.mp ht).1
    simp [sum_rect_row_other_mul_eq_zero (a := a) (b := b) ht0 hta (g := fun s => g t s)]
  calc
    ∑ t : I n, ∑ s : I n, rect a b t s * g t s
        = Finset.sum (Finset.univ.erase (0 : I n)) (fun t => ∑ s : I n, rect a b t s * g t s) +
            ∑ s : I n, rect a b 0 s * g 0 s := by
              simpa using (Finset.sum_erase_add Finset.univ (fun t => ∑ s : I n, rect a b t s * g t s) h0mem).symm
    _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase a) (fun t => ∑ s : I n, rect a b t s * g t s) +
          ∑ s : I n, rect a b a s * g a s) + ∑ s : I n, rect a b 0 s * g 0 s := by
            simpa [add_assoc] using congrArg (fun x => x + ∑ s : I n, rect a b 0 s * g 0 s)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun t => ∑ s : I n, rect a b t s * g t s) hamem).symm)
    _ = 0 + (∑ s : I n, rect a b a s * g a s) + (∑ s : I n, rect a b 0 s * g 0 s) := by simp [hrest]
    _ = (g a 0 + g a b) + (g 0 0 + g 0 b) := by
          rw [sum_rect_row_a_mul_eq (a := a) (b := b) ha hb (g := fun s => g a s)]
          rw [sum_rect_row_zero_mul_eq (a := a) (b := b) ha hb (g := fun s => g 0 s)]
          simp
    _ = g 0 0 + g 0 b + g a 0 + g a b := by ac_rfl

noncomputable def oddRectPair {n : ℕ} [NeZero n] (i j : OddRectIndex n) : F :=
  q (bPref (oddRectVec (n := n) i).1) (cPref (oddRectVec (n := n) j).1)

lemma sum_rect_mul_prefixR_rect_eq {n : ℕ} [NeZero n]
    {a b c d : I n} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∑ t : I n, ∑ s : I n, rect a b t s * prefixR (rect c d) t s =
      (if b.val ≤ d.val then 1 else 0) + (if a = c then (if b.val ≤ d.val then 1 else 0) else 0) := by
  rw [sum_rect_mul_eq_corners (a := a) (b := b) ha hb (g := fun t s => prefixR (rect c d) t s)]
  by_cases hac : a = c
  · subst hac
    simp [prefixR_zero, prefixR_rect_zero_s_eq_indicator (a := a) (b := d) hc hd,
      prefixR_rect_a_s_eq_indicator (a := a) (b := d) hc hd, hb]
  · have ha0 : a ≠ 0 := ha
    have hother : prefixR (rect c d) a b = 0 := prefixR_rect_other_eq_zero (a := c) (b := d) ha0 hac
    simp [prefixR_zero, prefixR_rect_zero_s_eq_indicator (a := c) (b := d) hc hd, hb, hac, hother]

lemma sum_prefixT_rect_mul_rect_eq {n : ℕ} [NeZero n]
    {a b c d : I n} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∑ t : I n, ∑ s : I n, prefixT (rect a b) t s * rect c d t s =
      (if c.val ≤ a.val then 1 else 0) + (if b = d then (if c.val ≤ a.val then 1 else 0) else 0) := by
  have hsum :
      ∑ t : I n, ∑ s : I n, prefixT (rect a b) t s * rect c d t s =
        prefixT (rect a b) 0 0 + prefixT (rect a b) 0 d + prefixT (rect a b) c 0 + prefixT (rect a b) c d := by
    simpa [mul_comm] using
      (sum_rect_mul_eq_corners (a := c) (b := d) hc hd (g := fun t s => prefixT (rect a b) t s))
  rw [hsum]
  by_cases hbd : b = d
  · subst hbd
    simp [prefixT_zero, prefixT_rect_t_zero_eq_indicator (a := a) (b := b) ha hb,
      prefixT_rect_t_b_eq_indicator (a := a) (b := b) ha hb, hc]
  · have hd0 : d ≠ 0 := hd
    have hdb : d ≠ b := by simpa [eq_comm] using hbd
    have hother : prefixT (rect a b) c d = 0 := prefixT_rect_t_other_eq_zero (a := a) (b := b) hd0 hdb
    simp [prefixT_zero, prefixT_rect_t_zero_eq_indicator (a := a) (b := b) ha hb,
      hc, hbd, hother]

lemma sum_rect_mul_rect_eq_indicator {n : ℕ} [NeZero n]
    {a b c d : I n} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∑ t : I n, ∑ s : I n, rect a b t s * rect c d t s =
      1 + (if b = d then 1 else 0) + (if a = c then 1 else 0) + (if a = c ∧ b = d then 1 else 0) := by
  rw [sum_rect_mul_eq_corners (a := a) (b := b) ha hb (g := fun t s => rect c d t s)]
  have h00 : rect c d 0 0 = 1 := by
    simp [rect_row_zero_eq (a := c) (b := d) hc hd, hd]
  have h0b : rect c d 0 b = if b = d then 1 else 0 := by
    simp [rect_row_zero_eq (a := c) (b := d) hc hd, hb]
  have ha0 : rect c d a 0 = if a = c then 1 else 0 := by
    simp [rect_col_zero_eq (a := c) (b := d) hc hd, ha]
  have hab : rect c d a b = if a = c ∧ b = d then 1 else 0 := by
    simpa using (rect_apply_nonzero_nonzero (a := c) (b := d) hc hd ha hb)
  rw [h00, h0b, ha0, hab]

lemma oddRectPair_formula_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (i j : OddRectIndex n) :
    oddRectPair (n := n) i j =
      ((if i.2.1.val ≤ j.2.1.val then 1 else 0) +
        (if i.1.1 = j.1.1 then (if i.2.1.val ≤ j.2.1.val then 1 else 0) else 0)) +
      (((if j.1.1.val ≤ i.1.1.val then 1 else 0) +
        (if i.2.1 = j.2.1 then (if j.1.1.val ≤ i.1.1.val then 1 else 0) else 0)) +
        (1 + (if i.2.1 = j.2.1 then 1 else 0) + (if i.1.1 = j.1.1 then 1 else 0) +
          (if i.1.1 = j.1.1 ∧ i.2.1 = j.2.1 then 1 else 0))) := by
  rcases i with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases j with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  have hha : rect a b ∈ HSpace (n := n) := rect_mem_HSpace a b
  have hhc : rect c d ∈ HSpace (n := n) := rect_mem_HSpace c d
  unfold oddRectPair
  change q (bPref (rect a b)) (cPref (rect c d)) = _
  rw [q_bPref_cPref_formula_mixed_of_odd (n := n) hn hha hhc]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_rect_mul_prefixR_rect_eq (a := a) (b := b) (c := c) (d := d) ha hb hc hd]
  rw [sum_prefixT_rect_mul_rect_eq (a := a) (b := b) (c := c) (d := d) ha hb hc hd]
  rw [sum_rect_mul_rect_eq_indicator (a := a) (b := b) (c := c) (d := d) ha hb hc hd]
  simpa [add_assoc, add_left_comm, add_comm]

lemma oddRectPair_symm_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (i j : OddRectIndex n) :
    oddRectPair (n := n) i j = oddRectPair (n := n) j i := by
  rw [oddRectPair_formula_of_odd (n := n) hn i j, oddRectPair_formula_of_odd (n := n) hn j i]
  rcases i with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rcases j with ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simp [F_add_self, add_assoc, add_left_comm, add_comm]
    · by_cases hbdle : b.val ≤ d.val
      · have hbdv : b.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b := by simpa [eq_comm] using hbd
        have hdblt : ¬ d.val ≤ b.val := by omega
        simp [hbd, hdb, hbdle, hdblt, F_add_self, add_assoc, add_left_comm, add_comm]
      · have hbdv : b.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b := by simpa [eq_comm] using hbd
        have hdble : d.val ≤ b.val := by omega
        simp [hbd, hdb, hbdle, hdble, F_add_self, add_assoc, add_left_comm, add_comm]
  · by_cases hbd : b = d
    · subst hbd
      by_cases hcale : c.val ≤ a.val
      · have hacv : a.val ≠ c.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
        have hca : ¬ c = a := by simpa [eq_comm] using hac
        have hacle : ¬ a.val ≤ c.val := by omega
        simp [hac, hca, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
      · have hacv : a.val ≠ c.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
        have hca : ¬ c = a := by simpa [eq_comm] using hac
        have hacle : a.val ≤ c.val := by omega
        simp [hac, hca, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
    · by_cases hbdle : b.val ≤ d.val
      · have hbdv : b.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b := by simpa [eq_comm] using hbd
        have hdble : ¬ d.val ≤ b.val := by omega
        by_cases hcale : c.val ≤ a.val
        · have hacv : a.val ≠ c.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c = a := by simpa [eq_comm] using hac
          have hacle : ¬ a.val ≤ c.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
        · have hacv : a.val ≠ c.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c = a := by simpa [eq_comm] using hac
          have hacle : a.val ≤ c.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
      · have hbdv : b.val ≠ d.val := by
            intro hv
            apply hbd
            exact ZMod.val_injective _ hv
        have hdb : ¬ d = b := by simpa [eq_comm] using hbd
        have hdble : d.val ≤ b.val := by omega
        by_cases hcale : c.val ≤ a.val
        · have hacv : a.val ≠ c.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c = a := by simpa [eq_comm] using hac
          have hacle : ¬ a.val ≤ c.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
        · have hacv : a.val ≠ c.val := by
              intro hv
              apply hac
              exact ZMod.val_injective _ hv
          have hca : ¬ c = a := by simpa [eq_comm] using hac
          have hacle : a.val ≤ c.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]

lemma q_bPref_cPref_rect_eq_zero_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (i : OddRectIndex n) :
    q (bPref (oddRectVec (n := n) i).1) (cPref (oddRectVec (n := n) i).1) = 0 := by
  rcases i with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hh : rect a b ∈ HSpace (n := n) := rect_mem_HSpace a b
  change q (bPref (rect a b)) (cPref (rect a b)) = 0
  rw [q_bPref_cPref_formula_of_odd (n := n) (h := rect a b) hn hh]
  let term : I n → I n → F := fun t s =>
    rect a b t s * (prefixT (rect a b) t s + prefixR (rect a b) t s + 1)
  have hrow_other : ∀ t : I n, t ≠ 0 → t ≠ a → ∑ s : I n, term t s = 0 := by
    intro t ht0 hta
    refine Finset.sum_eq_zero ?_
    intro s hs
    simp [term, rect_row_other_eq_zero (s := s) ht0 hta]
  have hrow_zero : ∑ s : I n, term 0 s = 1 := by
    have h0mem : (0 : I n) ∈ Finset.univ := by simp
    have hbmem : b ∈ Finset.univ.erase (0 : I n) := by simp [hb]
    have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun x => term 0 x) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro s hs
      have hsin : s ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp hs).2
      have hs0 : s ≠ 0 := by simpa using (Finset.mem_erase.mp hsin).1
      have hsb : s ≠ b := by simpa using (Finset.mem_erase.mp hs).1
      simp [term, rect_row_zero_eq (a := a) (b := b) ha hb, hs0, hsb]
    calc
      ∑ s : I n, term 0 s
          = Finset.sum (Finset.univ.erase (0 : I n)) (fun s => term 0 s) + term 0 0 := by
              simpa using (Finset.sum_erase_add Finset.univ (fun s => term 0 s) h0mem).symm
      _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun s => term 0 s) + term 0 b) + term 0 0 := by
            simpa [add_assoc] using congrArg (fun x => x + term 0 0)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun s => term 0 s) hbmem).symm)
      _ = 0 + term 0 b + term 0 0 := by simp [hrest]
      _ = 1 := by
            simp [term, rect_row_zero_eq (a := a) (b := b) ha hb, prefixT_zero, prefixR_zero,
              prefixR_rect_zero_b_eq_one (a := a) ha hb, hb, add_assoc, F_add_self]
  have hrow_a : ∑ s : I n, term a s = 1 := by
    have h0mem : (0 : I n) ∈ Finset.univ := by simp
    have hbmem : b ∈ Finset.univ.erase (0 : I n) := by simp [hb]
    have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun x => term a x) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro s hs
      have hsin : s ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp hs).2
      have hs0 : s ≠ 0 := by simpa using (Finset.mem_erase.mp hsin).1
      have hsb : s ≠ b := by simpa using (Finset.mem_erase.mp hs).1
      simp [term, rect_row_a_eq (a := a) ha hb, hs0, hsb]
    calc
      ∑ s : I n, term a s
          = Finset.sum (Finset.univ.erase (0 : I n)) (fun s => term a s) + term a 0 := by
              simpa using (Finset.sum_erase_add Finset.univ (fun s => term a s) h0mem).symm
      _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase b) (fun s => term a s) + term a b) + term a 0 := by
            simpa [add_assoc] using congrArg (fun x => x + term a 0)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n)) (fun s => term a s) hbmem).symm)
      _ = 0 + term a b + term a 0 := by simp [hrest]
      _ = 1 := by
            simp [term, rect_row_a_eq (a := a) ha hb, prefixR_zero,
              prefixT_rect_a_zero_eq_one (b := b) ha hb, prefixT_rect_a_b_eq_one ha hb,
              prefixR_rect_a_b_eq_one (b := b) ha hb, hb, add_assoc, F_add_self]
  have h0mem : (0 : I n) ∈ Finset.univ := by simp
  have hamem : a ∈ Finset.univ.erase (0 : I n) := by simp [ha]
  have hrest : Finset.sum ((Finset.univ.erase (0 : I n)).erase a) (fun x => ∑ s : I n, term x s) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have htin : t ∈ Finset.univ.erase (0 : I n) := (Finset.mem_erase.mp ht).2
    have ht0 : t ≠ 0 := by simpa using (Finset.mem_erase.mp htin).1
    have hta : t ≠ a := by simpa using Finset.mem_erase.mp ht |>.1
    simp [hrow_other t ht0 hta]
  calc
    ∑ t : I n, ∑ s : I n, term t s
        = Finset.sum (Finset.univ.erase (0 : I n)) (fun t => ∑ s : I n, term t s) + ∑ s : I n, term 0 s := by
            simpa using
              (Finset.sum_erase_add Finset.univ (fun t => ∑ s : I n, term t s) h0mem).symm
    _ = (Finset.sum ((Finset.univ.erase (0 : I n)).erase a) (fun t => ∑ s : I n, term t s) + ∑ s : I n, term a s)
          + ∑ s : I n, term 0 s := by
            simpa [add_assoc] using congrArg (fun x => x + ∑ s : I n, term 0 s)
              ((Finset.sum_erase_add (Finset.univ.erase (0 : I n))
                (fun t => ∑ s : I n, term t s) hamem).symm)
    _ = 0 + 1 + 1 := by simp [hrest, hrow_zero, hrow_a]
    _ = 0 := by simp [F_add_self]

lemma oddHeadB_add {n : ℕ} [NeZero n] (B₁ B₂ : BFun n) :
    oddHeadB (B₁ + B₂) = oddHeadB B₁ + oddHeadB B₂ := by
  funext t p q'
  simpa [oddHeadB, bSlice, sigma, Pi.add_apply] using
    (Finset.sum_add_distrib (f := fun a : I n => B₁ a t p q') (g := fun a => B₂ a t p q'))

lemma oddHeadC_add {n : ℕ} [NeZero n] (C₁ C₂ : CFun n) :
    oddHeadC (C₁ + C₂) = oddHeadC C₁ + oddHeadC C₂ := by
  funext v w r
  simpa [oddHeadC, cSlice, sigma, Pi.add_apply] using
    (Finset.sum_add_distrib (f := fun a : I n => C₁ a v w r) (g := fun a => C₂ a v w r))

lemma oddHeadB_tensor_oneProfile {n : ℕ} [NeZero n] (hn : Odd n) (b : BCoef n) :
    oddHeadB (tensorB (oneProfile (n := n)) b) = b := by
  funext t p q'
  rw [oddHeadB_eq_sigma_slice]
  have hs : bSlice (tensorB (oneProfile (n := n)) b) t p q' = fun _ : I n => b t p q' := by
    funext a
    simp [bSlice, tensorB, oneProfile]
  simpa [hs] using (sigma_const_odd (n := n) hn (b t p q'))

lemma oddHeadC_tensor_oneProfile {n : ℕ} [NeZero n] (hn : Odd n) (c : CCoef n) :
    oddHeadC (tensorC (oneProfile (n := n)) c) = c := by
  funext v w r
  rw [oddHeadC_eq_sigma_slice]
  have hs : cSlice (tensorC (oneProfile (n := n)) c) v w r = fun _ : I n => c v w r := by
    funext a
    simp [cSlice, tensorC, oneProfile]
  simpa [hs] using (sigma_const_odd (n := n) hn (c v w r))

lemma odd_decompose_B {n : ℕ} [NeZero n] (B : BFun n) :
    B = oddVisibleB B + oddTailB B := by
  funext a t p q'
  simp [oddVisibleB_apply, oddTailB, F_add_self, add_assoc, add_left_comm, add_comm]

lemma odd_decompose_C {n : ℕ} [NeZero n] (C : CFun n) :
    C = oddVisibleC C + oddTailC C := by
  funext a v w r
  simp [oddVisibleC_apply, oddTailC, F_add_self, add_assoc, add_left_comm, add_comm]

lemma oddTailB_slice_mem_Wodd {n : ℕ} [NeZero n] (hn : Odd n)
    (B : BFun n) (t p q' : I n) :
    bSlice (oddTailB B) t p q' ∈ Wodd (n := n) := by
  change sigmaMap (n := n) (bSlice (oddTailB B) t p q') = 0
  change (∑ a : I n, (B a t p q' + oddHeadB B t p q')) = 0
  calc
    (∑ a : I n, (B a t p q' + oddHeadB B t p q'))
        = (∑ a : I n, B a t p q') + ∑ a : I n, oddHeadB B t p q' := by
            rw [Finset.sum_add_distrib]
    _ = oddHeadB B t p q' + oddHeadB B t p q' := by
          rw [show (∑ a : I n, B a t p q') = sigma (bSlice B t p q') by rfl]
          rw [oddHeadB]
          rw [show (∑ a : I n, sigma (bSlice B t p q')) =
              sigma (fun _ : I n => sigma (bSlice B t p q')) by rfl]
          rw [sigma_const_odd (n := n) hn]
    _ = 0 := F_add_self _

lemma oddTailC_slice_mem_Wodd {n : ℕ} [NeZero n] (hn : Odd n)
    (C : CFun n) (v w r : I n) :
    cSlice (oddTailC C) v w r ∈ Wodd (n := n) := by
  change sigmaMap (n := n) (cSlice (oddTailC C) v w r) = 0
  change (∑ a : I n, (C a v w r + oddHeadC C v w r)) = 0
  calc
    (∑ a : I n, (C a v w r + oddHeadC C v w r))
        = (∑ a : I n, C a v w r) + ∑ a : I n, oddHeadC C v w r := by
            rw [Finset.sum_add_distrib]
    _ = oddHeadC C v w r + oddHeadC C v w r := by
          rw [show (∑ a : I n, C a v w r) = sigma (cSlice C v w r) by rfl]
          rw [oddHeadC]
          rw [show (∑ a : I n, sigma (cSlice C v w r)) =
              sigma (fun _ : I n => sigma (cSlice C v w r)) by rfl]
          rw [sigma_const_odd (n := n) hn]
    _ = 0 := F_add_self _

lemma oddTailB_slice_eq_original_plus_head {n : ℕ} [NeZero n] (B : BFun n) (t p q' : I n) :
    bSlice (oddTailB B) t p q' = bSlice B t p q' + oddHeadB B t p q' • oneProfile (n := n) := by
  funext a
  simp [bSlice, oddTailB, oneProfile]

lemma oddTailC_slice_eq_original_plus_head {n : ℕ} [NeZero n] (C : CFun n) (v w r : I n) :
    cSlice (oddTailC C) v w r = cSlice C v w r + oddHeadC C v w r • oneProfile (n := n) := by
  funext a
  simp [cSlice, oddTailC, oneProfile]

lemma kappa_eq_oddHeads {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    kappa B C = kappaB (oddHeadB B) + kappaC (oddHeadC C) := by
  funext u2 u3 u4 u5
  unfold kappa kappaB kappaC oddHeadB oddHeadC bSlice cSlice sigma
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rfl

lemma kappa_eq_visibleConstraint_oddHeads {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    kappa B C = visibleConstraint (oddHeadB B, oddHeadC C) := by
  funext u2 u3 u4 u5
  rw [kappa_eq_oddHeads (B := B) (C := C)]
  unfold visibleConstraint kappaB kappaC
  simp [Pi.add_apply, add_assoc]

lemma kappa_eq_zero_iff_oddHeads_mem_SSpace {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    kappa B C = 0 ↔ (oddHeadB B, oddHeadC C) ∈ SSpace (n := n) := by
  constructor
  · intro hk
    change visibleConstraintMap (n := n) (oddHeadB B, oddHeadC C) = 0
    change visibleConstraint (oddHeadB B, oddHeadC C) = 0
    simpa [kappa_eq_visibleConstraint_oddHeads (B := B) (C := C)] using hk
  · intro hs
    change visibleConstraintMap (n := n) (oddHeadB B, oddHeadC C) = 0 at hs
    change visibleConstraint (oddHeadB B, oddHeadC C) = 0 at hs
    simpa [kappa_eq_visibleConstraint_oddHeads (B := B) (C := C)] using hs

lemma oddHeadB_oddTailB_eq_zero {n : ℕ} [NeZero n] (hn : Odd n) (B : BFun n) :
    oddHeadB (oddTailB B) = 0 := by
  funext t p q'
  have hmem := oddTailB_slice_mem_Wodd (n := n) hn B t p q'
  change sigmaMap (n := n) (bSlice (oddTailB B) t p q') = 0 at hmem
  simpa [oddHeadB, sigmaMap] using hmem

lemma oddHeadC_oddTailC_eq_zero {n : ℕ} [NeZero n] (hn : Odd n) (C : CFun n) :
    oddHeadC (oddTailC C) = 0 := by
  funext v w r
  have hmem := oddTailC_slice_mem_Wodd (n := n) hn C v w r
  change sigmaMap (n := n) (cSlice (oddTailC C) v w r) = 0 at hmem
  simpa [oddHeadC, sigmaMap] using hmem

lemma oddHeadB_oddBuild_eq {n : ℕ} [NeZero n] (hn : Odd n) (b : BCoef n)
    (R : BFun n) (hR : oddHeadB R = 0) :
    oddHeadB (oddBuildB b R) = b := by
  rw [oddBuildB, oddHeadB_add, oddHeadB_tensor_oneProfile (n := n) hn, hR, add_zero]

lemma oddHeadC_oddBuild_eq {n : ℕ} [NeZero n] (hn : Odd n) (c : CCoef n)
    (R : CFun n) (hR : oddHeadC R = 0) :
    oddHeadC (oddBuildC c R) = c := by
  rw [oddBuildC, oddHeadC_add, oddHeadC_tensor_oneProfile (n := n) hn, hR, add_zero]

lemma oddTailB_oddBuild_eq {n : ℕ} [NeZero n] (hn : Odd n) (b : BCoef n)
    (R : BFun n) (hR : oddHeadB R = 0) :
    oddTailB (oddBuildB b R) = R := by
  have hhead : oddHeadB (tensorB (oneProfile (n := n)) b + R) = b := by
    simpa [oddBuildB] using oddHeadB_oddBuild_eq (n := n) hn b R hR
  funext a t p q'
  rw [oddTailB, oddBuildB, hhead]
  have hrewrite :
      (tensorB (oneProfile (n := n)) b + R) a t p q' + b t p q' =
        b t p q' + (b t p q' + R a t p q') := by
    simp [tensorB, oneProfile, add_assoc, add_left_comm, add_comm]
  rw [hrewrite]
  calc
    b t p q' + (b t p q' + R a t p q') = (b t p q' + b t p q') + R a t p q' := by
      ac_rfl
    _ = R a t p q' := by
      simp [F_add_self]

lemma oddTailC_oddBuild_eq {n : ℕ} [NeZero n] (hn : Odd n) (c : CCoef n)
    (R : CFun n) (hR : oddHeadC R = 0) :
    oddTailC (oddBuildC c R) = R := by
  have hhead : oddHeadC (tensorC (oneProfile (n := n)) c + R) = c := by
    simpa [oddBuildC] using oddHeadC_oddBuild_eq (n := n) hn c R hR
  funext a v w r
  rw [oddTailC, oddBuildC, hhead]
  have hrewrite :
      (tensorC (oneProfile (n := n)) c + R) a v w r + c v w r =
        c v w r + (c v w r + R a v w r) := by
    simp [tensorC, oneProfile, add_assoc, add_left_comm, add_comm]
  rw [hrewrite]
  calc
    c v w r + (c v w r + R a v w r) = (c v w r + c v w r) + R a v w r := by
      ac_rfl
    _ = R a v w r := by
      simp [F_add_self]

lemma kappa_eq_zero_iff_oddBuild_mem_SSpace {n : ℕ} [NeZero n] (hn : Odd n)
    (b : BCoef n) (c : CCoef n) (RB : BFun n) (RC : CFun n)
    (hRB : oddHeadB RB = 0) (hRC : oddHeadC RC = 0) :
    kappa (oddBuildB b RB) (oddBuildC c RC) = 0 ↔ (b, c) ∈ SSpace (n := n) := by
  rw [kappa_eq_zero_iff_oddHeads_mem_SSpace]
  simp [oddHeadB_oddBuild_eq (n := n) hn b RB hRB, oddHeadC_oddBuild_eq (n := n) hn c RC hRC]

abbrev OddVisibleData (n : ℕ) [NeZero n] :=
  { bc : BCoef n × CCoef n // bc ∈ SSpace (n := n) }

abbrev OddVisibleHUVData (n : ℕ) [NeZero n] :=
  HSpace (n := n) × UVFun n × UVFun n

abbrev OddZeroHeadB (n : ℕ) [NeZero n] :=
  { R : BFun n // oddHeadB R = 0 }

abbrev OddZeroHeadC (n : ℕ) [NeZero n] :=
  { R : CFun n // oddHeadC R = 0 }

abbrev OddSurvivingData (n : ℕ) [NeZero n] :=
  OddVisibleData n × OddZeroHeadB n × OddZeroHeadC n

abbrev WoddBCoef (n : ℕ) [NeZero n] := I n → I n → I n → ↥(Wodd (n := n))

abbrev WoddCCoef (n : ℕ) [NeZero n] := I n → I n → I n → ↥(Wodd (n := n))

noncomputable instance oddVisibleDataFintype {n : ℕ} [NeZero n] : Fintype (OddVisibleData n) := by
  classical
  infer_instance

noncomputable instance oddVisibleHUVDataFintype {n : ℕ} [NeZero n] :
    Fintype (OddVisibleHUVData n) := by
  classical
  infer_instance

noncomputable instance oddHSpaceFintype {n : ℕ} [NeZero n] : Fintype (HSpace (n := n)) := by
  classical
  infer_instance

noncomputable def oddVisibleToHUVData {n : ℕ} [NeZero n] :
    OddVisibleData n → OddVisibleHUVData n
  | ⟨bc, hbc⟩ => (⟨visibleHData bc, visibleHData_mem_HSpace (n := n) hbc⟩, visibleUData bc, visibleVData bc)

noncomputable def oddVisibleFromHUVData {n : ℕ} [NeZero n] :
    OddVisibleHUVData n → OddVisibleData n
  | ⟨h, u, v⟩ => ⟨(buildB h.1 u, buildC h.1 v), build_mem_SSpace_of_mem_HSpace (n := n) h u v⟩

lemma oddVisibleToHUVData_from {n : ℕ} [NeZero n] (z : OddVisibleHUVData n) :
    oddVisibleToHUVData (n := n) (oddVisibleFromHUVData (n := n) z) = z := by
  rcases z with ⟨h, u, v⟩
  apply Prod.ext
  · apply Subtype.ext
    exact visibleHData_build_eq (n := n) h u v
  · apply Prod.ext
    · exact visibleUData_build_eq (n := n) h u v
    · exact visibleVData_build_eq (n := n) h u v

lemma oddVisibleFromHUVData_to {n : ℕ} [NeZero n] (bc : OddVisibleData n) :
    oddVisibleFromHUVData (n := n) (oddVisibleToHUVData (n := n) bc) = bc := by
  rcases bc with ⟨bc, hbc⟩
  apply Subtype.ext
  exact Prod.ext
    (buildB_visibleData_eq (n := n) (bc := bc) hbc)
    (buildC_visibleData_eq (n := n) (bc := bc) hbc)

noncomputable def oddVisibleEquivHUVData {n : ℕ} [NeZero n] :
    OddVisibleData n ≃ OddVisibleHUVData n where
  toFun := oddVisibleToHUVData (n := n)
  invFun := oddVisibleFromHUVData (n := n)
  left_inv := oddVisibleFromHUVData_to (n := n)
  right_inv := oddVisibleToHUVData_from (n := n)

lemma natCard_oddVisibleData {n : ℕ} [NeZero n] :
    Nat.card (OddVisibleData n) = 2 ^ (3 * n ^ 2 + 1 - 2 * n) := by
  rw [Nat.card_congr (oddVisibleEquivHUVData (n := n))]
  rw [Nat.card_prod, Nat.card_prod, natCard_HSpace]
  have huv : Nat.card (UVFun n) = 2 ^ (n ^ 2) := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [F, finrank_uvFun]
  rw [huv]
  calc
    2 ^ ((n - 1) ^ 2) * (2 ^ (n ^ 2) * 2 ^ (n ^ 2))
        = 2 ^ ((n - 1) ^ 2) * 2 ^ (n ^ 2 + n ^ 2) := by
            rw [← pow_add]
    _ = 2 ^ (((n - 1) ^ 2) + (n ^ 2 + n ^ 2)) := by
          rw [← pow_add]
    _ = 2 ^ (3 * n ^ 2 + 1 - 2 * n) := by
          congr
          rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
          simp [pow_two]
          ring_nf
          omega

lemma fintypeCard_oddVisibleData {n : ℕ} [NeZero n] :
    Fintype.card (OddVisibleData n) = 2 ^ (3 * n ^ 2 + 1 - 2 * n) := by
  rw [← Nat.card_eq_fintype_card, natCard_oddVisibleData]

noncomputable instance oddZeroHeadBFintype {n : ℕ} [NeZero n] : Fintype (OddZeroHeadB n) := by
  classical
  infer_instance

noncomputable instance oddZeroHeadCFintype {n : ℕ} [NeZero n] : Fintype (OddZeroHeadC n) := by
  classical
  infer_instance

noncomputable instance oddSurvivingDataFintype {n : ℕ} [NeZero n] :
    Fintype (OddSurvivingData n) := by
  classical
  infer_instance

noncomputable instance woddBCoefFintype {n : ℕ} [NeZero n] : Fintype (WoddBCoef n) := by
  classical
  infer_instance

noncomputable instance woddCCoefFintype {n : ℕ} [NeZero n] : Fintype (WoddCCoef n) := by
  classical
  infer_instance

lemma zeroHeadB_slice_mem_Wodd {n : ℕ} [NeZero n] {R : BFun n} (hR : oddHeadB R = 0)
    (t p q' : I n) :
    bSlice R t p q' ∈ Wodd (n := n) := by
  change sigmaMap (n := n) (bSlice R t p q') = 0
  simpa [oddHeadB_eq_sigma_slice, hR] using congrFun (congrFun (congrFun hR t) p) q'

lemma zeroHeadC_slice_mem_Wodd {n : ℕ} [NeZero n] {R : CFun n} (hR : oddHeadC R = 0)
    (v w r : I n) :
    cSlice R v w r ∈ Wodd (n := n) := by
  change sigmaMap (n := n) (cSlice R v w r) = 0
  simpa [oddHeadC_eq_sigma_slice, hR] using congrFun (congrFun (congrFun hR v) w) r

noncomputable def oddZeroHeadBToWoddBCoef {n : ℕ} [NeZero n] (RB : OddZeroHeadB n) : WoddBCoef n :=
  fun t p q' => ⟨bSlice RB.1 t p q', zeroHeadB_slice_mem_Wodd RB.2 t p q'⟩

noncomputable def oddZeroHeadCToWoddCCoef {n : ℕ} [NeZero n] (RC : OddZeroHeadC n) : WoddCCoef n :=
  fun v w r => ⟨cSlice RC.1 v w r, zeroHeadC_slice_mem_Wodd RC.2 v w r⟩

noncomputable def woddBCoefToOddZeroHeadB {n : ℕ} [NeZero n] (f : WoddBCoef n) : OddZeroHeadB n :=
  ⟨fun a t p q' => (f t p q').1 a, by
    funext t p q'
    change sigmaMap (n := n) ((f t p q').1) = 0
    exact (f t p q').2⟩

noncomputable def woddCCoefToOddZeroHeadC {n : ℕ} [NeZero n] (f : WoddCCoef n) : OddZeroHeadC n :=
  ⟨fun a v w r => (f v w r).1 a, by
    funext v w r
    change sigmaMap (n := n) ((f v w r).1) = 0
    exact (f v w r).2⟩

noncomputable def oddZeroHeadBEquivWoddBCoef {n : ℕ} [NeZero n] : OddZeroHeadB n ≃ WoddBCoef n where
  toFun := oddZeroHeadBToWoddBCoef
  invFun := woddBCoefToOddZeroHeadB
  left_inv RB := by
    rcases RB with ⟨R, hR⟩
    apply Subtype.ext
    funext a t p q'
    rfl
  right_inv f := by
    funext t p q'
    apply Subtype.ext
    funext a
    rfl

noncomputable def oddZeroHeadCEquivWoddCCoef {n : ℕ} [NeZero n] : OddZeroHeadC n ≃ WoddCCoef n where
  toFun := oddZeroHeadCToWoddCCoef
  invFun := woddCCoefToOddZeroHeadC
  left_inv RC := by
    rcases RC with ⟨R, hR⟩
    apply Subtype.ext
    funext a v w r
    rfl
  right_inv f := by
    funext v w r
    apply Subtype.ext
    funext a
    rfl

noncomputable def woddQpair {n : ℕ} [NeZero n] (RB : WoddBCoef n) (RC : WoddCCoef n) : F :=
  ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
    (dot (RB (v + w) p q').1 (RC v w (p + q')).1 +
      dot (RB (v + w + 1) p q').1 (RC v w (p + q' + 1)).1)

abbrev OddCoordBCoef (m : ℕ) := Fin m → BCoef (2 * m + 1)

abbrev OddCoordCCoef (m : ℕ) := Fin m → CCoef (2 * m + 1)

noncomputable def woddBU {m : ℕ} (RB : WoddBCoef (2 * m + 1)) (i : Fin m) : BCoef (2 * m + 1) :=
  fun t p q' => oddUCoord (RB t p q') i

noncomputable def woddBV {m : ℕ} (RB : WoddBCoef (2 * m + 1)) (i : Fin m) : BCoef (2 * m + 1) :=
  fun t p q' => oddVCoord (RB t p q') i

noncomputable def woddCU {m : ℕ} (RC : WoddCCoef (2 * m + 1)) (i : Fin m) : CCoef (2 * m + 1) :=
  fun v w r => oddUCoord (RC v w r) i

noncomputable def woddCV {m : ℕ} (RC : WoddCCoef (2 * m + 1)) (i : Fin m) : CCoef (2 * m + 1) :=
  fun v w r => oddVCoord (RC v w r) i

set_option maxHeartbeats 800000 in
-- Reindexing `woddQpair` through the explicit odd symplectic coordinates produces
-- a sum of ordinary `q`-pairings.
lemma woddQpair_eq_sum_q {m : ℕ} (RB : WoddBCoef (2 * m + 1)) (RC : WoddCCoef (2 * m + 1)) :
    woddQpair RB RC =
      ∑ i : Fin m, (q (woddBU RB i) (woddCV RC i) + q (woddBV RB i) (woddCU RC i)) := by
  calc
    woddQpair RB RC
        = ∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1), ∑ q' : I (2 * m + 1),
            ∑ i : Fin m,
              ((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) +
                (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
                ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                  (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))) := by
          unfold woddQpair woddBU woddBV woddCU woddCV
          refine Finset.sum_congr rfl ?_
          intro v hv
          refine Finset.sum_congr rfl ?_
          intro w hw
          refine Finset.sum_congr rfl ?_
          intro p hp
          refine Finset.sum_congr rfl ?_
          intro q' hq
          rw [dot_oddSymplectic_coords, dot_oddSymplectic_coords, ← Finset.sum_add_distrib]
    _ = ∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1), ∑ i : Fin m,
          ∑ q' : I (2 * m + 1),
            ((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) +
              (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
              ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          refine Finset.sum_congr rfl ?_
          intro w hw
          refine Finset.sum_congr rfl ?_
          intro p hp
          simpa using
            (Finset.sum_comm
              (f := fun q' i =>
                ((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) : F) +
                  (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
                  ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                    (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))))
    _ = ∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ i : Fin m, ∑ p : I (2 * m + 1),
          ∑ q' : I (2 * m + 1),
            ((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) +
              (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
              ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          refine Finset.sum_congr rfl ?_
          intro w hw
          simpa using
            (Finset.sum_comm
              (f := fun p i =>
                (∑ q' : I (2 * m + 1),
                  (((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) : F) +
                    (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
                    ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                      (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))))))
    _ = ∑ v : I (2 * m + 1), ∑ i : Fin m, ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1),
          ∑ q' : I (2 * m + 1),
            ((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) +
              (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
              ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))) := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          simpa using
            (Finset.sum_comm
              (f := fun w i =>
                (∑ p : I (2 * m + 1), ∑ q' : I (2 * m + 1),
                  ((((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) : F) +
                    (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
                    ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                      (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1))))))))
    _ = ∑ i : Fin m, ∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1),
          ∑ q' : I (2 * m + 1),
            ((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) +
              (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
              ((woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1)) +
                (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin m, ∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1),
          ∑ q' : I (2 * m + 1),
            (((woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) +
                (woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1))) +
              ((woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
                (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1)))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro v hv
          refine Finset.sum_congr rfl ?_
          intro w hw
          refine Finset.sum_congr rfl ?_
          intro p hp
          refine Finset.sum_congr rfl ?_
          intro q' hq
          ac_rfl
    _ = ∑ i : Fin m, (q (woddBU RB i) (woddCV RC i) + q (woddBV RB i) (woddCU RC i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          let A : I (2 * m + 1) → I (2 * m + 1) → I (2 * m + 1) → I (2 * m + 1) → F :=
            fun v w p q' =>
              (woddBU RB i (v + w) p q' * woddCV RC i v w (p + q')) +
                (woddBU RB i (v + w + 1) p q' * woddCV RC i v w (p + q' + 1))
          let B : I (2 * m + 1) → I (2 * m + 1) → I (2 * m + 1) → I (2 * m + 1) → F :=
            fun v w p q' =>
              (woddBV RB i (v + w) p q' * woddCU RC i v w (p + q')) +
                (woddBV RB i (v + w + 1) p q' * woddCU RC i v w (p + q' + 1))
          change
            (∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1), ∑ q' : I (2 * m + 1),
              (A v w p q' + B v w p q')) =
              (∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1),
                ∑ q' : I (2 * m + 1), A v w p q') +
              ∑ v : I (2 * m + 1), ∑ w : I (2 * m + 1), ∑ p : I (2 * m + 1),
                ∑ q' : I (2 * m + 1), B v w p q'
          simp_rw [Finset.sum_add_distrib]

noncomputable def oddCoordPairEquivWodd {m : ℕ} :
    ↥(Wodd (n := 2 * m + 1)) ≃ ((Fin m → F) × (Fin m → F)) where
  toFun x := (oddUCoord x, oddVCoord x)
  invFun uv :=
    (oddSymplecticBasis (m := m)).repr.symm
      (Finsupp.equivFunOnFinite.symm (fun s : Fin m ⊕ Fin m => Sum.elim uv.1 uv.2 s))
  left_inv x := by
    have hrepr :
        Finsupp.equivFunOnFinite.symm (fun s : Fin m ⊕ Fin m => Sum.elim (oddUCoord x) (oddVCoord x) s) =
          (oddSymplecticBasis (m := m)).repr x := by
      apply (Finsupp.equivFunOnFinite : ((Fin m ⊕ Fin m) →₀ F) ≃ _).injective
      ext s
      cases s <;> rfl
    change (oddSymplecticBasis (m := m)).repr.symm
      (Finsupp.equivFunOnFinite.symm (fun s : Fin m ⊕ Fin m => Sum.elim (oddUCoord x) (oddVCoord x) s)) = x
    rw [hrepr]
    exact (oddSymplecticBasis (m := m)).repr.symm_apply_apply x
  right_inv uv := by
    apply Prod.ext
    · funext i
      change ((oddSymplecticBasis (m := m)).repr
        ((oddSymplecticBasis (m := m)).repr.symm
          (Finsupp.equivFunOnFinite.symm (fun s : Fin m ⊕ Fin m => Sum.elim uv.1 uv.2 s)))) (Sum.inl i) = uv.1 i
      rw [(oddSymplecticBasis (m := m)).repr.apply_symm_apply]
      exact congrFun
        (Equiv.apply_symm_apply Finsupp.equivFunOnFinite
          (fun s : Fin m ⊕ Fin m => Sum.elim uv.1 uv.2 s)) (Sum.inl i)
    · funext i
      change ((oddSymplecticBasis (m := m)).repr
        ((oddSymplecticBasis (m := m)).repr.symm
          (Finsupp.equivFunOnFinite.symm (fun s : Fin m ⊕ Fin m => Sum.elim uv.1 uv.2 s)))) (Sum.inr i) = uv.2 i
      rw [(oddSymplecticBasis (m := m)).repr.apply_symm_apply]
      exact congrFun
        (Equiv.apply_symm_apply Finsupp.equivFunOnFinite
          (fun s : Fin m ⊕ Fin m => Sum.elim uv.1 uv.2 s)) (Sum.inr i)

noncomputable def oddCoordBCoefEquivWoddBCoef {m : ℕ} :
    WoddBCoef (2 * m + 1) ≃ (OddCoordBCoef m × OddCoordBCoef m) where
  toFun RB := (woddBU RB, woddBV RB)
  invFun UV := fun t p q' =>
    (oddCoordPairEquivWodd (m := m)).symm ((fun i => UV.1 i t p q'), fun i => UV.2 i t p q')
  left_inv RB := by
    funext t p q'
    exact (oddCoordPairEquivWodd (m := m)).left_inv (RB t p q')
  right_inv UV := by
    apply Prod.ext
    · funext i t p q'
      change
        oddUCoord ((oddCoordPairEquivWodd (m := m)).symm
          ((fun j => UV.1 j t p q'), fun j => UV.2 j t p q')) i = UV.1 i t p q'
      exact congrFun
        (congrArg Prod.fst ((oddCoordPairEquivWodd (m := m)).right_inv
          ((fun j => UV.1 j t p q'), fun j => UV.2 j t p q'))) i
    · funext i t p q'
      change
        oddVCoord ((oddCoordPairEquivWodd (m := m)).symm
          ((fun j => UV.1 j t p q'), fun j => UV.2 j t p q')) i = UV.2 i t p q'
      exact congrFun
        (congrArg Prod.snd ((oddCoordPairEquivWodd (m := m)).right_inv
          ((fun j => UV.1 j t p q'), fun j => UV.2 j t p q'))) i

noncomputable def oddCoordCCoefEquivWoddCCoef {m : ℕ} :
    WoddCCoef (2 * m + 1) ≃ (OddCoordCCoef m × OddCoordCCoef m) where
  toFun RC := (woddCU RC, woddCV RC)
  invFun UV := fun v w r =>
    (oddCoordPairEquivWodd (m := m)).symm ((fun i => UV.1 i v w r), fun i => UV.2 i v w r)
  left_inv RC := by
    funext v w r
    exact (oddCoordPairEquivWodd (m := m)).left_inv (RC v w r)
  right_inv UV := by
    apply Prod.ext
    · funext i v w r
      change
        oddUCoord ((oddCoordPairEquivWodd (m := m)).symm
          ((fun j => UV.1 j v w r), fun j => UV.2 j v w r)) i = UV.1 i v w r
      exact congrFun
        (congrArg Prod.fst ((oddCoordPairEquivWodd (m := m)).right_inv
          ((fun j => UV.1 j v w r), fun j => UV.2 j v w r))) i
    · funext i v w r
      change
        oddVCoord ((oddCoordPairEquivWodd (m := m)).symm
          ((fun j => UV.1 j v w r), fun j => UV.2 j v w r)) i = UV.2 i v w r
      exact congrFun
        (congrArg Prod.snd ((oddCoordPairEquivWodd (m := m)).right_inv
          ((fun j => UV.1 j v w r), fun j => UV.2 j v w r))) i

noncomputable def oddSurvivingToData {n : ℕ} [NeZero n] (hn : Odd n) :
    SurvivingBC n → OddSurvivingData n :=
  fun bc =>
    (⟨(oddHeadB bc.1.1, oddHeadC bc.1.2),
        (kappa_eq_zero_iff_oddHeads_mem_SSpace (B := bc.1.1) (C := bc.1.2)).1 bc.2⟩,
      ⟨oddTailB bc.1.1, oddHeadB_oddTailB_eq_zero (n := n) hn bc.1.1⟩,
      ⟨oddTailC bc.1.2, oddHeadC_oddTailC_eq_zero (n := n) hn bc.1.2⟩)

noncomputable def oddDataToSurviving {n : ℕ} [NeZero n] (hn : Odd n) :
    OddSurvivingData n → SurvivingBC n
  | (bc, RB, RC) =>
      ⟨(oddBuildB bc.1.1 RB.1, oddBuildC bc.1.2 RC.1),
        (kappa_eq_zero_iff_oddBuild_mem_SSpace (n := n) hn bc.1.1 bc.1.2 RB.1 RC.1 RB.2 RC.2).2
          bc.2⟩

lemma oddDataToSurviving_oddSurvivingToData {n : ℕ} [NeZero n] (hn : Odd n)
    (bc : SurvivingBC n) :
    oddDataToSurviving (n := n) hn (oddSurvivingToData (n := n) hn bc) = bc := by
  rcases bc with ⟨⟨B, C⟩, hk⟩
  have hB : oddBuildB (oddHeadB B) (oddTailB B) = B := by
    simpa [oddBuildB, oddVisibleB] using (odd_decompose_B (B := B)).symm
  have hC : oddBuildC (oddHeadC C) (oddTailC C) = C := by
    simpa [oddBuildC, oddVisibleC] using (odd_decompose_C (C := C)).symm
  apply Subtype.ext
  apply Prod.ext
  · simpa [oddDataToSurviving, oddSurvivingToData] using hB
  · simpa [oddDataToSurviving, oddSurvivingToData] using hC

lemma oddSurvivingToData_oddDataToSurviving {n : ℕ} [NeZero n] (hn : Odd n)
    (d : OddSurvivingData n) :
    oddSurvivingToData (n := n) hn (oddDataToSurviving (n := n) hn d) = d := by
  rcases d with ⟨⟨⟨b, c⟩, hbc⟩, ⟨RB, hRB⟩, ⟨RC, hRC⟩⟩
  apply Prod.ext
  · apply Subtype.ext
    ext <;> simp [oddSurvivingToData, oddDataToSurviving,
      oddHeadB_oddBuild_eq (n := n) hn b RB hRB,
      oddHeadC_oddBuild_eq (n := n) hn c RC hRC]
  · apply Prod.ext
    · apply Subtype.ext
      simp [oddSurvivingToData, oddDataToSurviving, oddTailB_oddBuild_eq (n := n) hn b RB hRB]
    · apply Subtype.ext
      simp [oddSurvivingToData, oddDataToSurviving, oddTailC_oddBuild_eq (n := n) hn c RC hRC]

noncomputable def oddSurvivingEquiv {n : ℕ} [NeZero n] (hn : Odd n) :
    SurvivingBC n ≃ OddSurvivingData n where
  toFun := oddSurvivingToData (n := n) hn
  invFun := oddDataToSurviving (n := n) hn
  left_inv := oddDataToSurviving_oddSurvivingToData (n := n) hn
  right_inv := oddSurvivingToData_oddDataToSurviving (n := n) hn

lemma oddVisibleB_slice {n : ℕ} [NeZero n] (B : BFun n) (t p q' : I n) :
    bSlice (oddVisibleB B) t p q' = oddHeadB B t p q' • oneProfile (n := n) := by
  funext a
  simp [bSlice, oddVisibleB_apply, oneProfile]

lemma oddVisibleC_slice {n : ℕ} [NeZero n] (C : CFun n) (v w r : I n) :
    cSlice (oddVisibleC C) v w r = oddHeadC C v w r • oneProfile (n := n) := by
  funext a
  simp [cSlice, oddVisibleC_apply, oneProfile]

lemma dot_smul_oneProfile_left {n : ℕ} [NeZero n] (a : F) (x : Profile n) :
    dot (a • oneProfile (n := n)) x = a * sigma x := by
  unfold dot sigma oneProfile
  simp [mul_assoc, Finset.mul_sum]

lemma dot_x_oneProfile {n : ℕ} [NeZero n] (x : Profile n) :
    dot x (oneProfile (n := n)) = sigma x := by
  exact (sigma_eq_dot_oneProfile x).symm

lemma dot_x_smul_oneProfile {n : ℕ} [NeZero n] (x : Profile n) (a : F) :
    dot x (a • oneProfile (n := n)) = a * sigma x := by
  calc
    dot x (a • oneProfile (n := n)) = sigma x * a := by
      unfold dot sigma oneProfile
      simp [Finset.sum_mul]
    _ = a * sigma x := by
      simp [mul_comm]

lemma Qpair_eq_sum_dot {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    Qpair B C =
      ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
        (dot (bSlice B (v + w) p q') (cSlice C v w (p + q')) +
          dot (bSlice B (v + w + 1) p q') (cSlice C v w (p + q' + 1))) := by
  symm
  let f : I n → I n → I n → I n → I n → F :=
    fun a v w p q' =>
      B a (v + w) p q' * C a v w (p + q') +
        B a (v + w + 1) p q' * C a v w (p + q' + 1)
  calc
    (∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n,
        (dot (bSlice B (v + w) p q') (cSlice C v w (p + q')) +
          dot (bSlice B (v + w + 1) p q') (cSlice C v w (p + q' + 1))))
        = ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, ∑ a : I n, f a v w p q' := by
          unfold dot bSlice cSlice
          refine Finset.sum_congr rfl ?_
          intro v hv
          refine Finset.sum_congr rfl ?_
          intro w hw
          refine Finset.sum_congr rfl ?_
          intro p hp
          refine Finset.sum_congr rfl ?_
          intro q' hq
          unfold f
          rw [← Finset.sum_add_distrib]
    _ = ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ a : I n, ∑ q' : I n, f a v w p q' := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          refine Finset.sum_congr rfl ?_
          intro w hw
          refine Finset.sum_congr rfl ?_
          intro p hp
          simpa using (Finset.sum_comm (f := fun q' a => f a v w p q'))
    _ = ∑ v : I n, ∑ w : I n, ∑ a : I n, ∑ p : I n, ∑ q' : I n, f a v w p q' := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          refine Finset.sum_congr rfl ?_
          intro w hw
          simpa using (Finset.sum_comm (f := fun p a => ∑ q' : I n, f a v w p q'))
    _ = ∑ v : I n, ∑ a : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, f a v w p q' := by
          refine Finset.sum_congr rfl ?_
          intro v hv
          simpa using (Finset.sum_comm (f := fun w a => ∑ p : I n, ∑ q' : I n, f a v w p q'))
    _ = ∑ a : I n, ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, f a v w p q' := by
          simpa using (Finset.sum_comm (f := fun v a => ∑ w : I n, ∑ p : I n, ∑ q' : I n,
            f a v w p q'))
    _ = Qpair B C := by
          unfold Qpair f
          rfl

lemma Qpair_eq_woddQpair {n : ℕ} [NeZero n] (RB : OddZeroHeadB n) (RC : OddZeroHeadC n) :
    Qpair RB.1 RC.1 = woddQpair (oddZeroHeadBToWoddBCoef RB) (oddZeroHeadCToWoddCCoef RC) := by
  rw [Qpair_eq_sum_dot]
  rfl

lemma Qpair_add_left {n : ℕ} [NeZero n] (B₁ B₂ : BFun n) (C : CFun n) :
    Qpair (B₁ + B₂) C = Qpair B₁ C + Qpair B₂ C := by
  unfold Qpair
  simp [add_mul, Finset.sum_add_distrib]
  ac_rfl

lemma Qpair_add_right {n : ℕ} [NeZero n] (B : BFun n) (C₁ C₂ : CFun n) :
    Qpair B (C₁ + C₂) = Qpair B C₁ + Qpair B C₂ := by
  unfold Qpair
  simp [mul_add, Finset.sum_add_distrib]
  ac_rfl

lemma Qpair_oddVisible_oddTail_eq_zero {n : ℕ} [NeZero n] (hn : Odd n) (B : BFun n) (C : CFun n) :
    Qpair (oddVisibleB B) (oddTailC C) = 0 := by
  rw [Qpair_eq_sum_dot]
  refine Finset.sum_eq_zero ?_
  intro v hv
  refine Finset.sum_eq_zero ?_
  intro w hw
  refine Finset.sum_eq_zero ?_
  intro p hp
  refine Finset.sum_eq_zero ?_
  intro q' hq
  rw [oddVisibleB_slice, oddVisibleB_slice]
  have h₁ : sigma (cSlice (oddTailC C) v w (p + q')) = 0 :=
    sigma_eq_zero_of_mem_Wodd (oddTailC_slice_mem_Wodd (n := n) hn C v w (p + q'))
  have h₂ : sigma (cSlice (oddTailC C) v w (p + q' + 1)) = 0 :=
    sigma_eq_zero_of_mem_Wodd (oddTailC_slice_mem_Wodd (n := n) hn C v w (p + q' + 1))
  rw [dot_smul_oneProfile_left, dot_smul_oneProfile_left, h₁, h₂]
  simp

lemma Qpair_oddTail_oddVisible_eq_zero {n : ℕ} [NeZero n] (hn : Odd n) (B : BFun n) (C : CFun n) :
    Qpair (oddTailB B) (oddVisibleC C) = 0 := by
  rw [Qpair_eq_sum_dot]
  refine Finset.sum_eq_zero ?_
  intro v hv
  refine Finset.sum_eq_zero ?_
  intro w hw
  refine Finset.sum_eq_zero ?_
  intro p hp
  refine Finset.sum_eq_zero ?_
  intro q' hq
  rw [oddVisibleC_slice, oddVisibleC_slice]
  have h₁ : sigma (bSlice (oddTailB B) (v + w) p q') = 0 :=
    sigma_eq_zero_of_mem_Wodd (oddTailB_slice_mem_Wodd (n := n) hn B (v + w) p q')
  have h₂ : sigma (bSlice (oddTailB B) (v + w + 1) p q') = 0 :=
    sigma_eq_zero_of_mem_Wodd (oddTailB_slice_mem_Wodd (n := n) hn B (v + w + 1) p q')
  rw [dot_x_smul_oneProfile, dot_x_smul_oneProfile, h₁, h₂]
  simp

lemma Qpair_oddVisible_oddVisible {n : ℕ} [NeZero n] (hn : Odd n) (B : BFun n) (C : CFun n) :
    Qpair (oddVisibleB B) (oddVisibleC C) = q (oddHeadB B) (oddHeadC C) := by
  unfold oddVisibleB oddVisibleC
  rw [Qpair_tensor]
  simp [dot_oneProfile_oneProfile_odd (n := n) hn]

set_option maxHeartbeats 800000 in
-- Reordering the five finite sums for `pairBC` is elaboration-heavy but straightforward.
lemma sum_pairBC_eq_Qpair {n : ℕ} [NeZero n] (B : BFun n) (C : CFun n) :
    (∑ u : Quint n, pairBC B C u) = Qpair B C := by
  let f : I n → I n → I n → I n → I n → F :=
    fun a v w p q' =>
      B a (v + w) p q' * C a v w (p + q') +
        B a (v + w + 1) p q' * C a v w (p + q' + 1)
  calc
    (∑ u : Quint n, pairBC B C u) = ∑ q' : I n, ∑ p : I n, ∑ w : I n, ∑ v : I n, ∑ a : I n, f a v w p q' := by
      unfold Quint pairBC f
      rw [Fintype.sum_prod_type_right]
      rw [Fintype.sum_prod_type_right]
      rw [Fintype.sum_prod_type_right]
      rw [Fintype.sum_prod_type_right]
    _ = ∑ q' : I n, ∑ p : I n, ∑ w : I n, ∑ a : I n, ∑ v : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      refine Finset.sum_congr rfl ?_
      intro p hp
      refine Finset.sum_congr rfl ?_
      intro w hw
      simpa using (Finset.sum_comm (f := fun v a => f a v w p q'))
    _ = ∑ q' : I n, ∑ p : I n, ∑ a : I n, ∑ w : I n, ∑ v : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      refine Finset.sum_congr rfl ?_
      intro p hp
      simpa using (Finset.sum_comm (f := fun w a => ∑ v : I n, f a v w p q'))
    _ = ∑ q' : I n, ∑ a : I n, ∑ p : I n, ∑ w : I n, ∑ v : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      simpa using (Finset.sum_comm (f := fun p a => ∑ w : I n, ∑ v : I n, f a v w p q'))
    _ = ∑ a : I n, ∑ q' : I n, ∑ p : I n, ∑ w : I n, ∑ v : I n, f a v w p q' := by
      simpa using (Finset.sum_comm (f := fun q' a => ∑ p : I n, ∑ w : I n, ∑ v : I n,
        f a v w p q'))
    _ = ∑ a : I n, ∑ q' : I n, ∑ p : I n, ∑ v : I n, ∑ w : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      refine Finset.sum_congr rfl ?_
      intro p hp
      simpa using (Finset.sum_comm (f := fun w v => f a v w p q'))
    _ = ∑ a : I n, ∑ q' : I n, ∑ v : I n, ∑ p : I n, ∑ w : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      simpa using (Finset.sum_comm (f := fun p v => ∑ w : I n, f a v w p q'))
    _ = ∑ a : I n, ∑ v : I n, ∑ q' : I n, ∑ p : I n, ∑ w : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa using (Finset.sum_comm (f := fun q' v => ∑ p : I n, ∑ w : I n, f a v w p q'))
    _ = ∑ a : I n, ∑ v : I n, ∑ q' : I n, ∑ w : I n, ∑ p : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro v hv
      refine Finset.sum_congr rfl ?_
      intro q' hq'
      simpa using (Finset.sum_comm (f := fun p w => f a v w p q'))
    _ = ∑ a : I n, ∑ v : I n, ∑ w : I n, ∑ q' : I n, ∑ p : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro v hv
      simpa using (Finset.sum_comm (f := fun q' w => ∑ p : I n, f a v w p q'))
    _ = ∑ a : I n, ∑ v : I n, ∑ w : I n, ∑ p : I n, ∑ q' : I n, f a v w p q' := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      refine Finset.sum_congr rfl ?_
      intro v hv
      refine Finset.sum_congr rfl ?_
      intro w hw
      simpa using (Finset.sum_comm (f := fun q' p => f a v w p q'))
    _ = Qpair B C := by
      unfold Qpair f
      rfl

lemma sum_linBC_eq_zero_of_kappa_zero {n : ℕ} [NeZero n] {B : BFun n} {C : CFun n}
    (hk : kappa B C = 0) :
    (∑ u : Quint n, linBC B C u) = 0 := by
  rw [Fintype.sum_prod_type_right]
  rw [Fintype.sum_prod_type_right]
  rw [Fintype.sum_prod_type_right]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_eq_zero ?_
  intro u5 hu5
  refine Finset.sum_eq_zero ?_
  intro u4 hu4
  refine Finset.sum_eq_zero ?_
  intro u3 hu3
  refine Finset.sum_eq_zero ?_
  intro u2 hu2
  have hk' := congrFun (congrFun (congrFun (congrFun hk u2) u3) u4) u5
  simpa [kappa, linBC, Finset.sum_add_distrib, add_assoc] using hk'

lemma Qraw_eq_Qpair_of_kappa_zero {n : ℕ} [NeZero n] {B : BFun n} {C : CFun n}
    (hk : kappa B C = 0) :
    Qraw B C = Qpair B C := by
  unfold Qraw
  rw [Finset.sum_add_distrib]
  rw [sum_linBC_eq_zero_of_kappa_zero hk, zero_add]
  exact sum_pairBC_eq_Qpair B C

set_option maxHeartbeats 800000 in
-- The final odd `Qpair` split expands two bilinear decompositions at once.
lemma Qpair_eq_odd_split {n : ℕ} [NeZero n] (hn : Odd n) (B : BFun n) (C : CFun n) :
    Qpair B C = q (oddHeadB B) (oddHeadC C) + Qpair (oddTailB B) (oddTailC C) := by
  have hdecomp : Qpair B C = Qpair (oddVisibleB B + oddTailB B) (oddVisibleC C + oddTailC C) := by
    conv_lhs =>
      rw [odd_decompose_B (B := B), odd_decompose_C (C := C)]
  calc
    Qpair B C = Qpair (oddVisibleB B + oddTailB B) (oddVisibleC C + oddTailC C) := hdecomp
    _ = Qpair (oddVisibleB B) (oddVisibleC C) + Qpair (oddVisibleB B) (oddTailC C) +
          (Qpair (oddTailB B) (oddVisibleC C) + Qpair (oddTailB B) (oddTailC C)) := by
      rw [Qpair_add_left, Qpair_add_right, Qpair_add_right]
    _ = q (oddHeadB B) (oddHeadC C) + 0 + (0 + Qpair (oddTailB B) (oddTailC C)) := by
      rw [Qpair_oddVisible_oddVisible (n := n) hn]
      rw [Qpair_oddVisible_oddTail_eq_zero (n := n) hn]
      rw [Qpair_oddTail_oddVisible_eq_zero (n := n) hn]
    _ = q (oddHeadB B) (oddHeadC C) + Qpair (oddTailB B) (oddTailC C) := by
      simp

lemma Qraw_eq_odd_split_of_surviving {n : ℕ} [NeZero n] (hn : Odd n) {B : BFun n} {C : CFun n}
    (hk : kappa B C = 0) :
    Qraw B C = q (oddHeadB B) (oddHeadC C) + Qpair (oddTailB B) (oddTailC C) := by
  rw [Qraw_eq_Qpair_of_kappa_zero hk]
  exact Qpair_eq_odd_split (n := n) hn B C

lemma bitSign_Qraw_eq_odd_split_of_surviving {n : ℕ} [NeZero n] (hn : Odd n)
    {B : BFun n} {C : CFun n} (hk : kappa B C = 0) :
    bitSign (Qraw B C) =
      bitSign (q (oddHeadB B) (oddHeadC C) + Qpair (oddTailB B) (oddTailC C)) := by
  rw [Qraw_eq_odd_split_of_surviving (n := n) hn hk]

noncomputable def oddDataSign {n : ℕ} [NeZero n] (d : OddSurvivingData n) : ℤ :=
  match d with
  | (bc, RB, RC) => bitSign (q bc.1.1 bc.1.2 + Qpair RB.1 RC.1)

noncomputable def oddVisibleSign {n : ℕ} [NeZero n] (bc : OddVisibleData n) : ℤ :=
  bitSign (q bc.1.1 bc.1.2)

noncomputable def oddTailSign {n : ℕ} [NeZero n] (RB : OddZeroHeadB n) (RC : OddZeroHeadC n) : ℤ :=
  bitSign (Qpair RB.1 RC.1)

noncomputable def oddHSign {n : ℕ} [NeZero n] (h : HSpace (n := n)) : ℤ :=
  bitSign (q (bPref h.1) (cPref h.1))

noncomputable def oddRectCoeff {n : ℕ} [NeZero n] (h : HSpace (n := n)) (i : OddRectIndex n) : F :=
  oddRectBasis (n := n).repr h i

noncomputable def oddRectSupport {n : ℕ} [NeZero n] (h : HSpace (n := n)) : Finset (OddRectIndex n) :=
  Finset.univ.filter (fun i => oddRectCoeff h i = 1)

lemma oddRectCoeff_eq_zero_or_one {n : ℕ} [NeZero n] (h : HSpace (n := n)) (i : OddRectIndex n) :
    oddRectCoeff h i = 0 ∨ oddRectCoeff h i = 1 := by
  set x : F := oddRectCoeff h i with hx
  have hxlt : x.val < 2 := by simpa [F] using ZMod.val_lt x
  have hxeq : x.val = 0 ∨ x.val = 1 := by omega
  rcases hxeq with hx0 | hx1
  · left
    apply ZMod.val_injective
    simpa [hx0]
  · right
    apply ZMod.val_injective
    have hval1 : ZMod.val (1 : F) = 1 := by native_decide
    simpa [hx1] using hval1.symm

lemma oddRectCoeff_smul_eq_filter {n : ℕ} [NeZero n] (h : HSpace (n := n)) (i : OddRectIndex n) :
    oddRectCoeff h i • oddRectVec (n := n) i =
      if oddRectCoeff h i = 1 then oddRectVec (n := n) i else 0 := by
  rcases oddRectCoeff_eq_zero_or_one (n := n) h i with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    simp

lemma oddRectCoeff_oddRectVec {n : ℕ} [NeZero n] (i j : OddRectIndex n) :
    oddRectCoeff (oddRectVec (n := n) j) i = if i = j then 1 else 0 := by
  have hrepr : (oddRectBasis (n := n)).repr ((oddRectVec (n := n) j)) = Finsupp.single j 1 := by
    simpa [oddRectBasis_apply] using (oddRectBasis (n := n)).repr_self j
  have hval := congrArg (fun f => f i) hrepr
  simpa [oddRectCoeff, Finsupp.single_apply, eq_comm] using hval

lemma oddRectCoeff_add_oddRectVec {n : ℕ} [NeZero n] (h : HSpace (n := n))
    (i j : OddRectIndex n) :
    oddRectCoeff (h + oddRectVec (n := n) j) i =
      oddRectCoeff h i + if i = j then 1 else 0 := by
  rw [oddRectCoeff, LinearEquiv.map_add]
  change oddRectCoeff h i + (oddRectBasis (n := n)).repr (oddRectVec (n := n) j) i =
    oddRectCoeff h i + if i = j then 1 else 0
  simpa [oddRectCoeff] using
    congrArg (fun x => oddRectCoeff h i + x) (oddRectCoeff_oddRectVec (n := n) i j)

lemma oddRectCoeff_add_oddRectVec_eq_one_iff {n : ℕ} [NeZero n] (h : HSpace (n := n))
    (i j : OddRectIndex n) :
    oddRectCoeff (h + oddRectVec (n := n) j) i = 1 ↔
      if i = j then oddRectCoeff h i = 0 else oddRectCoeff h i = 1 := by
  by_cases hij : i = j
  · subst hij
    rw [oddRectCoeff_add_oddRectVec]
    simp
  · rw [oddRectCoeff_add_oddRectVec]
    simp [hij]

lemma mem_oddRectSupport_add_oddRectVec_iff {n : ℕ} [NeZero n] (h : HSpace (n := n))
    (i j : OddRectIndex n) :
    i ∈ oddRectSupport (n := n) (h + oddRectVec (n := n) j) ↔
      if i = j then i ∉ oddRectSupport (n := n) h else i ∈ oddRectSupport (n := n) h := by
  by_cases hij : i = j
  · subst hij
    simp [oddRectSupport, oddRectCoeff_add_oddRectVec_eq_one_iff]
    rcases oddRectCoeff_eq_zero_or_one (n := n) h i with h0 | h1
    · simp [h0]
    · simp [h1]
  · simp [oddRectSupport, oddRectCoeff_add_oddRectVec_eq_one_iff, hij]

lemma oddRect_sum_repr {n : ℕ} [NeZero n] (h : HSpace (n := n)) :
    h = ∑ i : OddRectIndex n, oddRectCoeff h i • oddRectVec (n := n) i := by
  have hs : (∑ i : OddRectIndex n, oddRectCoeff h i • oddRectVec (n := n) i) = h := by
    convert (oddRectBasis (n := n)).sum_repr h using 1
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [oddRectCoeff]
  exact hs.symm

lemma oddRect_sum_support {n : ℕ} [NeZero n] (h : HSpace (n := n)) :
    h = Finset.sum (oddRectSupport (n := n) h) (fun i => oddRectVec (n := n) i) := by
  calc
    h = ∑ i : OddRectIndex n, oddRectCoeff h i • oddRectVec (n := n) i := oddRect_sum_repr (n := n) h
    _ = ∑ i : OddRectIndex n,
          if oddRectCoeff h i = 1 then oddRectVec (n := n) i else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using oddRectCoeff_smul_eq_filter (n := n) h i
    _ = Finset.sum (oddRectSupport (n := n) h) (fun i => oddRectVec (n := n) i) := by
          simpa [oddRectSupport] using
            (Finset.sum_filter (s := Finset.univ) (p := fun i : OddRectIndex n => oddRectCoeff h i = 1)
              (f := fun i => oddRectVec (n := n) i)).symm

lemma oddRectCoeff_eq_apply_nonzero {n : ℕ} [NeZero n] (h : HSpace (n := n)) (i : OddRectIndex n) :
    oddRectCoeff h i = h.1 i.1.1 i.2.1 := by
  have hs :=
    congrFun (congrFun (congrArg Subtype.val (oddRect_sum_repr (n := n) h)) i.1.1) i.2.1
  have hs' : h.1 i.1.1 i.2.1 =
      ∑ j : OddRectIndex n, oddRectCoeff h j * (oddRectVec (n := n) j).1 i.1.1 i.2.1 := by
    simpa using hs
  rw [hs']
  symm
  calc
    ∑ j : OddRectIndex n, oddRectCoeff h j * (oddRectVec (n := n) j).1 i.1.1 i.2.1
        = ∑ j : OddRectIndex n, oddRectCoeff h j * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [oddRectVec, rect_apply_oddRectIndex, eq_comm]
    _ = oddRectCoeff h i := by
          simp

lemma mem_oddRectSupport_iff_apply_nonzero_eq_one {n : ℕ} [NeZero n] (h : HSpace (n := n))
    (i : OddRectIndex n) :
    i ∈ oddRectSupport (n := n) h ↔ h.1 i.1.1 i.2.1 = 1 := by
  simp [oddRectSupport, oddRectCoeff_eq_apply_nonzero]

@[simp] lemma oddRectSupport_zero {n : ℕ} [NeZero n] :
    oddRectSupport (n := n) (0 : HSpace (n := n)) = ∅ := by
  ext i
  rw [mem_oddRectSupport_iff_apply_nonzero_eq_one]
  simp

@[simp] lemma oddRectSupport_oddRectVec {n : ℕ} [NeZero n] (i : OddRectIndex n) :
    oddRectSupport (n := n) (oddRectVec (n := n) i) = {i} := by
  ext j
  rw [Finset.mem_singleton, mem_oddRectSupport_iff_apply_nonzero_eq_one]
  simp [oddRectVec, rect_apply_oddRectIndex, eq_comm]

lemma oddRectSupport_add_oddRectVec {n : ℕ} [NeZero n] (h : HSpace (n := n))
    (j : OddRectIndex n) :
    oddRectSupport (n := n) (h + oddRectVec (n := n) j) =
      if j ∈ oddRectSupport (n := n) h then (oddRectSupport (n := n) h).erase j
      else insert j (oddRectSupport (n := n) h) := by
  classical
  ext i
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ oddRectSupport (n := n) h
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hi]
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hi]
  · by_cases hj : j ∈ oddRectSupport (n := n) h
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hij, hj]
    · simp [mem_oddRectSupport_add_oddRectVec_iff, hij, hj]

@[simp] lemma oddRectSupport_sum {n : ℕ} [NeZero n] (S : Finset (OddRectIndex n)) :
    oddRectSupport (n := n) (Finset.sum S fun i => oddRectVec (n := n) i) = S := by
  classical
  refine Finset.induction_on S ?base ?step
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi]
    rw [add_comm]
    rw [oddRectSupport_add_oddRectVec]
    rw [hS]
    simp [hi]

noncomputable def oddRectSupportEquiv {n : ℕ} [NeZero n] :
    HSpace (n := n) ≃ Finset (OddRectIndex n) where
  toFun := oddRectSupport (n := n)
  invFun := fun S => Finset.sum S fun i => oddRectVec (n := n) i
  left_inv := by
    intro h
    simpa using (oddRect_sum_support (n := n) h).symm
  right_inv := by
    intro S
    simpa using oddRectSupport_sum (n := n) S

lemma bPref_sum_oddRectVec {n : ℕ} [NeZero n] (S : Finset (OddRectIndex n)) :
    bPref (Finset.sum S fun i => (oddRectVec (n := n) i).1) =
      Finset.sum S (fun i => bPref (oddRectVec (n := n) i).1) := by
  classical
  refine Finset.induction_on S ?base ?step
  · ext t p q'
    simp [bPref, buildB, prefixT]
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, bPref_add, hS]

lemma cPref_sum_oddRectVec {n : ℕ} [NeZero n] (S : Finset (OddRectIndex n)) :
    cPref (Finset.sum S fun i => (oddRectVec (n := n) i).1) =
      Finset.sum S (fun i => cPref (oddRectVec (n := n) i).1) := by
  classical
  refine Finset.induction_on S ?base ?step
  · ext x y r
    simp [cPref, buildC, prefixR]
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, cPref_add, hS]

lemma q_bPref_sum_oddRectVec_left {n : ℕ} [NeZero n] (S : Finset (OddRectIndex n)) (k : HFun n) :
    q (bPref (Finset.sum S fun i => (oddRectVec (n := n) i).1)) (cPref k) =
      Finset.sum S (fun i => q (bPref (oddRectVec (n := n) i).1) (cPref k)) := by
  classical
  refine Finset.induction_on S ?base ?step
  · simp [bPref, buildB, prefixT, q]
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, bPref_add, q_add_left, hS]

lemma q_bPref_sum_oddRectVec_right {n : ℕ} [NeZero n] (h : HFun n) (S : Finset (OddRectIndex n)) :
    q (bPref h) (cPref (Finset.sum S fun i => (oddRectVec (n := n) i).1)) =
      Finset.sum S (fun i => q (bPref h) (cPref (oddRectVec (n := n) i).1)) := by
  classical
  refine Finset.induction_on S ?base ?step
  · simp [cPref, buildC, prefixR, q]
  · intro i S hi hS
    rw [Finset.sum_insert hi, Finset.sum_insert hi, cPref_add, q_add_right, hS]

lemma q_bPref_cPref_eq_sum_support_support {n : ℕ} [NeZero n]
    (h k : HSpace (n := n)) :
    q (bPref h.1) (cPref k.1) =
      Finset.sum (oddRectSupport (n := n) h)
        (fun i =>
          Finset.sum (oddRectSupport (n := n) k)
            (fun j => q (bPref (oddRectVec (n := n) i).1) (cPref (oddRectVec (n := n) j).1))) := by
  have hh : h.1 = Finset.sum (oddRectSupport (n := n) h) fun i => (oddRectVec (n := n) i).1 := by
    simpa using congrArg Subtype.val (oddRect_sum_support (n := n) h)
  have hk : k.1 = Finset.sum (oddRectSupport (n := n) k) fun i => (oddRectVec (n := n) i).1 := by
    simpa using congrArg Subtype.val (oddRect_sum_support (n := n) k)
  rw [hh, hk]
  rw [q_bPref_sum_oddRectVec_left]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [q_bPref_sum_oddRectVec_right]

lemma sum_oddHSign_eq_sum_supportSubsets {n : ℕ} [NeZero n] :
    (∑ h : HSpace (n := n), oddHSign h) =
      ∑ S : Finset (OddRectIndex n), oddHSign ((oddRectSupportEquiv (n := n)).symm S) := by
  simpa using
    (((oddRectSupportEquiv (n := n)).symm.sum_comp
      (fun h : HSpace (n := n) => oddHSign h)).symm)

lemma oddHSign_add_oddRectVec_iff_qsymm {n : ℕ} [NeZero n] (hn : Odd n)
    (h : HSpace (n := n)) (i : OddRectIndex n)
    (hsymm :
      q (bPref h.1) (cPref (oddRectVec (n := n) i).1) =
        q (bPref (oddRectVec (n := n) i).1) (cPref h.1)) :
    oddHSign (h + oddRectVec (n := n) i) = oddHSign h := by
  unfold oddHSign
  have hadd :
      q (bPref (h + oddRectVec (n := n) i).1) (cPref (h + oddRectVec (n := n) i).1) =
        q (bPref h.1) (cPref h.1) +
          q (bPref h.1) (cPref (oddRectVec (n := n) i).1) +
          q (bPref (oddRectVec (n := n) i).1) (cPref h.1) +
          q (bPref (oddRectVec (n := n) i).1) (cPref (oddRectVec (n := n) i).1) := by
    change q (bPref (h.1 + (oddRectVec (n := n) i).1)) (cPref (h.1 + (oddRectVec (n := n) i).1)) = _
    rw [q_bPref_add_left, q_bPref_add_right, q_bPref_add_right]
    ac_rfl
  rw [hadd, hsymm, q_bPref_cPref_rect_eq_zero_of_odd (n := n) hn i]
  simp [bitSign, add_assoc, add_left_comm, add_comm, F_add_self]

lemma oddHSign_oddRectVec_eq_one {n : ℕ} [NeZero n] (hn : Odd n)
    (i : OddRectIndex n) :
    oddHSign (oddRectVec (n := n) i) = 1 := by
  unfold oddHSign
  rw [q_bPref_cPref_rect_eq_zero_of_odd (n := n) hn i]
  exact bitSign_zero

lemma q_bPref_cPref_symm_oddRectVec_right_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (h : HSpace (n := n)) (i : OddRectIndex n) :
    q (bPref h.1) (cPref (oddRectVec (n := n) i).1) =
      q (bPref (oddRectVec (n := n) i).1) (cPref h.1) := by
  rw [q_bPref_cPref_eq_sum_support_support (n := n) h (oddRectVec (n := n) i)]
  rw [q_bPref_cPref_eq_sum_support_support (n := n) (oddRectVec (n := n) i) h]
  simp only [oddRectSupport_oddRectVec, Finset.sum_singleton]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa [oddRectPair] using (oddRectPair_symm_of_odd (n := n) hn j i)

lemma oddHSign_add_oddRectVec_eq_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (h : HSpace (n := n)) (i : OddRectIndex n) :
    oddHSign (h + oddRectVec (n := n) i) = oddHSign h := by
  refine oddHSign_add_oddRectVec_iff_qsymm (n := n) hn h i ?_
  exact q_bPref_cPref_symm_oddRectVec_right_of_odd (n := n) hn h i

@[simp] lemma oddHSign_zero_eq_one {n : ℕ} [NeZero n] :
    oddHSign (0 : HSpace (n := n)) = 1 := by
  unfold oddHSign
  simp [q, bPref, cPref, buildB, buildC, prefixT, prefixR, bitSign_zero]

lemma oddHSign_sum_oddRectVec_eq_one_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (S : Finset (OddRectIndex n)) :
    oddHSign (Finset.sum S (fun i => oddRectVec (n := n) i)) = 1 := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S hi hS
    rw [Finset.sum_insert hi]
    calc
      oddHSign (oddRectVec (n := n) i + Finset.sum S (fun j => oddRectVec (n := n) j))
          = oddHSign ((Finset.sum S (fun j => oddRectVec (n := n) j)) + oddRectVec (n := n) i) := by
              simp [add_comm]
      _ = oddHSign (Finset.sum S (fun j => oddRectVec (n := n) j)) := by
            exact oddHSign_add_oddRectVec_eq_of_odd (n := n) hn _ i
      _ = 1 := hS

lemma oddHSign_eq_one_of_odd {n : ℕ} [NeZero n] (hn : Odd n)
    (h : HSpace (n := n)) :
    oddHSign h = 1 := by
  rw [oddRect_sum_support (n := n) h]
  exact oddHSign_sum_oddRectVec_eq_one_of_odd (n := n) hn (oddRectSupport (n := n) h)

lemma sum_oddHSign_eq_natCard_HSpace_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ h : HSpace (n := n), oddHSign h = (Nat.card (HSpace (n := n)) : ℤ) := by
  simp [oddHSign_eq_one_of_odd (n := n) hn]

lemma sum_oddRectVec_eq_card {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ i : OddRectIndex n, oddHSign (oddRectVec (n := n) i) = ((n - 1) ^ 2 : ℤ) := by
  calc
    ∑ i : OddRectIndex n, oddHSign (oddRectVec (n := n) i)
        = ∑ _i : OddRectIndex n, (1 : ℤ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact oddHSign_oddRectVec_eq_one (n := n) hn i
    _ = (Fintype.card (OddRectIndex n) : ℤ) := by simp
    _ = ((n : ℤ) - 1) * ((n : ℤ) - 1) := by
          have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
          simpa [card_oddRectIndex, pow_two, Nat.cast_sub hn1]
    _ = ((n - 1) ^ 2 : ℤ) := by
          have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
          simpa [pow_two, Nat.cast_sub hn1]

lemma oddVisibleSign_fromHUV_eq_oddHSign {n : ℕ} [NeZero n] (hn : Odd n)
    (z : OddVisibleHUVData n) :
    oddVisibleSign (oddVisibleFromHUVData (n := n) z) = oddHSign z.1 := by
  rcases z with ⟨h, u, v⟩
  simp [oddVisibleSign, oddHSign, oddVisibleFromHUVData]
  rw [q_build_eq_q_bPref_cPref_of_odd (hn := hn) h.2 u v]

lemma sum_oddVisible_eq_hspace_sum {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ bc : OddVisibleData n, oddVisibleSign bc =
      (2 : ℤ) ^ (n ^ 2 + n ^ 2) * ∑ h : HSpace (n := n), oddHSign h := by
  have hrew :
      ∑ bc : OddVisibleData n, oddVisibleSign bc
        =
      ∑ z : OddVisibleHUVData n, oddVisibleSign (oddVisibleFromHUVData (n := n) z) := by
    calc
      ∑ bc : OddVisibleData n, oddVisibleSign bc
        = ∑ bc : OddVisibleData n,
            oddVisibleSign
              (oddVisibleFromHUVData (n := n) (oddVisibleToHUVData (n := n) bc)) := by
                refine Finset.sum_congr rfl ?_
                intro bc hbc
                simpa using congrArg oddVisibleSign (oddVisibleFromHUVData_to (n := n) bc).symm
      _ = ∑ z : OddVisibleHUVData n, oddVisibleSign (oddVisibleFromHUVData (n := n) z) := by
            simpa using
              (Equiv.sum_comp (oddVisibleEquivHUVData (n := n))
                (fun z : OddVisibleHUVData n =>
                  oddVisibleSign (oddVisibleFromHUVData (n := n) z)))
  rw [hrew]
  rw [Fintype.sum_prod_type_right]
  rw [Fintype.sum_prod_type_right]
  have huv : (Fintype.card (UVFun n) : ℤ) = (2 : ℤ) ^ (n ^ 2) := by
    rw [← Nat.card_eq_fintype_card]
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [F, finrank_uvFun]
  have hsign :
      ∀ (y x : UVFun n) (h : HSpace (n := n)),
        oddVisibleSign (oddVisibleFromHUVData (n := n) (h, x, y)) = oddHSign h := by
    intro y x h
    rw [oddVisibleSign_fromHUV_eq_oddHSign (hn := hn) (z := (h, x, y))]
  calc
    ∑ y : UVFun n, ∑ x : UVFun n, ∑ h : HSpace (n := n),
        oddVisibleSign (oddVisibleFromHUVData (n := n) (h, x, y))
      = ∑ y : UVFun n, ∑ x : UVFun n, ∑ h : HSpace (n := n), oddHSign h := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro h hh
          exact hsign y x h
    _ = ∑ y : UVFun n, ∑ x : UVFun n, (∑ h : HSpace (n := n), oddHSign h) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp
    _ = ∑ y : UVFun n, (Fintype.card (UVFun n) : ℤ) * ∑ h : HSpace (n := n), oddHSign h := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp
    _ = (Fintype.card (UVFun n) : ℤ) *
          ((Fintype.card (UVFun n) : ℤ) * ∑ h : HSpace (n := n), oddHSign h) := by
          simp
    _ = (2 : ℤ) ^ (n ^ 2 + n ^ 2) * ∑ h : HSpace (n := n), oddHSign h := by
          let S : ℤ := ∑ h : HSpace (n := n), oddHSign h
          have hpow :
              (Fintype.card (UVFun n) : ℤ) *
                  ((Fintype.card (UVFun n) : ℤ) * S)
                =
              (2 : ℤ) ^ (n ^ 2 + n ^ 2) * S := by
            simpa [pow_add, pow_mul, pow_two, mul_assoc]
          simpa [S] using hpow

lemma sum_oddVisible_eq_natCard_oddVisibleData_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ bc : OddVisibleData n, oddVisibleSign bc = (Nat.card (OddVisibleData n) : ℤ) := by
  rw [sum_oddVisible_eq_hspace_sum (n := n) hn]
  rw [sum_oddHSign_eq_natCard_HSpace_of_odd (n := n) hn]
  rw [natCard_oddVisibleData (n := n), natCard_HSpace (n := n)]
  norm_num
  rw [mul_comm, ← pow_add]
  congr
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
  simp [pow_two]
  ring_nf
  omega

lemma sum_oddVisible_eq_closed_form_of_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ bc : OddVisibleData n, oddVisibleSign bc = (2 : ℤ) ^ (3 * n ^ 2 + 1 - 2 * n) := by
  rw [sum_oddVisible_eq_natCard_oddVisibleData_of_odd (n := n) hn]
  simpa using congrArg (fun x : ℕ => (x : ℤ)) (fintypeCard_oddVisibleData (n := n))

lemma oddDataSign_eq_mul {n : ℕ} [NeZero n] (d : OddSurvivingData n) :
    oddDataSign d =
      oddVisibleSign d.1 * oddTailSign d.2.1 d.2.2 := by
  rcases d with ⟨bc, RB, RC⟩
  simp [oddDataSign, oddVisibleSign, oddTailSign, bitSign_add]

lemma sum_survivingBC_eq_sum_oddData {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2) =
      ∑ d : OddSurvivingData n, oddDataSign d := by
  classical
  have hrew :
      ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2)
        = ∑ d : OddSurvivingData n,
            bitSign (Qraw (oddDataToSurviving (n := n) hn d).1.1
              (oddDataToSurviving (n := n) hn d).1.2) := by
        refine Fintype.sum_equiv (oddSurvivingEquiv (n := n) hn) _ _ ?_
        intro bc
        have hleft : oddDataToSurviving (n := n) hn ((oddSurvivingEquiv (n := n) hn) bc) = bc := by
          simpa [oddSurvivingEquiv] using oddDataToSurviving_oddSurvivingToData (n := n) hn bc
        simpa [hleft]
  calc
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2)
        = ∑ d : OddSurvivingData n,
            bitSign (Qraw (oddDataToSurviving (n := n) hn d).1.1
              (oddDataToSurviving (n := n) hn d).1.2) := hrew
    _ = ∑ d : OddSurvivingData n, oddDataSign d := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rcases d with ⟨⟨⟨b, c⟩, hbc⟩, ⟨RB, hRB⟩, ⟨RC, hRC⟩⟩
          have hk : kappa (oddBuildB b RB) (oddBuildC c RC) = 0 :=
            (kappa_eq_zero_iff_oddBuild_mem_SSpace (n := n) hn b c RB RC hRB hRC).2 hbc
          calc
            bitSign (Qraw (oddBuildB b RB) (oddBuildC c RC))
                = bitSign
                    (q (oddHeadB (oddBuildB b RB)) (oddHeadC (oddBuildC c RC)) +
                      Qpair (oddTailB (oddBuildB b RB)) (oddTailC (oddBuildC c RC))) := by
                        exact bitSign_Qraw_eq_odd_split_of_surviving (n := n) hn
                          (B := oddBuildB b RB) (C := oddBuildC c RC) hk
            _ = bitSign (q b c + Qpair RB RC) := by
                  simp [oddHeadB_oddBuild_eq (n := n) hn b RB hRB,
                    oddHeadC_oddBuild_eq (n := n) hn c RC hRC,
                    oddTailB_oddBuild_eq (n := n) hn b RB hRB,
                    oddTailC_oddBuild_eq (n := n) hn c RC hRC]

lemma sum_oddData_eq_iterated {n : ℕ} [NeZero n] :
    ∑ d : OddSurvivingData n, oddDataSign d =
      ∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n, ∑ bc : OddVisibleData n,
        oddVisibleSign bc * oddTailSign RB RC := by
  simp_rw [Fintype.sum_prod_type_right]
  simp [oddDataSign_eq_mul, oddVisibleSign, oddTailSign]

lemma sum_oddData_eq_visible_mul_tail {n : ℕ} [NeZero n] :
    ∑ d : OddSurvivingData n, oddDataSign d =
      (∑ bc : OddVisibleData n, oddVisibleSign bc) *
        (∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n, oddTailSign RB RC) := by
  rw [sum_oddData_eq_iterated]
  calc
    ∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n, ∑ bc : OddVisibleData n,
        oddVisibleSign bc * oddTailSign RB RC
      = ∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n,
          (∑ bc : OddVisibleData n, oddVisibleSign bc) * oddTailSign RB RC := by
            refine Finset.sum_congr rfl ?_
            intro RC hRC
            refine Finset.sum_congr rfl ?_
            intro RB hRB
            rw [← Finset.sum_mul]
    _ = ∑ RC : OddZeroHeadC n,
          (∑ bc : OddVisibleData n, oddVisibleSign bc) *
            ∑ RB : OddZeroHeadB n, oddTailSign RB RC := by
              refine Finset.sum_congr rfl ?_
              intro RC hRC
              rw [← Finset.mul_sum]
    _ = (∑ bc : OddVisibleData n, oddVisibleSign bc) *
          (∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n, oddTailSign RB RC) := by
            rw [← Finset.mul_sum]

lemma sum_survivingBC_eq_visible_mul_tail {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ bc : SurvivingBC n, bitSign (Qraw bc.1.1 bc.1.2) =
      (∑ bc : OddVisibleData n, oddVisibleSign bc) *
        (∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n, oddTailSign RB RC) := by
  rw [sum_survivingBC_eq_sum_oddData (n := n) hn, sum_oddData_eq_visible_mul_tail]

lemma sum_oddTail_eq_sum_woddQpair {n : ℕ} [NeZero n] :
    ∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n, oddTailSign RB RC =
      ∑ RC : WoddCCoef n, ∑ RB : WoddBCoef n, bitSign (woddQpair RB RC) := by
  classical
  calc
    ∑ RC : OddZeroHeadC n, ∑ RB : OddZeroHeadB n, oddTailSign RB RC
        = ∑ RC : WoddCCoef n,
            ∑ RB : OddZeroHeadB n, oddTailSign RB
              ((oddZeroHeadCEquivWoddCCoef (n := n)).symm RC) := by
              refine Fintype.sum_equiv (oddZeroHeadCEquivWoddCCoef (n := n)) _ _ ?_
              intro RC
              rfl
    _ = ∑ RC : WoddCCoef n,
          ∑ RB : WoddBCoef n,
            oddTailSign ((oddZeroHeadBEquivWoddBCoef (n := n)).symm RB)
              ((oddZeroHeadCEquivWoddCCoef (n := n)).symm RC) := by
              refine Finset.sum_congr rfl ?_
              intro RC hRC
              refine Fintype.sum_equiv (oddZeroHeadBEquivWoddBCoef (n := n)) _ _ ?_
              intro RB
              rfl
    _ = ∑ RC : WoddCCoef n, ∑ RB : WoddBCoef n, bitSign (woddQpair RB RC) := by
          refine Finset.sum_congr rfl ?_
          intro RC hRC
          refine Finset.sum_congr rfl ?_
          intro RB hRB
          have hRB' : oddZeroHeadBToWoddBCoef ((oddZeroHeadBEquivWoddBCoef (n := n)).symm RB) = RB :=
            (oddZeroHeadBEquivWoddBCoef (n := n)).apply_symm_apply RB
          have hRC' : oddZeroHeadCToWoddCCoef ((oddZeroHeadCEquivWoddCCoef (n := n)).symm RC) = RC :=
            (oddZeroHeadCEquivWoddCCoef (n := n)).apply_symm_apply RC
          simp [oddTailSign, Qpair_eq_woddQpair, hRB', hRC']

abbrev CoordHead (n : ℕ) := BCoef n × BCoef n × CCoef n × CCoef n

abbrev CoordData (n m : ℕ) := (Fin m → BCoef n) × (Fin m → BCoef n) ×
  (Fin m → CCoef n) × (Fin m → CCoef n)

abbrev coordHeadBU {n : ℕ} (h : CoordHead n) : BCoef n := h.1

abbrev coordHeadBV {n : ℕ} (h : CoordHead n) : BCoef n := h.2.1

abbrev coordHeadCU {n : ℕ} (h : CoordHead n) : CCoef n := h.2.2.1

abbrev coordHeadCV {n : ℕ} (h : CoordHead n) : CCoef n := h.2.2.2

abbrev coordBU {n m : ℕ} (d : CoordData n m) : Fin m → BCoef n := d.1

abbrev coordBV {n m : ℕ} (d : CoordData n m) : Fin m → BCoef n := d.2.1

abbrev coordCU {n m : ℕ} (d : CoordData n m) : Fin m → CCoef n := d.2.2.1

abbrev coordCV {n m : ℕ} (d : CoordData n m) : Fin m → CCoef n := d.2.2.2

noncomputable def coordHeadSign {n : ℕ} [NeZero n] (h : CoordHead n) : ℤ :=
  bitSign (q (coordHeadBU h) (coordHeadCV h) + q (coordHeadBV h) (coordHeadCU h))

noncomputable def coordDataSign {n m : ℕ} [NeZero n] (d : CoordData n m) : ℤ :=
  bitSign (∑ i : Fin m, (q (coordBU d i) (coordCV d i) + q (coordBV d i) (coordCU d i)))

noncomputable def coordDataSuccEquiv {n m : ℕ} :
    CoordData n (m + 1) ≃ CoordHead n × CoordData n m where
  toFun d :=
    ((coordBU d 0, coordBV d 0, coordCU d 0, coordCV d 0),
      (Fin.tail (coordBU d), Fin.tail (coordBV d), Fin.tail (coordCU d), Fin.tail (coordCV d)))
  invFun x :=
    ((Fin.cons (coordHeadBU x.1) (coordBU x.2)),
      (Fin.cons (coordHeadBV x.1) (coordBV x.2)),
      (Fin.cons (coordHeadCU x.1) (coordCU x.2)),
      (Fin.cons (coordHeadCV x.1) (coordCV x.2)))
  left_inv d := by
    rcases d with ⟨BU, BV, CU, CV⟩
    change
      ((Fin.cons (BU 0) (Fin.tail BU)),
        (Fin.cons (BV 0) (Fin.tail BV)),
        (Fin.cons (CU 0) (Fin.tail CU)),
        (Fin.cons (CV 0) (Fin.tail CV))) = (BU, BV, CU, CV)
    simp [Fin.cons_self_tail]
  right_inv x := by
    rcases x with ⟨⟨BU, BV, CU, CV⟩, ⟨BUt, BVt, CUt, CVt⟩⟩
    ext <;> simp [coordBU, coordBV, coordCU, coordCV, coordHeadBU, coordHeadBV, coordHeadCU,
      coordHeadCV, Fin.tail_cons]

lemma coordDataSign_succ {n m : ℕ} [NeZero n] (h : CoordHead n) (d : CoordData n m) :
    coordDataSign ((coordDataSuccEquiv (n := n) (m := m)).symm (h, d)) =
      coordHeadSign h * coordDataSign d := by
  rcases h with ⟨BU, BV, CU, CV⟩
  rcases d with ⟨BUt, BVt, CUt, CVt⟩
  simpa [coordDataSign, coordHeadSign, coordDataSuccEquiv, Fin.sum_univ_succ, add_assoc] using
    (bitSign_add (q BU CV + q BV CU)
      (∑ i : Fin m, (q (BUt i) (CVt i) + q (BVt i) (CUt i))))

noncomputable def ordinaryPairValue (n : ℕ) [NeZero n] : ℤ :=
  ∑ b : BCoef n, ∑ b' : BCoef n, ∑ c : CCoef n, ∑ c' : CCoef n, bitSign (q b c' + q b' c)

def ordinaryPairExponent (n : ℕ) : ℕ :=
  (n ^ 3 + (n ^ 3 - n * (n - 1))) + (n ^ 3 + (n ^ 3 - n * (n - 1)))

lemma sum_coordHeadSign_eq_ordinary_pair {n : ℕ} [NeZero n] :
    ∑ h : CoordHead n, coordHeadSign h = ordinaryPairValue n := by
  calc
    ∑ h : CoordHead n, coordHeadSign h
        = ∑ b : BCoef n, ∑ r : BCoef n × (CCoef n × CCoef n),
            bitSign (q b r.2.2 + q r.1 r.2.1) := by
              simpa [CoordHead, coordHeadSign] using
                (Fintype.sum_prod_type'
                  (f := fun b : BCoef n => fun r : BCoef n × (CCoef n × CCoef n) =>
                    bitSign (q b r.2.2 + q r.1 r.2.1)))
    _ = ∑ b : BCoef n, ∑ b' : BCoef n, ∑ r : CCoef n × CCoef n,
          bitSign (q b r.2 + q b' r.1) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            simpa using
              (Fintype.sum_prod_type'
                (f := fun b' : BCoef n => fun r : CCoef n × CCoef n =>
                  bitSign (q b r.2 + q b' r.1)))
    _ = ordinaryPairValue n := by
          unfold ordinaryPairValue
          refine Finset.sum_congr rfl ?_
          intro b hb
          refine Finset.sum_congr rfl ?_
          intro b' hb'
          simpa using
            (Fintype.sum_prod_type'
              (f := fun c : CCoef n => fun c' : CCoef n =>
                bitSign (q b c' + q b' c)))

lemma ordinaryPairValue_eq_closed_form {n : ℕ} [NeZero n] :
    ordinaryPairValue n =
      (2 : ℤ) ^ ordinaryPairExponent n := by
  simpa [ordinaryPairValue] using (ordinary_pair_sum (n := n))

lemma sum_coordDataSign_eq_pow {n : ℕ} [NeZero n] :
    ∀ m : ℕ, ∑ d : CoordData n m, coordDataSign d = (ordinaryPairValue n) ^ m
  | 0 => by
      simp [coordDataSign, ordinaryPairValue, bitSign_zero]
  | m + 1 => by
      calc
        ∑ d : CoordData n (m + 1), coordDataSign d
            = ∑ x : CoordHead n × CoordData n m,
                coordDataSign ((coordDataSuccEquiv (n := n) (m := m)).symm x) := by
                  refine Fintype.sum_equiv (coordDataSuccEquiv (n := n) (m := m))
                    (fun d => coordDataSign d)
                    (fun x => coordDataSign ((coordDataSuccEquiv (n := n) (m := m)).symm x)) ?_
                  intro d
                  simp
        _ = ∑ x : CoordHead n × CoordData n m, coordHeadSign x.1 * coordDataSign x.2 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rcases x with ⟨h, d⟩
              simpa using coordDataSign_succ (n := n) (m := m) h d
        _ = ∑ h : CoordHead n, ∑ d : CoordData n m, coordHeadSign h * coordDataSign d := by
              simpa using
                (Fintype.sum_prod_type' (f := fun h : CoordHead n => fun d : CoordData n m =>
                  coordHeadSign h * coordDataSign d))
        _ = ∑ h : CoordHead n, coordHeadSign h * ∑ d : CoordData n m, coordDataSign d := by
              refine Finset.sum_congr rfl ?_
              intro h hh
              rw [← Finset.mul_sum]
        _ = (∑ h : CoordHead n, coordHeadSign h) * ∑ d : CoordData n m, coordDataSign d := by
              rw [Finset.sum_mul]
        _ = ordinaryPairValue n * (ordinaryPairValue n) ^ m := by
              rw [sum_coordHeadSign_eq_ordinary_pair, sum_coordDataSign_eq_pow]
        _ = (ordinaryPairValue n) ^ (m + 1) := by
              simp [pow_succ, mul_comm]

noncomputable def coordDataPackEquiv {n m : ℕ} :
    ((Fin m → CCoef n) × (Fin m → CCoef n)) × ((Fin m → BCoef n) × (Fin m → BCoef n)) ≃
      CoordData n m where
  toFun x := (x.2.1, x.2.2, x.1.1, x.1.2)
  invFun d := ((coordCU d, coordCV d), (coordBU d, coordBV d))
  left_inv x := by
    rcases x with ⟨⟨CU, CV⟩, BU, BV⟩
    rfl
  right_inv d := by
    rcases d with ⟨BU, BV, CU, CV⟩
    rfl

noncomputable def woddCoordDataEquiv {m : ℕ} :
    WoddCCoef (2 * m + 1) × WoddBCoef (2 * m + 1) ≃ CoordData (2 * m + 1) m :=
  (Equiv.prodCongr (oddCoordCCoefEquivWoddCCoef (m := m)) (oddCoordBCoefEquivWoddBCoef (m := m))).trans
    (coordDataPackEquiv (n := 2 * m + 1) (m := m))

lemma sum_woddQpair_eq_sum_coordData {m : ℕ} :
    ∑ RC : WoddCCoef (2 * m + 1), ∑ RB : WoddBCoef (2 * m + 1), bitSign (woddQpair RB RC) =
      ∑ d : CoordData (2 * m + 1) m, coordDataSign d := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (woddCoordDataEquiv (m := m))
    (fun x => bitSign (woddQpair x.2 x.1))
    (fun d => coordDataSign d) ?_
  intro x
  rcases x with ⟨RC, RB⟩
  simpa [coordDataSign, woddCoordDataEquiv, coordDataPackEquiv] using
    congrArg bitSign (woddQpair_eq_sum_q (m := m) RB RC)

lemma sum_woddQpair_eq_ordinary_pair_pow {m : ℕ} :
    ∑ RC : WoddCCoef (2 * m + 1), ∑ RB : WoddBCoef (2 * m + 1), bitSign (woddQpair RB RC) =
      (ordinaryPairValue (2 * m + 1)) ^ m := by
  rw [sum_woddQpair_eq_sum_coordData]
  exact sum_coordDataSign_eq_pow (n := 2 * m + 1) m

lemma sum_oddTail_eq_ordinary_pair_pow {m : ℕ} :
    ∑ RC : OddZeroHeadC (2 * m + 1), ∑ RB : OddZeroHeadB (2 * m + 1), oddTailSign RB RC =
      (ordinaryPairValue (2 * m + 1)) ^ m := by
  rw [sum_oddTail_eq_sum_woddQpair, sum_woddQpair_eq_ordinary_pair_pow]

lemma sum_oddTail_eq_closed_form {m : ℕ} :
    ∑ RC : OddZeroHeadC (2 * m + 1), ∑ RB : OddZeroHeadB (2 * m + 1), oddTailSign RB RC =
      (2 : ℤ) ^ (ordinaryPairExponent (2 * m + 1) * m) := by
  rw [sum_oddTail_eq_ordinary_pair_pow, ordinaryPairValue_eq_closed_form, pow_mul]

lemma sum_survivingBC_eq_visible_mul_closed_form {m : ℕ} :
    ∑ bc : SurvivingBC (2 * m + 1), bitSign (Qraw bc.1.1 bc.1.2) =
      (∑ bc : OddVisibleData (2 * m + 1), oddVisibleSign bc) *
        (2 : ℤ) ^ (ordinaryPairExponent (2 * m + 1) * m) := by
  have hodd : Odd (2 * m + 1) := by
    refine ⟨m, by omega⟩
  rw [sum_survivingBC_eq_visible_mul_tail (n := 2 * m + 1) hodd]
  rw [sum_oddTail_eq_closed_form]

lemma sum_survivingBC_eq_hspace_mul_closed_form {m : ℕ} :
    ∑ bc : SurvivingBC (2 * m + 1), bitSign (Qraw bc.1.1 bc.1.2) =
      ((2 : ℤ) ^ ((2 * m + 1) ^ 2 + (2 * m + 1) ^ 2) *
          ∑ h : HSpace (n := 2 * m + 1), oddHSign h) *
        (2 : ℤ) ^ (ordinaryPairExponent (2 * m + 1) * m) := by
  have hodd : Odd (2 * m + 1) := by
    refine ⟨m, by omega⟩
  rw [sum_survivingBC_eq_visible_mul_closed_form]
  rw [sum_oddVisible_eq_hspace_sum (n := 2 * m + 1) hodd]

lemma sum_oddVisible_eq_supportSubsets_sum {n : ℕ} [NeZero n] (hn : Odd n) :
    ∑ bc : OddVisibleData n, oddVisibleSign bc =
      (2 : ℤ) ^ (n ^ 2 + n ^ 2) *
        ∑ S : Finset (OddRectIndex n), oddHSign ((oddRectSupportEquiv (n := n)).symm S) := by
  rw [sum_oddVisible_eq_hspace_sum (n := n) hn, sum_oddHSign_eq_sum_supportSubsets]

theorem Delta16_odd_factorized (m : ℕ) :
    Delta16 (2 * m + 1) =
      (∑ bc : OddVisibleData (2 * m + 1), oddVisibleSign bc) *
        (2 : ℤ) ^ ((2 * m + 1) ^ 4 + ordinaryPairExponent (2 * m + 1) * m) := by
  rw [delta_after_A (n := 2 * m + 1)]
  rw [sum_survivingBC_eq_visible_mul_closed_form (m := m)]
  calc
    (2 : ℤ) ^ ((2 * m + 1) ^ 4) *
        ((∑ bc : OddVisibleData (2 * m + 1), oddVisibleSign bc) *
          (2 : ℤ) ^ (ordinaryPairExponent (2 * m + 1) * m))
      =
        (∑ bc : OddVisibleData (2 * m + 1), oddVisibleSign bc) *
          ((2 : ℤ) ^ ((2 * m + 1) ^ 4) *
            (2 : ℤ) ^ (ordinaryPairExponent (2 * m + 1) * m)) := by
              ac_rfl
    _ =
        (∑ bc : OddVisibleData (2 * m + 1), oddVisibleSign bc) *
          (2 : ℤ) ^ (((2 * m + 1) ^ 4) + ordinaryPairExponent (2 * m + 1) * m) := by
            rw [← pow_add]

theorem Delta16_odd_hspace_factorized (m : ℕ) :
    Delta16 (2 * m + 1) =
      ((2 : ℤ) ^ ((2 * m + 1) ^ 2 + (2 * m + 1) ^ 2) *
          ∑ h : HSpace (n := 2 * m + 1), oddHSign h) *
        (2 : ℤ) ^ ((2 * m + 1) ^ 4 + ordinaryPairExponent (2 * m + 1) * m) := by
  rw [delta_after_A (n := 2 * m + 1)]
  rw [sum_survivingBC_eq_hspace_mul_closed_form (m := m)]
  calc
    (2 : ℤ) ^ ((2 * m + 1) ^ 4) *
        (((2 : ℤ) ^ ((2 * m + 1) ^ 2 + (2 * m + 1) ^ 2) *
            ∑ h : HSpace (n := 2 * m + 1), oddHSign h) *
          (2 : ℤ) ^ (ordinaryPairExponent (2 * m + 1) * m))
      =
        ((2 : ℤ) ^ ((2 * m + 1) ^ 2 + (2 * m + 1) ^ 2) *
            ∑ h : HSpace (n := 2 * m + 1), oddHSign h) *
          ((2 : ℤ) ^ ((2 * m + 1) ^ 4) *
            (2 : ℤ) ^ (ordinaryPairExponent (2 * m + 1) * m)) := by
              ac_rfl
    _ =
        ((2 : ℤ) ^ ((2 * m + 1) ^ 2 + (2 * m + 1) ^ 2) *
            ∑ h : HSpace (n := 2 * m + 1), oddHSign h) *
          (2 : ℤ) ^ (((2 * m + 1) ^ 4) + ordinaryPairExponent (2 * m + 1) * m) := by
            rw [← pow_add]

theorem Delta16_odd_support_factorized (m : ℕ) :
    Delta16 (2 * m + 1) =
      ((2 : ℤ) ^ ((2 * m + 1) ^ 2 + (2 * m + 1) ^ 2) *
          ∑ S : Finset (OddRectIndex (2 * m + 1)),
            oddHSign ((oddRectSupportEquiv (n := 2 * m + 1)).symm S)) *
        (2 : ℤ) ^ ((2 * m + 1) ^ 4 + ordinaryPairExponent (2 * m + 1) * m) := by
  rw [Delta16_odd_hspace_factorized (m := m), sum_oddHSign_eq_sum_supportSubsets (n := 2 * m + 1)]

end No16
