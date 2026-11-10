import Core4loop.ZeroSumSpaces.Profile

open scoped BigOperators

namespace Core4loop

noncomputable abbrev LineZeroSum (n : ℕ) [NeZero n] := ZeroSumProfileM n (Profile n)

lemma finrank_Profile {n : ℕ} [NeZero n] :
    Module.finrank F (Profile n) = n :=
  finrank_profile

theorem finrank_LineZeroSum {n : ℕ} [NeZero n] :
    Module.finrank F (LineZeroSum n) = (n - 1) * n := by
  rw [finrank_ZeroSumProfileM, finrank_Profile]

abbrev BDiagCoeff (n a d : ℕ) [NeZero n] :=
  PVec n a → WVec n d → LineZeroSum n

noncomputable def BDiagEmbed {n a b d : ℕ} [NeZero n] :
    BDiagCoeff n a d →ₗ[F] CFun4 n a b d where
  toFun U := fun p y sz w => (U p w).1 (vecSum y) (vecSum y + sz)
  map_add' U V := by
    funext p y sz w
    rfl
  map_smul' r U := by
    funext p y sz w
    rfl

noncomputable def BDiagSpace {n a b d : ℕ} [NeZero n] :
    Submodule F (CFun4 n a b d) :=
  LinearMap.range (BDiagEmbed (n := n) (a := a) (b := b) (d := d))

theorem BDiagEmbed_injective {n a b d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Injective (BDiagEmbed (n := n) (a := a) (b := b) (d := d)) := by
  intro U V h
  funext p w
  apply Subtype.ext
  funext sy t
  rcases vecSum_surjective (n := n) (k := b) hb sy with ⟨y, hy⟩
  let sz : I n := t - sy
  have hcoord :
      vecSum y + sz = t := by
    simp [sz, hy]
  have hv := congrFun (congrFun (congrFun (congrFun h p) y) sz) w
  rw [← hcoord]
  simpa [BDiagEmbed, hy] using hv

lemma finrank_BDiagCoeff {n a d : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (BDiagCoeff n a d) = (n - 1) * n ^ (a + d) := by
  calc
    Module.finrank F (BDiagCoeff n a d)
        = ∑ _ : PVec n a, Module.finrank F (WVec n d → LineZeroSum n) := by
            simp [BDiagCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : PVec n a => WVec n d → LineZeroSum n)]
    _ = Fintype.card (PVec n a) * (n ^ d * ((n - 1) * n)) := by
            simp [Module.finrank_pi_fintype
              (R := F) (M := fun _ : WVec n d => LineZeroSum n),
              finrank_LineZeroSum]
    _ = n ^ (a - 1) * (n ^ d * ((n - 1) * n)) := by
            rw [card_vec]
    _ = (n - 1) * n ^ (a + d) := by
            calc
              n ^ (a - 1) * (n ^ d * ((n - 1) * n))
                  = (n - 1) * (n ^ (a - 1) * n ^ d * n) := by ring
              _ = (n - 1) * (n ^ ((a - 1) + d) * n) := by
                    rw [← pow_add]
              _ = (n - 1) * n ^ ((a - 1) + d + 1) := by
                    rw [pow_succ]
              _ = (n - 1) * n ^ (a + d) := by
                    congr 1
                    congr 1
                    omega

theorem finrank_BDiagSpace {n a b d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) :
    Module.finrank F (BDiagSpace (n := n) (a := a) (b := b) (d := d)) =
      (n - 1) * n ^ (a + d) := by
  calc
    Module.finrank F (BDiagSpace (n := n) (a := a) (b := b) (d := d))
        = Module.finrank F (BDiagCoeff n a d) := by
            exact LinearMap.finrank_range_of_inj
              (BDiagEmbed_injective (n := n) (a := a) (b := b) (d := d) hb)
    _ = (n - 1) * n ^ (a + d) := finrank_BDiagCoeff ha

noncomputable def BDiagOfB {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) : BDiagCoeff n a d :=
  fun p w =>
    ⟨cycDiff (n := n) (Profile n)
      (fun sy : I n => fun t : I n =>
        ∑ z : ZVec n c, if vecSum z = t - sy then B p sy z w else 0),
      cycDiff_mem_ZeroSumProfileM
        (fun sy : I n => fun t : I n =>
          ∑ z : ZVec n c, if vecSum z = t - sy then B p sy z w else 0)⟩

noncomputable def BDiagOfBLinear {n a c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F] BDiagCoeff n a d where
  toFun B := BDiagOfB (n := n) (a := a) (c := c) (d := d) B
  map_add' B B' := by
    funext p w
    apply Subtype.ext
    change
      cycDiff (n := n) (Profile n)
          (fun sy : I n => fun t : I n =>
            ∑ z : ZVec n c, if vecSum z = t - sy then (B + B') p sy z w else 0) =
        cycDiff (n := n) (Profile n)
            (fun sy : I n => fun t : I n =>
              ∑ z : ZVec n c, if vecSum z = t - sy then B p sy z w else 0) +
          cycDiff (n := n) (Profile n)
            (fun sy : I n => fun t : I n =>
              ∑ z : ZVec n c, if vecSum z = t - sy then B' p sy z w else 0)
    rw [← (cycDiff (n := n) (Profile n)).map_add]
    congr
    funext sy t
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = t - sy <;> simp [hz]
  map_smul' r B := by
    funext p w
    apply Subtype.ext
    change
      cycDiff (n := n) (Profile n)
          (fun sy : I n => fun t : I n =>
            ∑ z : ZVec n c, if vecSum z = t - sy then (r • B) p sy z w else 0) =
        r • cycDiff (n := n) (Profile n)
          (fun sy : I n => fun t : I n =>
            ∑ z : ZVec n c, if vecSum z = t - sy then B p sy z w else 0)
    rw [← (cycDiff (n := n) (Profile n)).map_smul]
    congr
    funext sy t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = t - sy <;> simp [hz, mul_zero]

@[simp]
theorem BDiagOfBLinear_apply {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) :
    BDiagOfBLinear (n := n) (a := a) (c := c) (d := d) B =
      BDiagOfB (n := n) (a := a) (c := c) (d := d) B :=
  rfl

end Core4loop
