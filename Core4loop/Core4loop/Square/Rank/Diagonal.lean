import Core4loop.BDiag

open scoped BigOperators

namespace Core4loop

abbrev WDiagCoeff (n a b : ℕ) [NeZero n] :=
  PVec n a → YVec n b → LineZeroSum n

noncomputable def WDiagEmbed {n a b d : ℕ} [NeZero n] :
    WDiagCoeff n a b →ₗ[F] CFun4 n a b d where
  toFun U := fun p y sz w => (U p y).1 (vecSum w) (vecSum w + sz)
  map_add' U V := by
    funext p y sz w
    rfl
  map_smul' r U := by
    funext p y sz w
    rfl

noncomputable def WDiagSpace {n a b d : ℕ} [NeZero n] :
    Submodule F (CFun4 n a b d) :=
  LinearMap.range (WDiagEmbed (n := n) (a := a) (b := b) (d := d))

theorem WDiagEmbed_injective {n a b d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Injective (WDiagEmbed (n := n) (a := a) (b := b) (d := d)) := by
  intro U V h
  funext p y
  apply Subtype.ext
  funext sw t
  rcases vecSum_surjective (n := n) (k := d) hd sw with ⟨w, hw⟩
  let sz : I n := t - sw
  have hcoord :
      vecSum w + sz = t := by
    simp [sz, hw]
  have hv := congrFun (congrFun (congrFun (congrFun h p) y) sz) w
  rw [← hcoord]
  simpa [WDiagEmbed, hw] using hv

lemma finrank_WDiagCoeff {n a b : ℕ} [NeZero n] (ha : 0 < a) :
    Module.finrank F (WDiagCoeff n a b) = (n - 1) * n ^ (a + b) := by
  calc
    Module.finrank F (WDiagCoeff n a b)
        = ∑ _ : PVec n a, Module.finrank F (YVec n b → LineZeroSum n) := by
            simp [WDiagCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : PVec n a => YVec n b → LineZeroSum n)]
    _ = Fintype.card (PVec n a) * (n ^ b * ((n - 1) * n)) := by
            simp [Module.finrank_pi_fintype
              (R := F) (M := fun _ : YVec n b => LineZeroSum n),
              finrank_LineZeroSum]
    _ = n ^ (a - 1) * (n ^ b * ((n - 1) * n)) := by
            rw [card_vec]
    _ = (n - 1) * n ^ (a + b) := by
            calc
              n ^ (a - 1) * (n ^ b * ((n - 1) * n))
                  = (n - 1) * (n ^ (a - 1) * n ^ b * n) := by ring
              _ = (n - 1) * (n ^ ((a - 1) + b) * n) := by
                    rw [← pow_add]
              _ = (n - 1) * n ^ ((a - 1) + b + 1) := by
                    rw [pow_succ]
              _ = (n - 1) * n ^ (a + b) := by
                    congr 1
                    congr 1
                    omega

theorem finrank_WDiagSpace {n a b d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    Module.finrank F (WDiagSpace (n := n) (a := a) (b := b) (d := d)) =
      (n - 1) * n ^ (a + b) := by
  calc
    Module.finrank F (WDiagSpace (n := n) (a := a) (b := b) (d := d))
        = Module.finrank F (WDiagCoeff n a b) := by
            exact LinearMap.finrank_range_of_inj
              (WDiagEmbed_injective (n := n) (a := a) (b := b) (d := d) hd)
    _ = (n - 1) * n ^ (a + b) := finrank_WDiagCoeff ha

end Core4loop
