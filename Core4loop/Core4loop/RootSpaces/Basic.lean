import Core4loop.ZeroSumSpaces.Cube

namespace Core4loop

abbrev YCoeff (n c d : ℕ) [NeZero n] :=
  ZVec n c → WVec n d → ZeroSumProfile n

abbrev ZCoeff (n b d : ℕ) [NeZero n] :=
  YVec n b → WVec n d → ZeroSumProfile n

abbrev WCoeff (n b c : ℕ) [NeZero n] :=
  YVec n b → ZVec n c → ZeroSumProfile n

noncomputable def YDiffEmbed {n b c d : ℕ} [NeZero n] :
    YCoeff n c d →ₗ[F] RootTarget n b c d where
  toFun U := fun y z w => (U z w).1 (vecSum y)
  map_add' U V := by
    funext y z w
    rfl
  map_smul' r U := by
    funext y z w
    rfl

noncomputable def ZDiffEmbed {n b c d : ℕ} [NeZero n] :
    ZCoeff n b d →ₗ[F] RootTarget n b c d where
  toFun V := fun y z w => (V y w).1 (vecSum z)
  map_add' U V := by
    funext y z w
    rfl
  map_smul' r U := by
    funext y z w
    rfl

noncomputable def WDiffEmbed {n b c d : ℕ} [NeZero n] :
    WCoeff n b c →ₗ[F] RootTarget n b c d where
  toFun R := fun y z w => (R y z).1 (vecSum w)
  map_add' U V := by
    funext y z w
    rfl
  map_smul' r U := by
    funext y z w
    rfl

noncomputable def YDiffSpace {n b c d : ℕ} [NeZero n] :
    Submodule F (RootTarget n b c d) :=
  LinearMap.range (YDiffEmbed (n := n) (b := b) (c := c) (d := d))

noncomputable def ZDiffSpace {n b c d : ℕ} [NeZero n] :
    Submodule F (RootTarget n b c d) :=
  LinearMap.range (ZDiffEmbed (n := n) (b := b) (c := c) (d := d))

noncomputable def WDiffSpace {n b c d : ℕ} [NeZero n] :
    Submodule F (RootTarget n b c d) :=
  LinearMap.range (WDiffEmbed (n := n) (b := b) (c := c) (d := d))

theorem YDiffEmbed_injective {n b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Injective (YDiffEmbed (n := n) (b := b) (c := c) (d := d)) := by
  intro U V h
  funext z w
  apply Subtype.ext
  funext s
  rcases vecSum_surjective (n := n) (k := b) hb s with ⟨y, hy⟩
  have hv := congrFun (congrFun (congrFun h y) z) w
  simpa [YDiffEmbed, hy] using hv

theorem ZDiffEmbed_injective {n b c d : ℕ} [NeZero n] (hc : 0 < c) :
    Function.Injective (ZDiffEmbed (n := n) (b := b) (c := c) (d := d)) := by
  intro U V h
  funext y w
  apply Subtype.ext
  funext s
  rcases vecSum_surjective (n := n) (k := c) hc s with ⟨z, hz⟩
  have hv := congrFun (congrFun (congrFun h y) z) w
  simpa [ZDiffEmbed, hz] using hv

theorem WDiffEmbed_injective {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Function.Injective (WDiffEmbed (n := n) (b := b) (c := c) (d := d)) := by
  intro U V h
  funext y z
  apply Subtype.ext
  funext s
  rcases vecSum_surjective (n := n) (k := d) hd s with ⟨w, hw⟩
  have hv := congrFun (congrFun (congrFun h y) z) w
  simpa [WDiffEmbed, hw] using hv

lemma finrank_fun_vec_to_ZeroSumProfile {n k : ℕ} [NeZero n] :
    Module.finrank F (Vec n k → ZeroSumProfile n) = n ^ k * (n - 1) := by
  calc
    Module.finrank F (Vec n k → ZeroSumProfile n)
        = ∑ _ : Vec n k, Module.finrank F (ZeroSumProfile n) := by
            simp [Module.finrank_pi_fintype
              (R := F) (M := fun _ : Vec n k => ZeroSumProfile n)]
    _ = Fintype.card (Vec n k) * (n - 1) := by
            simp [finrank_ZeroSumProfile]
    _ = n ^ k * (n - 1) := by
            rw [card_vec]

lemma finrank_YCoeff {n c d : ℕ} [NeZero n] :
    Module.finrank F (YCoeff n c d) = n ^ (c + d) * (n - 1) := by
  calc
    Module.finrank F (YCoeff n c d)
        = ∑ _ : ZVec n c, Module.finrank F (WVec n d → ZeroSumProfile n) := by
            simp [YCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : ZVec n c => WVec n d → ZeroSumProfile n)]
    _ = Fintype.card (ZVec n c) * (n ^ d * (n - 1)) := by
            simp [finrank_fun_vec_to_ZeroSumProfile]
    _ = n ^ (c + d) * (n - 1) := by
            rw [card_vec, pow_add]
            ring

lemma finrank_ZCoeff {n b d : ℕ} [NeZero n] :
    Module.finrank F (ZCoeff n b d) = n ^ (b + d) * (n - 1) := by
  calc
    Module.finrank F (ZCoeff n b d)
        = ∑ _ : YVec n b, Module.finrank F (WVec n d → ZeroSumProfile n) := by
            simp [ZCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : YVec n b => WVec n d → ZeroSumProfile n)]
    _ = Fintype.card (YVec n b) * (n ^ d * (n - 1)) := by
            simp [finrank_fun_vec_to_ZeroSumProfile]
    _ = n ^ (b + d) * (n - 1) := by
            rw [card_vec, pow_add]
            ring

lemma finrank_WCoeff {n b c : ℕ} [NeZero n] :
    Module.finrank F (WCoeff n b c) = n ^ (b + c) * (n - 1) := by
  calc
    Module.finrank F (WCoeff n b c)
        = ∑ _ : YVec n b, Module.finrank F (ZVec n c → ZeroSumProfile n) := by
            simp [WCoeff, Module.finrank_pi_fintype
              (R := F) (M := fun _ : YVec n b => ZVec n c → ZeroSumProfile n)]
    _ = Fintype.card (YVec n b) * (n ^ c * (n - 1)) := by
            simp [finrank_fun_vec_to_ZeroSumProfile]
    _ = n ^ (b + c) * (n - 1) := by
            rw [card_vec, pow_add]
            ring

theorem finrank_YDiffSpace {n b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Module.finrank F (YDiffSpace (n := n) (b := b) (c := c) (d := d)) =
      (n - 1) * n ^ (c + d) := by
  calc
    Module.finrank F (YDiffSpace (n := n) (b := b) (c := c) (d := d))
        = Module.finrank F (YCoeff n c d) := by
            exact LinearMap.finrank_range_of_inj
              (YDiffEmbed_injective (n := n) (b := b) (c := c) (d := d) hb)
    _ = (n - 1) * n ^ (c + d) := by
            rw [finrank_YCoeff]
            ring

theorem finrank_ZDiffSpace {n b c d : ℕ} [NeZero n] (hc : 0 < c) :
    Module.finrank F (ZDiffSpace (n := n) (b := b) (c := c) (d := d)) =
      (n - 1) * n ^ (b + d) := by
  calc
    Module.finrank F (ZDiffSpace (n := n) (b := b) (c := c) (d := d))
        = Module.finrank F (ZCoeff n b d) := by
            exact LinearMap.finrank_range_of_inj
              (ZDiffEmbed_injective (n := n) (b := b) (c := c) (d := d) hc)
    _ = (n - 1) * n ^ (b + d) := by
            rw [finrank_ZCoeff]
            ring

theorem finrank_WDiffSpace {n b c d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (WDiffSpace (n := n) (b := b) (c := c) (d := d)) =
      (n - 1) * n ^ (b + c) := by
  calc
    Module.finrank F (WDiffSpace (n := n) (b := b) (c := c) (d := d))
        = Module.finrank F (WCoeff n b c) := by
            exact LinearMap.finrank_range_of_inj
              (WDiffEmbed_injective (n := n) (b := b) (c := c) (d := d) hd)
    _ = (n - 1) * n ^ (b + c) := by
            rw [finrank_WCoeff]
            ring

end Core4loop
