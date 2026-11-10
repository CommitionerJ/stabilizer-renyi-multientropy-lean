import Core4loop.TriangleLeaf.ProfilePair
import Core4loop.NormalFormDims

namespace Core4loop
namespace TriangleLeaf

abbrev LeafBVisible (n c d : ℕ) [NeZero n] :=
  I n → ZVec n c → PassiveQuot n d

abbrev LeafCVisible (n b d : ℕ) [NeZero n] :=
  YVec n b → I n → PassiveQuot n d

noncomputable def leafBVisMap {n a c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F] LeafBVisible n c d where
  toFun B := fun sy z => leafBVisQuot B sy z
  map_add' B B' := by
    funext sy z
    change
      leafSigmaQuot (n := n) (a := a) (d := d)
        (leafBProfile B sy z + leafBProfile B' sy z)
        =
      leafSigmaQuot (n := n) (a := a) (d := d) (leafBProfile B sy z)
        + leafSigmaQuot (n := n) (a := a) (d := d) (leafBProfile B' sy z)
    rw [map_add]
  map_smul' r B := by
    funext sy z
    change
      leafSigmaQuot (n := n) (a := a) (d := d)
        (r • leafBProfile B sy z)
        =
      r • leafSigmaQuot (n := n) (a := a) (d := d) (leafBProfile B sy z)
    rw [map_smul]

noncomputable def leafCVisMap {n a b d : ℕ} [NeZero n] :
    CFun4 n a b d →ₗ[F] LeafCVisible n b d where
  toFun C := fun y sz => leafCVisQuot C y sz
  map_add' C C' := by
    funext y sz
    change
      leafSigmaQuot (n := n) (a := a) (d := d)
        (leafCProfile C y sz + leafCProfile C' y sz)
        =
      leafSigmaQuot (n := n) (a := a) (d := d) (leafCProfile C y sz)
        + leafSigmaQuot (n := n) (a := a) (d := d) (leafCProfile C' y sz)
    rw [map_add]
  map_smul' r C := by
    funext y sz
    change
      leafSigmaQuot (n := n) (a := a) (d := d)
        (r • leafCProfile C y sz)
        =
      r • leafSigmaQuot (n := n) (a := a) (d := d) (leafCProfile C y sz)
    rw [map_smul]

theorem leafBVisMap_apply {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (sy : I n) (z : ZVec n c) :
    leafBVisMap (n := n) (a := a) (c := c) (d := d) B sy z =
      leafBVisQuot B sy z := rfl

theorem leafCVisMap_apply {n a b d : ℕ} [NeZero n]
    (C : CFun4 n a b d) (y : YVec n b) (sz : I n) :
    leafCVisMap (n := n) (a := a) (b := b) (d := d) C y sz =
      leafCVisQuot C y sz := rfl

theorem leafBVisMap_surjective {n a c d : ℕ} [NeZero n] :
    Function.Surjective (leafBVisMap (n := n) (a := a) (c := c) (d := d)) := by
  classical
  intro V
  choose φ hφ using fun sy z =>
    leafSigmaQuot_surjective (n := n) (a := a) (d := d) (V sy z)
  refine ⟨fun p sy z w => φ sy z p w, ?_⟩
  funext sy z
  simpa [leafBVisMap, leafBVisQuot, leafBProfile] using hφ sy z

theorem leafCVisMap_surjective {n a b d : ℕ} [NeZero n] :
    Function.Surjective (leafCVisMap (n := n) (a := a) (b := b) (d := d)) := by
  classical
  intro V
  choose φ hφ using fun y sz =>
    leafSigmaQuot_surjective (n := n) (a := a) (d := d) (V y sz)
  refine ⟨fun p y sz w => φ y sz p w, ?_⟩
  funext y sz
  simpa [leafCVisMap, leafCVisQuot, leafCProfile] using hφ y sz

theorem finrank_LeafBVisible {n c d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (LeafBVisible n c d) =
      n ^ (c + 1) * (n ^ d - (n - 1)) := by
  have hinner :
      Module.finrank F (ZVec n c → PassiveQuot n d) =
        n ^ c * (n ^ d - (n - 1)) := by
    calc
      Module.finrank F (ZVec n c → PassiveQuot n d)
          = ∑ _ : ZVec n c, Module.finrank F (PassiveQuot n d) := by
              simp [Module.finrank_pi_fintype
                (R := F) (M := fun _ : ZVec n c => PassiveQuot n d)]
      _ = Fintype.card (ZVec n c) * (n ^ d - (n - 1)) := by
              rw [finrank_PassiveQuot (n := n) (d := d) hd]
              simp
      _ = n ^ c * (n ^ d - (n - 1)) := by
              rw [card_vec]
  calc
    Module.finrank F (LeafBVisible n c d)
        = ∑ _ : I n, Module.finrank F (ZVec n c → PassiveQuot n d) := by
            simp [LeafBVisible, Module.finrank_pi_fintype
              (R := F) (M := fun _ : I n => ZVec n c → PassiveQuot n d)]
    _ = n * (n ^ c * (n ^ d - (n - 1))) := by
            rw [hinner]
            simp [I, ZMod.card]
    _ = n ^ (c + 1) * (n ^ d - (n - 1)) := by
            rw [pow_succ']
            ring

theorem finrank_LeafCVisible {n b d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F (LeafCVisible n b d) =
      n ^ (b + 1) * (n ^ d - (n - 1)) := by
  have hinner :
      Module.finrank F (I n → PassiveQuot n d) =
        n * (n ^ d - (n - 1)) := by
    calc
      Module.finrank F (I n → PassiveQuot n d)
          = ∑ _ : I n, Module.finrank F (PassiveQuot n d) := by
              simp [Module.finrank_pi_fintype
                (R := F) (M := fun _ : I n => PassiveQuot n d)]
      _ = Fintype.card (I n) * (n ^ d - (n - 1)) := by
              rw [finrank_PassiveQuot (n := n) (d := d) hd]
              simp
      _ = n * (n ^ d - (n - 1)) := by
              simp [I, ZMod.card]
  calc
    Module.finrank F (LeafCVisible n b d)
        = ∑ _ : YVec n b, Module.finrank F (I n → PassiveQuot n d) := by
            simp [LeafCVisible, Module.finrank_pi_fintype
              (R := F) (M := fun _ : YVec n b => I n → PassiveQuot n d)]
    _ = n ^ b * (n * (n ^ d - (n - 1))) := by
            rw [hinner]
            simp
    _ = n ^ (b + 1) * (n ^ d - (n - 1)) := by
            rw [pow_succ']
            ring

theorem finrank_ker_leafBVisMap_add {n a c d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d)))
      + n ^ (c + 1) * (n ^ d - (n - 1))
      =
      n ^ (a + c + d) := by
  let L := leafBVisMap (n := n) (a := a) (c := c) (d := d)
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  have hsurj : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr (leafBVisMap_surjective (n := n) (a := a) (c := c) (d := d))
  rw [hsurj, finrank_top, finrank_LeafBVisible (n := n) (c := c) (d := d) hd,
    finrank_BFun4 (n := n) (a := a) (c := c) (d := d) ha] at hnull
  simpa [L, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnull

theorem finrank_ker_leafCVisMap_add {n a b d : ℕ} [NeZero n]
    (ha : 0 < a) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)))
      + n ^ (b + 1) * (n ^ d - (n - 1))
      =
      n ^ (a + b + d) := by
  let L := leafCVisMap (n := n) (a := a) (b := b) (d := d)
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  have hsurj : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr (leafCVisMap_surjective (n := n) (a := a) (b := b) (d := d))
  rw [hsurj, finrank_top, finrank_LeafCVisible (n := n) (b := b) (d := d) hd,
    finrank_CFun4 (n := n) (a := a) (b := b) (d := d) ha] at hnull
  simpa [L, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnull

end TriangleLeaf
end Core4loop
