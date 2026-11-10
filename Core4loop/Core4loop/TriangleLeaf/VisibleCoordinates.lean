import Core4loop.TriangleLeaf.ProfileFibers
import Core4loop.TriangleLeaf.PassiveComplement

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafScalarBVisible (n c : ℕ) [NeZero n] :=
  I n → ZVec n c → F

abbrev LeafScalarCVisible (n b : ℕ) [NeZero n] :=
  YVec n b → I n → F

abbrev LeafScalarVisiblePair (n b c : ℕ) [NeZero n] :=
  LeafScalarBVisible n c × LeafScalarCVisible n b

noncomputable def leafScalarVisibleRootMap {n b c : ℕ} [NeZero n] :
    LeafScalarVisiblePair n b c →ₗ[F] (YVec n b → ZVec n c → F) where
  toFun X := fun y z =>
    X.1 (vecSum y) z
      + X.1 (vecSum y + 1) z
      + X.2 y (vecSum z)
      + X.2 y (vecSum z + 1)
  map_add' X Y := by
    funext y z
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    abel
  map_smul' r X := by
    funext y z
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    module

theorem leafScalarVisibleRootMap_apply {n b c : ℕ} [NeZero n]
    (X : LeafScalarVisiblePair n b c) (y : YVec n b) (z : ZVec n c) :
    leafScalarVisibleRootMap (n := n) (b := b) (c := c) X y z =
      X.1 (vecSum y) z
        + X.1 (vecSum y + 1) z
        + X.2 y (vecSum z)
        + X.2 y (vecSum z + 1) := rfl

abbrev LeafScalarVisibleKernel (n b c : ℕ) [NeZero n] :=
  LinearMap.ker (leafScalarVisibleRootMap (n := n) (b := b) (c := c))

abbrev LeafVisiblePairCoord (n b c d : ℕ) [NeZero n] (hd : 0 < d) :=
  PassiveVisibleIndex n d hd → LeafScalarVisiblePair n b c

noncomputable def leafVisiblePairEquivCoord {n b c d : ℕ} [NeZero n]
    (hd : 0 < d) :
    (LeafBVisible n c d × LeafCVisible n b d) ≃ₗ[F]
      LeafVisiblePairCoord n b c d hd where
  toFun X := fun ω =>
    (fun sy z =>
      passiveQuotEquivVisibleIndex (n := n) (d := d) hd (X.1 sy z) ω,
     fun y sz =>
      passiveQuotEquivVisibleIndex (n := n) (d := d) hd (X.2 y sz) ω)
  invFun G :=
    (fun sy z =>
      (passiveQuotEquivVisibleIndex (n := n) (d := d) hd).symm
        (fun ω => (G ω).1 sy z),
     fun y sz =>
      (passiveQuotEquivVisibleIndex (n := n) (d := d) hd).symm
        (fun ω => (G ω).2 y sz))
  left_inv X := by
    ext <;> simp
  right_inv G := by
    funext ω
    ext <;> simp
  map_add' X Y := by
    funext ω
    ext <;> simp
  map_smul' r X := by
    funext ω
    ext <;> simp

theorem leafVisiblePairEquivCoord_root_apply
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : LeafBVisible n c d × LeafCVisible n b d)
    (ω : PassiveVisibleIndex n d hd) (y : YVec n b) (z : ZVec n c) :
    leafScalarVisibleRootMap (n := n) (b := b) (c := c)
        ((leafVisiblePairEquivCoord (n := n) (b := b) (c := c) (d := d) hd X) ω)
        y z =
      passiveQuotEquivVisibleIndex (n := n) (d := d) hd
        (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d) X y z) ω := by
  simp [leafVisiblePairEquivCoord, leafScalarVisibleRootMap_apply, leafVisibleRootMap_apply]

theorem leafVisiblePair_mem_ker_iff_coord
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (X : LeafBVisible n c d × LeafCVisible n b d) :
    X ∈ LinearMap.ker (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d))
      ↔
      ∀ ω : PassiveVisibleIndex n d hd,
        (leafVisiblePairEquivCoord (n := n) (b := b) (c := c) (d := d) hd X) ω
          ∈ LeafScalarVisibleKernel n b c := by
  constructor
  · intro hX ω
    rw [LinearMap.mem_ker]
    funext y z
    rw [leafVisiblePairEquivCoord_root_apply
      (n := n) (b := b) (c := c) (d := d) hd X ω y z]
    rw [LinearMap.mem_ker] at hX
    simp [hX]
  · intro hX
    rw [LinearMap.mem_ker]
    funext y z
    let e := passiveQuotEquivVisibleIndex (n := n) (d := d) hd
    apply e.injective
    funext ω
    have hω := congrFun (congrFun (LinearMap.mem_ker.mp (hX ω)) y) z
    rw [leafVisiblePairEquivCoord_root_apply
      (n := n) (b := b) (c := c) (d := d) hd X ω y z] at hω
    simpa [e] using hω

noncomputable def leafVisibleKernelEquivCoord {n b c d : ℕ} [NeZero n]
    (hd : 0 < d) :
    LeafVisibleKernel n b c d ≃
      (PassiveVisibleIndex n d hd → LeafScalarVisibleKernel n b c) where
  toFun H := fun ω =>
    ⟨(leafVisiblePairEquivCoord (n := n) (b := b) (c := c) (d := d) hd H.1) ω,
      (leafVisiblePair_mem_ker_iff_coord
        (n := n) (b := b) (c := c) (d := d) hd H.1).1 H.2 ω⟩
  invFun G :=
    ⟨(leafVisiblePairEquivCoord (n := n) (b := b) (c := c) (d := d) hd).symm
        (fun ω => (G ω).1),
      by
        apply
          (leafVisiblePair_mem_ker_iff_coord
            (n := n) (b := b) (c := c) (d := d) hd
            ((leafVisiblePairEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd).symm
              (fun ω => (G ω).1))).2
        intro ω
        have hpoint :
            (leafVisiblePairEquivCoord (n := n) (b := b) (c := c) (d := d) hd
              ((leafVisiblePairEquivCoord
                (n := n) (b := b) (c := c) (d := d) hd).symm
                (fun ω => (G ω).1))) ω = (G ω).1 := by
          exact congrFun
            ((leafVisiblePairEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd).right_inv
              (fun ω => (G ω).1)) ω
        rw [hpoint]
        exact (G ω).2⟩
  left_inv H := by
    apply Subtype.ext
    exact
      (leafVisiblePairEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd).left_inv H.1
  right_inv G := by
    funext ω
    apply Subtype.ext
    exact congrFun
      ((leafVisiblePairEquivCoord
        (n := n) (b := b) (c := c) (d := d) hd).right_inv
        (fun ω => (G ω).1)) ω

end

end TriangleLeaf
end Core4loop
