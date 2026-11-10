import Core4loop.TriangleLeaf.VisibleMaps

namespace Core4loop
namespace TriangleLeaf

noncomputable def leafVisibleRootMap {n b c d : ℕ} [NeZero n] :
    (LeafBVisible n c d × LeafCVisible n b d) →ₗ[F] LeafVisibleCompat n b c d where
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

theorem leafVisibleRootMap_apply {n b c d : ℕ} [NeZero n]
    (X : LeafBVisible n c d × LeafCVisible n b d)
    (y : YVec n b) (z : ZVec n c) :
    leafVisibleRootMap (n := n) (b := b) (c := c) (d := d) X y z =
      X.1 (vecSum y) z
        + X.1 (vecSum y + 1) z
        + X.2 y (vecSum z)
        + X.2 y (vecSum z + 1) := rfl

theorem triangleLeaf_compatible_iff_visiblePair_mem_ker
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d) (C : CFun4 n a b d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
      + KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d)
      ↔
      (leafBVisMap (n := n) (a := a) (c := c) (d := d) B,
          leafCVisMap (n := n) (a := a) (b := b) (d := d) C)
        ∈ LinearMap.ker (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d)) := by
  rw [triangleLeaf_compatible_iff_leaf_visible_root_zero
    (n := n) (a := a) (b := b) (c := c) (d := d) B C]
  constructor
  · intro h
    rw [LinearMap.mem_ker]
    funext y z
    simpa [leafVisibleRootMap, leafBVisMap_apply, leafCVisMap_apply] using h y z
  · intro h y z
    have hz := congrFun (congrFun (LinearMap.mem_ker.mp h) y) z
    simpa [leafVisibleRootMap, leafBVisMap_apply, leafCVisMap_apply] using hz

end TriangleLeaf
end Core4loop
