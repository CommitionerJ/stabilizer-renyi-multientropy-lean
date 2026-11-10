import Core4loop.TriangleLeaf.ProfileKernelCard

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem leafVisibleBasePair_visMap_eq
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) :
    (leafBVisMap (n := n) (a := a) (c := c) (d := d)
        (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H),
      leafCVisMap (n := n) (a := a) (b := b) (d := d)
        (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))
      =
      H.1 := by
  exact
    Prod.ext
      (leafBVisBase_spec (n := n) (a := a) (c := c) (d := d) H.1.1)
      (leafCVisBase_spec (n := n) (a := a) (b := b) (d := d) H.1.2)

theorem leafVisibleBasePair_mem_ker
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) :
    (leafBVisMap (n := n) (a := a) (c := c) (d := d)
        (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H),
      leafCVisMap (n := n) (a := a) (b := b) (d := d)
        (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))
      ∈
      LinearMap.ker (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d)) := by
  rw [leafVisibleBasePair_visMap_eq (n := n) (a := a) (b := b) (c := c) (d := d) H]
  exact H.2

theorem leafVisibleRootMap_base_eq_zero
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) :
    leafVisibleRootMap (n := n) (b := b) (c := c) (d := d)
      (leafBVisMap (n := n) (a := a) (c := c) (d := d)
          (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H),
        leafCVisMap (n := n) (a := a) (b := b) (d := d)
          (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))
      =
      0 := by
  exact LinearMap.mem_ker.mp
    (leafVisibleBasePair_mem_ker
      (n := n) (a := a) (b := b) (c := c) (d := d) H)

theorem leafVisibleBase_compatible
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
      +
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [triangleLeaf_compatible_iff_visiblePair_mem_ker]
  exact leafVisibleBasePair_mem_ker
    (n := n) (a := a) (b := b) (c := c) (d := d) H

theorem leafVisibleKernelBaseB_visMap_eq
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d) :
    leafBVisMap (n := n) (a := a) (c := c) (d := d)
      (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB
        + leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
      =
      H.1.1 := by
  rw [map_add]
  rw [leafBVisMap_leafBVisKernelOfCoord
    (n := n) (a := a) (c := c) (d := d) kB]
  rw [leafBVisBase_spec (n := n) (a := a) (c := c) (d := d) H.1.1]
  simp

theorem leafVisibleKernelBaseC_visMap_eq
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafCVisMap (n := n) (a := a) (b := b) (d := d)
      (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC
        + leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
      =
      H.1.2 := by
  rw [map_add]
  rw [leafCVisMap_leafCVisKernelOfCoord
    (n := n) (a := a) (b := b) (d := d) kC]
  rw [leafCVisBase_spec (n := n) (a := a) (b := b) (d := d) H.1.2]
  simp

theorem leafVisibleKernelBasePair_visMap_eq
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    (leafBVisMap (n := n) (a := a) (c := c) (d := d)
        (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB
          + leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H),
      leafCVisMap (n := n) (a := a) (b := b) (d := d)
        (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC
          + leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))
      =
      H.1 := by
  exact
    Prod.ext
      (leafVisibleKernelBaseB_visMap_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) H kB)
      (leafVisibleKernelBaseC_visMap_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) H kC)

theorem leafVisibleKernelBasePair_mem_ker
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    (leafBVisMap (n := n) (a := a) (c := c) (d := d)
        (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB
          + leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H),
      leafCVisMap (n := n) (a := a) (b := b) (d := d)
        (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC
          + leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H))
      ∈
      LinearMap.ker (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d)) := by
  rw [leafVisibleKernelBasePair_visMap_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC]
  exact H.2

theorem leafVisibleKernelBase_compatible
    {n a b c d : ℕ} [NeZero n]
    (H : LeafVisibleKernel n b c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBKernelPart (n := n) (a := a) (c := c) (d := d) kB
          + leafVisibleBBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
      +
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleCKernelPart (n := n) (a := a) (b := b) (d := d) kC
          + leafVisibleCBase (n := n) (a := a) (b := b) (c := c) (d := d) H)
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [triangleLeaf_compatible_iff_visiblePair_mem_ker]
  exact leafVisibleKernelBasePair_mem_ker
    (n := n) (a := a) (b := b) (c := c) (d := d) H kB kC

end

end TriangleLeaf
end Core4loop
