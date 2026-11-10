import Core4loop.TriangleLeaf.ProfileKernelBase
import Core4loop.TriangleLeaf.VisibleCanonicalBase

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def leafBVisCanonicalFiberEquivKer
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d) :
    LeafBVisFiber (n := n) (a := a) (c := c) (d := d) V
      ≃
    LinearMap.ker (leafBVisMap (n := n) (a := a) (c := c) (d := d)) where
  toFun X :=
    ⟨X.1 - leafBVisCanonicalBase
        (n := n) (a := a) (c := c) (d := d) hd V, by
      rw [LinearMap.mem_ker]
      rw [map_sub, X.2,
        leafBVisCanonicalBase_spec (n := n) (a := a) (c := c) (d := d) hd V]
      simp⟩
  invFun K :=
    ⟨K.1 + leafBVisCanonicalBase
        (n := n) (a := a) (c := c) (d := d) hd V, by
      rw [map_add, LinearMap.mem_ker.mp K.2,
        leafBVisCanonicalBase_spec (n := n) (a := a) (c := c) (d := d) hd V]
      simp⟩
  left_inv X := by
    ext p sy z w
    simp
  right_inv K := by
    ext p sy z w
    simp

noncomputable def leafCVisCanonicalFiberEquivKer
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d) :
    LeafCVisFiber (n := n) (a := a) (b := b) (d := d) V
      ≃
    LinearMap.ker (leafCVisMap (n := n) (a := a) (b := b) (d := d)) where
  toFun X :=
    ⟨X.1 - leafCVisCanonicalBase
        (n := n) (a := a) (b := b) (d := d) hd V, by
      rw [LinearMap.mem_ker]
      rw [map_sub, X.2,
        leafCVisCanonicalBase_spec (n := n) (a := a) (b := b) (d := d) hd V]
      simp⟩
  invFun K :=
    ⟨K.1 + leafCVisCanonicalBase
        (n := n) (a := a) (b := b) (d := d) hd V, by
      rw [map_add, LinearMap.mem_ker.mp K.2,
        leafCVisCanonicalBase_spec (n := n) (a := a) (b := b) (d := d) hd V]
      simp⟩
  left_inv X := by
    ext p y sz w
    simp
  right_inv K := by
    ext p y sz w
    simp

noncomputable def leafBVisCanonicalFiberEquivProfileKernelCoord
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d) :
    LeafBVisFiber (n := n) (a := a) (c := c) (d := d) V
      ≃
    (I n → ZVec n c → LeafProfileKernel n a d) :=
  (leafBVisCanonicalFiberEquivKer
    (n := n) (a := a) (c := c) (d := d) hd V).trans
    (leafBVisKernelEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d))

noncomputable def leafCVisCanonicalFiberEquivProfileKernelCoord
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d) :
    LeafCVisFiber (n := n) (a := a) (b := b) (d := d) V
      ≃
    (YVec n b → I n → LeafProfileKernel n a d) :=
  (leafCVisCanonicalFiberEquivKer
    (n := n) (a := a) (b := b) (d := d) hd V).trans
    (leafCVisKernelEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d))

theorem leafBVisCanonicalFiberCoord_symm_val
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d) :
    ((leafBVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d) hd V).symm kB).1
      =
      leafBVisKernelOfCoord (n := n) (a := a) (c := c) (d := d) kB
        + leafBVisCanonicalBase (n := n) (a := a) (c := c) (d := d) hd V := by
  rfl

theorem leafCVisCanonicalFiberCoord_symm_val
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    ((leafCVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d) hd V).symm kC).1
      =
      leafCVisKernelOfCoord (n := n) (a := a) (b := b) (d := d) kC
        + leafCVisCanonicalBase (n := n) (a := a) (b := b) (d := d) hd V := by
  rfl

theorem leafBVisMap_canonicalKernelBase
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d) :
    leafBVisMap (n := n) (a := a) (c := c) (d := d)
      (leafBVisKernelOfCoord (n := n) (a := a) (c := c) (d := d) kB
        + leafBVisCanonicalBase (n := n) (a := a) (c := c) (d := d) hd V)
      =
      V := by
  rw [map_add,
    leafBVisMap_leafBVisKernelOfCoord (n := n) (a := a) (c := c) (d := d) kB,
    leafBVisCanonicalBase_spec (n := n) (a := a) (c := c) (d := d) hd V]
  simp

theorem leafCVisMap_canonicalKernelBase
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafCVisMap (n := n) (a := a) (b := b) (d := d)
      (leafCVisKernelOfCoord (n := n) (a := a) (b := b) (d := d) kC
        + leafCVisCanonicalBase (n := n) (a := a) (b := b) (d := d) hd V)
      =
      V := by
  rw [map_add,
    leafCVisMap_leafCVisKernelOfCoord (n := n) (a := a) (b := b) (d := d) kC,
    leafCVisCanonicalBase_spec (n := n) (a := a) (b := b) (d := d) hd V]
  simp

end

end TriangleLeaf
end Core4loop
