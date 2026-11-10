import Core4loop.TriangleLeaf.ProfileKernelSum

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def leafBVisBase {n a c d : ℕ} [NeZero n]
    (V : LeafBVisible n c d) : BFun4 n a c d :=
  Classical.choose
    (leafBVisMap_surjective (n := n) (a := a) (c := c) (d := d) V)

def leafCVisBase {n a b d : ℕ} [NeZero n]
    (V : LeafCVisible n b d) : CFun4 n a b d :=
  Classical.choose
    (leafCVisMap_surjective (n := n) (a := a) (b := b) (d := d) V)

theorem leafBVisBase_spec {n a c d : ℕ} [NeZero n]
    (V : LeafBVisible n c d) :
    leafBVisMap (n := n) (a := a) (c := c) (d := d)
      (leafBVisBase (n := n) (a := a) (c := c) (d := d) V) = V :=
  Classical.choose_spec
    (leafBVisMap_surjective (n := n) (a := a) (c := c) (d := d) V)

theorem leafCVisBase_spec {n a b d : ℕ} [NeZero n]
    (V : LeafCVisible n b d) :
    leafCVisMap (n := n) (a := a) (b := b) (d := d)
      (leafCVisBase (n := n) (a := a) (b := b) (d := d) V) = V :=
  Classical.choose_spec
    (leafCVisMap_surjective (n := n) (a := a) (b := b) (d := d) V)

def leafBVisKernelOfCoord {n a c d : ℕ} [NeZero n]
    (kB : I n → ZVec n c → LeafProfileKernel n a d) : BFun4 n a c d :=
  ((leafBVisKernelEquivProfileKernelCoord
    (n := n) (a := a) (c := c) (d := d)).symm kB).1

def leafCVisKernelOfCoord {n a b d : ℕ} [NeZero n]
    (kC : YVec n b → I n → LeafProfileKernel n a d) : CFun4 n a b d :=
  ((leafCVisKernelEquivProfileKernelCoord
    (n := n) (a := a) (b := b) (d := d)).symm kC).1

theorem leafBVisMap_leafBVisKernelOfCoord
    {n a c d : ℕ} [NeZero n]
    (kB : I n → ZVec n c → LeafProfileKernel n a d) :
    leafBVisMap (n := n) (a := a) (c := c) (d := d)
      (leafBVisKernelOfCoord (n := n) (a := a) (c := c) (d := d) kB)
      = 0 := by
  exact LinearMap.mem_ker.mp
    ((leafBVisKernelEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d)).symm kB).2

theorem leafCVisMap_leafCVisKernelOfCoord
    {n a b d : ℕ} [NeZero n]
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    leafCVisMap (n := n) (a := a) (b := b) (d := d)
      (leafCVisKernelOfCoord (n := n) (a := a) (b := b) (d := d) kC)
      = 0 := by
  exact LinearMap.mem_ker.mp
    ((leafCVisKernelEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d)).symm kC).2

theorem leafBProfile_leafBVisKernelOfCoord
    {n a c d : ℕ} [NeZero n]
    (kB : I n → ZVec n c → LeafProfileKernel n a d)
    (sy : I n) (z : ZVec n c) :
    leafBProfile
        (leafBVisKernelOfCoord (n := n) (a := a) (c := c) (d := d) kB) sy z
      =
      (kB sy z).1 := by
  rfl

theorem leafCProfile_leafCVisKernelOfCoord
    {n a b d : ℕ} [NeZero n]
    (kC : YVec n b → I n → LeafProfileKernel n a d)
    (y : YVec n b) (sz : I n) :
    leafCProfile
        (leafCVisKernelOfCoord (n := n) (a := a) (b := b) (d := d) kC) y sz
      =
      (kC y sz).1 := by
  rfl

theorem leafBVisFiberCoord_symm_val
    {n a c d : ℕ} [NeZero n]
    (V : LeafBVisible n c d)
    (kB : I n → ZVec n c → LeafProfileKernel n a d) :
    ((leafBVisFiberEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d) V).symm kB).1
      =
      leafBVisKernelOfCoord (n := n) (a := a) (c := c) (d := d) kB
        + leafBVisBase (n := n) (a := a) (c := c) (d := d) V := by
  rfl

theorem leafCVisFiberCoord_symm_val
    {n a b d : ℕ} [NeZero n]
    (V : LeafCVisible n b d)
    (kC : YVec n b → I n → LeafProfileKernel n a d) :
    ((leafCVisFiberEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d) V).symm kC).1
      =
      leafCVisKernelOfCoord (n := n) (a := a) (b := b) (d := d) kC
        + leafCVisBase (n := n) (a := a) (b := b) (d := d) V := by
  rfl

end

end TriangleLeaf
end Core4loop
