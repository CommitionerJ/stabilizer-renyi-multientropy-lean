import Core4loop.TriangleLeaf.TotalQCdZero
import Core4loop.TriangleLeaf.FiniteSelectors

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

abbrev LeafCdFamilyIndex (n b : ℕ) [NeZero n] :=
  YVec n b × I n

def qLeafProfileKernelRemainderCdCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n a) (s : I n) : F :=
  (∑ z : ZVec n c,
    if i.2 = vecSum z then
      (∑ ω : PassiveVisibleIndex n d hd,
        if s = vecSum ω.1 then
          (XB.1 ω (vecSum i.1) z).1 p
        else 0)
      +
      (Fintype.card (Vec n (d - 1)) : F) *
        (XB.2 (vecSum i.1) z p).1 s
    else 0)
  +
  (∑ z : ZVec n c,
    if i.2 = vecSum z + 1 then
      (∑ ω : PassiveVisibleIndex n d hd,
        if s = vecSum ω.1 then
          (XB.1 ω (vecSum i.1 + 1) z).1 p
        else 0)
      +
      (Fintype.card (Vec n (d - 1)) : F) *
        (XB.2 (vecSum i.1 + 1) z p).1 s
    else 0)

def qLeafScalarCanonicalProfileBlockCdCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n a) (s : I n) : F :=
  if p = (zeroVec : PVec n a) then
    if s = vecSum ω.1 then
      (∑ z : ZVec n c,
        if i.2 = vecSum z then
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum i.1) z
        else 0)
      +
      (∑ z : ZVec n c,
        if i.2 = vecSum z + 1 then
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
              (vecSum i.1 + 1) z
        else 0)
    else 0
  else 0

def qLeafProfileKernelTotalCdCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCdFamilyIndex n b) (p : PVec n a) (s : I n) : F :=
  qLeafProfileKernelRemainderCdCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p s
  +
  ∑ ω : PassiveVisibleIndex n d hd,
    qLeafScalarCanonicalProfileBlockCdCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω i p s

def qLeafProfileKernelTotalCdCoeffRead
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    LeafCdFamilyIndex n b × (PVec n a × NonzeroI n) → F :=
  leafDiffFamilyCoeffRead
    (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
    (qLeafProfileKernelTotalCdCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)

end

end TriangleLeaf
end Core4loop
