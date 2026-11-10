import Core4loop.TriangleLeaf.PassiveComplement
import Core4loop.TriangleLeaf.VisibleMaps
import Core4loop.TriangleLeaf.VisibleRoot

namespace Core4loop
namespace TriangleLeaf

noncomputable section

theorem passiveQuotEquivVisibleSpace_mkQ
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : PassiveRaw n d) :
    passiveQuotEquivVisibleSpace (n := n) (d := d) hd
        ((PassiveDiffSpace n d).mkQ f)
      =
      passiveVisiblePartToSpace (n := n) (d := d) hd f := by
  unfold passiveQuotEquivVisibleSpace
  simp [Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem passiveQuotEquivVisibleSpace_mkQ_visible
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (v : PassiveVisibleSpace n d hd) :
    passiveQuotEquivVisibleSpace (n := n) (d := d) hd
        ((PassiveDiffSpace n d).mkQ v.1)
      =
      v := by
  rw [passiveQuotEquivVisibleSpace_mkQ
    (n := n) (d := d) hd v.1]
  apply Subtype.ext
  exact passiveVisiblePart_fixed_of_mem_visibleSpace
    (n := n) (d := d) hd v

theorem passiveQuotEquivVisibleIndex_mkQ_visible
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (v : PassiveVisibleSpace n d hd) :
    passiveQuotEquivVisibleIndex (n := n) (d := d) hd
        ((PassiveDiffSpace n d).mkQ v.1)
      =
      passiveVisibleSpaceEquivIndex (n := n) (d := d) hd v := by
  unfold passiveQuotEquivVisibleIndex
  rw [LinearEquiv.trans_apply,
    passiveQuotEquivVisibleSpace_mkQ_visible (n := n) (d := d) hd v]

def leafBVisCanonicalBase
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d) : BFun4 n a c d :=
  fun p sy z w =>
    if p = (zeroVec : PVec n a) then
      (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (V sy z)).1 w
    else 0

def leafCVisCanonicalBase
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d) : CFun4 n a b d :=
  fun p y sz w =>
    if p = (zeroVec : PVec n a) then
      (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (V y sz)).1 w
    else 0

theorem leafBVisCanonicalBase_spec
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d) :
    leafBVisMap (n := n) (a := a) (c := c) (d := d)
      (leafBVisCanonicalBase (n := n) (a := a) (c := c) (d := d) hd V)
      =
      V := by
  funext sy z
  rw [leafBVisMap_apply]
  let v := passiveQuotEquivVisibleSpace (n := n) (d := d) hd (V sy z)
  unfold leafBVisQuot leafBProfile leafBVisCanonicalBase
  have hprofile :
      (fun p : PVec n a => fun w : WVec n d =>
        if p = (zeroVec : PVec n a) then v.1 w else 0)
        =
      (fun p : PVec n a =>
        if p = (zeroVec : PVec n a) then (v.1 : PassiveRaw n d) else 0) := by
    funext p w
    by_cases hp : p = (zeroVec : PVec n a) <;> simp [hp]
  rw [hprofile]
  unfold leafSigmaQuot
  rw [LinearMap.comp_apply,
    leafSigmaRaw_single_zeroVec (n := n) (a := a) (d := d) v.1]
  apply (passiveQuotEquivVisibleSpace (n := n) (d := d) hd).injective
  rw [passiveQuotEquivVisibleSpace_mkQ_visible (n := n) (d := d) hd v]

theorem leafCVisCanonicalBase_spec
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d) :
    leafCVisMap (n := n) (a := a) (b := b) (d := d)
      (leafCVisCanonicalBase (n := n) (a := a) (b := b) (d := d) hd V)
      =
      V := by
  funext y sz
  rw [leafCVisMap_apply]
  let v := passiveQuotEquivVisibleSpace (n := n) (d := d) hd (V y sz)
  unfold leafCVisQuot leafCProfile leafCVisCanonicalBase
  have hprofile :
      (fun p : PVec n a => fun w : WVec n d =>
        if p = (zeroVec : PVec n a) then v.1 w else 0)
        =
      (fun p : PVec n a =>
        if p = (zeroVec : PVec n a) then (v.1 : PassiveRaw n d) else 0) := by
    funext p w
    by_cases hp : p = (zeroVec : PVec n a) <;> simp [hp]
  rw [hprofile]
  unfold leafSigmaQuot
  rw [LinearMap.comp_apply,
    leafSigmaRaw_single_zeroVec (n := n) (a := a) (d := d) v.1]
  apply (passiveQuotEquivVisibleSpace (n := n) (d := d) hd).injective
  rw [passiveQuotEquivVisibleSpace_mkQ_visible (n := n) (d := d) hd v]

theorem leafBProfile_leafBVisCanonicalBase_zero
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d) (sy : I n) (z : ZVec n c) :
    leafBProfile
        (leafBVisCanonicalBase
          (n := n) (a := a) (c := c) (d := d) hd V) sy z
        (zeroVec : PVec n a)
      =
      (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (V sy z)).1 := by
  funext w
  simp [leafBProfile, leafBVisCanonicalBase]

theorem leafBProfile_leafBVisCanonicalBase_ne_zero
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafBVisible n c d) (sy : I n) (z : ZVec n c)
    (p : PVec n a) (hp : p ≠ (zeroVec : PVec n a)) :
    leafBProfile
        (leafBVisCanonicalBase
          (n := n) (a := a) (c := c) (d := d) hd V) sy z p
      =
      0 := by
  funext w
  simp [leafBProfile, leafBVisCanonicalBase, hp]

theorem leafCProfile_leafCVisCanonicalBase_zero
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d) (y : YVec n b) (sz : I n) :
    leafCProfile
        (leafCVisCanonicalBase
          (n := n) (a := a) (b := b) (d := d) hd V) y sz
        (zeroVec : PVec n a)
      =
      (passiveQuotEquivVisibleSpace (n := n) (d := d) hd (V y sz)).1 := by
  funext w
  simp [leafCProfile, leafCVisCanonicalBase]

theorem leafCProfile_leafCVisCanonicalBase_ne_zero
    {n a b d : ℕ} [NeZero n] (hd : 0 < d)
    (V : LeafCVisible n b d) (y : YVec n b) (sz : I n)
    (p : PVec n a) (hp : p ≠ (zeroVec : PVec n a)) :
    leafCProfile
        (leafCVisCanonicalBase
          (n := n) (a := a) (b := b) (d := d) hd V) y sz p
      =
      0 := by
  funext w
  simp [leafCProfile, leafCVisCanonicalBase, hp]

theorem leafVisibleCanonicalBasePair_visMap_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LinearMap.ker
      (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d))) :
    (leafBVisMap (n := n) (a := a) (c := c) (d := d)
        (leafBVisCanonicalBase
          (n := n) (a := a) (c := c) (d := d) hd H.1.1),
      leafCVisMap (n := n) (a := a) (b := b) (d := d)
        (leafCVisCanonicalBase
          (n := n) (a := a) (b := b) (d := d) hd H.1.2))
      =
      H.1 := by
  exact
    Prod.ext
      (leafBVisCanonicalBase_spec
        (n := n) (a := a) (c := c) (d := d) hd H.1.1)
      (leafCVisCanonicalBase_spec
        (n := n) (a := a) (b := b) (d := d) hd H.1.2)

theorem leafVisibleCanonicalBasePair_mem_ker
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LinearMap.ker
      (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d))) :
    (leafBVisMap (n := n) (a := a) (c := c) (d := d)
        (leafBVisCanonicalBase
          (n := n) (a := a) (c := c) (d := d) hd H.1.1),
      leafCVisMap (n := n) (a := a) (b := b) (d := d)
        (leafCVisCanonicalBase
          (n := n) (a := a) (b := b) (d := d) hd H.1.2))
      ∈
      LinearMap.ker
        (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d)) := by
  rw [leafVisibleCanonicalBasePair_visMap_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  exact H.2

theorem leafVisibleCanonicalBase_compatible
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LinearMap.ker
      (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d))) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafBVisCanonicalBase
          (n := n) (a := a) (c := c) (d := d) hd H.1.1)
      +
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafCVisCanonicalBase
          (n := n) (a := a) (b := b) (d := d) hd H.1.2)
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rw [triangleLeaf_compatible_iff_visiblePair_mem_ker]
  exact leafVisibleCanonicalBasePair_mem_ker
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H

end

end TriangleLeaf
end Core4loop
