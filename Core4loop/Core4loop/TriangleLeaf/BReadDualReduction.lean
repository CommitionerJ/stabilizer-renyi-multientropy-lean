import Core4loop.TriangleLeaf.BReadFourier
import Core4loop.TriangleLeaf.CoordinateBlocks

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

private def leafScalarProfileKernelOfNonzeroVal
    {n a : ℕ} [NeZero n]
    (f : {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F) :
    PVec n a → F :=
  fun p =>
    if h : p = (zeroVec : PVec n a) then
      ∑ q : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, f q
    else
      f ⟨p, h⟩

private theorem sum_PVec_eq_value_zeroVec_add_sum_nonzero
    {n a : ℕ} [NeZero n]
    (f : PVec n a → F) :
    (∑ p : PVec n a, f p)
      =
      f (zeroVec : PVec n a)
        + ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, f p.1 := by
  classical
  have hpart :=
    (Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (PVec n a)))
      (p := fun p : PVec n a => p = (zeroVec : PVec n a)) f).symm
  calc
    (∑ p : PVec n a, f p)
        =
        (∑ p ∈ (Finset.univ : Finset (PVec n a)) with
          p = (zeroVec : PVec n a), f p)
        +
        (∑ p ∈ (Finset.univ : Finset (PVec n a)) with
          ¬p = (zeroVec : PVec n a), f p) := by
          simpa using hpart
    _ =
        f (zeroVec : PVec n a)
        +
        (∑ p ∈ (Finset.univ : Finset (PVec n a)) with
          ¬p = (zeroVec : PVec n a), f p) := by
          congr 1
          rw [Finset.sum_eq_single (zeroVec : PVec n a)]
          · intro p hmem hp
            have hpz : p = (zeroVec : PVec n a) := by
              simpa using (Finset.mem_filter.mp hmem).2
            exact False.elim (hp hpz)
          · intro hnot
            simp at hnot
    _ =
        f (zeroVec : PVec n a)
        + ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, f p.1 := by
          congr 1
          simpa using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (PVec n a)))
              (p := fun p : PVec n a => p ≠ (zeroVec : PVec n a))
              (f := f)).symm

private theorem leafScalarProfileKernelOfNonzeroVal_zero_sum
    {n a : ℕ} [NeZero n]
    (f : {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F) :
    (∑ p : PVec n a, leafScalarProfileKernelOfNonzeroVal (n := n) (a := a) f p)
      =
      0 := by
  classical
  rw [sum_PVec_eq_value_zeroVec_add_sum_nonzero
    (n := n) (a := a)
    (f := leafScalarProfileKernelOfNonzeroVal (n := n) (a := a) f)]
  have hzero :
      leafScalarProfileKernelOfNonzeroVal (n := n) (a := a) f
          (zeroVec : PVec n a)
        =
        ∑ q : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, f q := by
    simp [leafScalarProfileKernelOfNonzeroVal]
  have hnonzero :
      (∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)},
        leafScalarProfileKernelOfNonzeroVal (n := n) (a := a) f p.1)
        =
        ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, f p := by
    refine Finset.sum_congr rfl ?_
    intro p _
    simp [leafScalarProfileKernelOfNonzeroVal, p.2]
  rw [hzero, hnonzero, F_add_self]

def leafScalarProfileKernelOfNonzero
    {n a : ℕ} [NeZero n]
    (f : {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F) :
    LeafScalarProfileKernel n a :=
  ⟨leafScalarProfileKernelOfNonzeroVal (n := n) (a := a) f,
    LinearMap.mem_ker.mpr
      (leafScalarProfileKernelOfNonzeroVal_zero_sum (n := n) (a := a) f)⟩

theorem leafScalarProfileKernelOfNonzero_apply_ne
    {n a : ℕ} [NeZero n]
    (f : {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F)
    (p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}) :
    (leafScalarProfileKernelOfNonzero (n := n) (a := a) f).1 p.1 = f p := by
  simp [leafScalarProfileKernelOfNonzero, leafScalarProfileKernelOfNonzeroVal, p.2]

theorem leafScalarProfileKernelOfNonzero_apply_zero
    {n a : ℕ} [NeZero n]
    (f : {p : PVec n a // p ≠ (zeroVec : PVec n a)} → F) :
    (leafScalarProfileKernelOfNonzero (n := n) (a := a) f).1
        (zeroVec : PVec n a)
      =
      ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, f p := by
  simp [leafScalarProfileKernelOfNonzero, leafScalarProfileKernelOfNonzeroVal]

private theorem coeffApply_comm
    {ι : Type*} [Fintype ι] (c f : ι → F) :
    coeffApply c f = coeffApply f c := by
  classical
  unfold coeffApply
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

private theorem leafScalarProfileKernel_value_zero_eq_sum_nonzero
    {n a : ℕ} [NeZero n]
    (X : LeafScalarProfileKernel n a) :
    X.1 (zeroVec : PVec n a)
      =
      ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, X.1 p.1 := by
  classical
  have hsum := LinearMap.mem_ker.mp X.2
  change (∑ p : PVec n a, X.1 p) = 0 at hsum
  rw [sum_PVec_eq_value_zeroVec_add_sum_nonzero
    (n := n) (a := a) (f := fun p : PVec n a => X.1 p)] at hsum
  calc
    X.1 (zeroVec : PVec n a)
        = X.1 (zeroVec : PVec n a) + 0 := by simp
    _ =
        X.1 (zeroVec : PVec n a)
          +
          (X.1 (zeroVec : PVec n a)
            + ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, X.1 p.1) := by
          rw [hsum]
    _ =
        ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, X.1 p.1 := by
          rw [← add_assoc, F_add_self, zero_add]

private theorem leafScalarCoeffApply_eq_coeffApply_read
    {n a : ℕ} [NeZero n]
    (C : PVec n a → F) (X : LeafScalarProfileKernel n a) :
    leafScalarCoeffApply (n := n) (a := a) C X
      =
      coeffApply
        (fun p : {p : PVec n a // p ≠ (zeroVec : PVec n a)} =>
          C p.1 + C (zeroVec : PVec n a))
        (fun p : {p : PVec n a // p ≠ (zeroVec : PVec n a)} => X.1 p.1) := by
  classical
  unfold leafScalarCoeffApply coeffApply
  rw [sum_PVec_eq_value_zeroVec_add_sum_nonzero
    (n := n) (a := a)
    (f := fun p : PVec n a => X.1 p * C p)]
  rw [leafScalarProfileKernel_value_zero_eq_sum_nonzero (n := n) (a := a) X]
  calc
    (∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, X.1 p.1)
          * C (zeroVec : PVec n a)
        +
        (∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, X.1 p.1 * C p.1)
        =
        (∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)},
          X.1 p.1 * C (zeroVec : PVec n a))
        +
        (∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)}, X.1 p.1 * C p.1) := by
          rw [Finset.sum_mul]
    _ =
        ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)},
          (X.1 p.1 * C (zeroVec : PVec n a) + X.1 p.1 * C p.1) := by
          rw [Finset.sum_add_distrib]
    _ =
        ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)},
          (X.1 p.1 * (C p.1 + C (zeroVec : PVec n a))) := by
          refine Finset.sum_congr rfl ?_
          intro p _
          ring

theorem leafScalarFamilyCoeffApply_eq_coeffApply_read
    {ι : Type*} [Fintype ι] {n a : ℕ} [NeZero n]
    (C : ι → PVec n a → F) (X : ι → LeafScalarProfileKernel n a) :
    leafScalarFamilyCoeffApply (n := n) (a := a) C X
      =
      coeffApply
        (leafScalarFamilyCoeffRead (n := n) (a := a) C)
        (fun ip : ι × {p : PVec n a // p ≠ (zeroVec : PVec n a)} =>
          (X ip.1).1 ip.2.1) := by
  classical
  unfold leafScalarFamilyCoeffApply
  calc
    (∑ i : ι, leafScalarCoeffApply (n := n) (a := a) (C i) (X i))
        =
        ∑ i : ι,
          coeffApply
            (fun p : {p : PVec n a // p ≠ (zeroVec : PVec n a)} =>
              C i p.1 + C i (zeroVec : PVec n a))
            (fun p : {p : PVec n a // p ≠ (zeroVec : PVec n a)} =>
              (X i).1 p.1) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [leafScalarCoeffApply_eq_coeffApply_read (n := n) (a := a)]
    _ =
        coeffApply
          (leafScalarFamilyCoeffRead (n := n) (a := a) C)
          (fun ip : ι × {p : PVec n a // p ≠ (zeroVec : PVec n a)} =>
            (X ip.1).1 ip.2.1) := by
          unfold coeffApply leafScalarFamilyCoeffRead
          rw [Fintype.sum_prod_type]

def leafBReadKernelScalarBTrace
    {n a c d : ℕ} [NeZero n] (hd : 0 < d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) : Core3loop.ScalarBCoef c n :=
  leafBKernelCanonicalScalarIndexDiff
    (n := n) (a := a) (c := c) (d := d) hd XB ω

theorem qLeafProfileKernelTotalCvConstLinearMap_eq_scalarBTrace_visibleC
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvConstLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          (leafBReadKernelScalarBTrace
            (n := n) (a := a) (c := c) (d := d) hd XB ω)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.2 := by
  unfold qLeafProfileKernelTotalCvConstLinearMap
    qScalarLeftLinearMap
    leafBKernelCanonicalScalarIndexDiffLinearMap
    leafBReadKernelScalarBTrace
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rfl

def leafBReadCdDualProfile
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (i : LeafCdFamilyIndex n b) : LeafDiffProfileCoord n a :=
  (leafDiffFamilyEquivNonzero
      (ι := LeafCdFamilyIndex n b) (n := n) (a := a)).symm U.1 i

theorem leafBReadCdDualProfile_read
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd) :
    leafDiffFamilyEquivNonzero
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
        (leafBReadCdDualProfile
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U)
      =
      U.1 := by
  exact
    (leafDiffFamilyEquivNonzero
      (ι := LeafCdFamilyIndex n b) (n := n) (a := a)).right_inv U.1

theorem leafBReadCdDualProfile_coeffApply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (C : LeafCdFamilyIndex n b → PVec n a → I n → F) :
    coeffApply U.1 (leafDiffFamilyCoeffRead (n := n) (a := a) C)
      =
      leafDiffFamilyCoeffApply
        (ι := LeafCdFamilyIndex n b) (n := n) (a := a) C
        (leafBReadCdDualProfile
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U) := by
  calc
    coeffApply U.1 (leafDiffFamilyCoeffRead (n := n) (a := a) C)
        =
        coeffApply (leafDiffFamilyCoeffRead (n := n) (a := a) C) U.1 := by
          rw [coeffApply_comm]
    _ =
        coeffApply (leafDiffFamilyCoeffRead (n := n) (a := a) C)
          (leafDiffFamilyEquivNonzero
            (ι := LeafCdFamilyIndex n b) (n := n) (a := a)
            (leafBReadCdDualProfile
              (n := n) (a := a) (b := b) (c := c) (d := d) hd U)) := by
          rw [leafBReadCdDualProfile_read
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U]
    _ =
        leafDiffFamilyCoeffApply
          (ι := LeafCdFamilyIndex n b) (n := n) (a := a) C
          (leafBReadCdDualProfile
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U) := by
          exact
            (leafDiffFamilyCoeffApply_eq_coeffApply_read
              (ι := LeafCdFamilyIndex n b) (n := n) (a := a) C
              (leafBReadCdDualProfile
                (n := n) (a := a) (b := b) (c := c) (d := d) hd U)).symm

def leafBReadCdDualScalarCTrace
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (ω : PassiveVisibleIndex n d hd) : Core3loop.ScalarCCoef b n :=
  fun y sz =>
      ((zeroSumProfileEquivNonzero (n := n)).symm
        (fun s : NonzeroI n =>
          U.1 ((y, sz), ((zeroVec : PVec n a), s)))).1 (vecSum ω.1)

theorem leafCDiffCanonicalScalarIndexDiff_leafBReadCdDualProfile
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafCDiffCanonicalScalarIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd
        (fun y sz =>
          leafBReadCdDualProfile
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U (y, sz)) ω
      =
      leafBReadCdDualScalarCTrace
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω := by
  ext y sz
  rfl

def leafBReadCvDualScalarCTrace
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (ω : PassiveVisibleIndex n d hd) : Core3loop.ScalarCCoef b n :=
  fun y sz =>
    ∑ p : {p : PVec n a // p ≠ (zeroVec : PVec n a)},
      U.2 ((ω, (y, sz)), p)

def leafBReadCvDualProfile
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (i : LeafCvFamilyIndex n b d hd) : LeafScalarProfileKernel n a :=
  leafScalarProfileKernelOfNonzero
    (n := n) (a := a)
    (fun p => U.2 (i, p))

theorem leafBReadCvDualProfile_read
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd) :
    (fun ip : LeafCvFamilyIndex n b d hd
        × {p : PVec n a // p ≠ (zeroVec : PVec n a)} =>
      (leafBReadCvDualProfile
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U ip.1).1
        ip.2.1)
      =
      U.2 := by
  funext ip
  exact
    leafScalarProfileKernelOfNonzero_apply_ne
      (n := n) (a := a) (fun p => U.2 (ip.1, p)) ip.2

theorem leafBReadCvDualProfile_coeffApply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (C : LeafCvFamilyIndex n b d hd → PVec n a → F) :
    coeffApply U.2 (leafScalarFamilyCoeffRead (n := n) (a := a) C)
      =
      leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a) C
        (leafBReadCvDualProfile
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U) := by
  calc
    coeffApply U.2 (leafScalarFamilyCoeffRead (n := n) (a := a) C)
        =
        coeffApply (leafScalarFamilyCoeffRead (n := n) (a := a) C) U.2 := by
          rw [coeffApply_comm]
    _ =
        coeffApply (leafScalarFamilyCoeffRead (n := n) (a := a) C)
          (fun ip : LeafCvFamilyIndex n b d hd
              × {p : PVec n a // p ≠ (zeroVec : PVec n a)} =>
            (leafBReadCvDualProfile
                (n := n) (a := a) (b := b) (c := c) (d := d) hd U ip.1).1
              ip.2.1) := by
          rw [leafBReadCvDualProfile_read
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U]
    _ =
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a) C
          (leafBReadCvDualProfile
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U) := by
          exact
            (leafScalarFamilyCoeffApply_eq_coeffApply_read
              (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a) C
              (leafBReadCvDualProfile
                (n := n) (a := a) (b := b) (c := c) (d := d) hd U)).symm

theorem leafBReadCvDualProfile_zero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (ω : PassiveVisibleIndex n d hd) (y : YVec n b) (sz : I n) :
    (leafBReadCvDualProfile
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U
        (ω, (y, sz))).1 (zeroVec : PVec n a)
      =
      leafBReadCvDualScalarCTrace
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω y sz := by
  simp [leafBReadCvDualProfile, leafBReadCvDualScalarCTrace,
    leafScalarProfileKernelOfNonzero_apply_zero]

theorem leafCVisibleScalarIndexDiffLinearMap_leafBReadCvDualProfile
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafCVisibleScalarIndexDiffLinearMap
        (n := n) (a := a) (b := b) (d := d) hd ω
        (fun ω y sz =>
          leafBReadCvDualProfile
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U
            (ω, (y, sz)))
      =
      leafBReadCvDualScalarCTrace
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω := by
  ext y sz
  exact
    leafBReadCvDualProfile_zero
      (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω y sz

private theorem qLeafProfileKernelRemainderCdPart_zero_XB
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (kCd : YVec n b → I n → LeafDiffProfileCoord n a) :
    qLeafProfileKernelRemainderCdPart
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafBProfileKernelIndexDiffCoord n a c d hd) kCd
      =
      0 := by
  unfold qLeafProfileKernelRemainderCdPart
  simp

theorem qLeafProfileKernelTotalCdExplicit_zeroXB_leafBReadCdDualProfile
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd) :
    qLeafProfileKernelTotalCdExplicit
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
        (fun y sz =>
          leafBReadCdDualProfile
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U (y, sz))
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (leafBReadCdDualScalarCTrace
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω) := by
  unfold qLeafProfileKernelTotalCdExplicit
  rw [qLeafProfileKernelRemainderCdPart_zero_XB
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  simp only [zero_add]
  refine Finset.sum_congr rfl ?_
  intro ω _
  simp [qLeafScalarCanonicalProfileBlockCdPart,
    leafCDiffCanonicalScalarIndexDiff_leafBReadCdDualProfile
      (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω]

private theorem qLeafProfileKernelRemainderCvLinearMap_zero_XB
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    qLeafProfileKernelRemainderCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : LeafBProfileKernelIndexDiffCoord n a c d hd) kCv
      =
      0 := by
  rw [qLeafProfileKernelRemainderCvLinearMap_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd
    (0 : LeafBProfileKernelIndexDiffCoord n a c d hd) kCv]
  unfold qLeafProfileKernelRemainderCvPart
  simp

private theorem qProfileABC_zero_left
    {n a b c : ℕ} [NeZero n]
    (ccoef : Core3loop.CCoefABC a b n) :
    Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
        0 ccoef
      =
      0 := by
  unfold Core3loop.qProfileABC Core3loop.qLeftProfileABC
    Core3loop.qRightProfileABC Core3loop.dotProfile
  simp

private theorem qProfileABCLeafCvRightLinearMap_zero_left
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (ω : PassiveVisibleIndex n d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    qProfileABCLeafCvRightLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (0 : PassiveVisibleIndex n d hd →
          I n → ZVec n c → LeafScalarProfileKernel n a) ω kCv
      =
      0 := by
  unfold qProfileABCLeafCvRightLinearMap
  change
    Core3loop.qProfileABC (a := a) (b := b) (c := c) (n := n)
        0
        (leafScalarCProfileKernelCoordEquivCore3CWodd
          (n := n) (a := a) (b := b) (kCv ω)).1
      =
      0
  exact
    qProfileABC_zero_left
      (n := n) (a := a) (b := b) (c := c)
      (leafScalarCProfileKernelCoordEquivCore3CWodd
        (n := n) (a := a) (b := b) (kCv ω)).1

private theorem qLeafScalarCanonicalProfileBlockCvLinearMap_zero_XB
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    qLeafScalarCanonicalProfileBlockCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        (0 : LeafBProfileKernelIndexDiffCoord n a c d hd) ω kCv
      =
      Core3loop.qScalar (b := b) (c := c) (n := n)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
        (leafCVisibleScalarIndexDiffLinearMap
          (n := n) (a := a) (b := b) (d := d) hd ω kCv) := by
  unfold qLeafScalarCanonicalProfileBlockCvLinearMap
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  have hzero :
      qProfileABCLeafCvRightLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : LeafBProfileKernelIndexDiffCoord n a c d hd).1 ω kCv
        =
        0 := by
    change
      qProfileABCLeafCvRightLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (0 : PassiveVisibleIndex n d hd →
            I n → ZVec n c → LeafScalarProfileKernel n a) ω kCv
        =
        0
    exact
      qProfileABCLeafCvRightLinearMap_zero_left
        (n := n) (a := a) (b := b) (c := c) (d := d) hd ω kCv
  rw [hzero]
  simp [qScalarRightLinearMap]

theorem qLeafProfileKernelTotalCvLinearMap_zeroXB_leafBReadCvDualProfile
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd) :
    qLeafProfileKernelTotalCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
        (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
        (fun ω y sz =>
          leafBReadCvDualProfile
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U
            (ω, (y, sz)))
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (leafBReadCvDualScalarCTrace
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω) := by
  unfold qLeafProfileKernelTotalCvLinearMap
  simp only [LinearMap.add_apply, LinearMap.sum_apply]
  rw [qLeafProfileKernelRemainderCvLinearMap_zero_XB
    (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  simp only [zero_add]
  refine Finset.sum_congr rfl ?_
  intro ω _
  rw [qLeafScalarCanonicalProfileBlockCvLinearMap_zero_XB
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H ω]
  rw [leafCVisibleScalarIndexDiffLinearMap_leafBReadCvDualProfile
    (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω]

def leafBReadDualScalarCTrace
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (ω : PassiveVisibleIndex n d hd) : Core3loop.ScalarCCoef b n :=
  leafBReadCdDualScalarCTrace
      (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω
    +
  leafBReadCvDualScalarCTrace
      (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω

theorem leafBReadTargetDot_target_eq_scalarCTrace_visibleB
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (H : LeafVisibleKernel n b c d) :
    leafBReadTargetDot (n := n) (a := a) (b := b) (c := c) (d := d)
        hd U
        (qLeafProfileKernelTotalBCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H
          (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (leafBReadDualScalarCTrace
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω) := by
  unfold leafBReadTargetDot qLeafProfileKernelTotalBCoeffRead
  change
    coeffApply U.1
        (qLeafProfileKernelTotalCdCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H
          (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))
      +
      coeffApply U.2
        (qLeafProfileKernelTotalCvCoeffRead
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H
          (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))
      =
      ∑ ω : PassiveVisibleIndex n d hd,
        Core3loop.qScalar (b := b) (c := c) (n := n)
          ((leafVisibleKernelEquivCoord
            (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1
          (leafBReadDualScalarCTrace
            (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω)
  unfold qLeafProfileKernelTotalCdCoeffRead qLeafProfileKernelTotalCvCoeffRead
  rw [leafBReadCdDualProfile_coeffApply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd U
    (qLeafProfileKernelTotalCdCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))]
  rw [leafBReadCvDualProfile_coeffApply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd U
    (qLeafProfileKernelTotalCvCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      (0 : LeafBProfileKernelIndexDiffCoord n a c d hd))]
  rw [qLeafProfileKernelTotalCdCoeff_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (fun y sz =>
      leafBReadCdDualProfile
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U (y, sz))]
  rw [qLeafProfileKernelTotalCvCoeff_apply
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (fun ω y sz =>
      leafBReadCvDualProfile
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U
        (ω, (y, sz)))]
  rw [qLeafProfileKernelTotalCdExplicit_zeroXB_leafBReadCdDualProfile
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H U]
  rw [qLeafProfileKernelTotalCvLinearMap_zeroXB_leafBReadCvDualProfile
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H U]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro ω _
  unfold leafBReadDualScalarCTrace
  rw [Core3loop.qScalar_add_right]

def leafBReadEvenBlockDataOfTraces
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) : LeafScalarEvenBlockData n b c :=
  (((leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd H) ω,
    leafBReadDualScalarCTrace
      (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω),
    leafBReadKernelScalarBTrace
      (n := n) (a := a) (c := c) (d := d) hd XB ω)

theorem leafScalarEvenBlockSign_traces
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (ω : PassiveVisibleIndex n d hd) :
    leafScalarEvenBlockSign
        (n := n) (b := b) (c := c)
        (leafBReadEvenBlockDataOfTraces
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB ω)
      =
      leafScalarEvenVisibleKernelSign
        (n := n) (b := b) (c := c)
        ((leafVisibleKernelEquivCoord
          (n := n) (b := b) (c := c) (d := d) hd H) ω)
        (leafBReadDualScalarCTrace
          (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω)
        (leafBReadKernelScalarBTrace
          (n := n) (a := a) (c := c) (d := d) hd XB ω) := by
  rfl

end

end TriangleLeaf
end Core4loop
