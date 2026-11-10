import Core4loop.TriangleLeaf.TotalQCvVisibleScalarCoeff

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def qLeafProfileKernelTotalCvCoeff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (i : LeafCvFamilyIndex n b d hd) (p : PVec n a) : F :=
  qLeafProfileKernelRemainderCvCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
  +
  qLeafProfileKernelProfileCvCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
  +
  qLeafProfileKernelVisibleScalarCvCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H i p

def TotalCvCoeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) : Prop :=
  leafScalarFamilyCoeffCondition
    (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
    (qLeafProfileKernelTotalCvCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)

theorem qLeafProfileKernelTotalCvCoeff_apply
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd)
    (kCv : LeafCvProfileKernelCoord n a b d hd) :
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (qLeafProfileKernelTotalCvCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB)
        (fun i => kCv i.1 i.2.1 i.2.2)
      =
      qLeafProfileKernelTotalCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv := by
  unfold qLeafProfileKernelTotalCvCoeff
  calc
    leafScalarFamilyCoeffApply
        (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
        (fun i p =>
          qLeafProfileKernelRemainderCvCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
          +
          qLeafProfileKernelProfileCvCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB i p
          +
          qLeafProfileKernelVisibleScalarCvCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H i p)
        (fun i => kCv i.1 i.2.1 i.2.2)
        =
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelRemainderCvCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCv i.1 i.2.1 i.2.2)
        +
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelProfileCvCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB)
          (fun i => kCv i.1 i.2.1 i.2.2)
        +
        leafScalarFamilyCoeffApply
          (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
          (qLeafProfileKernelVisibleScalarCvCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
          (fun i => kCv i.1 i.2.1 i.2.2) := by
          unfold leafScalarFamilyCoeffApply leafScalarCoeffApply
          simp only [Finset.sum_add_distrib, mul_add]
    _ =
        qLeafProfileKernelRemainderCvLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv
        +
        (∑ ω : PassiveVisibleIndex n d hd,
          qProfileABCLeafCvRightLinearMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd
            XB.1 ω kCv)
        +
        (∑ ω : PassiveVisibleIndex n d hd,
          (qScalarRightLinearMap
            (b := b) (c := c) (n := n)
            ((leafVisibleKernelEquivCoord
              (n := n) (b := b) (c := c) (d := d) hd H) ω).1.1)
            (leafCVisibleScalarIndexDiffLinearMap
              (n := n) (a := a) (b := b) (d := d) hd ω kCv)) := by
          rw [qLeafProfileKernelRemainderCvCoeff_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
          rw [qLeafProfileKernelProfileCvCoeff_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd XB kCv]
          rw [qLeafProfileKernelVisibleScalarCvCoeff_apply
            (n := n) (a := a) (b := b) (c := c) (d := d) hd H kCv]
    _ =
        qLeafProfileKernelTotalCvLinearMap
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB kCv := by
          unfold qLeafProfileKernelTotalCvLinearMap
            qLeafScalarCanonicalProfileBlockCvLinearMap
          simp only [LinearMap.add_apply, LinearMap.sum_apply]
          rw [Finset.sum_add_distrib]
          abel

private noncomputable def qLeafProfileKernelTotalCvPairLinearMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    (LeafCvFamilyIndex n b d hd → LeafScalarProfileKernel n a) →ₗ[F] F where
  toFun X :=
    qLeafProfileKernelTotalCvLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      (fun ω y sz => X (ω, (y, sz)))
  map_add' X Y := by
    let L :=
      qLeafProfileKernelTotalCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
    have hfun :
        (fun ω y sz =>
            ((X + Y : LeafCvFamilyIndex n b d hd → LeafScalarProfileKernel n a)
              (ω, (y, sz))))
          =
          (fun ω y sz => X (ω, (y, sz)))
            +
          (fun ω y sz => Y (ω, (y, sz))) := by
      ext ω y sz p
      rfl
    change L (fun ω y sz =>
        ((X + Y : LeafCvFamilyIndex n b d hd → LeafScalarProfileKernel n a)
          (ω, (y, sz)))) =
      L (fun ω y sz => X (ω, (y, sz)))
        + L (fun ω y sz => Y (ω, (y, sz)))
    rw [hfun]
    exact map_add L
      (fun ω y sz => X (ω, (y, sz)))
      (fun ω y sz => Y (ω, (y, sz)))
  map_smul' r X := by
    let L :=
      qLeafProfileKernelTotalCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
    have hfun :
        (fun ω y sz =>
            ((r • X : LeafCvFamilyIndex n b d hd → LeafScalarProfileKernel n a)
              (ω, (y, sz))))
          =
          r • (fun ω y sz => X (ω, (y, sz))) := by
      ext ω y sz p
      rfl
    change L (fun ω y sz =>
        ((r • X : LeafCvFamilyIndex n b d hd → LeafScalarProfileKernel n a)
          (ω, (y, sz)))) =
      r • L (fun ω y sz => X (ω, (y, sz)))
    rw [hfun]
    exact map_smul L r (fun ω y sz => X (ω, (y, sz)))

theorem qLeafProfileKernelTotalCvLinearMap_eq_zero_iff_coeffCondition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    qLeafProfileKernelTotalCvLinearMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB = 0
      ↔
      TotalCvCoeffCondition
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB := by
  let C :=
    qLeafProfileKernelTotalCvCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  let Lorig :=
    qLeafProfileKernelTotalCvLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  let Lpair :=
    qLeafProfileKernelTotalCvPairLinearMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  have hzeroDomain :
      Lorig = 0 ↔ Lpair = 0 := by
    constructor
    · intro h
      apply LinearMap.ext
      intro X
      change Lorig (fun ω y sz => X (ω, (y, sz))) = (0 : F)
      rw [h]
      rfl
    · intro h
      apply LinearMap.ext
      intro kCv
      have hx := LinearMap.congr_fun h
        (fun i : LeafCvFamilyIndex n b d hd => kCv i.1 i.2.1 i.2.2)
      dsimp [Lpair, qLeafProfileKernelTotalCvPairLinearMap] at hx
      simpa [Lorig] using hx
  have hLpair :
      ∀ X : LeafCvFamilyIndex n b d hd → LeafScalarProfileKernel n a,
        Lpair X =
          leafScalarFamilyCoeffApply
            (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a) C X := by
    intro X
    dsimp [Lpair, qLeafProfileKernelTotalCvPairLinearMap, C]
    symm
    exact qLeafProfileKernelTotalCvCoeff_apply
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
      (fun ω y sz => X (ω, (y, sz)))
  change Lorig = 0 ↔
    TotalCvCoeffCondition
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H XB
  rw [hzeroDomain]
  simpa [TotalCvCoeffCondition, C, Lpair] using
    linearMap_eq_zero_iff_of_apply_eq_leafScalarFamilyCoeffApply
      (ι := LeafCvFamilyIndex n b d hd) (n := n) (a := a)
      Lpair C hLpair

end

end TriangleLeaf
end Core4loop
