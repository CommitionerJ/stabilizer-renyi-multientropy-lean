import Core4loop.TriangleLeaf.BReadRawSpaces

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def leafBReadCTraceMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafBReadTarget n a b c d hd →ₗ[F] LeafRawCTraceSpace n b d hd where
  toFun U := fun ω =>
    leafBReadDualScalarCTrace
      (n := n) (a := a) (b := b) (c := c) (d := d) hd U ω
  map_add' U V := by
    rcases U with ⟨Ucd, Ucv⟩
    rcases V with ⟨Vcd, Vcv⟩
    ext ω y sz
    let E := (zeroSumProfileEquivNonzero (n := n)).symm
    let f : NonzeroI n → F := fun s =>
      Ucd ((y, sz), ((zeroVec : PVec n a), s))
    let g : NonzeroI n → F := fun s =>
      Vcd ((y, sz), ((zeroVec : PVec n a), s))
    have hcd :
        (E (f + g)).1 (vecSum ω.1)
          =
        (E f).1 (vecSum ω.1) + (E g).1 (vecSum ω.1) := by
      have h := map_add E f g
      exact congrFun (congrArg Subtype.val h) (vecSum ω.1)
    unfold leafBReadDualScalarCTrace
      leafBReadCdDualScalarCTrace
      leafBReadCvDualScalarCTrace
    simp only [Prod.mk_add_mk, Pi.add_apply, Finset.sum_add_distrib]
    change
      (E (f + g)).1 (vecSum ω.1)
          + ((∑ x, Ucv ((ω, (y, sz)), x))
            + ∑ x, Vcv ((ω, (y, sz)), x))
        =
      ((E f).1 (vecSum ω.1)
          + ∑ x, Ucv ((ω, (y, sz)), x))
        +
      ((E g).1 (vecSum ω.1)
          + ∑ x, Vcv ((ω, (y, sz)), x))
    rw [hcd]
    abel
  map_smul' r U := by
    rcases U with ⟨Ucd, Ucv⟩
    ext ω y sz
    let E := (zeroSumProfileEquivNonzero (n := n)).symm
    let f : NonzeroI n → F := fun s =>
      Ucd ((y, sz), ((zeroVec : PVec n a), s))
    have hcd :
        (E (r • f)).1 (vecSum ω.1)
          =
        r • (E f).1 (vecSum ω.1) := by
      have h := map_smul E r f
      exact congrFun (congrArg Subtype.val h) (vecSum ω.1)
    unfold leafBReadDualScalarCTrace
      leafBReadCdDualScalarCTrace
      leafBReadCvDualScalarCTrace
    simp only [Prod.smul_mk, Pi.smul_apply, RingHom.id_apply]
    change
      (E (r • f)).1 (vecSum ω.1)
          + (∑ x, r • Ucv ((ω, (y, sz)), x))
        =
      r •
        ((E f).1 (vecSum ω.1)
          + ∑ x, Ucv ((ω, (y, sz)), x))
    rw [hcd]
    rw [← Finset.smul_sum]
    exact
      (smul_add r ((E f).1 (vecSum ω.1))
        (∑ x, Ucv ((ω, (y, sz)), x))).symm

noncomputable def leafBReadBTraceMap
    {n a c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
      LeafRawBTraceSpace n c d hd where
  toFun XB := fun ω =>
    leafBReadKernelScalarBTrace
      (n := n) (a := a) (c := c) (d := d) hd XB ω
  map_add' X Y := by
    ext ω sy z
    exact congrFun
      (congrFun
        (leafBKernelCanonicalScalarIndexDiff_add
          (n := n) (a := a) (c := c) (d := d) hd X Y ω) sy) z
  map_smul' r X := by
    ext ω sy z
    exact congrFun
      (congrFun
        (leafBKernelCanonicalScalarIndexDiff_smul
          (n := n) (a := a) (c := c) (d := d) hd r X ω) sy) z

abbrev leafBReadTailReadMap
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d) :
    LeafBProfileKernelIndexDiffCoord n a c d hd →ₗ[F]
      LeafBReadTarget n a b c d hd :=
  qLeafProfileKernelTotalBCoeffReadZeroHLinearMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hd

theorem leafBReadFourierTailPhase_eq_dot_tailRead
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    leafBReadFourierTailPhase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd U XB
      =
    leafBReadTargetDot hd U
      ((leafBReadTailReadMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd) XB) := by
  rfl

noncomputable def leafBReadVisibleBAdjoint
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) : LeafBReadTarget n a b c d hd :=
  qLeafProfileKernelTotalBCoeffRead
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H
    (0 : LeafBProfileKernelIndexDiffCoord n a c d hd)

theorem leafBReadVisibleBAdjoint_spec
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (U : LeafBReadTarget n a b c d hd)
    (H : LeafVisibleKernel n b c d) :
    leafBReadTargetDot hd U
        (leafBReadVisibleBAdjoint
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      =
    leafRawCTraceVisibleBPair
      (n := n) (b := b) (c := c) (d := d) hd
      ((leafBReadCTraceMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd) U) H := by
  simpa [leafBReadVisibleBAdjoint, leafRawCTraceVisibleBPair,
    leafBReadCTraceMap] using
    leafBReadTargetDot_target_eq_scalarCTrace_visibleB
      (n := n) (a := a) (b := b) (c := c) (d := d) hd U H

theorem leafEvenRawBlockProductSign_traceData_eq_bitSign_actualRawPhase
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (U : LeafBReadTarget n a b c d hd)
    (XB : LeafBProfileKernelIndexDiffCoord n a c d hd) :
    leafEvenRawBlockProductSign
        (n := n) (b := b) (c := c) (d := d) hd
        (leafBReadTraceData
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB)
      =
    bitSign
      (leafRawVisibleBasePhase
          (n := n) (b := b) (c := c) (d := d) hd H
        + leafRawCTraceVisibleBPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadCTraceMap
            (n := n) (a := a) (b := b) (c := c) (d := d) hd) U) H
        + leafRawBTraceVisibleCPair
          (n := n) (b := b) (c := c) (d := d) hd
          ((leafBReadBTraceMap
            (n := n) (a := a) (c := c) (d := d) hd) XB) H) := by
  rw [leafBReadTraceData_eq_rawEvenBlockDataOfTraces
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H U XB]
  simpa [leafBReadCTraceMap, leafBReadBTraceMap] using
    leafEvenRawBlockProductSign_eq_bitSign_rawPhase
      (n := n) (b := b) (c := c) (d := d) hd H
      ((leafBReadCTraceMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hd) U)
      ((leafBReadBTraceMap
        (n := n) (a := a) (c := c) (d := d) hd) XB)

end

end TriangleLeaf
end Core4loop
