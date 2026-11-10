import Core4loop.TriangleLeaf.E5OneSidedQZero
import Core4loop.TriangleLeaf.CanonicalBaseQ
import Core4loop.TriangleLeaf.ProfileKernelIndexDiffScalarQ
import Core3loop.AeqOneClosed

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Production E6 q-zero structural certificate (logical layer 5).

This module proves the frozen all-large q-zero theorem directly in the exact
compatible source.  It does not import rank, residual, `DeltaNF`, or any
downstream consumer.
-/

def TriangleLeafE6QZeroContract : Prop :=
  ∀ {n a b c d : ℕ} [NeZero n],
    2 ≤ n → Even n →
    2 ≤ a → 2 ≤ b → 2 ≤ c → 2 ≤ d →
    ∀ X : triangleLeafE5LB n a b c d,
      triangleLeafCompatibleQ X.1 = 0

/-! The generic, exact-source consequence of membership in `BOnlyᗮ`. -/

theorem triangleLeafE6LB_annihilates_BOnly
    {n a b c d : ℕ} [NeZero n]
    (X : triangleLeafE5LB n a b c d)
    (Y : triangleLeafBOnly n a b c d) :
    Q1 Y.1.1.1 X.1.1.2 = 0 := by
  have hmap :
      triangleLeafBOnlyPolarMap
          (n := n) (a := a) (b := b) (c := c) (d := d) X.1 =
        0 :=
    LinearMap.mem_ker.mp X.2
  have hpoint := DFunLike.congr_fun hmap Y
  have hYC : Y.1.1.2 = 0 := by
    exact LinearMap.mem_ker.mp Y.2
  change
    Q1 X.1.1.1 Y.1.1.2 + Q1 Y.1.1.1 X.1.1.2 = 0 at hpoint
  rw [hYC] at hpoint
  have hzero : Q1 X.1.1.1 (0 : CFun4 n a b d) = 0 := by
    unfold Q1 deltaC etaC
    simp
  simpa [hzero] using hpoint

/-! The terminal Core3 phase on a canonical compatible visible pair. -/

theorem triangleLeaf_canonicalBase_q_zero_even_large
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    Q1
        (leafVisibleBCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
        (leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H)
      =
    0 := by
  rw [Q1_eq_qLeafProfile]
  rw [qLeafProfile_canonicalBase_eq_sum_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd H]
  apply Finset.sum_eq_zero
  intro ω _
  simpa [leafScalarVisibleKernelEquivCore3] using
    Core3loop.qScalar_eq_zero_on_visible_of_even_all_ge_two
      (b := b) (c := c) (n := n) hn (by omega) (by omega)
      (leafScalarVisibleKernelEquivCore3
        ((leafVisibleKernelEquivCoord hd H) ω))

/-! Constant/prefix splitting of the actual compatible visible source. -/

noncomputable def triangleLeafE6VisibleCore3
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd) :
    Core3loop.ScalarVisibleCompat b c n :=
  leafScalarVisibleKernelEquivCore3
    ((leafVisibleKernelEquivCoord hd H) ω)

noncomputable def triangleLeafE6ConstCore3
    {n b c : ℕ} [NeZero n]
    (bc : Core3loop.ScalarVisibleCompat b c n) :
    Core3loop.ScalarVisibleCompat b c n where
  bcoef :=
    Core3loop.scalarBConst
      (Core3loop.visibleUData bc)
  ccoef := 0
  compat := by
    intro y z
    simp only [Core3loop.scalarBConst, Pi.zero_apply]
    rw [F_add_self]
    simp

noncomputable def triangleLeafE6ConstCoord
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd) :
    LeafScalarVisibleKernel n b c :=
  (leafScalarVisibleKernelEquivCore3
    (n := n) (b := b) (c := c)).symm
      (triangleLeafE6ConstCore3
        (triangleLeafE6VisibleCore3 hd H ω))

noncomputable def triangleLeafE6VisibleConst
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    LeafVisibleKernel n b c d :=
  (leafVisibleKernelEquivCoord
    (n := n) (b := b) (c := c) (d := d) hd).symm
      (triangleLeafE6ConstCoord hd H)

noncomputable def triangleLeafE6VisiblePref
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    LeafVisibleKernel n b c d :=
  H + triangleLeafE6VisibleConst hd H

theorem triangleLeafE6VisibleConst_coord
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd) :
    (leafVisibleKernelEquivCoord hd
      (triangleLeafE6VisibleConst hd H)) ω
      =
    triangleLeafE6ConstCoord hd H ω := by
  have h :=
    (leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd).apply_symm_apply
      (triangleLeafE6ConstCoord hd H)
  exact congrFun h ω

theorem triangleLeafE6VisibleConst_coord_core3
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd) :
    leafScalarVisibleKernelEquivCore3
        ((leafVisibleKernelEquivCoord hd
          (triangleLeafE6VisibleConst hd H)) ω)
      =
    triangleLeafE6ConstCore3
      (triangleLeafE6VisibleCore3 hd H ω) := by
  rw [triangleLeafE6VisibleConst_coord]
  exact
    (leafScalarVisibleKernelEquivCore3
      (n := n) (b := b) (c := c)).apply_symm_apply _

theorem triangleLeafE6VisibleKernelEquivCoord_add
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) :
    leafVisibleKernelEquivCoord hd (H + K)
      =
    leafVisibleKernelEquivCoord hd H +
      leafVisibleKernelEquivCoord hd K := by
  funext ω
  apply Subtype.ext
  exact congrFun
    ((leafVisiblePairEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd).map_add H.1 K.1) ω

theorem triangleLeafE6VisiblePref_bcoef
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (ω : PassiveVisibleIndex n d hd) :
    ((leafVisibleKernelEquivCoord hd
      (triangleLeafE6VisiblePref hd H)) ω).1.1
      =
    Core3loop.scalarBPref
      (Core3loop.visibleHData hc
        (triangleLeafE6VisibleCore3 hd H ω)) := by
  let e :=
    leafVisibleKernelEquivCoord
      (n := n) (b := b) (c := c) (d := d) hd
  have hcoord :
      (e (triangleLeafE6VisiblePref hd H) ω).1.1 =
        (e H ω).1.1 +
          (e (triangleLeafE6VisibleConst hd H) ω).1.1 := by
    have h := congrFun
      (triangleLeafE6VisibleKernelEquivCoord_add
        hd H (triangleLeafE6VisibleConst hd H)) ω
    exact congrArg (fun K : LeafScalarVisibleKernel n b c => K.1.1) h
  rw [hcoord]
  rw [triangleLeafE6VisibleConst_coord]
  let bc := triangleLeafE6VisibleCore3 hd H ω
  change
    bc.bcoef +
        Core3loop.scalarBConst (Core3loop.visibleUData bc)
      =
    Core3loop.scalarBPref (Core3loop.visibleHData hc bc)
  rw [← Core3loop.buildScalarB_visibleData_eq
    (b := b) (c := c) (n := n) hb hc bc]
  rw [Core3loop.buildScalarB_eq_scalarBConst_add_scalarBPref]
  funext t z
  simp only [Pi.add_apply]
  calc
    Core3loop.scalarBConst (Core3loop.visibleUData bc) t z +
          Core3loop.scalarBPref (Core3loop.visibleHData hc bc) t z +
        Core3loop.scalarBConst (Core3loop.visibleUData bc) t z
        =
      (Core3loop.scalarBConst (Core3loop.visibleUData bc) t z +
          Core3loop.scalarBConst (Core3loop.visibleUData bc) t z) +
        Core3loop.scalarBPref (Core3loop.visibleHData hc bc) t z := by
          abel
    _ = _ := by rw [F_add_self, zero_add]

theorem triangleLeafE6VisibleConst_c_eq_zero
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (triangleLeafE6VisibleConst hd H).1.2 = 0 := by
  funext y sz
  apply
    (passiveQuotEquivVisibleIndex
      (n := n) (d := d) hd).injective
  funext ω
  have h := congrArg
    (fun bc : Core3loop.ScalarVisibleCompat b c n => bc.ccoef y sz)
    (triangleLeafE6VisibleConst_coord_core3 hd H ω)
  simpa [triangleLeafE6VisibleCore3, leafScalarVisibleKernelEquivCore3,
    leafVisibleKernelEquivCoord, leafVisiblePairEquivCoord,
    triangleLeafE6ConstCore3] using h

theorem leafVisibleBCanonicalBase_add
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) :
    leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd (H + K)
      =
    leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      +
    leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd K := by
  funext p sy z w
  by_cases hp : p = (zeroVec : PVec n a)
  · simp [leafVisibleBCanonicalBase, leafBVisCanonicalBase, hp]
  · simp [leafVisibleBCanonicalBase, leafBVisCanonicalBase, hp]

theorem leafVisibleCCanonicalBase_eq_zero_of_visibleC_eq_zero
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) (hC : H.1.2 = 0) :
    leafVisibleCCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
    0 := by
  funext p y sz w
  simp [leafVisibleCCanonicalBase, leafCVisCanonicalBase, hC]

/-! Exact B-only packages used by the one-sided orthogonality certificate. -/

noncomputable def triangleLeafE6BOnlyOfVisibleZero
    {n a b c d : ℕ} [NeZero n]
    (B : BFun4 n a c d)
    (hB :
      leafBVisMap (n := n) (a := a) (c := c) (d := d) B = 0) :
    triangleLeafBOnly n a b c d := by
  let Y : triangleLeafCompatibleSubmodule n a b c d :=
    ⟨(B, 0), by
      apply
        (triangleLeafCompatibleSubmodule_carrier_iff
          (n := n) (a := a) (b := b) (c := c) (d := d) (B, 0)).mpr
      rw [triangleLeaf_compatible_iff_visiblePair_mem_ker]
      change
        (leafBVisMap (n := n) (a := a) (c := c) (d := d) B,
          leafCVisMap (n := n) (a := a) (b := b) (d := d) 0)
          ∈
        LinearMap.ker
          (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d))
      rw [hB, map_zero]
      exact (LinearMap.ker
        (leafVisibleRootMap (n := n) (b := b) (c := c) (d := d))).zero_mem⟩
  exact ⟨Y, by rfl⟩

theorem triangleLeafE6LB_annihilates_visibleZeroB
    {n a b c d : ℕ} [NeZero n]
    (X : triangleLeafE5LB n a b c d)
    (B : BFun4 n a c d)
    (hB :
      leafBVisMap (n := n) (a := a) (c := c) (d := d) B = 0) :
    Q1 B X.1.1.2 = 0 := by
  exact
    triangleLeafE6LB_annihilates_BOnly X
      (triangleLeafE6BOnlyOfVisibleZero B hB)

theorem triangleLeafE6VisiblePref_c_eq
    {n b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    (triangleLeafE6VisiblePref hd H).1.2 = H.1.2 := by
  change (H + triangleLeafE6VisibleConst hd H).1.2 = H.1.2
  rw [show (H + triangleLeafE6VisibleConst hd H).1.2 =
      H.1.2 + (triangleLeafE6VisibleConst hd H).1.2 by rfl]
  rw [triangleLeafE6VisibleConst_c_eq_zero, add_zero]

theorem leafVisibleBCanonicalBase_eq_const_add_prefix
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d) :
    leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
    leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (triangleLeafE6VisibleConst hd H)
      +
    leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (triangleLeafE6VisiblePref hd H) := by
  have hsum :
      H = triangleLeafE6VisibleConst hd H + triangleLeafE6VisiblePref hd H := by
    unfold triangleLeafE6VisiblePref
    symm
    calc
      triangleLeafE6VisibleConst hd H +
          (H + triangleLeafE6VisibleConst hd H) =
        H + (triangleLeafE6VisibleConst hd H +
          triangleLeafE6VisibleConst hd H) := by abel
      _ = H + (((1 : F) + 1) • triangleLeafE6VisibleConst hd H) := by
        rw [add_smul, one_smul]
      _ = H := by rw [F_add_self, zero_smul, add_zero]
  calc
    leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H =
      leafVisibleBCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (triangleLeafE6VisibleConst hd H +
            triangleLeafE6VisiblePref hd H) :=
      congrArg _ hsum
    _ = _ := leafVisibleBCanonicalBase_add hd _ _

/-! The only new phase endpoint: prefix B against an arbitrary C kernel. -/

theorem triangleLeafE6_prefix_canonical_kernel_q_zero
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc2 : 2 ≤ c) (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (XC : LeafCProfileKernelIndexDiffCoord n a b d hd) :
    qLeafProfile
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (leafVisibleBCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd
          (triangleLeafE6VisiblePref hd H))
        (leafVisibleCKernelPart
          (n := n) (a := a) (b := b) (d := d)
          ((leafCProfileKernelCoordEquivIndexDiff
            (n := n) (a := a) (b := b) (d := d) hd).symm XC))
      =
    0 := by
  rw [qLeafProfile_canonical_kernel_indexDiff_eq
    (n := n) (a := a) (b := b) (c := c) (d := d) hd
    (triangleLeafE6VisiblePref hd H) XC]
  rw [qLeafProfileCanonicalKernelIndexDiff_eq_sum_qScalar
    (n := n) (a := a) (b := b) (c := c) (d := d) hd
    (triangleLeafE6VisiblePref hd H) XC]
  apply Finset.sum_eq_zero
  intro ω _
  rw [triangleLeafE6VisiblePref_bcoef
    (n := n) (b := b) (c := c) (d := d)
    hb (by omega) hd H ω]
  exact
    Core3loop.qScalar_left_scalarBPref_eq_zero_of_even_gt_one
      (b := b) (c := c) (n := n) hn (by omega)
      (Core3loop.visibleHData (by omega)
        (triangleLeafE6VisibleCore3 hd H ω))
      (leafCKernelCanonicalScalarIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd XC ω)

/-! Exact element decompositions in the existing canonical fibers. -/

theorem triangleLeafE6_B_decomposition
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (B : BFun4 n a c d)
    (hB :
      leafBVisMap (n := n) (a := a) (c := c) (d := d) B = H.1.1) :
    ∃ kB : I n → ZVec n c → LeafProfileKernel n a d,
      B =
        leafVisibleBKernelPart
          (n := n) (a := a) (c := c) (d := d) kB
          +
        leafVisibleBCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  let BF : LeafBVisFiber (n := n) (a := a) (c := c) (d := d) H.1.1 :=
    ⟨B, hB⟩
  let kB :=
    leafBVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d) hd H.1.1 BF
  refine ⟨kB, ?_⟩
  have hinv :=
    (leafBVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (c := c) (d := d) hd H.1.1).symm_apply_apply BF
  have hval := congrArg Subtype.val hinv
  rw [leafBVisCanonicalFiberCoord_symm_val
    (n := n) (a := a) (c := c) (d := d) hd H.1.1 kB] at hval
  exact hval.symm

theorem triangleLeafE6_C_decomposition_indexDiff
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H : LeafVisibleKernel n b c d)
    (C : CFun4 n a b d)
    (hC :
      leafCVisMap (n := n) (a := a) (b := b) (d := d) C = H.1.2) :
    ∃ XC : LeafCProfileKernelIndexDiffCoord n a b d hd,
      C =
        leafVisibleCKernelPart
          (n := n) (a := a) (b := b) (d := d)
          ((leafCProfileKernelCoordEquivIndexDiff
            (n := n) (a := a) (b := b) (d := d) hd).symm XC)
          +
        leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd H := by
  let CF : LeafCVisFiber (n := n) (a := a) (b := b) (d := d) H.1.2 :=
    ⟨C, hC⟩
  let kC :=
    leafCVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d) hd H.1.2 CF
  let XC :=
    leafCProfileKernelCoordEquivIndexDiff
      (n := n) (a := a) (b := b) (d := d) hd kC
  refine ⟨XC, ?_⟩
  have hinv :=
    (leafCVisCanonicalFiberEquivProfileKernelCoord
      (n := n) (a := a) (b := b) (d := d) hd H.1.2).symm_apply_apply CF
  have hval := congrArg Subtype.val hinv
  rw [leafCVisCanonicalFiberCoord_symm_val
    (n := n) (a := a) (b := b) (d := d) hd H.1.2 kC] at hval
  have hcoord :
      (leafCProfileKernelCoordEquivIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd).symm XC = kC := by
    exact
      (leafCProfileKernelCoordEquivIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd).symm_apply_apply kC
  rw [hcoord]
  exact hval.symm

theorem leafVisibleCCanonicalBase_eq_of_visibleC_eq
    {n a b c d : ℕ} [NeZero n] (hd : 0 < d)
    (H K : LeafVisibleKernel n b c d) (hC : H.1.2 = K.1.2) :
    leafVisibleCCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd H
      =
    leafVisibleCCanonicalBase
        (n := n) (a := a) (b := b) (c := c) (d := d) hd K := by
  funext p y sz w
  simp [leafVisibleCCanonicalBase, leafCVisCanonicalBase, hC]

/-!
The frozen E6 endpoint.  The proof is elementwise in the exact compatible
source: B profile-kernel and B-constant terms are killed by `BOnlyᗮ`; the
remaining prefix term is phase-neutral against both C summands.
-/

theorem triangleLeafE5LB_q_zero_even_large
    {n a b c d : ℕ} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (ha2 : 2 ≤ a) (hb2 : 2 ≤ b)
    (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (X : triangleLeafE5LB n a b c d) :
    triangleLeafCompatibleQ X.1 = 0 := by
  have hb : 0 < b := by omega
  have hd : 0 < d := by omega
  let H : LeafVisibleKernel n b c d :=
    ⟨leafVisiblePairMap
        (n := n) (a := a) (b := b) (c := c) (d := d) X.1.1,
      (leafCompatible_iff_visiblePairMap_mem_ker
        (n := n) (a := a) (b := b) (c := c) (d := d) X.1.1).mp
        ((triangleLeafCompatibleSubmodule_carrier_iff
          (n := n) (a := a) (b := b) (c := c) (d := d) X.1.1).mp
          X.1.2)⟩
  have hBvis :
      leafBVisMap (n := n) (a := a) (c := c) (d := d) X.1.1.1 =
        H.1.1 := by
    rfl
  have hCvis :
      leafCVisMap (n := n) (a := a) (b := b) (d := d) X.1.1.2 =
        H.1.2 := by
    rfl
  rcases triangleLeafE6_B_decomposition
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hd H X.1.1.1 hBvis with ⟨kB, hBdec⟩
  rcases triangleLeafE6_C_decomposition_indexDiff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hd H X.1.1.2 hCvis with ⟨XC, hCdec⟩
  let Bker : BFun4 n a c d :=
    leafVisibleBKernelPart
      (n := n) (a := a) (c := c) (d := d) kB
  let Bbase : BFun4 n a c d :=
    leafVisibleBCanonicalBase
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H
  let Hconst : LeafVisibleKernel n b c d :=
    triangleLeafE6VisibleConst hd H
  let Hpref : LeafVisibleKernel n b c d :=
    triangleLeafE6VisiblePref hd H
  let Bconst : BFun4 n a c d :=
    leafVisibleBCanonicalBase
      (n := n) (a := a) (b := b) (c := c) (d := d) hd Hconst
  let Bpref : BFun4 n a c d :=
    leafVisibleBCanonicalBase
      (n := n) (a := a) (b := b) (c := c) (d := d) hd Hpref
  let Cker : CFun4 n a b d :=
    leafVisibleCKernelPart
      (n := n) (a := a) (b := b) (d := d)
      ((leafCProfileKernelCoordEquivIndexDiff
        (n := n) (a := a) (b := b) (d := d) hd).symm XC)
  let Cbase : CFun4 n a b d :=
    leafVisibleCCanonicalBase
      (n := n) (a := a) (b := b) (c := c) (d := d) hd H
  have hBdec' : X.1.1.1 = Bker + Bbase := hBdec
  have hCdec' : X.1.1.2 = Cker + Cbase := hCdec
  have hBkerVis :
      leafBVisMap (n := n) (a := a) (c := c) (d := d) Bker = 0 := by
    exact
      leafBVisMap_leafBVisKernelOfCoord
        (n := n) (a := a) (c := c) (d := d) kB
  have hBkerQ : Q1 Bker X.1.1.2 = 0 :=
    triangleLeafE6LB_annihilates_visibleZeroB X Bker hBkerVis
  have hBkerq :
      qLeafProfile
        (n := n) (a := a) (b := b) (c := c) (d := d)
        Bker X.1.1.2 = 0 := by
    rw [← Q1_eq_qLeafProfile]
    exact hBkerQ
  have hHconstC : Hconst.1.2 = 0 := by
    exact triangleLeafE6VisibleConst_c_eq_zero hd H
  have hCconstBase :
      leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd Hconst
        =
      0 :=
    leafVisibleCCanonicalBase_eq_zero_of_visibleC_eq_zero
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hd Hconst hHconstC
  have hConstCompatible :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) Bconst
          +
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
          (0 : CFun4 n a b d)
        ∈
      WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    have h :=
      leafVisibleCanonicalBase_compatible
        (n := n) (a := a) (b := b) (c := c) (d := d) hd Hconst
    change
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) Bconst
          +
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
          (leafVisibleCCanonicalBase
            (n := n) (a := a) (b := b) (c := c) (d := d) hd Hconst)
        ∈
      WDiffSpace (n := n) (b := b) (c := c) (d := d) at h
    rw [hCconstBase] at h
    exact h
  let YconstCompatible : triangleLeafCompatibleSubmodule n a b c d :=
    ⟨(Bconst, 0),
      (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (Bconst, 0)).mpr hConstCompatible⟩
  let Yconst : triangleLeafBOnly n a b c d :=
    ⟨YconstCompatible, by rfl⟩
  have hBconstQ : Q1 Bconst X.1.1.2 = 0 :=
    triangleLeafE6LB_annihilates_BOnly X Yconst
  have hBconstq :
      qLeafProfile
        (n := n) (a := a) (b := b) (c := c) (d := d)
        Bconst X.1.1.2 = 0 := by
    rw [← Q1_eq_qLeafProfile]
    exact hBconstQ
  have hBsplit : Bbase = Bconst + Bpref := by
    exact leafVisibleBCanonicalBase_eq_const_add_prefix hd H
  have hBreduce : Q1 X.1.1.1 X.1.1.2 = Q1 Bpref X.1.1.2 := by
    rw [hBdec', Q1_eq_qLeafProfile, qLeafProfile_add_left]
    rw [hBkerq, zero_add]
    rw [hBsplit, qLeafProfile_add_left]
    rw [hBconstq, zero_add]
    rw [Q1_eq_qLeafProfile]
  have hCbasePref :
      Cbase =
        leafVisibleCCanonicalBase
          (n := n) (a := a) (b := b) (c := c) (d := d) hd Hpref := by
    exact
      leafVisibleCCanonicalBase_eq_of_visibleC_eq
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hd H Hpref (triangleLeafE6VisiblePref_c_eq hd H).symm
  have hPrefixKernel :
      qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          Bpref Cker
        =
      0 := by
    exact
      triangleLeafE6_prefix_canonical_kernel_q_zero
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn hb hc2 hd H XC
  have hPrefixCanonical :
      qLeafProfile
          (n := n) (a := a) (b := b) (c := c) (d := d)
          Bpref Cbase
        =
      0 := by
    rw [hCbasePref, ← Q1_eq_qLeafProfile]
    exact
      triangleLeaf_canonicalBase_q_zero_even_large
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn hb2 hc2 hd Hpref
  have hPrefix : Q1 Bpref X.1.1.2 = 0 := by
    rw [hCdec', Q1_eq_qLeafProfile, qLeafProfile_add_right]
    rw [hPrefixKernel, hPrefixCanonical, add_zero]
  change Q1 X.1.1.1 X.1.1.2 = 0
  rw [hBreduce]
  exact hPrefix

end

end TriangleLeaf
end Core4loop
