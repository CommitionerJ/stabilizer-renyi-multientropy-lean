import Core4loop.TriangleLeaf.E6PairCurlCertificates
import Core4loop.TriangleLeaf.BOnlyBDiagCore
import Core4loop.Square.Rank.PairExact

/-!
# Triangle+leaf E6 theta quotient

The maps in this module are logical-level 1 definitions.  The source,
range, kernel, and quotient theorems are logical-level 5 structural
certificates.  The finrank evaluations are the coefficient-rank part of
logical level 5.

This module proves no residual signed-sum evaluation, raw `Delta`, support,
`Gamma`, or catalogue theorem.
-/

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable abbrev triangleLeafE6PairCurlHdiff
    (n d : ℕ) [NeZero n] :
    Submodule F (WVec n d → PairCurlSpace n) :=
  LinearMap.range
    (triangleLeafE6PairCurlHdiffEmbed (n := n) (d := d))

noncomputable def triangleLeafE6Theta
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    BDiagCoeff n a d →ₗ[F]
      (WVec n d → PairCurlSpace n) ⧸
        triangleLeafE6PairCurlHdiff n d :=
  (Submodule.mkQ (triangleLeafE6PairCurlHdiff n d)).comp
    (triangleLeafE6BDiagCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hb)

noncomputable def triangleLeafE6BOnlyRoot
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafBOnly n a b c d →ₗ[F]
      TriangleLeafE6PairCurlJ n b c d where
  toFun Y := by
    let B : BFun4 n a c d := Y.1.1.1
    have hYDiff :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B ∈
          YDiffSpace (n := n) (b := b) (c := c) (d := d) := by
      rw [← range_KBMap_eq_YDiffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d)]
      exact ⟨B, rfl⟩
    have hC : Y.1.1.2 = 0 := by
      have h := LinearMap.mem_ker.mp Y.2
      change Y.1.1.2 = 0 at h
      exact h
    have hCompatible :=
      (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) Y.1.1).mp Y.1.2
    have hWDiff :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B ∈
          WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
      rw [hC,
        (KCMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero,
        add_zero] at hCompatible
      exact hCompatible
    exact
      ⟨KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B,
        ⟨hYDiff, hWDiff⟩⟩
  map_add' Y Z := by
    apply Subtype.ext
    exact
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_add
        Y.1.1.1 Z.1.1.1
  map_smul' r Y := by
    apply Subtype.ext
    exact
      (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul
        r Y.1.1.1

theorem triangleLeafE6BOnlyRoot_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (triangleLeafE6BOnlyRoot
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro j
  have hjRange :
      j.1 ∈
        LinearMap.range
          (KBMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rw [range_KBMap_eq_YDiffSpace
      (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact j.2.1
  rcases hjRange with ⟨B, hB⟩
  have hCompatible :
      (B, (0 : CFun4 n a b d)) ∈
        triangleLeafCompatibleSubmodule n a b c d := by
    apply
      (triangleLeafCompatibleSubmodule_carrier_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (B, (0 : CFun4 n a b d))).mpr
    rw [
      (KCMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero,
      add_zero, hB]
    exact j.2.2
  let X : triangleLeafCompatibleSubmodule n a b c d :=
    ⟨(B, (0 : CFun4 n a b d)), hCompatible⟩
  have hX : X ∈
      LinearMap.ker
        (triangleLeafCompatibleCProj
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    apply LinearMap.mem_ker.mpr
    rfl
  let Y : triangleLeafBOnly n a b c d := ⟨X, hX⟩
  refine ⟨Y, ?_⟩
  apply Subtype.ext
  exact hB

noncomputable def triangleLeafE6BOnlyJoint
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafBOnly n a b c d →ₗ[F]
      TriangleLeafE6PairCurlJ n b c d × BDiagCoeff n a d :=
  LinearMap.prod
    (triangleLeafE6BOnlyRoot
      (n := n) (a := a) (b := b) (c := c) (d := d))
    (triangleLeafBOnlyBDiagMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def triangleLeafE6PairRootDiagInclude
    {n a b c d : ℕ} [NeZero n] :
    (TriangleLeafE6PairCurlJ n b c d × BDiagCoeff n a d) →ₗ[F]
      BPairAmbient n a b c d :=
  (triangleLeafE6BPairRootInclude
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (LinearMap.fst F
        (TriangleLeafE6PairCurlJ n b c d) (BDiagCoeff n a d)) +
    (triangleLeafE6BDiagInclude
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
      (LinearMap.snd F
        (TriangleLeafE6PairCurlJ n b c d) (BDiagCoeff n a d))

noncomputable def triangleLeafE6PairRootDiagCurl
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    (TriangleLeafE6PairCurlJ n b c d × BDiagCoeff n a d) →ₗ[F]
      (WVec n d → PairCurlSpace n) :=
  (BPairCurlMap
    (n := n) (a := a) (b := b) (c := c) (d := d) hb).comp
      (triangleLeafE6PairRootDiagInclude
        (n := n) (a := a) (b := b) (c := c) (d := d))

theorem triangleLeafE6PairRootDiagCurl_eq_pairCurl_comp
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    triangleLeafE6PairRootDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb =
      (BPairCurlMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hb).comp
        (triangleLeafE6PairRootDiagInclude
          (n := n) (a := a) (b := b) (c := c) (d := d)) :=
  rfl

private theorem triangleLeafE6PairRootDiagCurl_apply
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b)
    (x : TriangleLeafE6PairCurlJ n b c d × BDiagCoeff n a d) :
    triangleLeafE6PairRootDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb x =
      triangleLeafE6BPairRootCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb x.1 +
        triangleLeafE6BDiagCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb x.2 := by
  change
    (BPairCurlMap
      (n := n) (a := a) (b := b) (c := c) (d := d) hb)
        (triangleLeafE6BPairRootInclude
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 +
          triangleLeafE6BDiagInclude
            (n := n) (a := a) (b := b) (c := c) (d := d) x.2) =
      _
  rw [LinearMap.map_add]
  rfl

private theorem triangleLeafE6PairRootDiagInclude_joint
    {n a b c d : ℕ} [NeZero n]
    (Y : triangleLeafBOnly n a b c d) :
    triangleLeafE6PairRootDiagInclude
        (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6BOnlyJoint
          (n := n) (a := a) (b := b) (c := c) (d := d) Y) =
      SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) Y.1.1.1 := by
  apply Prod.ext
  · apply Subtype.ext
    change
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) Y.1.1.1 + 0 =
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) Y.1.1.1
    simp
  · apply Subtype.ext
    change
      0 +
          BDiagEmbed (n := n) (a := a) (b := b) (d := d)
            (BDiagOfB (n := n) (a := a) (c := c) (d := d) Y.1.1.1) =
        ((squareCompat
            (n := n) (a := a) (b := b) (c := c) (d := d)).comp
          (SquareBInclusion
            (n := n) (a := a) (b := b) (c := c) (d := d))) Y.1.1.1
    rw [zero_add]
    exact
      BDiagEmbed_BDiagOfB_eq_squareCompat_B
        (n := n) (a := a) (b := b) (c := c) (d := d) Y.1.1.1

private theorem triangleLeafE6PairRootDiagInclude_injective
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Injective
      (triangleLeafE6PairRootDiagInclude
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    have hroot :=
      congrArg (fun z : BPairAmbient n a b c d => z.1.1) h
    change x.1.1 + 0 = y.1.1 + 0 at hroot
    simpa using hroot
  · have hdiag :=
      congrArg (fun z : BPairAmbient n a b c d => z.2.1) h
    change
      0 + BDiagEmbed (n := n) (a := a) (b := b) (d := d) x.2 =
        0 + BDiagEmbed (n := n) (a := a) (b := b) (d := d) y.2 at hdiag
    simp only [zero_add] at hdiag
    exact
      BDiagEmbed_injective
        (n := n) (a := a) (b := b) (d := d) hb hdiag

theorem range_triangleLeafE6BOnlyJoint_eq_ker_pairRootDiagCurl
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) :
    LinearMap.range
        (triangleLeafE6BOnlyJoint
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.ker
        (triangleLeafE6PairRootDiagCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨Y, rfl⟩
    apply LinearMap.mem_ker.mpr
    change
      (BPairCurlMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hb)
        (triangleLeafE6PairRootDiagInclude
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (triangleLeafE6BOnlyJoint
            (n := n) (a := a) (b := b) (c := c) (d := d) Y)) = 0
    rw [triangleLeafE6PairRootDiagInclude_joint]
    exact LinearMap.mem_ker.mp
      (SquareBMapAmbient_mem_ker_pairCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb Y.1.1.1)
  · intro x hx
    have hIncludeKer :
        triangleLeafE6PairRootDiagInclude
            (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
          LinearMap.ker
            (BPairCurlMap
              (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
      apply LinearMap.mem_ker.mpr
      exact LinearMap.mem_ker.mp hx
    have hIncludeRange :
        triangleLeafE6PairRootDiagInclude
            (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
          LinearMap.range
            (SquareBMapAmbient
              (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rw [← ker_BPairCurlMap_eq_range_SquareBMapAmbient
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc]
      exact hIncludeKer
    rcases hIncludeRange with ⟨B, hB⟩
    have hRoot0 :=
      congrArg (fun z : BPairAmbient n a b c d => z.1.1) hB
    have hRoot :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B = x.1.1 := by
      change
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B =
          x.1.1 + 0 at hRoot0
      simpa using hRoot0
    have hCompatible :
        (B, (0 : CFun4 n a b d)) ∈
          triangleLeafCompatibleSubmodule n a b c d := by
      apply
        (triangleLeafCompatibleSubmodule_carrier_iff
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (B, (0 : CFun4 n a b d))).mpr
      rw [
        (KCMap
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero,
        add_zero, hRoot]
      exact x.1.2.2
    let X : triangleLeafCompatibleSubmodule n a b c d :=
      ⟨(B, (0 : CFun4 n a b d)), hCompatible⟩
    have hX : X ∈
        LinearMap.ker
          (triangleLeafCompatibleCProj
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      apply LinearMap.mem_ker.mpr
      rfl
    let Y : triangleLeafBOnly n a b c d := ⟨X, hX⟩
    refine ⟨Y, ?_⟩
    apply
      triangleLeafE6PairRootDiagInclude_injective
        (n := n) (a := a) (b := b) (c := c) (d := d) hb
    rw [triangleLeafE6PairRootDiagInclude_joint]
    exact hB

theorem ker_triangleLeafE6Theta_eq_range_BOnlyBDiag
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    LinearMap.ker
        (triangleLeafE6Theta
          (n := n) (a := a) (b := b) (c := c) (d := d) hb) =
      LinearMap.range
        (triangleLeafBOnlyBDiagMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · intro U hU
    have hDiag :
        triangleLeafE6BDiagCurl
            (n := n) (a := a) (b := b) (c := c) (d := d) hb U ∈
          triangleLeafE6PairCurlHdiff n d := by
      have hzero := LinearMap.mem_ker.mp hU
      have hker :
          triangleLeafE6BDiagCurl
              (n := n) (a := a) (b := b) (c := c) (d := d) hb U ∈
            LinearMap.ker
              (Submodule.mkQ (triangleLeafE6PairCurlHdiff n d)) :=
        LinearMap.mem_ker.mpr hzero
      rw [Submodule.ker_mkQ] at hker
      exact hker
    have hRootRange :
        triangleLeafE6BDiagCurl
            (n := n) (a := a) (b := b) (c := c) (d := d) hb U ∈
          LinearMap.range
            (triangleLeafE6BPairRootCurl
              (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
      rw [range_triangleLeafE6BPairRootCurl_eq_hdiff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd]
      exact hDiag
    rcases hRootRange with ⟨j, hj⟩
    have hPair :
        (j, U) ∈
          LinearMap.ker
            (triangleLeafE6PairRootDiagCurl
              (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
      apply LinearMap.mem_ker.mpr
      rw [triangleLeafE6PairRootDiagCurl_apply, hj]
      exact F_module_add_self _
    have hJoint :
        (j, U) ∈
          LinearMap.range
            (triangleLeafE6BOnlyJoint
              (n := n) (a := a) (b := b) (c := c) (d := d)) := by
      rw [range_triangleLeafE6BOnlyJoint_eq_ker_pairRootDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc]
      exact hPair
    rcases hJoint with ⟨Y, hY⟩
    refine ⟨Y, ?_⟩
    exact congrArg Prod.snd hY
  · intro U hU
    rcases hU with ⟨Y, rfl⟩
    apply LinearMap.mem_ker.mpr
    change
      (Submodule.mkQ (triangleLeafE6PairCurlHdiff n d))
        (triangleLeafE6BDiagCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d) Y)) = 0
    have hJoint :
        triangleLeafE6BOnlyJoint
            (n := n) (a := a) (b := b) (c := c) (d := d) Y ∈
          LinearMap.ker
            (triangleLeafE6PairRootDiagCurl
              (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
      rw [← range_triangleLeafE6BOnlyJoint_eq_ker_pairRootDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc]
      exact ⟨Y, rfl⟩
    have hsum := LinearMap.mem_ker.mp hJoint
    rw [triangleLeafE6PairRootDiagCurl_apply] at hsum
    have hRootEqDiag :
        triangleLeafE6BPairRootCurl
            (n := n) (a := a) (b := b) (c := c) (d := d) hb
            (triangleLeafE6BOnlyRoot
              (n := n) (a := a) (b := b) (c := c) (d := d) Y) =
          triangleLeafE6BDiagCurl
            (n := n) (a := a) (b := b) (c := c) (d := d) hb
            (triangleLeafBOnlyBDiagMap
              (n := n) (a := a) (b := b) (c := c) (d := d) Y) := by
      let R :=
        triangleLeafE6BPairRootCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb
          (triangleLeafE6BOnlyRoot
            (n := n) (a := a) (b := b) (c := c) (d := d) Y)
      let D :=
        triangleLeafE6BDiagCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d) Y)
      change R + D = 0 at hsum
      change R = D
      calc
        R = R + 0 := by simp
        _ = R + (R + D) := by rw [hsum]
        _ = (R + R) + D := by abel
        _ = 0 + D := by rw [F_module_add_self]
        _ = D := by simp
    have hEq :
        triangleLeafE6BDiagCurl
            (n := n) (a := a) (b := b) (c := c) (d := d) hb
            (triangleLeafBOnlyBDiagMap
              (n := n) (a := a) (b := b) (c := c) (d := d) Y) =
          triangleLeafE6BPairRootCurl
            (n := n) (a := a) (b := b) (c := c) (d := d) hb
            (triangleLeafE6BOnlyRoot
              (n := n) (a := a) (b := b) (c := c) (d := d) Y) :=
      hRootEqDiag.symm
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    rw [hEq]
    change
      triangleLeafE6BPairRootCurl
          (n := n) (a := a) (b := b) (c := c) (d := d) hb
          (triangleLeafE6BOnlyRoot
            (n := n) (a := a) (b := b) (c := c) (d := d) Y) ∈
        LinearMap.range
          (triangleLeafE6PairCurlHdiffEmbed (n := n) (d := d))
    rw [← range_triangleLeafE6BPairRootCurl_eq_hdiff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd]
    exact
      ⟨triangleLeafE6BOnlyRoot
          (n := n) (a := a) (b := b) (c := c) (d := d) Y, rfl⟩

theorem triangleLeafE6Theta_surjective
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective
      (triangleLeafE6Theta
        (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  intro q
  rcases
      Submodule.mkQ_surjective (triangleLeafE6PairCurlHdiff n d) q with
    ⟨N, hN⟩
  rcases
      triangleLeafE6BDiagCurl_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d) hb N with
    ⟨U, hU⟩
  refine ⟨U, ?_⟩
  change
    (Submodule.mkQ (triangleLeafE6PairCurlHdiff n d))
      (triangleLeafE6BDiagCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb U) = q
  rw [hU]
  exact hN

theorem finrank_triangleLeafE6ThetaQuotient
    {n d : ℕ} [NeZero n] (hd : 0 < d) :
    Module.finrank F
        ((WVec n d → PairCurlSpace n) ⧸
          triangleLeafE6PairCurlHdiff n d) =
      (n - 1) ^ 2 * (n ^ d - (n - 1)) := by
  have hfin :=
    Submodule.finrank_quotient_add_finrank
      (triangleLeafE6PairCurlHdiff n d)
  rw [finrank_triangleLeafE6PairCurlHdiff (n := n) (d := d) hd,
    finrank_WVec_to_PairCurlSpace (n := n) (d := d)] at hfin
  have hpow : n - 1 ≤ n ^ d := by
    exact le_trans (Nat.sub_le n 1) (Nat.le_pow hd)
  have hcubic : (n - 1) ^ 3 = (n - 1) ^ 2 * (n - 1) := by
    ring
  have hsplit :
      (n - 1) ^ 2 * (n ^ d - (n - 1)) + (n - 1) ^ 3 =
        n ^ d * (n - 1) ^ 2 := by
    rw [hcubic]
    calc
      (n - 1) ^ 2 * (n ^ d - (n - 1)) +
          (n - 1) ^ 2 * (n - 1) =
        (n - 1) ^ 2 * ((n ^ d - (n - 1)) + (n - 1)) := by ring
      _ = (n - 1) ^ 2 * n ^ d := by rw [Nat.sub_add_cancel hpow]
      _ = n ^ d * (n - 1) ^ 2 := by ring
  omega

theorem finrank_range_triangleLeafBOnlyBDiagMap_add_firstDefect
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) ^ 2 * (n ^ d - (n - 1)) =
    Module.finrank F (BDiagCoeff n a d) := by
  have hnull :=
    LinearMap.finrank_range_add_finrank_ker
      (triangleLeafE6Theta
        (n := n) (a := a) (b := b) (c := c) (d := d) hb)
  have htop :
      LinearMap.range
          (triangleLeafE6Theta
            (n := n) (a := a) (b := b) (c := c) (d := d) hb) = ⊤ :=
    LinearMap.range_eq_top.mpr
      (triangleLeafE6Theta_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d) hb)
  have hrange :
      Module.finrank F
          (LinearMap.range
            (triangleLeafE6Theta
              (n := n) (a := a) (b := b) (c := c) (d := d) hb)) =
        Module.finrank F
          ((WVec n d → PairCurlSpace n) ⧸
            triangleLeafE6PairCurlHdiff n d) :=
    LinearEquiv.finrank_eq
      (LinearEquiv.ofTop
        (LinearMap.range
          (triangleLeafE6Theta
            (n := n) (a := a) (b := b) (c := c) (d := d) hb)) htop)
  rw [hrange,
    ker_triangleLeafE6Theta_eq_range_BOnlyBDiag
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd] at hnull
  rw [finrank_triangleLeafE6ThetaQuotient (n := n) (d := d) hd] at hnull
  exact
    (Nat.add_comm
      (Module.finrank F
        (LinearMap.range
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d))))
      ((n - 1) ^ 2 * (n ^ d - (n - 1)))).trans hnull

theorem finrank_range_triangleLeafBOnlyBDiagMap_add_firstDefect_closed
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F
        (LinearMap.range
          (triangleLeafBOnlyBDiagMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      (n - 1) ^ 2 * (n ^ d - (n - 1)) =
    (n - 1) * n ^ (a + d) := by
  rw [finrank_range_triangleLeafBOnlyBDiagMap_add_firstDefect
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd]
  exact finrank_BDiagCoeff (n := n) (a := a) (d := d) ha

end

end TriangleLeaf
end Core4loop
