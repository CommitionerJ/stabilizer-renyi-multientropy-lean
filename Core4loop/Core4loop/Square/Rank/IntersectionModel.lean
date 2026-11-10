import Core4loop.Square.Rank.IntersectionCompat

namespace Core4loop

abbrev SquareBWTraceDomain (n a c : ℕ) [NeZero n] :=
  YWCoeff n c × SquareCompatCoeff n a

noncomputable def SquareBWTrace {n a c : ℕ} [NeZero n] :
    SquareBWTraceDomain n a c →ₗ[F]
      (SquareRootCore n × SquareCompatCore n) where
  toFun x :=
    (SquareRootTrace (n := n) (c := c) x.1,
     SquareCompatTrace (n := n) (a := a) x.2)
  map_add' x y := by
    apply Prod.ext
    · exact (SquareRootTrace (n := n) (c := c)).map_add x.1 y.1
    · exact (SquareCompatTrace (n := n) (a := a)).map_add x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · exact (SquareRootTrace (n := n) (c := c)).map_smul r x.1
    · exact (SquareCompatTrace (n := n) (a := a)).map_smul r x.2

noncomputable def SquareBWModel (n a c : ℕ) [NeZero n] :
    Submodule F (SquareBWTraceDomain n a c) :=
  Submodule.comap (SquareBWTrace (n := n) (a := a) (c := c))
    (SquareCoreAllowed n)

theorem mem_SquareBWModel_iff
    {n a c : ℕ} [NeZero n]
    (x : SquareBWTraceDomain n a c) :
    x ∈ SquareBWModel n a c ↔
      (SquareRootTrace (n := n) (c := c) x.1,
       SquareCompatTrace (n := n) (a := a) x.2) ∈ SquareCoreAllowed n := by
  rfl

noncomputable def SquareBWModelTrace
    {n a c : ℕ} [NeZero n] :
    SquareBWModel n a c →ₗ[F] SquareCoreAllowed n where
  toFun x :=
    ⟨SquareBWTrace (n := n) (a := a) (c := c) x.1, x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact (SquareBWTrace (n := n) (a := a) (c := c)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (SquareBWTrace (n := n) (a := a) (c := c)).map_smul r x.1

theorem SquareBWModelTrace_surjective
    {n a c : ℕ} [NeZero n]
    (hc : 0 < c) :
    Function.Surjective (SquareBWModelTrace (n := n) (a := a) (c := c)) := by
  intro x
  rcases SquareRootTrace_surjective (n := n) (c := c) hc x.1.1 with ⟨M, hM⟩
  rcases SquareCompatTrace_surjective (n := n) (a := a) x.1.2 with ⟨T, hT⟩
  let y : SquareBWTraceDomain n a c := (M, T)
  have hy : y ∈ SquareBWModel n a c := by
    rw [mem_SquareBWModel_iff]
    change (SquareRootTrace (n := n) (c := c) M,
      SquareCompatTrace (n := n) (a := a) T) ∈ SquareCoreAllowed n
    simp [hM, hT, x.2]
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  change SquareBWTrace (n := n) (a := a) (c := c) y = x.1
  ext <;> simp [SquareBWTrace, y, hM, hT]

noncomputable def ker_SquareBWModelTrace_equiv
    {n a c : ℕ} [NeZero n] :
    LinearMap.ker (SquareBWModelTrace (n := n) (a := a) (c := c)) ≃ₗ[F]
      (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
       LinearMap.ker (SquareCompatTrace (n := n) (a := a))) where
  toFun x :=
    (⟨x.1.1.1, by
      have hx0 := LinearMap.mem_ker.mp x.2
      have hxval := congrArg Subtype.val hx0
      exact LinearMap.mem_ker.mpr (congrArg Prod.fst hxval)⟩,
     ⟨x.1.1.2, by
      have hx0 := LinearMap.mem_ker.mp x.2
      have hxval := congrArg Subtype.val hx0
      exact LinearMap.mem_ker.mpr (congrArg Prod.snd hxval)⟩)
  invFun x :=
    ⟨⟨(x.1.1, x.2.1), by
      rw [mem_SquareBWModel_iff]
      have hroot := LinearMap.mem_ker.mp x.1.2
      have hcompat := LinearMap.mem_ker.mp x.2.2
      change (SquareRootTrace (n := n) (c := c) x.1.1,
        SquareCompatTrace (n := n) (a := a) x.2.1) ∈ SquareCoreAllowed n
      rw [hroot, hcompat]
      exact Submodule.zero_mem (SquareCoreAllowed n)⟩, by
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      have hroot := LinearMap.mem_ker.mp x.1.2
      have hcompat := LinearMap.mem_ker.mp x.2.2
      change SquareBWTrace (n := n) (a := a) (c := c) (x.1.1, x.2.1) = 0
      ext <;> simp [SquareBWTrace, hroot, hcompat]⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    ext <;> rfl
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

theorem finrank_ker_SquareBWModelTrace
    {n a c : ℕ} [NeZero n] :
    Module.finrank F (LinearMap.ker (SquareBWModelTrace (n := n) (a := a) (c := c))) =
      Module.finrank F (LinearMap.ker (SquareRootTrace (n := n) (c := c))) +
      Module.finrank F (LinearMap.ker (SquareCompatTrace (n := n) (a := a))) := by
  calc
    Module.finrank F (LinearMap.ker (SquareBWModelTrace (n := n) (a := a) (c := c)))
        = Module.finrank F
            (LinearMap.ker (SquareRootTrace (n := n) (c := c)) ×
             LinearMap.ker (SquareCompatTrace (n := n) (a := a))) := by
              exact LinearEquiv.finrank_eq
                (ker_SquareBWModelTrace_equiv (n := n) (a := a) (c := c))
    _ = Module.finrank F (LinearMap.ker (SquareRootTrace (n := n) (c := c))) +
        Module.finrank F (LinearMap.ker (SquareCompatTrace (n := n) (a := a))) := by
          rw [Module.finrank_prod]

lemma square_intersection_nat_algebra
    {n r k core total A B : ℕ} [NeZero n]
    (hroot : r + n * (n - 1) ^ 2 = A)
    (hcompat : k + n * (n - 1) ^ 2 = B)
    (hcore : core = 2 * (n - 1) ^ 2 + (n - 1))
    (htotal : total = core + (r + k)) :
    total + 2 * (n - 1) ^ 3 = A + B + (n - 1) := by
  have hn : n = (n - 1) + 1 := by
    have hpos : 1 ≤ n := one_le_of_neZero
    omega
  nlinarith

theorem finrank_SquareBWModel_add_core
    {n a c : ℕ} [NeZero n]
    (ha : 0 < a) (hc : 0 < c) :
    Module.finrank F (SquareBWModel n a c)
      + 2 * (n - 1) ^ 3 =
    (n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1) := by
  let L := SquareBWModelTrace (n := n) (a := a) (c := c)
  let r := Module.finrank F (LinearMap.ker (SquareRootTrace (n := n) (c := c)))
  let k := Module.finrank F (LinearMap.ker (SquareCompatTrace (n := n) (a := a)))
  let core := Module.finrank F (SquareCoreAllowed n)
  let total := Module.finrank F (SquareBWModel n a c)
  let A := (n - 1) ^ 2 * n ^ c
  let B := (n - 1) ^ 2 * n ^ a
  have hroot : r + n * (n - 1) ^ 2 = A := by
    dsimp [r, A]
    exact finrank_ker_SquareRootTrace_add_core (n := n) (c := c) hc
  have hcompat : k + n * (n - 1) ^ 2 = B := by
    dsimp [k, B]
    exact finrank_ker_SquareCompatTrace_add_core (n := n) (a := a) ha
  have hcore : core = 2 * (n - 1) ^ 2 + (n - 1) := by
    dsimp [core]
    exact finrank_SquareCoreAllowed (n := n)
  have hker :
      Module.finrank F (LinearMap.ker L) = r + k := by
    dsimp [L, r, k]
    exact finrank_ker_SquareBWModelTrace (n := n) (a := a) (c := c)
  have hnull := LinearMap.finrank_range_add_finrank_ker L
  have hsurj : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr (SquareBWModelTrace_surjective (n := n) (a := a) (c := c) hc)
  rw [hsurj, finrank_top] at hnull
  have htotal : total = core + (r + k) := by
    dsimp [total, core]
    rw [← hnull, hker]
  exact square_intersection_nat_algebra
    (n := n) (r := r) (k := k) (core := core) (total := total) (A := A) (B := B)
    hroot hcompat hcore htotal

noncomputable abbrev SquareBWIntersection (n a b c d : ℕ) [NeZero n] :=
  ↑(LinearMap.range
      (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
    LinearMap.range
      (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)))

theorem range_SquareBMap_root_le_YDiff
    {n a b c d : ℕ} [NeZero n]
    {x : RootTarget n b c d × CFun4 n a b d}
    (hx : x ∈ LinearMap.range
      (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) :
    x.1 ∈ YDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rcases hx with ⟨B, rfl⟩
  rw [← range_KBMap_eq_YDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact ⟨B, rfl⟩

theorem range_SquareWMap_root_le_WDiff
    {n a b c d : ℕ} [NeZero n]
    {x : RootTarget n b c d × CFun4 n a b d}
    (hx : x ∈ LinearMap.range
      (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) :
    x.1 ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  rcases hx with ⟨W, rfl⟩
  rw [← range_KWMap_eq_WDiffSpace (n := n) (a := a) (b := b) (c := c) (d := d)]
  exact ⟨W, rfl⟩

theorem range_SquareBMap_compat_le_BDiag
    {n a b c d : ℕ} [NeZero n]
    {x : RootTarget n b c d × CFun4 n a b d}
    (hx : x ∈ LinearMap.range
      (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d))) :
    x.2 ∈ BDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  rcases hx with ⟨B, rfl⟩
  exact range_squareCompat_B_le_BDiagSpace
    (n := n) (a := a) (b := b) (c := c) (d := d) ⟨B, rfl⟩

theorem range_SquareWMap_compat_le_WDiag
    {n a b c d : ℕ} [NeZero n]
    {x : RootTarget n b c d × CFun4 n a b d}
    (hx : x ∈ LinearMap.range
      (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d))) :
    x.2 ∈ WDiagSpace (n := n) (a := a) (b := b) (d := d) := by
  rcases hx with ⟨W, rfl⟩
  exact range_squareCompat_W_le_WDiagSpace
    (n := n) (a := a) (b := b) (c := c) (d := d) ⟨W, rfl⟩

noncomputable def SquareBWIntersectionRootSubmodule
    {n a b c d : ℕ} [NeZero n] :
    SquareBWIntersection n a b c d →ₗ[F]
      ↑(YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊓
        WDiffSpace (n := n) (b := b) (c := c) (d := d)) where
  toFun x :=
    ⟨x.1.1,
      ⟨range_SquareBMap_root_le_YDiff (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1,
       range_SquareWMap_root_le_WDiff (n := n) (a := a) (b := b) (c := c) (d := d) x.2.2⟩⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

noncomputable def SquareBWIntersectionCompatSubmodule
    {n a b c d : ℕ} [NeZero n] :
    SquareBWIntersection n a b c d →ₗ[F]
      ↑(BDiagSpace (n := n) (a := a) (b := b) (d := d) ⊓
        WDiagSpace (n := n) (a := a) (b := b) (d := d)) where
  toFun x :=
    ⟨x.1.2,
      ⟨range_SquareBMap_compat_le_BDiag (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1,
       range_SquareWMap_compat_le_WDiag (n := n) (a := a) (b := b) (c := c) (d := d) x.2.2⟩⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

noncomputable def SquareBWIntersectionRootCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F] YWCoeff n c :=
  (YWInfEquivCoeff (n := n) (b := b) (c := c) (d := d) hb hd).toLinearMap.comp
    (SquareBWIntersectionRootSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def SquareBWIntersectionCompatCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F] SquareCompatCoeff n a :=
  (BDiagWDiagInfEquivCoeff (n := n) (a := a) (b := b) (d := d) hb hd).toLinearMap.comp
    (SquareBWIntersectionCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def SquareBWIntersectionRead
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F] SquareBWTraceDomain n a c :=
  LinearMap.prod
    (SquareBWIntersectionRootCoeff (n := n) (a := a) (b := b) (c := c) (d := d) hb hd)
    (SquareBWIntersectionCompatCoeff (n := n) (a := a) (b := b) (c := c) (d := d) hb hd)

lemma BRootFiberSum_pullYW_eq_rootTrace
    {n b c d : ℕ} [NeZero n]
    (hb : 0 < b) (M : YWCoeff n c) (sy sz : I n) (w : WVec n d) :
    BRootFiberSum (n := n) (b := b) (c := c) (d := d) hb
        (pullYW (n := n) (b := b) (c := c) (d := d) M) sy sz w =
      (SquareRootTrace (n := n) (c := c) M sz).1 sy (vecSum w) := by
  unfold BRootFiberSum
  change
    (∑ z : ZVec n c,
      if vecSum z = sz then (M z).1 (vecSum (vecSumRep (n := n) (k := b) hb sy)) (vecSum w)
      else 0) =
      (SquareRootTrace (n := n) (c := c) M sz).1 sy (vecSum w)
  rw [vecSum_vecSumRep (n := n) (k := b) hb sy]
  change
    (∑ z : ZVec n c, if vecSum z = sz then (M z).1 sy (vecSum w) else 0) =
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ z : ZVec n c, if vecSum z = sz then M z else 0)) sy (vecSum w)
  rw [map_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : vecSum z = sz <;> simp [hz]

lemma WRootFiberSum_pullYW_eq_rootTrace
    {n b c d : ℕ} [NeZero n]
    (hd : 0 < d) (M : YWCoeff n c) (y : YVec n b) (sw sz : I n) :
    WRootFiberSum (n := n) (b := b) (c := c) (d := d) hd
        (pullYW (n := n) (b := b) (c := c) (d := d) M) y sw sz =
      (SquareRootTrace (n := n) (c := c) M sz).1 (vecSum y) sw := by
  unfold WRootFiberSum
  change
    (∑ z : ZVec n c,
      if vecSum z = sz then (M z).1 (vecSum y) (vecSum (vecSumRep (n := n) (k := d) hd sw))
      else 0) =
      (SquareRootTrace (n := n) (c := c) M sz).1 (vecSum y) sw
  rw [vecSum_vecSumRep (n := n) (k := d) hd sw]
  change
    (∑ z : ZVec n c, if vecSum z = sz then (M z).1 (vecSum y) sw else 0) =
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ z : ZVec n c, if vecSum z = sz then M z else 0)) (vecSum y) sw
  rw [map_sum]
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases hz : vecSum z = sz <;> simp [hz]

lemma BCompatPSum_squareCompatEmbed_eq_compatTrace
    {n a b d : ℕ} [NeZero n]
    (hb : 0 < b) (T : SquareCompatCoeff n a) (sy sz : I n) (w : WVec n d) :
    BCompatPSum (n := n) (a := a) (b := b) (d := d) hb
        (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T) sy sz w =
      (SquareCompatTrace (n := n) (a := a) T (sy + sz + vecSum w)).1 sy (vecSum w) := by
  unfold BCompatPSum
  change
    (∑ p : PVec n a,
      compatCoreEval (T p) (vecSum (vecSumRep (n := n) (k := b) hb sy)) sz (vecSum w)) =
      (SquareCompatTrace (n := n) (a := a) T (sy + sz + vecSum w)).1 sy (vecSum w)
  rw [vecSum_vecSumRep (n := n) (k := b) hb sy]
  unfold compatCoreEval
  change
    (∑ p : PVec n a, (T p (sy + sz + vecSum w)).1 sy (vecSum w)) =
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ p : PVec n a, T p (sy + sz + vecSum w))) sy (vecSum w)
  rw [map_sum]
  simp only [Finset.sum_apply]
  rfl

lemma WCompatPSum_squareCompatEmbed_eq_compatTrace
    {n a b d : ℕ} [NeZero n]
    (hd : 0 < d) (T : SquareCompatCoeff n a) (y : YVec n b) (sw sz : I n) :
    WCompatPSum (n := n) (a := a) (b := b) (d := d) hd
        (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T) y sw sz =
      (SquareCompatTrace (n := n) (a := a) T (vecSum y + sz + sw)).1 (vecSum y) sw := by
  unfold WCompatPSum
  change
    (∑ p : PVec n a,
      compatCoreEval (T p) (vecSum y) sz (vecSum (vecSumRep (n := n) (k := d) hd sw))) =
      (SquareCompatTrace (n := n) (a := a) T (vecSum y + sz + sw)).1 (vecSum y) sw
  rw [vecSum_vecSumRep (n := n) (k := d) hd sw]
  unfold compatCoreEval
  change
    (∑ p : PVec n a, (T p (vecSum y + sz + sw)).1 (vecSum y) sw) =
      ((Submodule.subtype (MatrixZeroSum n))
        (∑ p : PVec n a, T p (vecSum y + sz + sw))) (vecSum y) sw
  rw [map_sum]
  simp only [Finset.sum_apply]
  rfl

noncomputable def BPairAmbientOfTraceData
    {n a b c d : ℕ} [NeZero n]
    (M : YWCoeff n c) (T : SquareCompatCoeff n a) :
    BPairAmbient n a b c d :=
  (⟨pullYW (n := n) (b := b) (c := c) (d := d) M,
      (range_pullYW_le_inf_YW (n := n) (b := b) (c := c) (d := d) ⟨M, rfl⟩).1⟩,
   ⟨SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T,
      range_SquareCompatEmbed_le_BDiagSpace
        (n := n) (a := a) (b := b) (d := d) ⟨T, rfl⟩⟩)

noncomputable def WPairAmbientOfTraceData
    {n a b c d : ℕ} [NeZero n]
    (M : YWCoeff n c) (T : SquareCompatCoeff n a) :
    WPairAmbient n a b c d :=
  (⟨pullYW (n := n) (b := b) (c := c) (d := d) M,
      (range_pullYW_le_inf_YW (n := n) (b := b) (c := c) (d := d) ⟨M, rfl⟩).2⟩,
   ⟨SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T,
      range_SquareCompatEmbed_le_WDiagSpace
        (n := n) (a := a) (b := b) (d := d) ⟨T, rfl⟩⟩)

lemma BPairRawCurl_of_traceData
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b)
    (M : YWCoeff n c) (T : SquareCompatCoeff n a)
    (w : WVec n d) (sy sz : I n) :
    BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb
        (BPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) M T)
        w sy sz =
      squareCoreCurlB
        (SquareRootTrace (n := n) (c := c) M)
        (SquareCompatTrace (n := n) (a := a) T)
        sy sz (vecSum w) := by
  unfold BPairRawCurl squareCoreCurlB rootCoreEval compatCoreEval BPairAmbientOfTraceData
  rw [BRootFiberSum_pullYW_eq_rootTrace (n := n) (b := b) (c := c) (d := d) hb M sy sz w]
  rw [BRootFiberSum_pullYW_eq_rootTrace
    (n := n) (b := b) (c := c) (d := d) hb M (sy + 1) (sz - 1) w]
  rw [BCompatPSum_squareCompatEmbed_eq_compatTrace
    (n := n) (a := a) (b := b) (d := d) hb T sy sz w]
  rw [BCompatPSum_squareCompatEmbed_eq_compatTrace
    (n := n) (a := a) (b := b) (d := d) hb T (sy + 1) sz w]

lemma WPairRawCurl_of_traceData
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d)
    (M : YWCoeff n c) (T : SquareCompatCoeff n a)
    (y : YVec n b) (sw sz : I n) :
    WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd
        (WPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) M T)
        y sw sz =
      squareCoreCurlW
        (SquareRootTrace (n := n) (c := c) M)
        (SquareCompatTrace (n := n) (a := a) T)
        (vecSum y) sz sw := by
  unfold WPairRawCurl squareCoreCurlW rootCoreEval compatCoreEval WPairAmbientOfTraceData
  rw [WRootFiberSum_pullYW_eq_rootTrace (n := n) (b := b) (c := c) (d := d) hd M y sw sz]
  rw [WRootFiberSum_pullYW_eq_rootTrace
    (n := n) (b := b) (c := c) (d := d) hd M y (sw + 1) (sz - 1)]
  rw [WCompatPSum_squareCompatEmbed_eq_compatTrace
    (n := n) (a := a) (b := b) (d := d) hd T y sw sz]
  rw [WCompatPSum_squareCompatEmbed_eq_compatTrace
    (n := n) (a := a) (b := b) (d := d) hd T y (sw + 1) sz]

noncomputable def SquareBWModelEmbed
    {n a b c d : ℕ} [NeZero n] :
    SquareBWTraceDomain n a c →ₗ[F]
      (RootTarget n b c d × CFun4 n a b d) where
  toFun x :=
    (pullYW (n := n) (b := b) (c := c) (d := d) x.1,
     SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) x.2)
  map_add' x y := by
    apply Prod.ext
    · exact (pullYW (n := n) (b := b) (c := c) (d := d)).map_add x.1 y.1
    · exact (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_add x.2 y.2
  map_smul' r x := by
    apply Prod.ext
    · exact (pullYW (n := n) (b := b) (c := c) (d := d)).map_smul r x.1
    · exact (SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)).map_smul r x.2

lemma BPairAmbientOfTraceData_mem_ker_pairCurl
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (x : SquareBWModel n a c) :
    BPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 ∈
      LinearMap.ker (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
  have hmem :
      (SquareRootTrace (n := n) (c := c) x.1.1,
       SquareCompatTrace (n := n) (a := a) x.1.2) ∈ SquareCoreAllowed n :=
    (mem_SquareBWModel_iff (n := n) (a := a) (c := c) x.1).1 x.2
  have hallowed :=
    (mem_SquareCoreAllowed_iff (n := n)
      (SquareBWTrace (n := n) (a := a) (c := c) x.1)).1 hmem
  apply LinearMap.mem_ker.mpr
  rw [BPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d) hb]
  funext w sy sz
  change BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb
      (BPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      w sy sz = 0
  rw [BPairRawCurl_of_traceData (n := n) (a := a) (b := b) (c := c) (d := d)
    hb x.1.1 x.1.2 w sy sz]
  exact (hallowed sy sz (vecSum w)).1

lemma WPairAmbientOfTraceData_mem_ker_pairCurl
    {n a b c d : ℕ} [NeZero n]
    (hd : 0 < d) (x : SquareBWModel n a c) :
    WPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2 ∈
      LinearMap.ker (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
  have hmem :
      (SquareRootTrace (n := n) (c := c) x.1.1,
       SquareCompatTrace (n := n) (a := a) x.1.2) ∈ SquareCoreAllowed n :=
    (mem_SquareBWModel_iff (n := n) (a := a) (c := c) x.1).1 x.2
  have hallowed :=
    (mem_SquareCoreAllowed_iff (n := n)
      (SquareBWTrace (n := n) (a := a) (c := c) x.1)).1 hmem
  apply LinearMap.mem_ker.mpr
  rw [WPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d) hd]
  funext y sw sz
  change WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd
      (WPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2)
      y sw sz = 0
  rw [WPairRawCurl_of_traceData (n := n) (a := a) (b := b) (c := c) (d := d)
    hd x.1.1 x.1.2 y sw sz]
  exact (hallowed (vecSum y) sz sw).2

theorem SquareBWModelEmbed_mem_range_SquareBMap
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (x : SquareBWModel n a c) :
    SquareBWModelEmbed (n := n) (a := a) (b := b) (c := c) (d := d) x.1 ∈
      LinearMap.range (SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  let bAmb : BPairAmbient n a b c d :=
    BPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2
  have hbker : bAmb ∈
      LinearMap.ker (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
    exact BPairAmbientOfTraceData_mem_ker_pairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hb x
  have hbrange : bAmb ∈ LinearMap.range
      (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rw [← ker_BPairCurlMap_eq_range_SquareBMapAmbient
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc]
    exact hbker
  rcases hbrange with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  calc
    SquareBMap (n := n) (a := a) (b := b) (c := c) (d := d) B
        = BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
            (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B) := by
            rw [BPairInclude_SquareBMapAmbient]
    _ = BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) bAmb := by
            rw [hB]
    _ = SquareBWModelEmbed (n := n) (a := a) (b := b) (c := c) (d := d) x.1 := rfl

theorem SquareBWModelEmbed_mem_range_SquareWMap
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (hd : 0 < d) (x : SquareBWModel n a c) :
    SquareBWModelEmbed (n := n) (a := a) (b := b) (c := c) (d := d) x.1 ∈
      LinearMap.range (SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  let wAmb : WPairAmbient n a b c d :=
    WPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 x.1.2
  have hwker : wAmb ∈
      LinearMap.ker (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
    exact WPairAmbientOfTraceData_mem_ker_pairCurl
      (n := n) (a := a) (b := b) (c := c) (d := d) hd x
  have hwrange : wAmb ∈ LinearMap.range
      (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    rw [← ker_WPairCurlMap_eq_range_SquareWMapAmbient
      (n := n) (a := a) (b := b) (c := c) (d := d) hc hd]
    exact hwker
  rcases hwrange with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  calc
    SquareWMap (n := n) (a := a) (b := b) (c := c) (d := d) W
        = WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
            (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W) := by
            rw [WPairInclude_SquareWMapAmbient]
    _ = WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d) wAmb := by
            rw [hW]
    _ = SquareBWModelEmbed (n := n) (a := a) (b := b) (c := c) (d := d) x.1 := rfl

noncomputable def SquareBWModelToIntersection
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWModel n a c →ₗ[F] SquareBWIntersection n a b c d where
  toFun x :=
    ⟨SquareBWModelEmbed (n := n) (a := a) (b := b) (c := c) (d := d) x.1,
      ⟨SquareBWModelEmbed_mem_range_SquareBMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc x,
       SquareBWModelEmbed_mem_range_SquareWMap
        (n := n) (a := a) (b := b) (c := c) (d := d) hc hd x⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact (SquareBWModelEmbed (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (SquareBWModelEmbed (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

lemma pullYW_SquareBWIntersectionRootCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    pullYW (n := n) (b := b) (c := c) (d := d)
        (SquareBWIntersectionRootCoeff (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) =
      x.1.1 := by
  change pullYW (n := n) (b := b) (c := c) (d := d)
      ((YWInfEquivCoeff (n := n) (b := b) (c := c) (d := d) hb hd)
        (SquareBWIntersectionRootSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) x)) =
    x.1.1
  exact pullYW_YWInfCoeffRead (n := n) (b := b) (c := c) (d := d) hb hd
    (SquareBWIntersectionRootSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) x)

lemma SquareCompatEmbed_SquareBWIntersectionCompatCoeff
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
        (SquareBWIntersectionCompatCoeff (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x) =
      x.1.2 := by
  change SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
      ((BDiagWDiagInfEquivCoeff (n := n) (a := a) (b := b) (d := d) hb hd)
        (SquareBWIntersectionCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) x)) =
    x.1.2
  exact SquareCompatEmbed_BDiagWDiagInfCoeffRead
    (n := n) (a := a) (b := b) (d := d) hb hd
    (SquareBWIntersectionCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) x)

theorem SquareBWIntersectionRead_mem_model
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (_hc : 0 < c) (hd : 0 < d)
    (x : SquareBWIntersection n a b c d) :
    SquareBWIntersectionRead (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x
      ∈ SquareBWModel n a c := by
  let M := SquareBWIntersectionRootCoeff (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x
  let T := SquareBWIntersectionCompatCoeff (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x
  have hroot :
      pullYW (n := n) (b := b) (c := c) (d := d) M = x.1.1 := by
    simpa [M] using pullYW_SquareBWIntersectionRootCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x
  have hcompat :
      SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) T = x.1.2 := by
    simpa [T] using SquareCompatEmbed_SquareBWIntersectionCompatCoeff
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x
  have htraceIncludeB :
      BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (BPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) M T) = x.1 := by
    apply Prod.ext
    · exact hroot
    · exact hcompat
  have htraceIncludeW :
      WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
        (WPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) M T) = x.1 := by
    apply Prod.ext
    · exact hroot
    · exact hcompat
  rw [mem_SquareBWModel_iff]
  change (SquareRootTrace (n := n) (c := c) M,
    SquareCompatTrace (n := n) (a := a) T) ∈ SquareCoreAllowed n
  apply (mem_SquareCoreAllowed_iff (n := n)
    (SquareRootTrace (n := n) (c := c) M,
     SquareCompatTrace (n := n) (a := a) T)).2
  intro sy sz sw
  constructor
  · rcases x.2.1 with ⟨B, hB⟩
    let bTrace : BPairAmbient n a b c d :=
      BPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) M T
    have hincludeB :
        BPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
          (SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B) = x.1 := by
      rw [BPairInclude_SquareBMapAmbient, hB]
    have hbTraceEq : bTrace =
        SquareBMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) B := by
      apply BPairInclude_injective (n := n) (a := a) (b := b) (c := c) (d := d)
      rw [htraceIncludeB, hincludeB]
    have hbker : bTrace ∈
        LinearMap.ker (BPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hb) := by
      rw [hbTraceEq]
      exact SquareBMapAmbient_mem_ker_pairCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hb B
    have hraw :=
      (BPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d)
        hb bTrace).1 (LinearMap.mem_ker.mp hbker)
    let w : WVec n d := vecSumRep (n := n) (k := d) hd sw
    have hw : vecSum w = sw := vecSum_vecSumRep (n := n) (k := d) hd sw
    have hpoint := congrFun (congrFun (congrFun hraw w) sy) sz
    change BPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hb
      bTrace w sy sz = 0 at hpoint
    rw [BPairRawCurl_of_traceData (n := n) (a := a) (b := b) (c := c) (d := d)
      hb M T w sy sz] at hpoint
    simpa [w, hw] using hpoint
  · rcases x.2.2 with ⟨W, hW⟩
    let wTrace : WPairAmbient n a b c d :=
      WPairAmbientOfTraceData (n := n) (a := a) (b := b) (c := c) (d := d) M T
    have hincludeW :
        WPairInclude (n := n) (a := a) (b := b) (c := c) (d := d)
          (SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W) = x.1 := by
      rw [WPairInclude_SquareWMapAmbient, hW]
    have hwTraceEq : wTrace =
        SquareWMapAmbient (n := n) (a := a) (b := b) (c := c) (d := d) W := by
      apply WPairInclude_injective (n := n) (a := a) (b := b) (c := c) (d := d)
      rw [htraceIncludeW, hincludeW]
    have hwker : wTrace ∈
        LinearMap.ker (WPairCurlMap (n := n) (a := a) (b := b) (c := c) (d := d) hd) := by
      rw [hwTraceEq]
      exact SquareWMapAmbient_mem_ker_pairCurl
        (n := n) (a := a) (b := b) (c := c) (d := d) hd W
    have hraw :=
      (WPairCurl_eq_zero_iff_raw (n := n) (a := a) (b := b) (c := c) (d := d)
        hd wTrace).1 (LinearMap.mem_ker.mp hwker)
    let y : YVec n b := vecSumRep (n := n) (k := b) hb sy
    have hy : vecSum y = sy := vecSum_vecSumRep (n := n) (k := b) hb sy
    have hpoint := congrFun (congrFun (congrFun hraw y) sw) sz
    change WPairRawCurl (n := n) (a := a) (b := b) (c := c) (d := d) hd
      wTrace y sw sz = 0 at hpoint
    rw [WPairRawCurl_of_traceData (n := n) (a := a) (b := b) (c := c) (d := d)
      hd M T y sw sz] at hpoint
    simpa [y, hy] using hpoint

noncomputable def SquareBWIntersectionToModel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWIntersection n a b c d →ₗ[F] SquareBWModel n a c where
  toFun x :=
    ⟨SquareBWIntersectionRead (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x,
      SquareBWIntersectionRead_mem_model
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x⟩
  map_add' x y := by
    apply Subtype.ext
    exact (SquareBWIntersectionRead (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_add x y
  map_smul' r x := by
    apply Subtype.ext
    exact (SquareBWIntersectionRead (n := n) (a := a) (b := b) (c := c) (d := d) hb hd).map_smul r x

noncomputable def SquareBWIntersectionEquivModel
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    SquareBWIntersection n a b c d ≃ₗ[F] SquareBWModel n a c where
  toFun := SquareBWIntersectionToModel
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
  invFun := SquareBWModelToIntersection
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · exact pullYW_SquareBWIntersectionRootCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x
    · exact SquareCompatEmbed_SquareBWIntersectionCompatCoeff
        (n := n) (a := a) (b := b) (c := c) (d := d) hb hd x
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply pullYW_injective (n := n) (b := b) (c := c) (d := d) hb hd
      calc
        pullYW (n := n) (b := b) (c := c) (d := d)
            ((SquareBWIntersectionToModel
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
              ((SquareBWModelToIntersection
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd) x)).1.1)
            =
          (SquareBWModelToIntersection
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1.1 := by
              exact pullYW_SquareBWIntersectionRootCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
                ((SquareBWModelToIntersection
                  (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd) x)
        _ = pullYW (n := n) (b := b) (c := c) (d := d) x.1.1 := rfl
    · apply SquareCompatEmbed_injective (n := n) (a := a) (b := b) (d := d) hb hd
      calc
        SquareCompatEmbed (n := n) (a := a) (b := b) (d := d)
            ((SquareBWIntersectionToModel
              (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd
              ((SquareBWModelToIntersection
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd) x)).1.2)
            =
          (SquareBWModelToIntersection
            (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd x).1.2 := by
              exact SquareCompatEmbed_SquareBWIntersectionCompatCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d) hb hd
                ((SquareBWModelToIntersection
                  (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd) x)
        _ = SquareCompatEmbed (n := n) (a := a) (b := b) (d := d) x.1.2 := rfl
  map_add' x y :=
    (SquareBWIntersectionToModel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).map_add x y
  map_smul' r x :=
    (SquareBWIntersectionToModel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd).map_smul r x

theorem finrank_SquareBWIntersection_eq_model
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (SquareBWIntersection n a b c d) =
      Module.finrank F (SquareBWModel n a c) :=
  LinearEquiv.finrank_eq
    (SquareBWIntersectionEquivModel
      (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd)

theorem finrank_SquareBWIntersection_add_core
    {n a b c d : ℕ} [NeZero n]
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Module.finrank F (SquareBWIntersection n a b c d)
      + 2 * (n - 1) ^ 3 =
    (n - 1) ^ 2 * n ^ c + (n - 1) ^ 2 * n ^ a + (n - 1) := by
  rw [finrank_SquareBWIntersection_eq_model
    (n := n) (a := a) (b := b) (c := c) (d := d) hb hc hd]
  exact finrank_SquareBWModel_add_core (n := n) (a := a) (c := c) ha hc

end Core4loop
