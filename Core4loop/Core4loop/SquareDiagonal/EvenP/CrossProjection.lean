import Core4loop.SquareDiagonal.EvenP.SourceSplit

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

local instance (S : Type*) : DecidableEq S := Classical.decEq S

/-!
The strict even-`P` source has pointed coordinates
`(Sigma × K) × TailZero`.  This file retains only `(Sigma, A)`, proves that
the resulting cross projection is onto, and identifies its phase-free kernel
without selecting a global `K` witness for reachable `A`.
-/

noncomputable abbrev DiamondEvenPLeft
    (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (squareCompat (n := n) (a := 1) (b := b) (c := c) (d := d))

noncomputable abbrev DiamondEvenPReachableA
    (n b c d : Nat) [NeZero n] :=
  Submodule.comap
    (diamondEvenPAConstraint
      (n := n) (a := 1) (b := b) (c := c) (d := d))
    (LinearMap.range
      (squareCompat (n := n) (a := 1) (b := b) (c := c) (d := d)))

noncomputable def diamondEvenPLeftRoot
    {n b c d : Nat} [NeZero n] :
    DiamondEvenPLeft n b c d →ₗ[F] RootTarget n b c d where
  toFun l :=
    KBMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) l.1.1 +
      KWMap
        (n := n) (a := 1) (b := b) (c := c) (d := d) l.1.2
  map_add' l l' := by
    change KBMap (l.1.1 + l'.1.1) + KWMap (l.1.2 + l'.1.2) =
      (KBMap l.1.1 + KWMap l.1.2) +
        (KBMap l'.1.1 + KWMap l'.1.2)
    simp
    abel
  map_smul' r l := by
    change KBMap (r • l.1.1) + KWMap (r • l.1.2) =
      r • (KBMap l.1.1 + KWMap l.1.2)
    simp

noncomputable def diamondEvenPRootPairing
    {n b c d : Nat} [NeZero n] :
    RootTarget n b c d →ₗ[F] Module.Dual F (AFun4 n b c d) :=
  LinearMap.mk₂ F coeffApplyA
    (by
      intro R S A
      simp only [coeffApplyA_eq_sum, Pi.add_apply, mul_add,
        Finset.sum_add_distrib])
    (by
      intro r R A
      unfold coeffApplyA coeffApply
      simp only [smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rcases i with ⟨y, z, w⟩
      simp [aFun4Equiv]
      ring)
    (by
      intro R A A'
      simp only [coeffApplyA_eq_sum, Pi.add_apply, add_mul,
        Finset.sum_add_distrib])
    (by
      intro r R A
      unfold coeffApplyA coeffApply
      simp only [smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rcases i with ⟨y, z, w⟩
      simp [aFun4Equiv]
      ring)

noncomputable def diamondEvenPCross
    {n b c d : Nat} [NeZero n] :
    DiamondEvenPLeft n b c d →ₗ[F]
      Module.Dual F (DiamondEvenPReachableA n b c d) :=
  (LinearMap.dualMap
      (DiamondEvenPReachableA n b c d).subtype).comp
    (diamondEvenPRootPairing.comp diamondEvenPLeftRoot)

noncomputable def diamondEvenPCrossQ
    {n b c d : Nat} [NeZero n]
    (z : DiamondEvenPLeft n b c d ×
      DiamondEvenPReachableA n b c d) : F :=
  diamondEvenPCross z.1 z.2

noncomputable def diamondEvenPCrossProjection
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    DiamondPreCSource n a b c d →ₗ[F]
      (DiamondEvenPLeft n b c d ×
        DiamondEvenPReachableA n b c d) where
  toFun x := by
    let q :=
      diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 (x.1.2.1, x.1.2.2)
    have hs :=
      (diamondEvenP_source_equations_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 x.1.1 x.1.2.1 x.1.2.2).mp
        (LinearMap.mem_ker.mp x.2)
    refine (⟨q.1.1, ?_⟩, ⟨x.1.1, ?_⟩)
    · simpa only [q, diamondEvenPBWPointedEquiv_apply_sigma] using hs.1
    · refine ⟨q.1.2, ?_⟩
      simpa only [q, diamondEvenPBWPointedEquiv_apply_K] using hs.2.1.symm
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg
        (fun q => q.1.1)
        ((diamondEvenPBWPointedEquiv hn ha2).map_add
          (x.1.2.1, x.1.2.2) (y.1.2.1, y.1.2.2))
    · apply Subtype.ext
      rfl
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg
        (fun q => q.1.1)
        ((diamondEvenPBWPointedEquiv hn ha2).map_smul
          r (x.1.2.1, x.1.2.2))
    · apply Subtype.ext
      rfl

theorem diamondEvenPCrossProjection_surjective
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Function.Surjective
      (diamondEvenPCrossProjection
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2) := by
  rintro ⟨l, A⟩
  rcases A.2 with ⟨K, hK⟩
  let e :=
    diamondEvenPBWPointedEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  let coords :
      (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d :=
    ((l.1, K), 0)
  let BW := e.symm coords
  have he : e BW = coords := e.apply_symm_apply coords
  have hsigma : (e BW).1.1 = l.1 :=
    congrArg (fun q => q.1.1) he
  have hKread : (e BW).1.2 = K :=
    congrArg (fun q => q.1.2) he
  have htail : (e BW).2 = 0 :=
    congrArg (fun q => q.2) he
  have hsigmaRead :
      (diamondEvenPBSigma BW.1, diamondEvenPWSigma BW.2) = l.1 := by
    calc
      _ = (e BW).1.1 := by
        symm
        exact diamondEvenPBWPointedEquiv_apply_sigma hn ha2 BW.1 BW.2
      _ = l.1 := hsigma
  have hKRead :
      (diamondEvenPBK BW.1, diamondEvenPWK BW.2) = K := by
    calc
      _ = (e BW).1.2 := by
        symm
        exact diamondEvenPBWPointedEquiv_apply_K hn ha2 BW.1 BW.2
      _ = K := hKread
  have htailRead :
      ∀ t : PointedTail (PVec n a) (zeroVec : PVec n a),
        (diamondEvenPBTail BW.1 t, diamondEvenPWTail BW.2 t) = 0 := by
    intro t
    calc
      _ = (e BW).2.1 t := by
        symm
        exact diamondEvenPBWPointedEquiv_apply_tail hn ha2 BW.1 BW.2 t
      _ = 0 := by
        have ht := congrArg (fun u => u.1 t) htail
        simpa only [Submodule.coe_zero, Pi.zero_apply] using ht
  have hsource :
      diamondPreCMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (A.1, BW.1, BW.2) = 0 := by
    apply
      (diamondEvenP_source_equations_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 A.1 BW.1 BW.2).2
    refine ⟨?_, ?_, ?_⟩
    · rw [hsigmaRead]
      exact LinearMap.mem_ker.mp l.2
    · rw [hKRead]
      exact hK.symm
    · intro t
      rw [htailRead t]
      exact LinearMap.map_zero _
  let x : DiamondPreCSource n a b c d :=
    ⟨(A.1, BW.1, BW.2), LinearMap.mem_ker.mpr hsource⟩
  refine ⟨x, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    exact hsigma
  · apply Subtype.ext
    rfl

theorem diamondEvenPCrossProjection_phase
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (x : DiamondPreCSource n a b c d) :
    diamondPreCQ x =
      diamondEvenPCrossQ
        (diamondEvenPCrossProjection
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2 x) := by
  rw [diamondEvenP_q_reads_sigma_only hn ha2]
  rfl

noncomputable abbrev DiamondEvenPTailIndex
    (n a : Nat) [NeZero n] :=
  PointedTail (PVec n a) (zeroVec : PVec n a)

theorem diamondEvenPTailIndex_nonempty
    {n a : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Nonempty (DiamondEvenPTailIndex n a) := by
  let i0 : Fin (a - 1) := ⟨0, by omega⟩
  let p : PVec n a := fun i => if i = i0 then 1 else 0
  refine ⟨⟨p, ?_⟩⟩
  intro hp
  have hp0 := congrFun hp i0
  have hn2 : 2 ≤ n := by
    rcases hn with ⟨k, hk⟩
    have hnpos : 0 < n :=
      Nat.pos_of_ne_zero (NeZero.ne n)
    omega
  letI : Fact (1 < n) := ⟨by omega⟩
  simp [p, i0, zeroVec] at hp0

noncomputable local instance instFintypeDiamondPreCSource
    {n a b c d : Nat} [NeZero n] :
    Fintype (DiamondPreCSource n a b c d) :=
  Fintype.ofInjective
    (fun x : DiamondPreCSource n a b c d => x.1)
    Subtype.val_injective

noncomputable local instance instFintypeDiamondEvenPLeft
    {n b c d : Nat} [NeZero n] :
    Fintype (DiamondEvenPLeft n b c d) :=
  Fintype.ofInjective
    (fun x : DiamondEvenPLeft n b c d => x.1)
    Subtype.val_injective

noncomputable local instance instFintypeDiamondEvenPReachableA
    {n b c d : Nat} [NeZero n] :
    Fintype (DiamondEvenPReachableA n b c d) :=
  Fintype.ofInjective
    (fun x : DiamondEvenPReachableA n b c d => x.1)
    Subtype.val_injective

noncomputable abbrev DiamondEvenPLeftTailZero
    (n a b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (fintypeSumLinearMap
      (S := DiamondEvenPTailIndex n a)
      (V := DiamondEvenPLeft n b c d))

private noncomputable def diamondEvenPCrossProjectionKernelRead
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    LinearMap.ker
        (diamondEvenPCrossProjection
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2) →ₗ[F]
      (DiamondEvenPLeft n b c d ×
        DiamondEvenPLeftTailZero n a b c d) where
  toFun x := by
    let e :=
      diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
    let q := e (x.1.1.2.1, x.1.1.2.2)
    have hproj :=
      LinearMap.mem_ker.mp x.2
    have hA0 : x.1.1.1 = 0 := by
      have h := congrArg (fun z => z.2.1) hproj
      change x.1.1.1 = (0 : AFun4 n b c d) at h
      exact h
    have hs :=
      (diamondEvenP_source_equations_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 x.1.1.1 x.1.1.2.1 x.1.1.2.2).mp
        (LinearMap.mem_ker.mp x.1.2)
    have hK :
        squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)
            q.1.2 = 0 := by
      simpa only [q, diamondEvenPBWPointedEquiv_apply_K,
        hA0, LinearMap.map_zero] using hs.2.1.symm
    have hTail :
        ∀ t : DiamondEvenPTailIndex n a,
          squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d)
              (q.2.1 t) = 0 := by
      intro t
      simpa only [q, diamondEvenPBWPointedEquiv_apply_tail] using hs.2.2 t
    let tailLeft : DiamondEvenPTailIndex n a →
        DiamondEvenPLeft n b c d :=
      fun t => ⟨q.2.1 t, hTail t⟩
    have hsum : fintypeSumLinearMap tailLeft = 0 := by
      change (∑ t, tailLeft t) = 0
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change (∑ t, q.2.1 t) = 0
      exact LinearMap.mem_ker.mp q.2.2
    exact
      (⟨q.1.2, hK⟩,
        ⟨tailLeft, LinearMap.mem_ker.mpr hsum⟩)
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg
        (fun q => q.1.2)
        ((diamondEvenPBWPointedEquiv hn ha2).map_add
          (x.1.1.2.1, x.1.1.2.2) (y.1.1.2.1, y.1.1.2.2))
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg
        (fun q => q.2.1 t)
        ((diamondEvenPBWPointedEquiv hn ha2).map_add
          (x.1.1.2.1, x.1.1.2.2) (y.1.1.2.1, y.1.1.2.2))
  map_smul' r x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg
        (fun q => q.1.2)
        ((diamondEvenPBWPointedEquiv hn ha2).map_smul
          r (x.1.1.2.1, x.1.1.2.2))
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrArg
        (fun q => q.2.1 t)
        ((diamondEvenPBWPointedEquiv hn ha2).map_smul
          r (x.1.1.2.1, x.1.1.2.2))

private theorem diamondEvenPCrossProjectionKernelRead_injective
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Function.Injective
      (diamondEvenPCrossProjectionKernelRead
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2) := by
  intro x y hxy
  have hxproj :=
    LinearMap.mem_ker.mp x.2
  have hyproj :=
    LinearMap.mem_ker.mp y.2
  have hxSigma0 :
      (diamondEvenPBWPointedEquiv hn ha2
        (x.1.1.2.1, x.1.1.2.2)).1.1 = 0 := by
    have h := congrArg (fun z => z.1.1) hxproj
    change
      (diamondEvenPBWPointedEquiv hn ha2
        (x.1.1.2.1, x.1.1.2.2)).1.1 =
          (0 : DiamondEvenPBWSlice n b c d) at h
    exact h
  have hySigma0 :
      (diamondEvenPBWPointedEquiv hn ha2
        (y.1.1.2.1, y.1.1.2.2)).1.1 = 0 := by
    have h := congrArg (fun z => z.1.1) hyproj
    change
      (diamondEvenPBWPointedEquiv hn ha2
        (y.1.1.2.1, y.1.1.2.2)).1.1 =
          (0 : DiamondEvenPBWSlice n b c d) at h
    exact h
  have hxA0 : x.1.1.1 = 0 := by
    have h := congrArg (fun z => z.2.1) hxproj
    change x.1.1.1 = (0 : AFun4 n b c d) at h
    exact h
  have hyA0 : y.1.1.1 = 0 := by
    have h := congrArg (fun z => z.2.1) hyproj
    change y.1.1.1 = (0 : AFun4 n b c d) at h
    exact h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hxA0.trans hyA0.symm
  · apply (diamondEvenPBWPointedEquiv hn ha2).injective
    apply Prod.ext
    · apply Prod.ext
      · exact hxSigma0.trans hySigma0.symm
      · exact congrArg (fun z => z.1.1) hxy
    · apply Subtype.ext
      funext t
      exact congrArg (fun z => (z.2.1 t).1) hxy

private theorem diamondEvenPCrossProjectionKernelRead_surjective
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Function.Surjective
      (diamondEvenPCrossProjectionKernelRead
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2) := by
  rintro ⟨K, tail⟩
  have hleftSum :
      (∑ t : DiamondEvenPTailIndex n a, tail.1 t) = 0 :=
    LinearMap.mem_ker.mp tail.2
  have hrawSum :
      (∑ t : DiamondEvenPTailIndex n a, (tail.1 t).1) = 0 := by
    have h := congrArg Subtype.val hleftSum
    rw [Submodule.coe_sum] at h
    exact h
  let rawTailZero : DiamondEvenPBWTailZero n a b c d :=
    ⟨fun t => (tail.1 t).1, by
      change (∑ t : DiamondEvenPTailIndex n a, (tail.1 t).1) = 0
      exact hrawSum⟩
  let e :=
    diamondEvenPBWPointedEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  let coords :
      (DiamondEvenPBWSlice n b c d ×
        DiamondEvenPBWSlice n b c d) ×
          DiamondEvenPBWTailZero n a b c d :=
    ((0, K.1), rawTailZero)
  let BW := e.symm coords
  have he : e BW = coords := e.apply_symm_apply coords
  have hsigma : (e BW).1.1 = 0 :=
    congrArg (fun q => q.1.1) he
  have hKread : (e BW).1.2 = K.1 :=
    congrArg (fun q => q.1.2) he
  have htailread :
      ∀ t : DiamondEvenPTailIndex n a,
        (e BW).2.1 t = (tail.1 t).1 := by
    intro t
    exact congrArg (fun q => q.2.1 t) he
  have hsigmaRead :
      (diamondEvenPBSigma BW.1, diamondEvenPWSigma BW.2) = 0 := by
    calc
      _ = (e BW).1.1 := by
        symm
        exact diamondEvenPBWPointedEquiv_apply_sigma hn ha2 BW.1 BW.2
      _ = 0 := hsigma
  have hKRead :
      (diamondEvenPBK BW.1, diamondEvenPWK BW.2) = K.1 := by
    calc
      _ = (e BW).1.2 := by
        symm
        exact diamondEvenPBWPointedEquiv_apply_K hn ha2 BW.1 BW.2
      _ = K.1 := hKread
  have htailRead :
      ∀ t : DiamondEvenPTailIndex n a,
        (diamondEvenPBTail BW.1 t, diamondEvenPWTail BW.2 t) =
          (tail.1 t).1 := by
    intro t
    calc
      _ = (e BW).2.1 t := by
        symm
        exact diamondEvenPBWPointedEquiv_apply_tail hn ha2 BW.1 BW.2 t
      _ = (tail.1 t).1 := htailread t
  have hsource :
      diamondPreCMap
          (n := n) (a := a) (b := b) (c := c) (d := d)
          (0, BW.1, BW.2) = 0 := by
    apply
      (diamondEvenP_source_equations_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 0 BW.1 BW.2).2
    refine ⟨?_, ?_, ?_⟩
    · rw [hsigmaRead]
      exact LinearMap.map_zero _
    · rw [hKRead, LinearMap.map_zero]
      exact (LinearMap.mem_ker.mp K.2).symm
    · intro t
      rw [htailRead t]
      exact LinearMap.mem_ker.mp (tail.1 t).2
  let x : DiamondPreCSource n a b c d :=
    ⟨(0, BW.1, BW.2), LinearMap.mem_ker.mpr hsource⟩
  have hprojection :
      diamondEvenPCrossProjection
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2 x = 0 := by
    apply Prod.ext
    · apply Subtype.ext
      exact hsigma
    · apply Subtype.ext
      rfl
  let xker :
      LinearMap.ker
        (diamondEvenPCrossProjection
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2) :=
    ⟨x, LinearMap.mem_ker.mpr hprojection⟩
  refine ⟨xker, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    exact hKread
  · apply Subtype.ext
    funext t
    apply Subtype.ext
    exact htailread t

noncomputable def diamondEvenPCrossProjectionKernelEquiv
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    LinearMap.ker
        (diamondEvenPCrossProjection
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2) ≃ₗ[F]
      (DiamondEvenPLeft n b c d ×
        DiamondEvenPLeftTailZero n a b c d) :=
  LinearEquiv.ofBijective
    (diamondEvenPCrossProjectionKernelRead
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2)
    ⟨diamondEvenPCrossProjectionKernelRead_injective hn ha2,
      diamondEvenPCrossProjectionKernelRead_surjective hn ha2⟩

set_option maxHeartbeats 4000000 in
-- Product and kernel finranks require a larger elaboration budget here.
set_option synthInstance.maxHeartbeats 500000 in
-- The nested finite-dimensional submodules need deeper instance search.
theorem finrank_ker_diamondEvenPCrossProjection_add
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Module.finrank F
        (LinearMap.ker
          (diamondEvenPCrossProjection
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hn ha2)) +
      Module.finrank F (DiamondEvenPLeft n b c d) =
        n ^ (a - 1) *
          Module.finrank F (DiamondEvenPLeft n b c d) := by
  letI : Nonempty (DiamondEvenPTailIndex n a) :=
    diamondEvenPTailIndex_nonempty hn ha2
  have hequiv :=
    LinearEquiv.finrank_eq
      (diamondEvenPCrossProjectionKernelEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2)
  rw [Module.finrank_prod] at hequiv
  have htail :=
    finrank_ker_fintype_sum
      (S := DiamondEvenPTailIndex n a)
      (V := DiamondEvenPLeft n b c d)
  have hnpos : 0 < n :=
    Nat.pos_of_ne_zero (NeZero.ne n)
  have hpowpos : 0 < n ^ (a - 1) :=
    pow_pos hnpos _
  have hcard :
      Fintype.card (DiamondEvenPTailIndex n a) + 1 =
        n ^ (a - 1) := by
    have htailNatCard :
        Nat.card (PointedTail (PVec n a) (zeroVec : PVec n a)) =
          Nat.card (PVec n a) - 1 := by
      simpa only [← Nat.card_eq_fintype_card] using
        (card_pointedTail (zeroVec : PVec n a))
    have htailCard :
        Fintype.card (DiamondEvenPTailIndex n a) =
          Fintype.card (PVec n a) - 1 := by
      calc
        Fintype.card (DiamondEvenPTailIndex n a) =
            Nat.card (DiamondEvenPTailIndex n a) :=
          Nat.card_eq_fintype_card.symm
        _ = Nat.card (PVec n a) - 1 := by
          simpa only [DiamondEvenPTailIndex] using htailNatCard
        _ = Fintype.card (PVec n a) - 1 := by
          rw [Nat.card_eq_fintype_card]
    rw [htailCard, card_vec]
    omega
  calc
    Module.finrank F
          (LinearMap.ker
            (diamondEvenPCrossProjection
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hn ha2)) +
        Module.finrank F (DiamondEvenPLeft n b c d) =
      (Module.finrank F (DiamondEvenPLeft n b c d) +
          Module.finrank F (DiamondEvenPLeftTailZero n a b c d)) +
        Module.finrank F (DiamondEvenPLeft n b c d) := by
          rw [hequiv]
    _ =
      Module.finrank F (DiamondEvenPLeft n b c d) +
        (Module.finrank F (DiamondEvenPLeftTailZero n a b c d) +
          Module.finrank F (DiamondEvenPLeft n b c d)) := by
            omega
    _ =
      Module.finrank F (DiamondEvenPLeft n b c d) +
        Fintype.card (DiamondEvenPTailIndex n a) *
          Module.finrank F (DiamondEvenPLeft n b c d) := by
            rw [htail]
    _ =
      (Fintype.card (DiamondEvenPTailIndex n a) + 1) *
        Module.finrank F (DiamondEvenPLeft n b c d) := by
          ring
    _ = n ^ (a - 1) *
        Module.finrank F (DiamondEvenPLeft n b c d) := by
          rw [hcard]

set_option synthInstance.maxHeartbeats 500000 in
-- Reusing the kernel-rank endpoint still elaborates its nested submodules.
theorem finrank_ker_diamondEvenPCrossProjection
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Module.finrank F
        (LinearMap.ker
          (diamondEvenPCrossProjection
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hn ha2)) =
      (n ^ (a - 1) - 1) *
        Module.finrank F (DiamondEvenPLeft n b c d) := by
  have hadd :=
    finrank_ker_diamondEvenPCrossProjection_add
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn ha2
  calc
    Module.finrank F
        (LinearMap.ker
          (diamondEvenPCrossProjection
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hn ha2)) =
      n ^ (a - 1) *
          Module.finrank F (DiamondEvenPLeft n b c d) -
        Module.finrank F (DiamondEvenPLeft n b c d) :=
          Nat.eq_sub_of_add_eq hadd
    _ =
      (n ^ (a - 1) - 1) *
        Module.finrank F (DiamondEvenPLeft n b c d) := by
          rw [Nat.sub_mul]
          simp

noncomputable def linearMapFiberEquivKerOfPreimageNoChoice
    {V W : Type*}
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]
    (L : V →ₗ[F] W) (target : W)
    (x0 : V) (hx0 : L x0 = target) :
    {x : V // L x = target} ≃ LinearMap.ker L where
  toFun x :=
    ⟨x.1 - x0, by
      rw [LinearMap.mem_ker, map_sub, x.2, hx0, sub_self]⟩
  invFun k :=
    ⟨k.1 + x0, by
      rw [map_add, LinearMap.mem_ker.mp k.2, hx0, zero_add]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv k := by
    apply Subtype.ext
    simp

theorem diamondEvenPCrossProjection_fiber_natCard
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (z : DiamondEvenPLeft n b c d ×
      DiamondEvenPReachableA n b c d) :
    Nat.card
        {x : DiamondPreCSource n a b c d //
          diamondEvenPCrossProjection
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hn ha2 x = z} =
      Nat.card
        (LinearMap.ker
          (diamondEvenPCrossProjection
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hn ha2)) := by
  rcases
      diamondEvenPCrossProjection_surjective
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 z with
    ⟨x0, hx0⟩
  exact Nat.card_congr
    (linearMapFiberEquivKerOfPreimageNoChoice
      (diamondEvenPCrossProjection
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2)
      z x0 hx0)

set_option linter.unusedDecidableInType false in
theorem sum_comp_surjective_linearMap_eq_natCard_ker_mul
    {V W : Type*}
    [AddCommGroup V] [Module F V] [Fintype V]
    [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]
    (L : V →ₗ[F] W) (hL : Function.Surjective L)
    (g : W → Int) :
    (∑ x : V, g (L x)) =
      (Nat.card (LinearMap.ker L) : Int) * ∑ y : W, g y := by
  classical
  letI : Fintype (LinearMap.ker L) :=
    Fintype.ofInjective
      (fun x : LinearMap.ker L => x.1)
      Subtype.val_injective
  calc
    (∑ x : V, g (L x)) =
        ∑ y : W, ∑ x : {x : V // L x = y}, g (L x.1) := by
      symm
      exact Fintype.sum_fiberwise L (fun x : V => g (L x))
    _ = ∑ y : W,
        (Nat.card (LinearMap.ker L) : Int) * g y := by
      refine Finset.sum_congr rfl ?_
      intro y _
      rcases hL y with ⟨x0, hx0⟩
      have hcard :
          Fintype.card {x : V // L x = y} =
            Nat.card (LinearMap.ker L) := by
        calc
          Fintype.card {x : V // L x = y} =
              Fintype.card (LinearMap.ker L) :=
            Fintype.card_congr
              (linearMapFiberEquivKerOfPreimageNoChoice L y x0 hx0)
          _ = Nat.card (LinearMap.ker L) :=
            Nat.card_eq_fintype_card.symm
      calc
        (∑ x : {x : V // L x = y}, g (L x.1)) =
            ∑ _x : {x : V // L x = y}, g y := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [x.2]
        _ = (Fintype.card {x : V // L x = y} : Int) * g y := by
          simp
        _ = (Nat.card (LinearMap.ker L) : Int) * g y := by
          rw [hcard]
    _ = (Nat.card (LinearMap.ker L) : Int) * ∑ y : W, g y := by
      rw [Finset.mul_sum]

theorem diamondEvenP_sum_eq_kerCard_mul_crossSum
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    (∑ x : DiamondPreCSource n a b c d,
        bitSign (diamondPreCQ x)) =
      (Nat.card
          (LinearMap.ker
            (diamondEvenPCrossProjection
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hn ha2)) : Int) *
        ∑ z :
            DiamondEvenPLeft n b c d ×
              DiamondEvenPReachableA n b c d,
          bitSign (diamondEvenPCrossQ z) := by
  classical
  calc
    (∑ x : DiamondPreCSource n a b c d,
        bitSign (diamondPreCQ x)) =
      ∑ x : DiamondPreCSource n a b c d,
        bitSign
          (diamondEvenPCrossQ
            (diamondEvenPCrossProjection hn ha2 x)) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [diamondEvenPCrossProjection_phase hn ha2]
    _ = _ :=
      sum_comp_surjective_linearMap_eq_natCard_ker_mul
        (V := DiamondPreCSource n a b c d)
        (W :=
          DiamondEvenPLeft n b c d ×
            DiamondEvenPReachableA n b c d)
        (diamondEvenPCrossProjection
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2)
        (diamondEvenPCrossProjection_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d)
          hn ha2)
        (fun z => bitSign (diamondEvenPCrossQ z))

set_option maxHeartbeats 4000000 in
-- The generic finite-module cardinality theorem expands the nested kernel.
set_option synthInstance.maxHeartbeats 500000 in
-- The kernel's finite/free module instances require deeper search.
private theorem natCard_ker_diamondEvenPCrossProjection
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    Nat.card
        (LinearMap.ker
          (diamondEvenPCrossProjection
            (n := n) (a := a) (b := b) (c := c) (d := d)
            hn ha2)) =
      2 ^
        Module.finrank F
          (LinearMap.ker
            (diamondEvenPCrossProjection
              (n := n) (a := a) (b := b) (c := c) (d := d)
              hn ha2)) := by
  rw [Module.natCard_eq_pow_finrank (K := F)]
  simp [F]

set_option synthInstance.maxHeartbeats 500000 in
-- The terminal rewrite elaborates both nested finite signed sums.
theorem diamondEvenP_sum_eq_phaseFree_mul_crossSum
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a) :
    (∑ x : DiamondPreCSource n a b c d,
        bitSign (diamondPreCQ x)) =
      (2 : Int) ^
          ((n ^ (a - 1) - 1) *
            Module.finrank F (DiamondEvenPLeft n b c d)) *
        ∑ z :
            DiamondEvenPLeft n b c d ×
              DiamondEvenPReachableA n b c d,
          bitSign (diamondEvenPCrossQ z) := by
  rw [diamondEvenP_sum_eq_kerCard_mul_crossSum hn ha2]
  rw [natCard_ker_diamondEvenPCrossProjection hn ha2,
    finrank_ker_diamondEvenPCrossProjection hn ha2]
  norm_num

end

end Core4loop.SquareDiagonal.EvenP
