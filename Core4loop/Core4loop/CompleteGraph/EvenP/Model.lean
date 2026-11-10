import Core4loop.CompleteGraph.EvenP.AddedPhase

set_option autoImplicit false
set_option warningAsError true
set_option synthInstance.maxSize 512

open scoped BigOperators

namespace Core4loop.CompleteGraph.EvenP

open Core4loop
open Core4loop.SquareDiagonal.EvenP

noncomputable section

attribute [local instance] Fintype.ofFinite

/-! ## Frozen Base/Tail model definitions -/

abbrev K4EvenPSlice (n b c d : Nat) :=
  DiamondEvenPBWSlice n b c d

noncomputable abbrev K4EvenPLeft (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (squareCompat (n := n) (a := 1) (b := b) (c := c) (d := d))

noncomputable def k4EvenPBaseRightMap
    {n b c d : Nat} [NeZero n] :
    (AFun4 n b c d × K4EvenPSlice n b c d) →ₗ[F]
      CFun4 n 1 b d where
  toFun x :=
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := b) (c := c) (d := d) x.1 +
      squareCompat
        (n := n) (a := 1) (b := b) (c := c) (d := d) x.2
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul,
      RingHom.id_apply, smul_add]

abbrev K4EvenPBaseRight (n b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (k4EvenPBaseRightMap (n := n) (b := b) (c := c) (d := d))

abbrev K4EvenPBase (n b c d : Nat) [NeZero n] :=
  K4EvenPLeft n b c d × K4EvenPBaseRight n b c d

noncomputable abbrev K4EvenPTailIndex (n a : Nat) [NeZero n] :=
  PointedTail (PVec n a) (zeroVec : PVec n a)

noncomputable abbrev K4EvenPTail (n a b c d : Nat) [NeZero n] :=
  LinearMap.ker
    (fintypeSumLinearMap
      (S := K4EvenPTailIndex n a)
      (V := K4EvenPLeft n b c d))

def k4EvenPSliceQ
    {n b c d : Nat} [NeZero n]
    (x : K4EvenPSlice n b c d) : F :=
  k4BWSlice x.1 x.2

def k4EvenPSlicePolar
    {n b c d : Nat} [NeZero n]
    (x y : K4EvenPSlice n b c d) : F :=
  k4BWSlice x.1 y.2 + k4BWSlice y.1 x.2

theorem k4EvenPSliceQ_add
    {n b c d : Nat} [NeZero n]
    (x y : K4EvenPSlice n b c d) :
    k4EvenPSliceQ (x + y) =
      k4EvenPSliceQ x + k4EvenPSliceQ y +
        k4EvenPSlicePolar x y := by
  simp only [k4EvenPSliceQ, k4EvenPSlicePolar,
    Prod.fst_add, Prod.snd_add]
  rw [k4BWSlice_add_left, k4BWSlice_add_right,
    k4BWSlice_add_right]
  abel

private theorem k4EvenP_F_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem k4EvenPSlicePolar_add_left
    {n b c d : Nat} [NeZero n]
    (x y z : K4EvenPSlice n b c d) :
    k4EvenPSlicePolar (x + y) z =
      k4EvenPSlicePolar x z + k4EvenPSlicePolar y z := by
  simp only [k4EvenPSlicePolar, Prod.fst_add, Prod.snd_add]
  rw [k4BWSlice_add_left, k4BWSlice_add_right]
  abel

private theorem k4EvenPSlicePolar_add_right
    {n b c d : Nat} [NeZero n]
    (x y z : K4EvenPSlice n b c d) :
    k4EvenPSlicePolar x (y + z) =
      k4EvenPSlicePolar x y + k4EvenPSlicePolar x z := by
  simp only [k4EvenPSlicePolar, Prod.fst_add, Prod.snd_add]
  rw [k4BWSlice_add_right, k4BWSlice_add_left]
  abel

private theorem k4EvenPSlicePolar_smul_left
    {n b c d : Nat} [NeZero n]
    (r : F) (x y : K4EvenPSlice n b c d) :
    k4EvenPSlicePolar (r • x) y =
      r * k4EvenPSlicePolar x y := by
  rcases k4EvenP_F_eq_zero_or_one r with rfl | rfl
  · simp [k4EvenPSlicePolar, k4BWSlice_zero_left,
      k4BWSlice_zero_right]
  · simp

private theorem k4EvenPSlicePolar_smul_right
    {n b c d : Nat} [NeZero n]
    (r : F) (x y : K4EvenPSlice n b c d) :
    k4EvenPSlicePolar x (r • y) =
      r * k4EvenPSlicePolar x y := by
  rcases k4EvenP_F_eq_zero_or_one r with rfl | rfl
  · simp [k4EvenPSlicePolar, k4BWSlice_zero_left,
      k4BWSlice_zero_right]
  · simp

noncomputable def k4EvenPGPolarAmbient
    {n b c d : Nat} [NeZero n] :
    K4EvenPSlice n b c d →ₗ[F]
      Module.Dual F (K4EvenPSlice n b c d) :=
  LinearMap.mk₂ F k4EvenPSlicePolar
    k4EvenPSlicePolar_add_left
    k4EvenPSlicePolar_smul_left
    k4EvenPSlicePolar_add_right
    k4EvenPSlicePolar_smul_right

noncomputable def k4EvenPGPolar
    {n b c d : Nat} [NeZero n] :
    K4EvenPLeft n b c d →ₗ[F]
      Module.Dual F (K4EvenPLeft n b c d) :=
  (LinearMap.dualMap (K4EvenPLeft n b c d).subtype).comp
    (k4EvenPGPolarAmbient.comp (K4EvenPLeft n b c d).subtype)

def k4EvenPBaseCrossScalar
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d)
    (r : K4EvenPBaseRight n b c d) : F :=
  coeffApplyA
      (KBMap
          (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.1 +
        KWMap
          (n := n) (a := 1) (b := b) (c := c) (d := d) sigma.1.2)
      r.1.1 +
    k4EvenPSlicePolar sigma.1 r.1.2

noncomputable def k4EvenPBaseCross
    {n b c d : Nat} [NeZero n] :
    K4EvenPLeft n b c d →ₗ[F]
      Module.Dual F (K4EvenPBaseRight n b c d) :=
  LinearMap.mk₂ F k4EvenPBaseCrossScalar
    (by
      intro x y r
      simp only [k4EvenPBaseCrossScalar, Submodule.coe_add,
        Prod.fst_add, Prod.snd_add, map_add]
      rw [k4EvenPSlicePolar_add_left]
      simp only [coeffApplyA_eq_sum, Pi.add_apply, mul_add,
        Finset.sum_add_distrib]
      abel)
    (by
      intro a x r
      rcases k4EvenP_F_eq_zero_or_one a with rfl | rfl
      · simp [k4EvenPBaseCrossScalar, k4EvenPSlicePolar,
          k4BWSlice_zero_left, k4BWSlice_zero_right,
          coeffApplyA_eq_sum]
      · simp)
    (by
      intro sigma x y
      simp only [k4EvenPBaseCrossScalar, Submodule.coe_add,
        Prod.fst_add, Prod.snd_add]
      rw [k4EvenPSlicePolar_add_right]
      simp only [coeffApplyA_eq_sum, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]
      abel)
    (by
      intro a sigma r
      rcases k4EvenP_F_eq_zero_or_one a with rfl | rfl
      · simp [k4EvenPBaseCrossScalar, k4EvenPSlicePolar,
          k4BWSlice_zero_left, k4BWSlice_zero_right,
          coeffApplyA_eq_sum]
      · simp)

private theorem k4EvenPBaseCross_apply
    {n b c d : Nat} [NeZero n]
    (sigma : K4EvenPLeft n b c d)
    (r : K4EvenPBaseRight n b c d) :
    k4EvenPBaseCross sigma r = k4EvenPBaseCrossScalar sigma r := by
  rfl

def k4EvenPBaseQ
    {n b c d : Nat} [NeZero n]
    (x : K4EvenPBase n b c d) : F :=
  k4EvenPSliceQ x.1.1 + k4EvenPBaseCross x.1 x.2

def k4EvenPTailQ
    {n a b c d : Nat} [NeZero n]
    (U : K4EvenPTail n a b c d) : F :=
  ∑ t : K4EvenPTailIndex n a, k4EvenPSliceQ (U.1 t).1

/-! ## Exact tail forgetful map used by the source equivalence -/

private noncomputable def k4EvenPTailToRaw
    {n a b c d : Nat} [NeZero n] :
    K4EvenPTail n a b c d →ₗ[F]
      DiamondEvenPBWTailZero n a b c d where
  toFun U := ⟨fun t => (U.1 t).1, by
    apply LinearMap.mem_ker.mpr
    change (∑ t, (U.1 t).1) = 0
    have h := LinearMap.mem_ker.mp U.2
    change (∑ t, U.1 t) = 0 at h
    simpa only [Submodule.coe_sum, Submodule.coe_zero] using
      congrArg Subtype.val h⟩
  map_add' U V := by
    apply Subtype.ext
    rfl
  map_smul' r U := by
    apply Subtype.ext
    rfl

private noncomputable def k4EvenPModelCoords
    {n a b c d : Nat} [NeZero n] :
    (K4EvenPBase n b c d × K4EvenPTail n a b c d) →ₗ[F]
      ((K4EvenPSlice n b c d × K4EvenPSlice n b c d) ×
        DiamondEvenPBWTailZero n a b c d) where
  toFun z :=
    ((z.1.1.1, z.1.2.1.2), k4EvenPTailToRaw z.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-! ## Read/build maps for the strict source equivalence -/

private noncomputable def k4EvenPModelRead
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a) :
    K4PreCSource n a b c d →ₗ[F]
      (K4EvenPBase n b c d × K4EvenPTail n a b c d) where
  toFun x := by
    let e :=
      diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
    let q := e (x.1.2.1, x.1.2.2)
    have hsource :
        diamondPreCMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 = 0 := by
      rw [← k4PreCMap_eq_diamondPreCMap]
      exact LinearMap.mem_ker.mp x.2
    have hs :=
      (diamondEvenP_source_equations_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 x.1.1 x.1.2.1 x.1.2.2).mp hsource
    let tailLeft : K4EvenPTailIndex n a → K4EvenPLeft n b c d :=
      fun t => ⟨q.2.1 t, hs.2.2 t⟩
    refine
      ((⟨q.1.1, ?_⟩, ⟨(x.1.1, q.1.2), ?_⟩),
        ⟨tailLeft, ?_⟩)
    · simpa only [q, diamondEvenPBWPointedEquiv_apply_sigma] using hs.1
    · apply LinearMap.mem_ker.mpr
      change
        diamondEvenPAConstraint
              (n := n) (a := 1) (b := b) (c := c) (d := d) x.1.1 +
            squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d) q.1.2 = 0
      apply (add_eq_zero_iff_eq_of_F_module _ _).mpr
      simpa only [q, diamondEvenPBWPointedEquiv_apply_K] using hs.2.1
    · apply LinearMap.mem_ker.mpr
      change (∑ t, tailLeft t) = 0
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change (∑ t, q.2.1 t) = 0
      exact LinearMap.mem_ker.mp q.2.2
  map_add' x y := by
    let e :=
      diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
    have he := e.map_add
      (x.1.2.1, x.1.2.2) (y.1.2.1, y.1.2.2)
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) he
      · apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact congrArg (fun q => q.1.2) he
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrFun (congrArg (fun q => q.2.1) he) t
  map_smul' r x := by
    let e :=
      diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
    have he := e.map_smul r (x.1.2.1, x.1.2.2)
    apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        exact congrArg (fun q => q.1.1) he
      · apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact congrArg (fun q => q.1.2) he
    · apply Subtype.ext
      funext t
      apply Subtype.ext
      exact congrFun (congrArg (fun q => q.2.1) he) t

private noncomputable def k4EvenPModelBWBuild
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a) :
    (K4EvenPBase n b c d × K4EvenPTail n a b c d) →ₗ[F]
      (BFun4 n a c d × WFun4 n a b c) :=
  (diamondEvenPBWPointedEquiv
    (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2).symm.toLinearMap.comp
      k4EvenPModelCoords

private noncomputable def k4EvenPModelBuild
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a) :
    (K4EvenPBase n b c d × K4EvenPTail n a b c d) →ₗ[F]
      K4PreCSource n a b c d where
  toFun z := by
    let e :=
      diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
    let coords := k4EvenPModelCoords z
    let BW := e.symm coords
    have he : e BW = coords := e.apply_symm_apply coords
    refine ⟨(z.1.2.1.1, BW.1, BW.2), ?_⟩
    apply LinearMap.mem_ker.mpr
    rw [k4PreCMap_eq_diamondPreCMap]
    apply
      (diamondEvenP_source_equations_iff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 z.1.2.1.1 BW.1 BW.2).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [← diamondEvenPBWPointedEquiv_apply_sigma hn ha2 BW.1 BW.2]
      rw [show (e (BW.1, BW.2)).1.1 = z.1.1.1 from
        congrArg (fun q => q.1.1) he]
      exact LinearMap.mem_ker.mp z.1.1.2
    · rw [← diamondEvenPBWPointedEquiv_apply_K hn ha2 BW.1 BW.2]
      rw [show (e (BW.1, BW.2)).1.2 = z.1.2.1.2 from
        congrArg (fun q => q.1.2) he]
      have hr := LinearMap.mem_ker.mp z.1.2.2
      change
        diamondEvenPAConstraint
              (n := n) (a := 1) (b := b) (c := c) (d := d) z.1.2.1.1 +
            squareCompat
              (n := n) (a := 1) (b := b) (c := c) (d := d) z.1.2.1.2 = 0
        at hr
      exact (add_eq_zero_iff_eq_of_F_module _ _).mp hr
    · intro t
      rw [← diamondEvenPBWPointedEquiv_apply_tail hn ha2 BW.1 BW.2 t]
      rw [show (e (BW.1, BW.2)).2.1 t = (z.2.1 t).1 from
        congrFun (congrArg (fun q => q.2.1) he) t]
      exact LinearMap.mem_ker.mp (z.2.1 t).2
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (k4EvenPModelBWBuild hn ha2).map_add z w
  map_smul' r z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (k4EvenPModelBWBuild hn ha2).map_smul r z

private theorem k4EvenPModelBuild_read
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (x : K4PreCSource n a b c d) :
    k4EvenPModelBuild hn ha2 (k4EvenPModelRead hn ha2 x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · let e :=
      diamondEvenPBWPointedEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
    apply e.injective
    change
      e (k4EvenPModelBWBuild hn ha2 (k4EvenPModelRead hn ha2 x)) =
        e (x.1.2.1, x.1.2.2)
    rw [show
      k4EvenPModelBWBuild hn ha2 (k4EvenPModelRead hn ha2 x) =
        e.symm (k4EvenPModelCoords (k4EvenPModelRead hn ha2 x)) from rfl]
    rw [e.apply_symm_apply]
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · apply Subtype.ext
      rfl

private theorem k4EvenPModelRead_build
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (z : K4EvenPBase n b c d × K4EvenPTail n a b c d) :
    k4EvenPModelRead hn ha2 (k4EvenPModelBuild hn ha2 z) = z := by
  let e :=
    diamondEvenPBWPointedEquiv
      (n := n) (a := a) (b := b) (c := c) (d := d) hn ha2
  let coords := k4EvenPModelCoords z
  let BW := e.symm coords
  have he : e BW = coords := e.apply_symm_apply coords
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun q => q.1.1) he
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact congrArg (fun q => q.1.2) he
  · apply Subtype.ext
    funext t
    apply Subtype.ext
    exact congrFun (congrArg (fun q => q.2.1) he) t

/-! ## Frozen public Model owner contracts -/

noncomputable def k4EvenAllLargeSourceEquiv
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a) :
    K4PreCSource n a b c d ≃ₗ[F]
      (K4EvenPBase n b c d × K4EvenPTail n a b c d) where
  toLinearMap := k4EvenPModelRead hn ha2
  invFun := k4EvenPModelBuild hn ha2
  left_inv := k4EvenPModelBuild_read hn ha2
  right_inv := k4EvenPModelRead_build hn ha2

private theorem k4EvenAllLargeSourceEquiv_left_val
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (x : K4PreCSource n a b c d) :
    (k4EvenAllLargeSourceEquiv hn ha2 x).1.1.1 =
      (diamondEvenPBSigma x.1.2.1, diamondEvenPWSigma x.1.2.2) := by
  rfl

private theorem k4EvenAllLargeSourceEquiv_right_val
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (x : K4PreCSource n a b c d) :
    (k4EvenAllLargeSourceEquiv hn ha2 x).1.2.1 =
      (x.1.1, (diamondEvenPBK x.1.2.1, diamondEvenPWK x.1.2.2)) := by
  rfl

private theorem k4EvenAllLargeSourceEquiv_tail_val
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (x : K4PreCSource n a b c d)
    (t : K4EvenPTailIndex n a) :
    ((k4EvenAllLargeSourceEquiv hn ha2 x).2.1 t).1 =
      (diamondEvenPBTail x.1.2.1 t, diamondEvenPWTail x.1.2.2 t) := by
  rfl

theorem k4PreCQ_eq_base_add_tail
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 <= a)
    (x : K4PreCSource n a b c d) :
    k4PreCQ x =
      k4EvenPBaseQ (k4EvenAllLargeSourceEquiv hn ha2 x).1 +
        k4EvenPTailQ (k4EvenAllLargeSourceEquiv hn ha2 x).2 := by
  rw [k4PreCQ_evenP_pointed hn ha2]
  unfold k4EvenPBaseQ k4EvenPTailQ
  rw [k4EvenPBaseCross_apply]
  unfold k4EvenPBaseCrossScalar
  unfold k4EvenPSliceQ k4EvenPSlicePolar
  rw [k4EvenAllLargeSourceEquiv_left_val hn ha2 x]
  rw [k4EvenAllLargeSourceEquiv_right_val hn ha2 x]
  simp_rw [k4EvenAllLargeSourceEquiv_tail_val hn ha2 x]
  abel

end

end Core4loop.CompleteGraph.EvenP
