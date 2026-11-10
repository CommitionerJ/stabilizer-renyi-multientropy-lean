import Core4loop.SquareDiagonal.BWQuadratic

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

abbrev sqdiagBWAAdjointGraphRootZero
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagBWAAdjointGraph n a b c d) :=
  LinearMap.ker
    (sqdiagBWAAdjointGraphRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable instance instFintypeSqdiagBWAAdjointGraphRootZero
    {n a b c d : ℕ} [NeZero n] :
    Fintype (sqdiagBWAAdjointGraphRootZero n a b c d) :=
  Fintype.ofInjective
    (fun x : sqdiagBWAAdjointGraphRootZero n a b c d =>
      (x : SqdiagBWAAdjointGraph n a b c d))
    (by
      intro x y hxy
      exact Subtype.ext hxy)

noncomputable def sqdiagBWAAdjointGraphPolarToRootZero
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZero n a b c d) where
  toFun x :=
    (sqdiagBWAAdjointGraphPolar
      (n := n) (a := a) (b := b) (c := c) (d := d) x).comp
      (sqdiagBWAAdjointGraphRootZero n a b c d).subtype
  map_add' x y := by
    ext z
    change
      sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) (x + y) z.1 =
        sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x z.1 +
        sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) y z.1
    exact
      congrArg
        (fun L : SqdiagBWAAdjointGraph n a b c d →ₗ[F] F => L z.1)
        ((sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x y)
  map_smul' r x := by
    ext z
    change
      sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) (r • x) z.1 =
        r •
          sqdiagBWAAdjointGraphPolar
            (n := n) (a := a) (b := b) (c := c) (d := d) x z.1
    exact
      congrArg
        (fun L : SqdiagBWAAdjointGraph n a b c d →ₗ[F] F => L z.1)
        ((sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x)

abbrev sqdiagBWAAdjointGraphLagrangian
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (SqdiagBWAAdjointGraph n a b c d) :=
  LinearMap.ker
    (sqdiagBWAAdjointGraphPolarToRootZero
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable instance instFintypeSqdiagBWAAdjointGraphLagrangian
    {n a b c d : ℕ} [NeZero n] :
    Fintype (sqdiagBWAAdjointGraphLagrangian n a b c d) :=
  Fintype.ofInjective
    (fun x : sqdiagBWAAdjointGraphLagrangian n a b c d =>
      (x : SqdiagBWAAdjointGraph n a b c d))
    (by
      intro x y hxy
      exact Subtype.ext hxy)

lemma sqdiagBWAAdjointGraphQ_eq_zero_of_mem_rootZero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphRootZero n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  have hxroot :
      sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
    LinearMap.mem_ker.mp hx
  simp [sqdiagBWAAdjointGraphQ, hxroot, sqdiagRootCoeffApply]

lemma sqdiagBWAAdjointGraphRootZero_le_lagrangian
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootZero n a b c d ≤
      sqdiagBWAAdjointGraphLagrangian n a b c d := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  have hxroot :
      sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
    LinearMap.mem_ker.mp hx
  have hyroot :
      sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1 = 0 :=
    LinearMap.mem_ker.mp y.2
  change
    sqdiagRootCoeffApply
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x)
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1) +
      sqdiagRootCoeffApply
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1)
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x) = 0
  rw [hxroot, hyroot]
  simp [sqdiagRootCoeffApply]

theorem sqdiagBWAAdjointGraph_rootZero_phaseWitness_of_compat_same_root
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d)
    (t : sqdiagBWZCompatSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))
    (ht :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) t.1 =
        sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x) :
    ∃ y : sqdiagBWAAdjointGraphRootZero n a b c d,
      sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 =
        sqdiagBWAAdjointGraphQ x := by
  have hxGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2
  have htCompat :
      sqdiagBWZCompatSupportPred
        (n := n) (a := a) (b := b) (c := c) (d := d) t.1 :=
    (sqdiagBWZCompatSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) t.1).mp t.2
  let src : BFun4 n a c d × WFun4 n a b c :=
    (x.1.1.1 + t.1.1, x.1.1.2 + t.1.2)
  have hKsrc :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) src =
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 +
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d) t.1 := by
    change
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d)
          (x.1.1.1 + t.1.1, x.1.1.2 + t.1.2) =
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 +
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d) t.1
    rw [← Prod.mk_add_mk]
    exact
      (K_yw (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1.1 t.1
  have hsquaresrc :
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) src =
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 +
          squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) t.1 := by
    change
      squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)
          (x.1.1.1 + t.1.1, x.1.1.2 + t.1.2) =
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 +
          squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) t.1
    rw [← Prod.mk_add_mk]
    exact
      (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1.1 t.1
  let yRaw :
      (BFun4 n a c d × WFun4 n a b c) × RootTarget n b c d :=
    (src, x.1.2)
  have hyGraph :
      yRaw ∈
        sqdiagBWAAdjointGraphSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
    constructor
    · change
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) src ∈
          ZDiffSpace (n := n) (b := b) (c := c) (d := d)
      rw [hKsrc]
      exact
        (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).add_mem
          hxGraph.1 htCompat.1
    · have hxphase :
          squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 =
            sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2 := by
        simpa [sqdiagCPhaseCoeff] using hxGraph.2
      change
        squareCompat (n := n) (a := a) (b := b) (c := c) (d := d) src =
          sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2
      rw [hsquaresrc, htCompat.2, add_zero]
      exact hxphase
  let yGraph : SqdiagBWAAdjointGraph n a b c d := ⟨yRaw, hyGraph⟩
  have hyRoot :
      sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) yGraph = 0 := by
    change
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) src = 0
    rw [hKsrc]
    rw [ht, sqdiagBWAAdjointGraphRootMap_apply]
    exact (add_eq_zero_iff_eq_of_F_module _ _).mpr rfl
  let yRootZero : sqdiagBWAAdjointGraphRootZero n a b c d :=
    ⟨yGraph, LinearMap.mem_ker.mpr hyRoot⟩
  refine ⟨yRootZero, ?_⟩
  have hyRoot' :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) yGraph.1.1 = 0 := by
    simpa [sqdiagBWAAdjointGraphRootMap_apply] using hyRoot
  simp [sqdiagBWAAdjointGraphQ, yRootZero, yGraph, yRaw, hyRoot',
    sqdiagRootCoeffApply]

theorem sqdiagBWAAdjointGraph_lagrangian_selfDual_of_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hQzero :
      ∀ x : SqdiagBWAAdjointGraph n a b c d,
        x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d →
          sqdiagBWAAdjointGraphQ x = 0)
    (x : SqdiagBWAAdjointGraph n a b c d) :
    ((sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x).comp
        (sqdiagBWAAdjointGraphLagrangian n a b c d).subtype = 0) ↔
      x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d := by
  constructor
  · intro horth
    rw [LinearMap.mem_ker]
    ext y
    have hyL :
        (y.1 : SqdiagBWAAdjointGraph n a b c d) ∈
          sqdiagBWAAdjointGraphLagrangian n a b c d :=
      sqdiagBWAAdjointGraphRootZero_le_lagrangian
        (n := n) (a := a) (b := b) (c := c) (d := d) y.2
    have happly :=
      congrArg
        (fun L : sqdiagBWAAdjointGraphLagrangian n a b c d →ₗ[F] F =>
          L ⟨y.1, hyL⟩)
        horth
    simpa using happly
  · intro hx
    ext y
    have hy := y.2
    have hxy :
        x + y.1 ∈ sqdiagBWAAdjointGraphLagrangian n a b c d :=
      (sqdiagBWAAdjointGraphLagrangian n a b c d).add_mem hx hy
    have hadd :=
      sqdiagBWAAdjointGraphQ_add
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1
    rw [hQzero (x + y.1) hxy, hQzero x hx, hQzero y.1 hy] at hadd
    simpa using hadd.symm

theorem sqdiagBWAAdjointGraphRootSignSum_eq_lagrangian_card_of_Q_zero
    {n a b c d : ℕ} [NeZero n]
    (hQzero :
      ∀ x : SqdiagBWAAdjointGraph n a b c d,
        x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d →
          sqdiagBWAAdjointGraphQ x = 0) :
    sqdiagBWAAdjointGraphRootSignSum
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
  let hLFintype : Fintype (sqdiagBWAAdjointGraphLagrangian n a b c d) :=
    Fintype.ofInjective
      (fun x : sqdiagBWAAdjointGraphLagrangian n a b c d =>
        (x : SqdiagBWAAdjointGraph n a b c d))
      (by
        intro x y hxy
        exact Subtype.ext hxy)
  letI : Fintype (sqdiagBWAAdjointGraphLagrangian n a b c d) := hLFintype
  rw [sqdiagBWAAdjointGraphRootSignSum_eq_submodule_sum]
  have hsum :=
    @sum_bitSign_eq_card_of_selfDual_isotropic
      (SqdiagBWAAdjointGraph n a b c d) _ _ _
      (sqdiagBWAAdjointGraphQ
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (sqdiagBWAAdjointGraphQ_add
        (n := n) (a := a) (b := b) (c := c) (d := d))
      (sqdiagBWAAdjointGraphLagrangian n a b c d)
      hLFintype
      (fun x =>
        hQzero x.1 x.2)
      (sqdiagBWAAdjointGraph_lagrangian_selfDual_of_Q_zero
        (n := n) (a := a) (b := b) (c := c) (d := d) hQzero)
  have hcard :
      (Nat.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) =
        (Fintype.card (sqdiagBWAAdjointGraphLagrangian n a b c d) : ℤ) := by
    exact_mod_cast
      (@Nat.card_eq_fintype_card
        (sqdiagBWAAdjointGraphLagrangian n a b c d) hLFintype)
  rw [hcard]
  exact hsum

end

end SquareDiagonal
end Core4loop
