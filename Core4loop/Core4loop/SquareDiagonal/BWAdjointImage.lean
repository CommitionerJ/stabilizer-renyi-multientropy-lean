import Core4loop.SquareDiagonal.BWQuadraticMetabolic

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

abbrev SqdiagBWZAdjointImage
    (n a b c d : ℕ) [NeZero n] :=
  ↑(LinearMap.range
        (SquareCombined
          (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
      sqdiagZAdjointTargetSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def sqdiagBWAAdjointGraphToAdjointImage
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      SqdiagBWZAdjointImage n a b c d where
  toFun x :=
    ⟨SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1,
      by
        constructor
        · exact ⟨x.1.1, rfl⟩
        · apply (sqdiagZAdjointTargetSubmodule_mem_iff
            (n := n) (a := a) (b := b) (c := c) (d := d)
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1)).mpr
          have hxGraph :
              sqdiagBWAAdjointGraphPred
                (n := n) (a := a) (b := b) (c := c) (d := d) x.1 :=
            (sqdiagBWAAdjointGraphSubmodule_mem_iff
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2
          constructor
          · simpa [SquareCombined] using hxGraph.1
          · exact ⟨x.1.2, by
              simpa [SquareCombined, sqdiagCPhaseCoeff] using hxGraph.2.symm⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)).map_add
        x.1.1 y.1.1
  map_smul' r x := by
    apply Subtype.ext
    exact
      (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul
        r x.1.1

@[simp]
theorem sqdiagBWAAdjointGraphToAdjointImage_apply
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    (sqdiagBWAAdjointGraphToAdjointImage
      (n := n) (a := a) (b := b) (c := c) (d := d) x).1 =
      SquareCombined
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 := rfl

theorem sqdiagBWAAdjointGraphToAdjointImage_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWAAdjointGraphToAdjointImage
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro h
  rcases h.2.1 with ⟨u, hu⟩
  have htarget :=
    (sqdiagZAdjointTargetSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) h.1).mp h.2.2
  rcases htarget.2 with ⟨A, hA⟩
  have hGraph :
      (u, A) ∈
        sqdiagBWAAdjointGraphSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
    constructor
    · have hroot :
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) u).1 ∈
            ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
        simpa [hu] using htarget.1
      simpa [SquareCombined] using hroot
    · have hsquare :
          (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) u).2 =
            h.1.2 :=
        congrArg Prod.snd hu
      simpa [SquareCombined, sqdiagCPhaseCoeff] using hsquare.trans hA.symm
  refine ⟨⟨(u, A), hGraph⟩, ?_⟩
  apply Subtype.ext
  exact hu

noncomputable def sqdiagBWAAdjointGraphToAdjointImageKerEquiv
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWAAdjointGraphToAdjointImage
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    SquareCombinedKernel n a b c d ×
      LinearMap.ker
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun x :=
    let hval :
        SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.1 =
          0 := by
      have hmap :
          (sqdiagBWAAdjointGraphToAdjointImage
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1).1 =
            (0 : SqdiagBWZAdjointImage n a b c d).1 :=
        congrArg
          (fun z : SqdiagBWZAdjointImage n a b c d => z.1)
          (LinearMap.mem_ker.mp x.2)
      change
        SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
            x.1.1.1 = 0
      change
        SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
            x.1.1.1 = 0 at hmap
      exact hmap
    let hGraph :
        sqdiagBWAAdjointGraphPred
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 :=
      (sqdiagBWAAdjointGraphSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1).mp x.1.2
    let hsquare :
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
            x.1.1.1.1 x.1.1.1.2 = 0 := by
      have hsnd := congrArg Prod.snd hval
      simpa [SquareCombined, sqdiagCPhaseCoeff] using hsnd
    (⟨x.1.1.1, LinearMap.mem_ker.mpr hval⟩,
      ⟨x.1.1.2, LinearMap.mem_ker.mpr (by
        change
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.2 = 0
        exact hGraph.2.symm.trans hsquare)⟩)
  invFun x :=
    let hT :
        SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 =
          0 :=
      LinearMap.mem_ker.mp x.1.2
    let hA :
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1 = 0 := by
      change
        sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.2.1 = 0
      exact LinearMap.mem_ker.mp x.2.2
    let hGraph :
        (x.1.1, x.2.1) ∈
          sqdiagBWAAdjointGraphSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d) := by
      rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
      constructor
      · have hroot :
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1).1 =
              (0 : RootTarget n b c d × CFun4 n a b d).1 :=
          congrArg Prod.fst hT
        have hrootMem :
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1).1 ∈
              ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
          rw [hroot]
          exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).zero_mem
        change
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 ∈
            ZDiffSpace (n := n) (b := b) (c := c) (d := d) at hrootMem
        exact hrootMem
      · have hsquare :
            (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)
              x.1.1).2 =
              (0 : RootTarget n b c d × CFun4 n a b d).2 :=
          congrArg Prod.snd hT
        have hsquare' :
            sqdiagCPhaseCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d)
                x.1.1.1 x.1.1.2 = 0 := by
          change
            sqdiagCPhaseCoeff
                (n := n) (a := a) (b := b) (c := c) (d := d)
                x.1.1.1 x.1.1.2 = 0 at hsquare
          exact hsquare
        exact hsquare'.trans hA.symm
    ⟨⟨(x.1.1, x.2.1), hGraph⟩,
      LinearMap.mem_ker.mpr (by
        apply Subtype.ext
        exact hT)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
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

set_option synthInstance.maxHeartbeats 200000 in
-- The domain and kernel are nested subtypes of graph/range modules; build-mode synthesis needs more budget.
theorem finrank_sqdiagBWAAdjointGraph_eq_adjointImage_add_kernels
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagBWAAdjointGraph n a b c d) =
      Module.finrank F (SqdiagBWZAdjointImage n a b c d) +
      Module.finrank F (SquareCombinedKernel n a b c d) +
      Module.finrank F
        (LinearMap.ker
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagBWAAdjointGraphToAdjointImage
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange :
      Module.finrank F (LinearMap.range f) =
        Module.finrank F (SqdiagBWZAdjointImage n a b c d) := by
    have htop : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr
        (sqdiagBWAAdjointGraphToAdjointImage_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d))
    rw [htop, finrank_top]
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F
          (SquareCombinedKernel n a b c d ×
            LinearMap.ker
              (sqdiagKCAdjointMap
                (n := n) (a := a) (b := b) (c := c) (d := d))) := by
    exact LinearEquiv.finrank_eq
      (sqdiagBWAAdjointGraphToAdjointImageKerEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [hrange, hker, Module.finrank_prod] at h
  omega

noncomputable def sqdiagBWAAdjointGraphToBWZAdjointSubmodule
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) where
  toFun x :=
    ⟨x.1.1, by
      rw [sqdiagBWZAdjointSubmodule_mem_iff]
      have hxGraph :
          sqdiagBWAAdjointGraphPred
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 :=
        (sqdiagBWAAdjointGraphSubmodule_mem_iff
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2
      exact
        ⟨hxGraph.1,
          sqdiagCPhaseKernelZero_of_coeff_eq_KCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d)
            x.1.1.1 x.1.1.2 x.1.2 hxGraph.2⟩⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

theorem sqdiagBWAAdjointGraphToBWZAdjointSubmodule_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWAAdjointGraphToBWZAdjointSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro u
  have huPred :
      sqdiagBWZAdjointSupportPred
        (n := n) (a := a) (b := b) (c := c) (d := d) u.1 :=
    (sqdiagBWZAdjointSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) u.1).mp u.2
  rcases (sqdiagCPhaseKernelZero_iff_exists_KCAdjointCoeff
    (n := n) (a := a) (b := b) (c := c) (d := d)
    u.1.1 u.1.2).mp huPred.2 with ⟨A, hA⟩
  have hGraph :
      (u.1, A) ∈
        sqdiagBWAAdjointGraphSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
    exact ⟨huPred.1, hA⟩
  refine ⟨⟨(u.1, A), hGraph⟩, ?_⟩
  apply Subtype.ext
  rfl

noncomputable def sqdiagBWAAdjointGraphToBWZAdjointSubmoduleKerEquiv
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWAAdjointGraphToBWZAdjointSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    LinearMap.ker
        (sqdiagKCAdjointMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun x :=
    let hsource :
        x.1.1.1 = 0 := by
      exact congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
    let hxGraph :
        sqdiagBWAAdjointGraphPred
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 :=
      (sqdiagBWAAdjointGraphSubmodule_mem_iff
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1).mp x.1.2
    let hphase :
        sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
            x.1.1.1.1 x.1.1.1.2 = 0 := by
      have h :=
        congrArg
          (fun u : BFun4 n a c d × WFun4 n a b c =>
            sqdiagCPhaseCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) u.1 u.2)
          hsource
      have hzero :
          sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
              (0 : BFun4 n a c d) (0 : WFun4 n a b c) = 0 := by
        simpa [sqdiagCPhaseCoeff] using
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
      exact h.trans hzero
    ⟨x.1.1.2,
      LinearMap.mem_ker.mpr (by
        change
          sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.2 = 0
        exact hxGraph.2.symm.trans hphase)⟩
  invFun A :=
    let hA :
        sqdiagKCAdjointCoeff
            (n := n) (a := a) (b := b) (c := c) (d := d) A.1 = 0 := by
      change
        sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d) A.1 = 0
      exact LinearMap.mem_ker.mp A.2
    let hGraph :
        ((0 : BFun4 n a c d × WFun4 n a b c), A.1) ∈
          sqdiagBWAAdjointGraphSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d) := by
      rw [sqdiagBWAAdjointGraphSubmodule_mem_iff]
      constructor
      · change
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d)
              (0 : BFun4 n a c d × WFun4 n a b c) ∈
            ZDiffSpace (n := n) (b := b) (c := c) (d := d)
        rw [(K_yw (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero]
        exact (ZDiffSpace (n := n) (b := b) (c := c) (d := d)).zero_mem
      · change
          sqdiagCPhaseCoeff (n := n) (a := a) (b := b) (c := c) (d := d)
              (0 : BFun4 n a c d) (0 : WFun4 n a b c) =
            sqdiagKCAdjointCoeff
              (n := n) (a := a) (b := b) (c := c) (d := d) A.1
        rw [hA]
        simpa [sqdiagCPhaseCoeff] using
          (squareCompat (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero
    ⟨⟨((0 : BFun4 n a c d × WFun4 n a b c), A.1), hGraph⟩,
      LinearMap.mem_ker.mpr (by
        apply Subtype.ext
        rfl)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hsource : x.1.1.1 = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
    exact Prod.ext hsource.symm rfl
  right_inv A := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 500000 in
-- The source projection from the adjoint graph has KC-adjoint kernel fibers.
theorem finrank_sqdiagBWAAdjointGraph_eq_adjointSupport_add_KCAdjointKer
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagBWAAdjointGraph n a b c d) =
      Module.finrank F
        (sqdiagBWZAdjointSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)) +
      Module.finrank F
        (LinearMap.ker
          (sqdiagKCAdjointMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagBWAAdjointGraphToBWZAdjointSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hrange :
      Module.finrank F (LinearMap.range f) =
        Module.finrank F
          (sqdiagBWZAdjointSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    have htop : LinearMap.range f = ⊤ :=
      LinearMap.range_eq_top.mpr
        (sqdiagBWAAdjointGraphToBWZAdjointSubmodule_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d))
    rw [htop, finrank_top]
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F
          (LinearMap.ker
            (sqdiagKCAdjointMap
              (n := n) (a := a) (b := b) (c := c) (d := d))) :=
    LinearEquiv.finrank_eq
      (sqdiagBWAAdjointGraphToBWZAdjointSubmoduleKerEquiv
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rw [hrange, hker] at h
  omega

noncomputable def sqdiagBWZAdjointRestrictedMap
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) →ₗ[F]
      sqdiagZAdjointTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) where
  toFun x :=
    ⟨SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x.1, x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r x.1

noncomputable def sqdiagBWZAdjointRestrictedRangeToAdjointImage
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWZAdjointRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) →ₗ[F]
      SqdiagBWZAdjointImage n a b c d where
  toFun y :=
    ⟨(y.1 : RootTarget n b c d × CFun4 n a b d), by
      constructor
      · rcases y.2 with ⟨x, hx⟩
        refine ⟨x.1, ?_⟩
        exact congrArg Subtype.val hx
      · exact y.1.2⟩
  map_add' y z := by
    apply Subtype.ext
    rfl
  map_smul' r y := by
    apply Subtype.ext
    rfl

theorem sqdiagBWZAdjointRestrictedRangeToAdjointImage_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagBWZAdjointRestrictedRangeToAdjointImage
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro y z hyz
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun t : SqdiagBWZAdjointImage n a b c d =>
      (t : RootTarget n b c d × CFun4 n a b d))
    hyz

theorem sqdiagBWZAdjointRestrictedRangeToAdjointImage_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWZAdjointRestrictedRangeToAdjointImage
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro z
  rcases z.2.1 with ⟨x0, hx0⟩
  have hxSupport :
      x0 ∈ sqdiagBWZAdjointSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d) := by
    change
      SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) x0 ∈
        sqdiagZAdjointTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)
    rw [hx0]
    exact z.2.2
  let xs : sqdiagBWZAdjointSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d) :=
    ⟨x0, hxSupport⟩
  let yTarget : sqdiagZAdjointTargetSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d) :=
    ⟨z.1, z.2.2⟩
  have hyRange :
      yTarget ∈ LinearMap.range
        (sqdiagBWZAdjointRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
    refine ⟨xs, ?_⟩
    apply Subtype.ext
    exact hx0
  refine ⟨⟨yTarget, hyRange⟩, ?_⟩
  apply Subtype.ext
  rfl

noncomputable def sqdiagBWZAdjointRestrictedRangeEquivAdjointImage
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWZAdjointRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      SqdiagBWZAdjointImage n a b c d :=
  LinearEquiv.ofBijective
    (sqdiagBWZAdjointRestrictedRangeToAdjointImage
      (n := n) (a := a) (b := b) (c := c) (d := d))
    ⟨sqdiagBWZAdjointRestrictedRangeToAdjointImage_injective
      (n := n) (a := a) (b := b) (c := c) (d := d),
     sqdiagBWZAdjointRestrictedRangeToAdjointImage_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d)⟩

theorem finrank_range_sqdiagBWZAdjointRestrictedMap_eq_adjointImage
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWZAdjointRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F (SqdiagBWZAdjointImage n a b c d) := by
  exact (sqdiagBWZAdjointRestrictedRangeEquivAdjointImage
    (n := n) (a := a) (b := b) (c := c) (d := d)).finrank_eq

theorem SquareCombinedKernel_le_sqdiagBWZAdjointSubmodule
    {n a b c d : ℕ} [NeZero n] :
    SquareCombinedKernel n a b c d ≤
      sqdiagBWZAdjointSubmodule (n := n) (a := a) (b := b) (c := c) (d := d) := by
  intro x hx
  exact
    (sqdiagBWZCompatSubmodule_le_sqdiagBWZAdjointSubmodule
      (n := n) (a := a) (b := b) (c := c) (d := d))
      ((SquareCombinedKernel_le_sqdiagBWZCompatSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d)) hx)

noncomputable def sqdiagBWZAdjointRestrictedKerEquivSquareCombinedKernel
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWZAdjointRestrictedMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      SquareCombinedKernel n a b c d where
  toFun x :=
    ⟨x.1.1, by
      apply LinearMap.mem_ker.mpr
      have hx0 :
          sqdiagBWZAdjointRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x.1 = 0 :=
        LinearMap.mem_ker.mp x.2
      exact congrArg Subtype.val hx0⟩
  invFun x :=
    ⟨⟨x.1,
        SquareCombinedKernel_le_sqdiagBWZAdjointSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) x.2⟩,
      by
        apply LinearMap.mem_ker.mpr
        apply Subtype.ext
        exact LinearMap.mem_ker.mp x.2⟩
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem finrank_ker_sqdiagBWZAdjointRestrictedMap
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.ker
          (sqdiagBWZAdjointRestrictedMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F (SquareCombinedKernel n a b c d) := by
  exact (sqdiagBWZAdjointRestrictedKerEquivSquareCombinedKernel
    (n := n) (a := a) (b := b) (c := c) (d := d)).finrank_eq

theorem finrank_sqdiagBWZAdjointImage_add_SquareCombinedKernel_eq_adjointSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (SqdiagBWZAdjointImage n a b c d) +
        Module.finrank F (SquareCombinedKernel n a b c d) =
      Module.finrank F
        (sqdiagBWZAdjointSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  have h :=
    LinearMap.finrank_range_add_finrank_ker
      (sqdiagBWZAdjointRestrictedMap
        (n := n) (a := a) (b := b) (c := c) (d := d))
  rwa [finrank_range_sqdiagBWZAdjointRestrictedMap_eq_adjointImage
    (n := n) (a := a) (b := b) (c := c) (d := d),
    finrank_ker_sqdiagBWZAdjointRestrictedMap
      (n := n) (a := a) (b := b) (c := c) (d := d)] at h

theorem sqdiagBWAAdjointGraphQ_eq_of_adjointImage_eq
    {n a b c d : ℕ} [NeZero n]
    (x y : SqdiagBWAAdjointGraph n a b c d)
    (hxy :
      sqdiagBWAAdjointGraphToAdjointImage
          (n := n) (a := a) (b := b) (c := c) (d := d) x =
        sqdiagBWAAdjointGraphToAdjointImage
          (n := n) (a := a) (b := b) (c := c) (d := d) y) :
    sqdiagBWAAdjointGraphQ x = sqdiagBWAAdjointGraphQ y := by
  have hval := congrArg Subtype.val hxy
  have hroot :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 =
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1 := by
    simpa [SquareCombined] using congrArg Prod.fst hval
  have hsquare :
      sqdiagCPhaseCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1.1 x.1.1.2 =
        sqdiagCPhaseCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1.1 y.1.1.2 := by
    simpa [SquareCombined, sqdiagCPhaseCoeff] using congrArg Prod.snd hval
  have hxGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2
  have hyGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) y.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) y.1).mp y.2
  have hcoeff :
      sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) x.1.2 =
        sqdiagKCAdjointCoeff
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1.2 := by
    exact hxGraph.2.symm.trans (hsquare.trans hyGraph.2)
  calc
    sqdiagBWAAdjointGraphQ x =
        sqdiagRootCoeffApply x.1.2
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) := rfl
    _ =
        sqdiagRootCoeffApply y.1.2
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) :=
      sqdiagRootCoeffApply_eq_of_KCAdjointCoeff_eq_of_mem_ZDiff
        (n := n) (a := a) (b := b) (c := c) (d := d)
        x.1.2 y.1.2
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1)
        hcoeff hxGraph.1
    _ =
        sqdiagRootCoeffApply y.1.2
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1) := by
      rw [hroot]
    _ = sqdiagBWAAdjointGraphQ y := rfl

noncomputable def sqdiagBWAAdjointGraphRootZeroAMap
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootZero n a b c d →ₗ[F]
      RootTarget n b c d :=
  (sqdiagBWAAdjointGraphAMap
      (n := n) (a := a) (b := b) (c := c) (d := d)).comp
    (sqdiagBWAAdjointGraphRootZero n a b c d).subtype

abbrev sqdiagBWAAdjointGraphRootZeroACoeffSpace
    (n a b c d : ℕ) [NeZero n] :=
  LinearMap.range
    (sqdiagBWAAdjointGraphRootZeroAMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable def sqdiagBWAAdjointGraphRootZeroAMapToCoeffSpace
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootZero n a b c d →ₗ[F]
      sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d where
  toFun y :=
    ⟨sqdiagBWAAdjointGraphRootZeroAMap
        (n := n) (a := a) (b := b) (c := c) (d := d) y,
      ⟨y, rfl⟩⟩
  map_add' y z := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphRootZeroAMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add y z
  map_smul' r y := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphRootZeroAMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r y

theorem sqdiagBWAAdjointGraphPolar_rootZero
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d)
    (y : sqdiagBWAAdjointGraphRootZero n a b c d) :
    sqdiagBWAAdjointGraphPolar
        (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 =
      sqdiagRootCoeffApply
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1)
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x) := by
  have hyroot :
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1.1 = 0 := by
    have hyrootMap :
        sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1 = 0 :=
      LinearMap.mem_ker.mp y.2
    change
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1.1 = 0 at hyrootMap
    exact hyrootMap
  rw [sqdiagBWAAdjointGraphPolar_apply]
  change
    sqdiagRootCoeffApply x.1.2
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) y.1.1.1) +
      sqdiagRootCoeffApply y.1.1.2
        (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) =
    sqdiagRootCoeffApply y.1.1.2
      (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1)
  rw [hyroot]
  simp [sqdiagRootCoeffApply]

noncomputable def sqdiagBWAAdjointGraphRootZeroACoeffDualMap
    {n a b c d : ℕ} [NeZero n] :
    SqdiagBWAAdjointGraph n a b c d →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) where
  toFun x :=
    { toFun := fun A =>
        sqdiagRootCoeffApply A.1
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) x)
      map_add' := by
        intro A B
        change
          sqdiagRootCoeffApply (A.1 + B.1)
              (sqdiagBWAAdjointGraphRootMap
                (n := n) (a := a) (b := b) (c := c) (d := d) x) =
            sqdiagRootCoeffApply A.1
                (sqdiagBWAAdjointGraphRootMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) x) +
              sqdiagRootCoeffApply B.1
                (sqdiagBWAAdjointGraphRootMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) x)
        rw [sqdiagRootCoeffApply_add_left]
      map_smul' := by
        intro r A
        change
          sqdiagRootCoeffApply (r • A.1)
              (sqdiagBWAAdjointGraphRootMap
                (n := n) (a := a) (b := b) (c := c) (d := d) x) =
            r •
              sqdiagRootCoeffApply A.1
                (sqdiagBWAAdjointGraphRootMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) x)
        rw [sqdiagRootCoeffApply_smul_left] }
  map_add' x y := by
    ext A
    change
      sqdiagRootCoeffApply A.1
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) (x + y)) =
        sqdiagRootCoeffApply A.1
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x) +
          sqdiagRootCoeffApply A.1
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) y)
    rw [
      (sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add,
      sqdiagRootCoeffApply_add_right]
  map_smul' r x := by
    ext A
    change
      sqdiagRootCoeffApply A.1
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d) (r • x)) =
        r •
          sqdiagRootCoeffApply A.1
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
    rw [
      (sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul,
      sqdiagRootCoeffApply_smul_right]

noncomputable def sqdiagRootZeroACoeffEvalMap
    {n a b c d : ℕ} [NeZero n] :
    RootTarget n b c d →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) where
  toFun R :=
    (sqdiagRootCoeffLinearMap (n := n) (b := b) (c := c) (d := d) R).comp
      (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d).subtype
  map_add' R S := by
    ext A
    change
      sqdiagRootCoeffApply A.1 (R + S) =
        sqdiagRootCoeffApply A.1 R + sqdiagRootCoeffApply A.1 S
    rw [sqdiagRootCoeffApply_add_right]
  map_smul' r R := by
    ext A
    change
      sqdiagRootCoeffApply A.1 (r • R) =
        r • sqdiagRootCoeffApply A.1 R
    rw [sqdiagRootCoeffApply_smul_right]

theorem sqdiagBWAAdjointGraphRootZeroACoeffDualMap_eq_eval_comp_rootMap
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphRootZeroACoeffDualMap
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  ext x A
  rfl

noncomputable def sqdiagBWAAdjointGraphRootImageEvalMap
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) where
  toFun R :=
    sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d) R.1
  map_add' R S := by
    exact
      (sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add R.1 S.1
  map_smul' r R := by
    exact
      (sqdiagRootZeroACoeffEvalMap
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r R.1

theorem sqdiagBWAAdjointGraphRootImageEvalMap_range_eq_rootZeroACoeffDualMap_range
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWAAdjointGraphRootImageEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      LinearMap.range
        (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  ext L
  constructor
  · intro hL
    rcases hL with ⟨R, hR⟩
    rcases R.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← hR]
    ext A
    have hxroot :
        K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1 =
          R.1 := by
      simpa [sqdiagBWAAdjointGraphRootMap] using hx
    change
      sqdiagRootCoeffApply A.1
          (K_yw (n := n) (a := a) (b := b) (c := c) (d := d) x.1.1) =
        sqdiagRootCoeffApply A.1 R.1
    rw [hxroot]
  · intro hL
    rcases hL with ⟨x, hL⟩
    let R :
        LinearMap.range
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) :=
      ⟨sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x,
        ⟨x, rfl⟩⟩
    refine ⟨R, ?_⟩
    rw [← hL]
    ext A
    rfl

set_option synthInstance.maxHeartbeats 300000 in
-- Both sides are ranges into the same nested dual space; the preceding range equality is the substance.
theorem finrank_sqdiagBWAAdjointGraphRootImageEvalRange_eq_rootZeroACoeffDualRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootImageEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  rw [sqdiagBWAAdjointGraphRootImageEvalMap_range_eq_rootZeroACoeffDualMap_range
    (n := n) (a := a) (b := b) (c := c) (d := d)]

abbrev sqdiagRootZeroACoeffAnnihilator
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (RootTarget n b c d) :=
  LinearMap.ker
    (sqdiagRootZeroACoeffEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d))

theorem sqdiagRootZeroACoeffAnnihilator_mem_iff
    {n a b c d : ℕ} [NeZero n]
    (R : RootTarget n b c d) :
    R ∈ sqdiagRootZeroACoeffAnnihilator n a b c d ↔
      ∀ A : RootTarget n b c d,
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply (n := n) (b := b) (c := c) (d := d) A R = 0 := by
  constructor
  · intro hR A hA
    have hmap :
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d) R = 0 :=
      LinearMap.mem_ker.mp hR
    have happ :=
      congrArg
        (fun L : Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) =>
          L ⟨A, hA⟩)
        hmap
    simpa [sqdiagRootZeroACoeffEvalMap] using happ
  · intro hann
    apply LinearMap.mem_ker.mpr
    ext A
    exact hann A.1 A.2

abbrev sqdiagBWAAdjointGraphRootImageAnnihilator
    (n a b c d : ℕ) [NeZero n] :
    Submodule F (RootTarget n b c d) :=
  LinearMap.range
      (sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
    sqdiagRootZeroACoeffAnnihilator n a b c d

noncomputable def sqdiagBWAAdjointGraphRootImageEvalMapKerEquivAnnihilator
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWAAdjointGraphRootImageEvalMap
          (n := n) (a := a) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d where
  toFun x :=
    ⟨x.1.1, by
      constructor
      · exact x.1.2
      · apply LinearMap.mem_ker.mpr
        change
          sqdiagBWAAdjointGraphRootImageEvalMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x.1 =
            0
        exact LinearMap.mem_ker.mp x.2⟩
  invFun R :=
    ⟨⟨R.1, R.2.1⟩, by
      apply LinearMap.mem_ker.mpr
      change
        sqdiagRootZeroACoeffEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d) R.1 =
          0
      exact LinearMap.mem_ker.mp R.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv R := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    rfl

set_option synthInstance.maxHeartbeats 500000 in
-- Rank-nullity for the root-image evaluation map, with its kernel moved back to RootTarget.
theorem finrank_sqdiagBWAAdjointGraphRootImageEvalRange_add_annihilator_eq_rootImage
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootImageEvalMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      Module.finrank F
        (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) =
    Module.finrank F
      (LinearMap.range
        (sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  let f :=
    sqdiagBWAAdjointGraphRootImageEvalMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) :=
    LinearEquiv.finrank_eq
      (sqdiagBWAAdjointGraphRootImageEvalMapKerEquivAnnihilator
        (n := n) (a := a) (b := b) (c := c) (d := d))
  change
    Module.finrank F (LinearMap.range f) +
        Module.finrank F (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) =
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))
        )
  rw [← hker]
  exact h

set_option synthInstance.maxHeartbeats 300000 in
-- Rank-nullity for the graph root map itself.
theorem finrank_sqdiagBWAAdjointGraphRootImage_add_rootZero_eq_graph
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      Module.finrank F (sqdiagBWAAdjointGraphRootZero n a b c d) =
    Module.finrank F (SqdiagBWAAdjointGraph n a b c d) := by
  let f :=
    sqdiagBWAAdjointGraphRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  change
    Module.finrank F (LinearMap.range f) +
        Module.finrank F (LinearMap.ker f) =
      Module.finrank F (SqdiagBWAAdjointGraph n a b c d)
  exact LinearMap.finrank_range_add_finrank_ker f

noncomputable def sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
    {n a b c d : ℕ} [NeZero n] :
    Module.Dual F (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) →ₗ[F]
      Module.Dual F (sqdiagBWAAdjointGraphRootZero n a b c d) where
  toFun L :=
    L.comp
      (sqdiagBWAAdjointGraphRootZeroAMapToCoeffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d))
  map_add' L M := by
    ext y
    rfl
  map_smul' r L := by
    ext y
    rfl

theorem sqdiagBWAAdjointGraphRootZeroACoeffDualPullback_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro L M hLM
  ext A
  rcases A.2 with ⟨y, hy⟩
  have hA :
      sqdiagBWAAdjointGraphRootZeroAMapToCoeffSpace
          (n := n) (a := a) (b := b) (c := c) (d := d) y =
        A := by
    apply Subtype.ext
    exact hy
  have happ :=
    congrArg
      (fun T : Module.Dual F (sqdiagBWAAdjointGraphRootZero n a b c d) => T y)
      hLM
  simpa [sqdiagBWAAdjointGraphRootZeroACoeffDualPullback, hA] using happ

theorem sqdiagBWAAdjointGraphPolarToRootZero_eq_rootZeroACoeffDualPullback_comp
    {n a b c d : ℕ} [NeZero n] :
    sqdiagBWAAdjointGraphPolarToRootZero
        (n := n) (a := a) (b := b) (c := c) (d := d) =
      (sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
        (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  ext x y
  have hpolar :=
    sqdiagBWAAdjointGraphPolar_rootZero
      (n := n) (a := a) (b := b) (c := c) (d := d) x y
  simpa [sqdiagBWAAdjointGraphPolarToRootZero,
    sqdiagBWAAdjointGraphRootZeroACoeffDualPullback,
    sqdiagBWAAdjointGraphRootZeroACoeffDualMap,
    sqdiagBWAAdjointGraphRootZeroAMapToCoeffSpace,
    sqdiagBWAAdjointGraphRootZeroAMap] using hpolar

noncomputable def sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) →ₗ[F]
      LinearMap.range
        (sqdiagBWAAdjointGraphPolarToRootZero
          (n := n) (a := a) (b := b) (c := c) (d := d)) where
  toFun L :=
    ⟨sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
        (n := n) (a := a) (b := b) (c := c) (d := d) L.1, by
      rcases L.2 with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [sqdiagBWAAdjointGraphPolarToRootZero_eq_rootZeroACoeffDualPullback_comp]
      change
        sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
            (n := n) (a := a) (b := b) (c := c) (d := d)
            ((sqdiagBWAAdjointGraphRootZeroACoeffDualMap
              (n := n) (a := a) (b := b) (c := c) (d := d)) x) =
          sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
            (n := n) (a := a) (b := b) (c := c) (d := d) L.1
      rw [hx]⟩
  map_add' L M := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_add L.1 M.1
  map_smul' r L := by
    apply Subtype.ext
    exact
      (sqdiagBWAAdjointGraphRootZeroACoeffDualPullback
        (n := n) (a := a) (b := b) (c := c) (d := d)).map_smul r L.1

theorem sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange_injective
    {n a b c d : ℕ} [NeZero n] :
    Function.Injective
      (sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro L M hLM
  apply Subtype.ext
  apply
    sqdiagBWAAdjointGraphRootZeroACoeffDualPullback_injective
      (n := n) (a := a) (b := b) (c := c) (d := d)
  exact congrArg Subtype.val hLM

theorem sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange_surjective
    {n a b c d : ℕ} [NeZero n] :
    Function.Surjective
      (sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  intro P
  rcases P.2 with ⟨x, hx⟩
  let L :
      LinearMap.range
        (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) :=
    ⟨sqdiagBWAAdjointGraphRootZeroACoeffDualMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x,
      ⟨x, rfl⟩⟩
  refine ⟨L, ?_⟩
  apply Subtype.ext
  rw [← hx]
  have hcomp :=
    congrArg
      (fun T : SqdiagBWAAdjointGraph n a b c d →ₗ[F]
          Module.Dual F (sqdiagBWAAdjointGraphRootZero n a b c d) => T x)
      (sqdiagBWAAdjointGraphPolarToRootZero_eq_rootZeroACoeffDualPullback_comp
        (n := n) (a := a) (b := b) (c := c) (d := d))
  exact hcomp.symm

noncomputable def sqdiagBWAAdjointGraphRootZeroACoeffDualRangeEquivPolarRange
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.range
        (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≃ₗ[F]
      LinearMap.range
        (sqdiagBWAAdjointGraphPolarToRootZero
          (n := n) (a := a) (b := b) (c := c) (d := d)) :=
  LinearEquiv.ofBijective
    (sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange
      (n := n) (a := a) (b := b) (c := c) (d := d))
    ⟨sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange_injective
      (n := n) (a := a) (b := b) (c := c) (d := d),
     sqdiagBWAAdjointGraphRootZeroACoeffDualRangeToPolarRange_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d)⟩

theorem finrank_sqdiagBWAAdjointGraphPolarRange_eq_rootZeroACoeffDualRange
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphPolarToRootZero
            (n := n) (a := a) (b := b) (c := c) (d := d))) =
      Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) := by
  exact (sqdiagBWAAdjointGraphRootZeroACoeffDualRangeEquivPolarRange
    (n := n) (a := a) (b := b) (c := c) (d := d)).finrank_eq.symm

theorem sqdiagBWAAdjointGraph_mem_lagrangian_iff_annihilates_rootZeroACoeffSpace
    {n a b c d : ℕ} [NeZero n]
    (x : SqdiagBWAAdjointGraph n a b c d) :
    x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d ↔
      ∀ A : RootTarget n b c d,
        A ∈ sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d →
          sqdiagRootCoeffApply A
            (sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x) = 0 := by
  constructor
  · intro hx A hA
    rcases hA with ⟨y, rfl⟩
    have hker :
        sqdiagBWAAdjointGraphPolarToRootZero
            (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
      LinearMap.mem_ker.mp hx
    have hpolar0 :
        sqdiagBWAAdjointGraphPolar
            (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 = 0 := by
      have happly :=
        congrArg
          (fun L : Module.Dual F (sqdiagBWAAdjointGraphRootZero n a b c d) => L y)
          hker
      simpa [sqdiagBWAAdjointGraphPolarToRootZero] using happly
    have hpolar :=
      sqdiagBWAAdjointGraphPolar_rootZero
        (n := n) (a := a) (b := b) (c := c) (d := d) x y
    exact by
      simpa [sqdiagBWAAdjointGraphRootZeroAMap] using hpolar.symm.trans hpolar0
  · intro hann
    rw [LinearMap.mem_ker]
    ext y
    have hA :
        sqdiagBWAAdjointGraphAMap
            (n := n) (a := a) (b := b) (c := c) (d := d) y.1 ∈
          sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d := by
      exact ⟨y, rfl⟩
    have hzero :=
      hann
        (sqdiagBWAAdjointGraphAMap
          (n := n) (a := a) (b := b) (c := c) (d := d) y.1) hA
    have hpolar :=
      sqdiagBWAAdjointGraphPolar_rootZero
        (n := n) (a := a) (b := b) (c := c) (d := d) x y
    exact by
      simpa [sqdiagBWAAdjointGraphPolarToRootZero] using hpolar.trans hzero

theorem sqdiagBWAAdjointGraphRootZeroACoeffDualMap_ker_eq_lagrangian
    {n a b c d : ℕ} [NeZero n] :
    LinearMap.ker
        (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) =
      sqdiagBWAAdjointGraphLagrangian n a b c d := by
  ext x
  constructor
  · intro hx
    exact
      (sqdiagBWAAdjointGraph_mem_lagrangian_iff_annihilates_rootZeroACoeffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d) x).mpr
        (by
          intro A hA
          have hmap :
              sqdiagBWAAdjointGraphRootZeroACoeffDualMap
                  (n := n) (a := a) (b := b) (c := c) (d := d) x =
                0 :=
            LinearMap.mem_ker.mp hx
          have happ :=
            congrArg
              (fun L :
                  Module.Dual F
                    (sqdiagBWAAdjointGraphRootZeroACoeffSpace n a b c d) =>
                L ⟨A, hA⟩)
              hmap
          simpa [sqdiagBWAAdjointGraphRootZeroACoeffDualMap] using happ)
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext A
    have hzero :=
      (sqdiagBWAAdjointGraph_mem_lagrangian_iff_annihilates_rootZeroACoeffSpace
        (n := n) (a := a) (b := b) (c := c) (d := d) x).mp hx A.1 A.2
    simpa [sqdiagBWAAdjointGraphRootZeroACoeffDualMap] using hzero

set_option synthInstance.maxHeartbeats 500000 in
-- The dual-map range is a nested submodule of a function-space dual, so finrank instances need room.
theorem finrank_sqdiagBWAAdjointGraphRootZeroACoeffDualRange_add_lagrangian_eq_graph
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (sqdiagBWAAdjointGraphRootZeroACoeffDualMap
            (n := n) (a := a) (b := b) (c := c) (d := d))) +
      Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) =
    Module.finrank F (SqdiagBWAAdjointGraph n a b c d) := by
  let f :=
    sqdiagBWAAdjointGraphRootZeroACoeffDualMap
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hker :
      Module.finrank F (LinearMap.ker f) =
        Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) := by
    rw [sqdiagBWAAdjointGraphRootZeroACoeffDualMap_ker_eq_lagrangian
      (n := n) (a := a) (b := b) (c := c) (d := d)]
  change
    Module.finrank F (LinearMap.range f) +
        Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) =
      Module.finrank F (SqdiagBWAAdjointGraph n a b c d)
  rw [← hker]
  exact h

set_option synthInstance.maxHeartbeats 500000 in
-- Combining root rank-nullity, root-image evaluation rank-nullity, and the
-- dual-map rank-nullity gives the intrinsic lagrangian/root-zero split.
theorem finrank_sqdiagBWAAdjointGraphLagrangian_eq_rootZero_add_rootImageAnnihilator
    {n a b c d : ℕ} [NeZero n] :
    Module.finrank F (sqdiagBWAAdjointGraphLagrangian n a b c d) =
      Module.finrank F (sqdiagBWAAdjointGraphRootZero n a b c d) +
        Module.finrank F
          (sqdiagBWAAdjointGraphRootImageAnnihilator n a b c d) := by
  have hdual :=
    finrank_sqdiagBWAAdjointGraphRootZeroACoeffDualRange_add_lagrangian_eq_graph
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hrange :=
    finrank_sqdiagBWAAdjointGraphRootImageEvalRange_eq_rootZeroACoeffDualRange
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hann :=
    finrank_sqdiagBWAAdjointGraphRootImageEvalRange_add_annihilator_eq_rootImage
      (n := n) (a := a) (b := b) (c := c) (d := d)
  have hroot :=
    finrank_sqdiagBWAAdjointGraphRootImage_add_rootZero_eq_graph
      (n := n) (a := a) (b := b) (c := c) (d := d)
  omega

end

end SquareDiagonal
end Core4loop
