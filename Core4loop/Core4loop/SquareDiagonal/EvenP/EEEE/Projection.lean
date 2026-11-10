import Core4loop.SquareDiagonal.EvenP.EEEE.Definitions

open scoped BigOperators

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

namespace EEEEInternal

theorem dual_exists_cubeDot
    {n : Nat} [NeZero n] (phi : Module.Dual F (CyclicCube n)) :
    ∃ lambda : CyclicCube n,
      ∀ x : CyclicCube n, phi x = cubeDot lambda x := by
  let lambda := (cubeDotEquiv (n := n)).symm phi
  refine ⟨lambda, fun x => ?_⟩
  have h := LinearMap.congr_fun
    ((cubeDotEquiv (n := n)).apply_symm_apply phi) x
  exact h.symm

theorem dual_factor_of_vanishes_on_comap_range
    {U V : Type*}
    [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    (d : V →ₗ[F] V) (p : U →ₗ[F] V)
    (phi : Module.Dual F V)
    (hphi : ∀ x : V, d x ∈ LinearMap.range p → phi x = 0) :
    ∃ psi : Module.Dual F V,
      phi = psi.comp d ∧ ∀ u : U, psi (p u) = 0 := by
  let S : Submodule F V := LinearMap.range p
  let f : V →ₗ[F] V ⧸ S := S.mkQ.comp d
  have hmem : phi ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    apply hphi x
    have hzero : S.mkQ (d x) = 0 := by
      simpa [f, LinearMap.mem_ker] using hx
    exact (Submodule.Quotient.mk_eq_zero S).mp hzero
  have hrange : phi ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact hmem
  rcases hrange with ⟨eta, heta⟩
  refine ⟨eta.comp S.mkQ, ?_, ?_⟩
  · symm
    simpa [f] using heta
  · intro u
    change eta (S.mkQ (p u)) = 0
    rw [Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero S).mpr
        (LinearMap.mem_range_self p u), map_zero]

theorem cube_add_self
    {n : Nat} [NeZero n] (x : CyclicCube n) : x + x = 0 := by
  funext i j k
  exact F_add_self _

theorem cube_eq_of_add_eq_zero
    {n : Nat} [NeZero n] {x y : CyclicCube n}
    (h : x + y = 0) : x = y := by
  rw [← cube_add_self y] at h
  exact add_right_cancel h

theorem pairing_zero_of_j
    {n : Nat} [NeZero n]
    (R lambda A : CyclicCube n)
    (hR : R = cubeDiffJStar lambda)
    (hA : cubeDiffJInv A = 0) :
    cubeDot R A = 0 := by
  rw [hR, cubeDiffJ_pairing_adjoint, hA]
  simp [cubeDot]

theorem pairing_zero_of_j_range_r
    {n : Nat} [NeZero n]
    (R lambda A X : CyclicCube n)
    (hR : R = cubeDiffJStar lambda)
    (hr : cubeDiffRStar lambda = 0)
    (hA : cubeDiffJInv A = cubeDiffR X) :
    cubeDot R A = 0 := by
  rw [hR, cubeDiffJ_pairing_adjoint, hA,
    ← cubeDiffR_pairing_adjoint, hr]
  simp [cubeDot]

theorem pairing_zero_of_j_range_p
    {n : Nat} [NeZero n]
    (R lambda A X : CyclicCube n)
    (hR : R = cubeDiffJStar lambda)
    (hp : cubeDiffPStar lambda = 0)
    (hA : cubeDiffJInv A = cubeDiffP X) :
    cubeDot R A = 0 := by
  rw [hR, cubeDiffJ_pairing_adjoint, hA,
    ← cubeDiffP_pairing_adjoint, hp]
  simp [cubeDot]

end EEEEInternal

set_option maxHeartbeats 1200000 in
-- The reverse exactness proof constructs three finite-dual factorizations.
theorem range_EEEE_projection_eq_leftKernel
    {n : Nat} [NeZero n] :
    LinearMap.range (diamondEEEEProjection (n := n)) =
      DiamondEEEELeftKernel n := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro A
    let R := diamondEEEECoeffMap z.1.1.1
    let lambda00 := z.1.2.1.1
    let lambda01 := z.1.2.1.2
    let lambda10 := z.1.2.2.1
    have hcon := LinearMap.mem_ker.mp z.2
    have h0 := congrFun hcon (0 : Fin 11)
    have h1 := congrFun hcon (1 : Fin 11)
    have h2 := congrFun hcon (2 : Fin 11)
    have h3 := congrFun hcon (3 : Fin 11)
    have h4 := congrFun hcon (4 : Fin 11)
    have h5 := congrFun hcon (5 : Fin 11)
    have h6 := congrFun hcon (6 : Fin 11)
    have h7 := congrFun hcon (7 : Fin 11)
    change R.1.2.2 = 0 at h0
    change R.2.2.1 = 0 at h1
    change R.1.2.1 = 0 at h2
    change R.1.1.2 + cubeDiffJStar lambda01 = 0 at h3
    change cubeDiffRStar lambda01 = 0 at h4
    change R.2.1.1 + cubeDiffJStar lambda10 = 0 at h5
    change cubeDiffPStar lambda10 = 0 at h6
    change R.1.1.1 + cubeDiffJStar lambda00 = 0 at h7
    have hR001 : R.1.1.2 = cubeDiffJStar lambda01 :=
      EEEEInternal.cube_eq_of_add_eq_zero h3
    have hR100 : R.2.1.1 = cubeDiffJStar lambda10 :=
      EEEEInternal.cube_eq_of_add_eq_zero h5
    have hR000 : R.1.1.1 = cubeDiffJStar lambda00 :=
      EEEEInternal.cube_eq_of_add_eq_zero h7
    rcases A.2.2.1 with ⟨X01, hX01⟩
    rcases A.2.2.2.1 with ⟨X10, hX10⟩
    have hpair000 :=
      EEEEInternal.pairing_zero_of_j
        R.1.1.1 lambda00 A.1.1.1.1 hR000 A.2.1
    have hpair001 :=
      EEEEInternal.pairing_zero_of_j_range_r
        R.1.1.2 lambda01 A.1.1.1.2 X01 hR001 h4 hX01.symm
    have hpair100 :=
      EEEEInternal.pairing_zero_of_j_range_p
        R.2.1.1 lambda10 A.1.2.1.1 X10 hR100 h6 hX10.symm
    have hpair :
        cubeDot R.1.1.1 A.1.1.1.1 + cubeDot R.1.1.2 A.1.1.1.2 +
          cubeDot R.1.2.1 A.1.1.2.1 + cubeDot R.1.2.2 A.1.1.2.2 +
          cubeDot R.2.1.1 A.1.2.1.1 + cubeDot R.2.1.2 A.1.2.1.2 +
          cubeDot R.2.2.1 A.1.2.2.1 + cubeDot R.2.2.2 A.1.2.2.2 = 0 := by
      rw [hpair000, hpair001, hpair100, h0, h1, h2]
      simp [R, diamondEEEECoeffMap, cubeDot]
    simpa [diamondEEEECross,
      EEEEInternal.diamondEEEERestrictRightDual,
      EEEEInternal.diamondEEEERightPairing, R] using hpair
  · intro l hl
    let R := diamondEEEECoeffMap l.1
    have hcross (A : DiamondEEEERightSource n) :
        cubeDot R.1.1.1 A.1.1.1.1 + cubeDot R.1.1.2 A.1.1.1.2 +
          cubeDot R.1.2.1 A.1.1.2.1 + cubeDot R.1.2.2 A.1.1.2.2 +
          cubeDot R.2.1.1 A.1.2.1.1 + cubeDot R.2.1.2 A.1.2.1.2 +
          cubeDot R.2.2.1 A.1.2.2.1 + cubeDot R.2.2.2 A.1.2.2.2 = 0 := by
      have hA := LinearMap.congr_fun (LinearMap.mem_ker.mp hl) A
      simpa [diamondEEEECross,
        EEEEInternal.diamondEEEERestrictRightDual,
        EEEEInternal.diamondEEEERightPairing, R] using hA
    have hR010 : R.1.2.1 = 0 := by
      apply EEEEInternal.cubeDot_left_ext R.1.2.1 0
      intro A010
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (A010, 0)), ((0, 0), (0, 0))), by
          constructor
          · exact map_zero cubeDiffJInv
          constructor
          · exact (LinearMap.range (cubeDiffR (n := n))).zero_mem
          constructor
          · exact (LinearMap.range (cubeDiffP (n := n))).zero_mem
          · exact (LinearMap.range
              (LinearMap.coprod (cubeDiffP (n := n))
                (cubeDiffR (n := n)))).zero_mem⟩
      simpa [A, cubeDot] using hcross A
    have hR011 : R.1.2.2 = 0 := by
      apply EEEEInternal.cubeDot_left_ext R.1.2.2 0
      intro A011
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (0, A011)), ((0, 0), (0, 0))), by
          constructor
          · exact map_zero cubeDiffJInv
          constructor
          · exact (LinearMap.range (cubeDiffR (n := n))).zero_mem
          constructor
          · exact (LinearMap.range (cubeDiffP (n := n))).zero_mem
          · exact (LinearMap.range
              (LinearMap.coprod (cubeDiffP (n := n))
                (cubeDiffR (n := n)))).zero_mem⟩
      simpa [A, cubeDot] using hcross A
    have hR110 : R.2.2.1 = 0 := by
      apply EEEEInternal.cubeDot_left_ext R.2.2.1 0
      intro A110
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (0, 0)), ((0, 0), (A110, 0))), by
          constructor
          · exact map_zero cubeDiffJInv
          constructor
          · exact (LinearMap.range (cubeDiffR (n := n))).zero_mem
          constructor
          · exact (LinearMap.range (cubeDiffP (n := n))).zero_mem
          · exact (LinearMap.range
              (LinearMap.coprod (cubeDiffP (n := n))
                (cubeDiffR (n := n)))).zero_mem⟩
      simpa [A, cubeDot] using hcross A
    have hvanish000 (A000 : CyclicCube n)
        (hA000 : cubeDiffJInv A000 = 0) :
        EEEEInternal.cubeDotDual R.1.1.1 A000 = 0 := by
      let A : DiamondEEEERightSource n :=
        ⟨(((A000, 0), (0, 0)), ((0, 0), (0, 0))), by
          constructor
          · exact hA000
          simp⟩
      simpa [A, hR010, hR011, hR110,
        EEEEInternal.cubeDotDual, cubeDot] using hcross A
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        (U := CyclicCube n) cubeDiffJInv
        (0 : CyclicCube n →ₗ[F] CyclicCube n)
        (EEEEInternal.cubeDotDual R.1.1.1)
        (fun A000 hmem => hvanish000 A000 (by simpa using hmem)) with
      ⟨psi00, hfactor00, _⟩
    rcases EEEEInternal.dual_exists_cubeDot psi00 with
      ⟨lambda00, hpsi00⟩
    have hR000 : R.1.1.1 = cubeDiffJStar lambda00 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A000
      calc
        cubeDot R.1.1.1 A000 = psi00 (cubeDiffJInv A000) :=
          LinearMap.congr_fun hfactor00 A000
        _ = cubeDot lambda00 (cubeDiffJInv A000) := hpsi00 _
        _ = cubeDot (cubeDiffJStar lambda00) A000 :=
          (cubeDiffJ_pairing_adjoint lambda00 A000).symm
    have hvanish001 (A001 : CyclicCube n)
        (hA001 : cubeDiffJInv A001 ∈
          LinearMap.range (cubeDiffR (n := n))) :
        EEEEInternal.cubeDotDual R.1.1.2 A001 = 0 := by
      let A : DiamondEEEERightSource n :=
        ⟨(((0, A001), (0, 0)), ((0, 0), (0, 0))), by
          constructor
          · simp
          constructor
          · exact hA001
          simp⟩
      simpa [A, hR010, hR011, hR110,
        EEEEInternal.cubeDotDual, cubeDot] using hcross A
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv cubeDiffR
        (EEEEInternal.cubeDotDual R.1.1.2) hvanish001 with
      ⟨psi01, hfactor01, hann01⟩
    rcases EEEEInternal.dual_exists_cubeDot psi01 with
      ⟨lambda01, hpsi01⟩
    have hR001 : R.1.1.2 = cubeDiffJStar lambda01 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A001
      calc
        cubeDot R.1.1.2 A001 = psi01 (cubeDiffJInv A001) :=
          LinearMap.congr_fun hfactor01 A001
        _ = cubeDot lambda01 (cubeDiffJInv A001) := hpsi01 _
        _ = cubeDot (cubeDiffJStar lambda01) A001 :=
          (cubeDiffJ_pairing_adjoint lambda01 A001).symm
    have hr01 : cubeDiffRStar lambda01 = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffRStar lambda01) X =
            cubeDot lambda01 (cubeDiffR X) :=
          cubeDiffR_pairing_adjoint lambda01 X
        _ = psi01 (cubeDiffR X) := (hpsi01 _).symm
        _ = 0 := hann01 X
        _ = cubeDot 0 X := by simp [cubeDot]
    have hvanish100 (A100 : CyclicCube n)
        (hA100 : cubeDiffJInv A100 ∈
          LinearMap.range (cubeDiffP (n := n))) :
        EEEEInternal.cubeDotDual R.2.1.1 A100 = 0 := by
      let A : DiamondEEEERightSource n :=
        ⟨(((0, 0), (0, 0)), ((A100, 0), (0, 0))), by
          constructor
          · simp
          constructor
          · simp
          constructor
          · exact hA100
          simp⟩
      simpa [A, hR010, hR011, hR110,
        EEEEInternal.cubeDotDual, cubeDot] using hcross A
    rcases EEEEInternal.dual_factor_of_vanishes_on_comap_range
        cubeDiffJInv cubeDiffP
        (EEEEInternal.cubeDotDual R.2.1.1) hvanish100 with
      ⟨psi10, hfactor10, hann10⟩
    rcases EEEEInternal.dual_exists_cubeDot psi10 with
      ⟨lambda10, hpsi10⟩
    have hR100 : R.2.1.1 = cubeDiffJStar lambda10 := by
      apply EEEEInternal.cubeDot_left_ext
      intro A100
      calc
        cubeDot R.2.1.1 A100 = psi10 (cubeDiffJInv A100) :=
          LinearMap.congr_fun hfactor10 A100
        _ = cubeDot lambda10 (cubeDiffJInv A100) := hpsi10 _
        _ = cubeDot (cubeDiffJStar lambda10) A100 :=
          (cubeDiffJ_pairing_adjoint lambda10 A100).symm
    have hp10 : cubeDiffPStar lambda10 = 0 := by
      apply EEEEInternal.cubeDot_left_ext
      intro X
      calc
        cubeDot (cubeDiffPStar lambda10) X =
            cubeDot lambda10 (cubeDiffP X) :=
          cubeDiffP_pairing_adjoint lambda10 X
        _ = psi10 (cubeDiffP X) := (hpsi10 _).symm
        _ = 0 := hann10 X
        _ = cubeDot 0 X := by simp [cubeDot]
    let z0 : DiamondEEEEMultiplierAmbient n :=
      (l, ((lambda00, lambda01), (lambda10, 0)))
    have hz0 : diamondEEEEMultiplierConstraintMap z0 = 0 := by
      funext q
      fin_cases q <;>
        simp [diamondEEEEMultiplierConstraintMap, z0, R,
          hR011, hR110, hR010, hR001, hr01, hR100, hp10,
          hR000, EEEEInternal.cube_add_self]
    exact ⟨⟨z0, hz0⟩, rfl⟩

end

end Core4loop.SquareDiagonal.EvenP
