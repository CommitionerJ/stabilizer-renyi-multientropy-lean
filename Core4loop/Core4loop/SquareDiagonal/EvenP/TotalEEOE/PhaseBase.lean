import Core4loop.SquareDiagonal.EvenP.EEOE
import Core4loop.SquareDiagonal.EvenP.TailPairing

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

noncomputable abbrev T37JKernel
    (n : Nat) [NeZero n] :=
  LinearMap.ker (cubeDiffJInv (n := n))

abbrev T37YRightBase
    (n : Nat) [NeZero n] :=
  T37JKernel n × EEOEInternal.RReachRight n

abbrev T37WRightBase
    (n : Nat) [NeZero n] :=
  T37JKernel n × EEOEInternal.PReachRight n

noncomputable abbrev T37MixedLeftBase
    (n : Nat) [NeZero n] :=
  (⊥ : Submodule F (CyclicCube n))

noncomputable def t37YBaseCross
    {n : Nat} [NeZero n] :
    EEOEInternal.RBlockLeft n →ₗ[F]
      Module.Dual F (T37YRightBase n) :=
  LinearMap.mk₂ F
    (fun u v => cubeDot (cubeDiffK u.1) v.2.1)
    (by
      intro u u' v
      simp only [Submodule.coe_add, map_add, EEOEInternal.cubeDot_add_left])
    (by
      intro r u v
      simp only [SetLike.val_smul, map_smul,
        EEOEInternal.cubeDot_smul_left])
    (by
      intro u v v'
      simp only [Prod.snd_add, Submodule.coe_add,
        EEOEInternal.cubeDot_add_right])
    (by
      intro r u v
      simp only [Prod.smul_snd, SetLike.val_smul,
        EEOEInternal.cubeDot_smul_right])

noncomputable def t37WBaseCross
    {n : Nat} [NeZero n] :
    EEOEInternal.PBlockLeft n →ₗ[F]
      Module.Dual F (T37WRightBase n) :=
  LinearMap.mk₂ F
    (fun u v => cubeDot (cubeDiffI u.1) v.2.1)
    (by
      intro u u' v
      simp only [Submodule.coe_add, map_add, EEOEInternal.cubeDot_add_left])
    (by
      intro r u v
      simp only [SetLike.val_smul, map_smul,
        EEOEInternal.cubeDot_smul_left])
    (by
      intro u v v'
      simp only [Prod.snd_add, Submodule.coe_add,
        EEOEInternal.cubeDot_add_right])
    (by
      intro r u v
      simp only [Prod.smul_snd, SetLike.val_smul,
        EEOEInternal.cubeDot_smul_right])

noncomputable def t37MixedBaseCross
    {n : Nat} [NeZero n] :
    T37MixedLeftBase n →ₗ[F]
      Module.Dual F (T37JKernel n) :=
  EEOEInternal.cubeDotDual.compl₁₂
    (T37MixedLeftBase n).subtype
    (T37JKernel n).subtype

private theorem cubeDiffI_eq_cubeDiffJStar_of_p_zero
    {n : Nat} [NeZero n]
    (u : CyclicCube n)
    (hu : cubeDiffP u = 0) :
    cubeDiffI u = cubeDiffJStar u := by
  funext i j k
  rw [EEOEInternal.cubeDiffI_apply,
    EEOEInternal.cubeDiffJStar_apply]
  have h :=
    congrFun (congrFun (congrFun hu i) (j + 1)) k
  simp only [Pi.zero_apply] at h
  rw [EEOEInternal.cubeDiffP_apply] at h
  rw [show (j + 1) - 1 = j by abel] at h
  exact (EEOEInternal.eq_of_add_eq_zero h).symm ▸ rfl

private theorem cubeDiffPStar_eq_zero_of_p_zero
    {n : Nat} [NeZero n]
    (u : CyclicCube n)
    (hu : cubeDiffP u = 0) :
    cubeDiffPStar u = 0 := by
  funext i j k
  simp only [Pi.zero_apply]
  rw [EEOEInternal.cubeDiffPStar_apply]
  have h :=
    congrFun
      (congrFun
        (congrFun hu (i - 1)) (j + 1)) k
  simp only [Pi.zero_apply] at h
  rw [EEOEInternal.cubeDiffP_apply] at h
  rw [add_comm]
  simpa only [sub_add_cancel, add_sub_cancel_right] using h

private theorem pTailBase_phase_zero
    {n : Nat} [NeZero n]
    (u : EEOEInternal.PBlockLeft n)
    (v : EEOEInternal.PReachRight n) :
    cubeDot (cubeDiffI u.1) v.1 = 0 := by
  have hu : cubeDiffP u.1 = 0 :=
    LinearMap.mem_ker.mp u.2
  rcases v.2 with ⟨x, hx⟩
  rw [cubeDiffI_eq_cubeDiffJStar_of_p_zero u.1 hu,
    cubeDiffJ_pairing_adjoint, ← hx,
    ← cubeDiffP_pairing_adjoint,
    cubeDiffPStar_eq_zero_of_p_zero u.1 hu]
  simp [cubeDot]

theorem t37WBaseCross_eq_zero
    {n : Nat} [NeZero n] :
    t37WBaseCross (n := n) = 0 := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  exact pTailBase_phase_zero u v.2

theorem t37YBaseCross_eq_zero
    {n : Nat} [NeZero n] :
    t37YBaseCross (n := n) = 0 := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  let up := EEOEInternal.rLeftEquivP u
  let vp := EEOEInternal.pReachEquivR.symm v.2
  have hzero : cubeDot (cubeDiffI up.1) vp.1 = 0 :=
    pTailBase_phase_zero up vp
  change cubeDot (cubeDiffK u.1) v.2.1 = 0
  calc
    cubeDot (cubeDiffK u.1) v.2.1 =
        cubeDot
          (EEOEInternal.swapIK (cubeDiffK u.1))
          (EEOEInternal.swapIK v.2.1) :=
      (EEOEInternal.cubeDot_swap_both
        (cubeDiffK u.1) v.2.1).symm
    _ =
        cubeDot
          (cubeDiffI (EEOEInternal.swapIK u.1))
          (EEOEInternal.swapIK v.2.1) := by
      rw [EEOEInternal.swapIK_cubeDiffK]
    _ = 0 := hzero

theorem t37MixedBaseCross_eq_zero
    {n : Nat} [NeZero n] :
    t37MixedBaseCross (n := n) = 0 := by
  apply LinearMap.ext
  intro u
  have hu : u = 0 := by
    apply Subtype.ext
    exact u.2
  subst u
  simp [t37MixedBaseCross, EEOEInternal.cubeDotDual, cubeDot]

end

end Core4loop.SquareDiagonal.EvenP
