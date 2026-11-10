import Core4loop.SquareDiagonal.EvenP.CrossProjection
import Core4loop.SquareDiagonal.EvenP.BWSymmetry

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.SquareDiagonal.EvenP

open Core4loop

noncomputable section

private noncomputable def diamondEvenPBWAmbientSwapEquiv
    {n b c d : Nat} [NeZero n] :
    (BFun4 n 1 c d × WFun4 n 1 b c) ≃ₗ[F]
      (BFun4 n 1 c b × WFun4 n 1 d c) where
  toFun x :=
    (fun p sw z y => x.2 p y z sw,
      fun p w z sy => x.1 p sy z w)
  invFun x :=
    (fun p sy z w => x.2 p w z sy,
      fun p y z sw => x.1 p sw z y)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def diamondEvenPARootAmbientSwapEquiv
    {n b c d : Nat} [NeZero n] :
    AFun4 n b c d ≃ₗ[F] AFun4 n d c b where
  toFun A := fun w z y => A y z w
  invFun A := fun y z w => A w z y
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem diamondEvenPAConstraint_swap
    {n a b c d : Nat} [NeZero n]
    (A : AFun4 n b c d)
    (p : PVec n a) (w : WVec n d) (sz : I n) (y : YVec n b) :
    diamondEvenPAConstraint
        (n := n) (a := a) (b := d) (c := c) (d := b)
        (diamondEvenPARootAmbientSwapEquiv A) p w sz y =
      diamondEvenPAConstraint
        (n := n) (a := a) (b := b) (c := c) (d := d)
        A p y sz w := by
  rfl

private theorem diamondEvenPBWAmbientSwapEquiv_mem_left_iff
    {n b c d : Nat} [NeZero n]
    (x : BFun4 n 1 c d × WFun4 n 1 b c) :
    x ∈ DiamondEvenPLeft n b c d ↔
      diamondEvenPBWAmbientSwapEquiv x ∈
        DiamondEvenPLeft n d c b := by
  simp only [DiamondEvenPLeft, LinearMap.mem_ker]
  constructor
  · intro hx
    funext p w sz y
    change
      squareCompat
          ((fun p sw z y => x.2 p y z sw),
            (fun p w z sy => x.1 p sy z w))
          p w sz y = 0
    rw [BWSymmetryInternal.swapCompat x.1 x.2 p w sz y]
    have hp := congrFun hx p
    have hy := congrFun hp y
    have hsz := congrFun hy sz
    exact congrFun hsz w
  · intro hx
    funext p y sz w
    have hp := congrFun hx p
    have hw := congrFun hp w
    have hsz := congrFun hw sz
    have hy := congrFun hsz y
    change
      squareCompat
          ((fun p sw z y => x.2 p y z sw),
            (fun p w z sy => x.1 p sy z w))
          p w sz y = 0 at hy
    rw [BWSymmetryInternal.swapCompat x.1 x.2 p w sz y] at hy
    exact hy

private theorem diamondEvenPARootAmbientSwapEquiv_mem_reachable_iff
    {n b c d : Nat} [NeZero n]
    (A : AFun4 n b c d) :
    A ∈ DiamondEvenPReachableA n b c d ↔
      diamondEvenPARootAmbientSwapEquiv A ∈
        DiamondEvenPReachableA n d c b := by
  change
    diamondEvenPAConstraint
        (n := n) (a := 1) (b := b) (c := c) (d := d) A ∈
        LinearMap.range
          (squareCompat
            (n := n) (a := 1) (b := b) (c := c) (d := d)) ↔
      diamondEvenPAConstraint
        (n := n) (a := 1) (b := d) (c := c) (d := b)
        (diamondEvenPARootAmbientSwapEquiv A) ∈
        LinearMap.range
          (squareCompat
            (n := n) (a := 1) (b := d) (c := c) (d := b))
  constructor
  · rintro ⟨bw, hbw⟩
    refine ⟨diamondEvenPBWAmbientSwapEquiv bw, ?_⟩
    funext p w sz y
    change
      squareCompat
          ((fun p sw z y => bw.2 p y z sw),
            (fun p w z sy => bw.1 p sy z w))
          p w sz y =
        diamondEvenPAConstraint
          (n := n) (a := 1) (b := d) (c := c) (d := b)
          (diamondEvenPARootAmbientSwapEquiv A) p w sz y
    rw [BWSymmetryInternal.swapCompat bw.1 bw.2 p w sz y,
      diamondEvenPAConstraint_swap A p w sz y]
    have hp := congrFun hbw p
    have hy := congrFun hp y
    have hsz := congrFun hy sz
    exact congrFun hsz w
  · rintro ⟨bw', hbw'⟩
    let bw :=
      (diamondEvenPBWAmbientSwapEquiv
        (n := n) (b := b) (c := c) (d := d)).symm bw'
    refine ⟨bw, ?_⟩
    funext p y sz w
    have hp := congrFun hbw' p
    have hw := congrFun hp w
    have hsz := congrFun hw sz
    have hy := congrFun hsz y
    have hswap :
        diamondEvenPBWAmbientSwapEquiv bw = bw' :=
      (diamondEvenPBWAmbientSwapEquiv
        (n := n) (b := b) (c := c) (d := d)).apply_symm_apply bw'
    rw [← hswap] at hy
    change
      squareCompat bw p y sz w =
        diamondEvenPAConstraint
          (n := n) (a := 1) (b := b) (c := c) (d := d)
          A p y sz w
    rw [← diamondEvenPAConstraint_swap A p w sz y]
    rw [← BWSymmetryInternal.swapCompat bw.1 bw.2 p w sz y]
    exact hy

noncomputable def diamondEvenPLeftBWSwapEquiv
    {n b c d : Nat} [NeZero n] :
    DiamondEvenPLeft n b c d ≃ₗ[F]
      DiamondEvenPLeft n d c b where
  toFun x :=
    ⟨diamondEvenPBWAmbientSwapEquiv x.1,
      (diamondEvenPBWAmbientSwapEquiv_mem_left_iff x.1).mp x.2⟩
  invFun x :=
    ⟨(diamondEvenPBWAmbientSwapEquiv
        (n := n) (b := b) (c := c) (d := d)).symm x.1,
      (diamondEvenPBWAmbientSwapEquiv_mem_left_iff
        ((diamondEvenPBWAmbientSwapEquiv
          (n := n) (b := b) (c := c) (d := d)).symm x.1)).mpr
        x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ x.1
  right_inv x := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ x.1
  map_add' x y := by
    apply Subtype.ext
    exact (diamondEvenPBWAmbientSwapEquiv
      (n := n) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (diamondEvenPBWAmbientSwapEquiv
      (n := n) (b := b) (c := c) (d := d)).map_smul r x.1

noncomputable def diamondEvenPReachableABWSwapEquiv
    {n b c d : Nat} [NeZero n] :
    DiamondEvenPReachableA n b c d ≃ₗ[F]
      DiamondEvenPReachableA n d c b where
  toFun x :=
    ⟨diamondEvenPARootAmbientSwapEquiv x.1,
      (diamondEvenPARootAmbientSwapEquiv_mem_reachable_iff x.1).mp x.2⟩
  invFun x :=
    ⟨(diamondEvenPARootAmbientSwapEquiv
        (n := n) (b := b) (c := c) (d := d)).symm x.1,
      (diamondEvenPARootAmbientSwapEquiv_mem_reachable_iff
        ((diamondEvenPARootAmbientSwapEquiv
          (n := n) (b := b) (c := c) (d := d)).symm x.1)).mpr
        x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact LinearEquiv.symm_apply_apply _ x.1
  right_inv x := by
    apply Subtype.ext
    exact LinearEquiv.apply_symm_apply _ x.1
  map_add' x y := by
    apply Subtype.ext
    exact (diamondEvenPARootAmbientSwapEquiv
      (n := n) (b := b) (c := c) (d := d)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (diamondEvenPARootAmbientSwapEquiv
      (n := n) (b := b) (c := c) (d := d)).map_smul r x.1

theorem diamondEvenPCross_BWSwap_phase
    {n b c d : Nat} [NeZero n]
    (l : DiamondEvenPLeft n b c d)
    (A : DiamondEvenPReachableA n b c d) :
    diamondEvenPCross
        (n := n) (b := d) (c := c) (d := b)
        (diamondEvenPLeftBWSwapEquiv l)
        (diamondEvenPReachableABWSwapEquiv A)
      =
    diamondEvenPCross
      (n := n) (b := b) (c := c) (d := d) l A := by
  change
    coeffApplyA
        (KBMap
            (n := n) (a := 1) (b := d) (c := c) (d := b)
            (diamondEvenPBWAmbientSwapEquiv l.1).1 +
          KWMap
            (n := n) (a := 1) (b := d) (c := c) (d := b)
            (diamondEvenPBWAmbientSwapEquiv l.1).2)
        (diamondEvenPARootAmbientSwapEquiv A.1) =
      coeffApplyA
        (KBMap
            (n := n) (a := 1) (b := b) (c := c) (d := d) l.1.1 +
          KWMap
            (n := n) (a := 1) (b := b) (c := c) (d := d) l.1.2)
        A.1
  exact BWSymmetryInternal.phaseCore A.1 l.1.1 l.1.2

theorem diamondEvenPCrossProjection_BWSwap
    {n a b c d : Nat} [NeZero n]
    (hn : Even n) (ha2 : 2 ≤ a)
    (x : DiamondPreCSource n a b c d) :
    diamondEvenPCrossProjection
        (n := n) (a := a) (b := d) (c := c) (d := b)
        hn ha2
        (diamondBWSwapEquiv
          (n := n) (a := a) (b := b) (c := c) (d := d) x)
      =
    ((diamondEvenPLeftBWSwapEquiv
        (n := n) (b := b) (c := c) (d := d)).prodCongr
      (diamondEvenPReachableABWSwapEquiv
        (n := n) (b := b) (c := c) (d := d)))
      (diamondEvenPCrossProjection
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn ha2 x) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl

noncomputable def diamondEvenPCross_BWSwap_rangeEquiv
    {n b c d : Nat} [NeZero n] :
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := b) (c := c) (d := d))
      ≃ₗ[F]
    LinearMap.range
        (diamondEvenPCross
          (n := n) (b := d) (c := c) (d := b)) :=
  BWSymmetryInternal.rangeTransportEquiv
    (diamondEvenPCross
      (n := n) (b := b) (c := c) (d := d))
    (diamondEvenPCross
      (n := n) (b := d) (c := c) (d := b))
    (diamondEvenPLeftBWSwapEquiv
      (n := n) (b := b) (c := c) (d := d))
    (diamondEvenPReachableABWSwapEquiv
      (n := n) (b := b) (c := c) (d := d))
    (diamondEvenPCross_BWSwap_phase
      (n := n) (b := b) (c := c) (d := d))

theorem rank_diamondEvenPCross_bw
    {n b c d : Nat} [NeZero n] :
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := d) (c := c) (d := b)))
      =
    Module.finrank F
        (LinearMap.range
          (diamondEvenPCross
            (n := n) (b := b) (c := c) (d := d))) := by
  exact
    (LinearEquiv.finrank_eq
      (diamondEvenPCross_BWSwap_rangeEquiv
        (n := n) (b := b) (c := c) (d := d))).symm


end

end Core4loop.SquareDiagonal.EvenP
