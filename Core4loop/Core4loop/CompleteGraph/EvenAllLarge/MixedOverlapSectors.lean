import Core4loop.CompleteGraph.EvenAllLarge.AggregateKernelEEEE

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop.CompleteGraph.EvenP.BaseKKT

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal

noncomputable section

set_option linter.style.setOption false in
section

set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-! Polar coordinates grouped by the only two rows on which they act. -/

noncomputable abbrev K4AggregatePolarScalarCoordinates
    (n : Nat) [NeZero n] :=
  (Profile n × K4BFreeHeadRadical n) ×
    (K4WFreeHeadRadical n × Profile n)

noncomputable abbrev K4AggregatePolarZCoordinates
    (n c : Nat) [NeZero n] :=
  DiamondEvenAxisValueTailZero n c (MatrixProfile n) ×
    DiamondEvenAxisValueTailZero n c (MatrixProfile n)

noncomputable abbrev K4BaseMixedScalarSector
    (n : Nat) [NeZero n] :=
  K4AggregateEEEEScalarKernel n ×
    K4AggregatePolarScalarCoordinates n

noncomputable abbrev K4BaseMixedZSector
    (n c : Nat) [NeZero n] :=
  K4AggregateEEEEZKernelTail n c ×
    K4AggregatePolarZCoordinates n c

/-! The six passive EEEE sectors retain their exact existing types. -/

noncomputable abbrev K4BaseMixedOverlapSectorSource
    (n b c d : Nat) [NeZero n] :=
  K4BaseMixedScalarSector n ×
    (TotalEEEEYTailLeft n b ×
      (TotalEEEEWTailLeft n d ×
        (K4BaseMixedZSector n c ×
          (TotalEEEEYZTailLeft n b c ×
            (TotalEEEEWZTailLeft n c d ×
              (TotalEEEEYWLeftZero n b d ×
                TotalEEEEYWZLeftZero n b c d))))))

private noncomputable def k4MixedOverlapReassociateEquiv
    {n b c d : Nat} [NeZero n] :
    (K4AggregateKernelEEEESource n b c d ×
        K4AggregatePolarCoordinateTarget n c) ≃ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d where
  toFun x :=
    ((x.1.1, (x.2.1.1, x.2.2.1)),
      x.1.2.1,
      x.1.2.2.1,
      (x.1.2.2.2.1, (x.2.1.2, x.2.2.2)),
      x.1.2.2.2.2.1,
      x.1.2.2.2.2.2.1,
      x.1.2.2.2.2.2.2.1,
      x.1.2.2.2.2.2.2.2)
  invFun x :=
    ((x.1.1,
        x.2.1,
        x.2.2.1,
        x.2.2.2.1.1,
        x.2.2.2.2.1,
        x.2.2.2.2.2.1,
        x.2.2.2.2.2.2.1,
        x.2.2.2.2.2.2.2),
      ((x.1.2.1, x.2.2.2.1.2.1),
        (x.1.2.2, x.2.2.2.1.2.2)))
  left_inv x := by
    rcases x with ⟨x, p⟩
    rcases x with ⟨s, y, w, z, yz, wz, yw, ywz⟩
    rcases p with ⟨⟨pbs, pbt⟩, ⟨pws, pwt⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨s, ps⟩, y, w, ⟨z, pz⟩, yz, wz, yw, ywz⟩
    rcases ps with ⟨pbs, pws⟩
    rcases pz with ⟨pbt, pwt⟩
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def k4BaseMixedOverlapSectorEquivCore
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 ≃ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d :=
  (((k4AggregateKernelEEEEEquiv hn hb2 hc2 hd2).prodCongr
      (LinearEquiv.refl F (K4AggregatePolarCoordinateTarget n c))).trans
    k4MixedOverlapReassociateEquiv)

noncomputable def k4BaseMixedOverlapSectorRead
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 →ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d :=
  (k4BaseMixedOverlapSectorEquivCore hn hb2 hc2 hd2).toLinearMap

noncomputable def k4BaseMixedOverlapSectorBuild
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedOverlapSectorSource n b c d →ₗ[F]
      K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 :=
  (k4BaseMixedOverlapSectorEquivCore hn hb2 hc2 hd2).symm.toLinearMap

theorem k4BaseMixedOverlapSectorRead_coordinates
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2) :
    let q := k4AggregateKernelEEEERead hn hb2 hc2 hd2 x.1
    k4BaseMixedOverlapSectorRead hn hb2 hc2 hd2 x =
      ((q.1, (x.2.1.1, x.2.2.1)),
        q.2.1,
        q.2.2.1,
        (q.2.2.2.1, (x.2.1.2, x.2.2.2)),
        q.2.2.2.2.1,
        q.2.2.2.2.2.1,
        q.2.2.2.2.2.2.1,
        q.2.2.2.2.2.2.2) := by
  rfl

theorem k4BaseMixedOverlapSectorBuild_coordinates
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BaseMixedOverlapSectorSource n b c d) :
    k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x =
      (k4AggregateKernelEEEEBuild hn hb2 hc2 hd2
          (x.1.1,
            x.2.1,
            x.2.2.1,
            x.2.2.2.1.1,
            x.2.2.2.2.1,
            x.2.2.2.2.2.1,
            x.2.2.2.2.2.2.1,
            x.2.2.2.2.2.2.2),
        ((x.1.2.1, x.2.2.2.1.2.1),
          (x.1.2.2, x.2.2.2.1.2.2))) := by
  rfl

@[simp] theorem k4BaseMixedOverlapSectorRead_build
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BaseMixedOverlapSectorSource n b c d) :
    k4BaseMixedOverlapSectorRead hn hb2 hc2 hd2
        (k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2 x) = x :=
  (k4BaseMixedOverlapSectorEquivCore
    hn hb2 hc2 hd2).apply_symm_apply x

@[simp] theorem k4BaseMixedOverlapSectorBuild_read
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2) :
    k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
        (k4BaseMixedOverlapSectorRead hn hb2 hc2 hd2 x) = x :=
  (k4BaseMixedOverlapSectorEquivCore
    hn hb2 hc2 hd2).symm_apply_apply x

noncomputable def k4BaseMixedOverlapSectorEquiv
    {n b c d : Nat} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedOverlapSource n b c d hn hb2 hc2 hd2 ≃ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d where
  toLinearMap := k4BaseMixedOverlapSectorRead hn hb2 hc2 hd2
  invFun := k4BaseMixedOverlapSectorBuild hn hb2 hc2 hd2
  left_inv := k4BaseMixedOverlapSectorBuild_read hn hb2 hc2 hd2
  right_inv := k4BaseMixedOverlapSectorRead_build hn hb2 hc2 hd2

noncomputable def k4GPolarKernelMixedOverlapSectorEquiv
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4GPolarKernel n b c d ≃ₗ[F]
      K4BaseMixedOverlapSectorSource n b c d :=
  (k4GPolarKernelMixedOverlapEquiv hn2 hn hb2 hc2 hd2).trans
    (k4BaseMixedOverlapSectorEquiv hn hb2 hc2 hd2)

theorem k4GPolarKernelMixedOverlapSectorEquiv_intertwines
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (x : K4GPolarKernel n b c d) :
    k4GPolarKernelMixedOverlapSectorEquiv
        hn2 hn hb2 hc2 hd2 x =
      k4BaseMixedOverlapSectorEquiv hn hb2 hc2 hd2
        (k4GPolarKernelMixedOverlapEquiv
          hn2 hn hb2 hc2 hd2 x) := by
  rfl


end


end


end Core4loop.CompleteGraph.EvenP.BaseKKT
