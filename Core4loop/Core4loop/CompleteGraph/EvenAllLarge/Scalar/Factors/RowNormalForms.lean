import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Factors.RowNormalFormsCore

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.EEEEInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT
open Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar

noncomputable section

private theorem add_seven_reassoc
    {V : Type*} [AddCommGroup V] (a b c d e f g : V) :
    (((a + b) + d) + e) + ((f + c) + g) =
      (a + (b + c)) + ((d + e) + (f + g)) := by
  ac_rfl

theorem b11Read_apply
    {n : Nat} [NeZero n] (q : K4AggregateEEEEScalarKernel n) :
    b11Read q = q.1.1.1.2.2 := rfl

theorem w11Read_apply
    {n : Nat} [NeZero n] (q : K4AggregateEEEEScalarKernel n) :
    w11Read q = q.1.1.2.2.2 := rfl

noncomputable def scalarAggregateRead
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F] K4AggregateEEEEScalarKernel n where
  toFun s := s.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def scalarPBRead
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F] Profile n where
  toFun s := s.2.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def scalarBFreeHeadRead
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F] CyclicCube n where
  toFun s := s.2.1.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def scalarWFreeHeadRead
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F] CyclicCube n where
  toFun s := s.2.2.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def scalarStarRead
    {n : Nat} [NeZero n] :
    K4BaseMixedScalarSector n →ₗ[F]
      (CyclicCube n × CyclicCube n) :=
  LinearMap.prod
    (scalarBFreeHeadRead + b11Read.comp scalarAggregateRead)
    (scalarWFreeHeadRead + w11Read.comp scalarAggregateRead)

theorem scalarStarRead_fst_apply
    {n : Nat} [NeZero n] (s : K4BaseMixedScalarSector n) :
    (scalarStarRead s).1 = s.2.1.2.1 + b11Read s.1 := rfl

theorem scalarStarRead_snd_apply
    {n : Nat} [NeZero n] (s : K4BaseMixedScalarSector n) :
    (scalarStarRead s).2 = s.2.2.1.1 + w11Read s.1 := rfl

noncomputable def row000CanonicalMap
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    K4BaseMixedScalarSector n →ₗ[F] CyclicCube n :=
  (baseBRow hn2 hn hb2 hc2 hd2).comp scalarPBRead +
    (linkedRow hn2 hn hb2 hc2 hd2).comp
      (linkedRead.comp scalarAggregateRead) +
    (starRow hn2 hn hb2 hc2 hd2).comp scalarStarRead

theorem row000_lhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.1 =
      row000CanonicalMap hn2 hn hb2 hc2 hd2 s := by
  simp only [row000CanonicalMap, LinearMap.add_apply,
    LinearMap.comp_apply, scalarPBRead, scalarAggregateRead,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [baseBRow_normalized, linkedRow_normalized,
    starRow_normalized, row000_apply,
    ShallowProjectionProbe.scalarLeftCoordinate_B00,
    ShallowProjectionProbe.scalarLeftCoordinate_B10,
    ShallowProjectionProbe.scalarLeftCoordinate_Wsum,
    AllCoordinatesProbe.scalarLeftCoordinate_B01,
    AllCoordinatesProbe.scalarLeftCoordinate_B11,
    AllCoordinatesProbe.scalarLeftCoordinate_W10,
    AllCoordinatesProbe.scalarLeftCoordinate_W11]
  rw [scalarStarRead_fst_apply, scalarStarRead_snd_apply,
    linkedRead_fst, linkedRead_snd, b11Read_apply, w11Read_apply]
  simp only [map_add]
  exact add_seven_reassoc _ _ _ _ _ _ _

theorem row000_rhs_normalized
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    row000CanonicalMap hn2 hn hb2 hc2 hd2 =
      (baseBRow hn2 hn hb2 hc2 hd2).comp scalarPBRead +
        (linkedRow hn2 hn hb2 hc2 hd2).comp
          (linkedRead.comp scalarAggregateRead) +
        (starRow hn2 hn hb2 hc2 hd2).comp scalarStarRead := rfl

theorem row000_normal_form
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : K4BaseMixedScalarSector n) :
    (scalarCoeffMap hn2 hn hb2 hc2 hd2 s).1.1.1 =
      row000CanonicalMap hn2 hn hb2 hc2 hd2 s :=
  row000_lhs_normalized hn2 hn hb2 hc2 hd2 s


end

end Core4loop.CompleteGraph.EvenP.BaseKKT.Scalar
