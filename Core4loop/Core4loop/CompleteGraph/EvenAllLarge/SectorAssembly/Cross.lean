import Core4loop.CompleteGraph.EvenAllLarge.Scalar.Phase
import Core4loop.CompleteGraph.EvenAllLarge.PassiveY.FullSupport
import Core4loop.CompleteGraph.EvenAllLarge.PassiveW.FullSupport
import Core4loop.CompleteGraph.EvenAllLarge.PureZ.Phase
import Core4loop.CompleteGraph.EvenAllLarge.PassiveYZ.FullSupport
import Core4loop.CompleteGraph.EvenAllLarge.PassiveWZ.FullSupport
import Core4loop.CompleteGraph.EvenAllLarge.PassiveYW.ZeroRange
import Core4loop.CompleteGraph.EvenAllLarge.PassiveYWZ.ZeroRange

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.setOption false
set_option synthInstance.maxSize 512
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

namespace Core4loop.CompleteGraph.EvenP.BaseKKT.SectorAssembly

open Core4loop
open Core4loop.SquareDiagonal.EvenP
open Core4loop.SquareDiagonal.EvenP.TotalEEEEInternal
open Core4loop.SquareDiagonal.EvenP.TotalEEEERightInternal
open Core4loop.CompleteGraph.EvenP
open Core4loop.CompleteGraph.EvenP.BaseKKT

noncomputable section

attribute [local instance] Fintype.ofFinite

private noncomputable def crossProdMonoid
    {U₁ U₂ V₁ V₂ : Type*}
    [AddCommMonoid U₁] [Module F U₁]
    [AddCommMonoid U₂] [Module F U₂]
    [AddCommMonoid V₁] [Module F V₁]
    [AddCommMonoid V₂] [Module F V₂]
    (f : U₁ →ₗ[F] Module.Dual F V₁)
    (g : U₂ →ₗ[F] Module.Dual F V₂) :
    (U₁ × U₂) →ₗ[F] Module.Dual F (V₁ × V₂) :=
  (Module.dualProdDualEquivDual F V₁ V₂).toLinearMap.comp
    (f.prodMap g)

private noncomputable abbrev SectorSource
    (n b c d : Nat) [NeZero n] :=
  K4BaseMixedOverlapSectorSource n b c d

private noncomputable abbrev SectorRight
    (n b c d : Nat) [NeZero n] :=
  TotalEEEERightReachableTarget n b c d

noncomputable def k4BaseEightSectorProductCross
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    SectorSource n b c d →ₗ[F]
      Module.Dual F (SectorRight n b c d) :=
  crossProdMonoid
    (Scalar.localScalarCross hn2 hn hb2 hc2 hd2)
    (crossProdMonoid
      (PassiveY.tailCross (n := n) (b := b))
      (crossProdMonoid
        (PassiveW.tailCross (n := n) (d := d))
        (crossProdMonoid
          (PureZ.tailCross (n := n) (c := c))
          (crossProdMonoid
            (PassiveYZ.tailCross (n := n) (b := b) (c := c))
            (crossProdMonoid
              (PassiveWZ.tailCross (n := n) (c := c) (d := d))
              (crossProdMonoid
                (0 : TotalEEEEYWLeftZero n b d →ₗ[F]
                  Module.Dual F
                    (DiamondMixedTailZero n b d (YWRightBase n)))
                (0 : TotalEEEEYWZLeftZero n b c d →ₗ[F]
                  Module.Dual F
                    (DiamondEvenAxisValueTailZero n b
                      (DiamondEvenAxisValueTailZero n c
                        (DiamondEvenAxisValueTailZero n d
                          (CyclicCube n)))))))))))

theorem k4BaseEightSectorProductCross_apply
    {n b c d : Nat} [NeZero n]
    (hn2 : 2 ≤ n) (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d)
    (s : SectorSource n b c d)
    (q : SectorRight n b c d) :
    k4BaseEightSectorProductCross hn2 hn hb2 hc2 hd2 s q =
      Scalar.localScalarCross hn2 hn hb2 hc2 hd2 s.1 q.1 +
      (PassiveY.tailCross s.2.1 q.2.1 +
      (PassiveW.tailCross s.2.2.1 q.2.2.1 +
      (PureZ.tailCross s.2.2.2.1 q.2.2.2.1 +
      (PassiveYZ.tailCross s.2.2.2.2.1 q.2.2.2.2.1 +
      (PassiveWZ.tailCross s.2.2.2.2.2.1 q.2.2.2.2.2.1 +
        (0 + 0)))))) := by
  rfl

end

end Core4loop.CompleteGraph.EvenP.BaseKKT.SectorAssembly
