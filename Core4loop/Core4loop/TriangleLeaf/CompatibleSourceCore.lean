import Core4loop.RootSpaces.KRange

namespace Core4loop
namespace TriangleLeaf

noncomputable section

noncomputable def triangleLeafBCToWQuotient
    {n a b c d : ℕ} [NeZero n] :
    (BFun4 n a c d × CFun4 n a b d) →ₗ[F]
      RootTarget n b c d ⧸ WDiffSpace :=
  (Submodule.mkQ
      (WDiffSpace (n := n) (b := b) (c := c) (d := d))).comp
    ((KBMap (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (LinearMap.fst F (BFun4 n a c d) (CFun4 n a b d)) +
      (KCMap (n := n) (a := a) (b := b) (c := c) (d := d)).comp
        (LinearMap.snd F (BFun4 n a c d) (CFun4 n a b d)))

abbrev triangleLeafCompatibleSubmodule
    (n a b c d : ℕ) [NeZero n] :=
  LinearMap.ker
    (triangleLeafBCToWQuotient
      (n := n) (a := a) (b := b) (c := c) (d := d))

noncomputable instance instFintypeTriangleLeafCompatibleSubmodule
    {n a b c d : ℕ} [NeZero n] :
    Fintype (triangleLeafCompatibleSubmodule n a b c d) :=
  Fintype.ofFinite _

theorem triangleLeafCompatibleSubmodule_carrier_iff
    {n a b c d : ℕ} [NeZero n]
    (X : BFun4 n a c d × CFun4 n a b d) :
    X ∈ triangleLeafCompatibleSubmodule n a b c d ↔
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1 +
          KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2
        ∈ WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
  change
    (Submodule.mkQ
        (WDiffSpace (n := n) (b := b) (c := c) (d := d)))
          (KBMap (n := n) (a := a) (b := b) (c := c) (d := d) X.1 +
            KCMap (n := n) (a := a) (b := b) (c := c) (d := d) X.2) = 0 ↔ _
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]

noncomputable def triangleLeafCompatibleCProj
    {n a b c d : ℕ} [NeZero n] :
    triangleLeafCompatibleSubmodule n a b c d →ₗ[F] CFun4 n a b d :=
  (LinearMap.snd F (BFun4 n a c d) (CFun4 n a b d)).comp
    (triangleLeafCompatibleSubmodule n a b c d).subtype

abbrev triangleLeafBOnly (n a b c d : ℕ) [NeZero n] :=
  LinearMap.ker
    (triangleLeafCompatibleCProj
      (n := n) (a := a) (b := b) (c := c) (d := d))

end

end TriangleLeaf
end Core4loop
