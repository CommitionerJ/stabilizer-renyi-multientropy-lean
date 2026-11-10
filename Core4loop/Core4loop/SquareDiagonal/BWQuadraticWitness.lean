import Core4loop.SquareDiagonal.BWQuadraticMetabolic
import Core4loop.SquareDiagonal.BWSupportRank

open scoped BigOperators

namespace Core4loop
namespace SquareDiagonal

noncomputable section

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_rootZero_phaseWitness
    {n a b c d : ℕ} [NeZero n]
    (hwitness :
      ∀ x : SqdiagBWAAdjointGraph n a b c d,
        ∃ y : sqdiagBWAAdjointGraphRootZero n a b c d,
          sqdiagBWAAdjointGraphPolar
              (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 =
            sqdiagBWAAdjointGraphQ x)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  rcases hwitness x with ⟨y, hy⟩
  have hker :
      sqdiagBWAAdjointGraphPolarToRootZero
        (n := n) (a := a) (b := b) (c := c) (d := d) x = 0 :=
    LinearMap.mem_ker.mp hx
  have horth :
      sqdiagBWAAdjointGraphPolar
          (n := n) (a := a) (b := b) (c := c) (d := d) x y.1 = 0 := by
    have happly :=
      congrArg
        (fun L : Module.Dual F (sqdiagBWAAdjointGraphRootZero n a b c d) => L y)
        hker
    simpa [sqdiagBWAAdjointGraphPolarToRootZero] using happly
  exact hy.symm.trans horth

/--
Conditional diagnostic route only.
The same-root compatibility premise, and in particular surjectivity of
`sqdiagBWZCompatImageRootMap`, is false in the general positive
SquareDiagonal family; it fails for `n = 3` and `a = b = c = d = 1`.
Production proofs must use the adjoint-image/reduced-root route instead.
-/
theorem sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_compat_same_root
    {n a b c d : ℕ} [NeZero n]
    (hcompat :
      ∀ x : SqdiagBWAAdjointGraph n a b c d,
        ∃ t : sqdiagBWZCompatSubmodule
            (n := n) (a := a) (b := b) (c := c) (d := d),
          K_yw (n := n) (a := a) (b := b) (c := c) (d := d) t.1 =
            sqdiagBWAAdjointGraphRootMap
              (n := n) (a := a) (b := b) (c := c) (d := d) x)
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  refine
    sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_rootZero_phaseWitness
      (n := n) (a := a) (b := b) (c := c) (d := d) ?_ x hx
  intro x
  rcases hcompat x with ⟨t, ht⟩
  exact
    sqdiagBWAAdjointGraph_rootZero_phaseWitness_of_compat_same_root
      (n := n) (a := a) (b := b) (c := c) (d := d) x t ht

theorem sqdiagBWAAdjointGraph_compatSameRoot_of_imageRootMap_surjective
    {n a b c d : ℕ} [NeZero n]
    (hsurj :
      Function.Surjective
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagBWAAdjointGraph n a b c d) :
    ∃ t : sqdiagBWZCompatSubmodule
        (n := n) (a := a) (b := b) (c := c) (d := d),
      K_yw (n := n) (a := a) (b := b) (c := c) (d := d) t.1 =
        sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x := by
  have hxGraph :
      sqdiagBWAAdjointGraphPred
        (n := n) (a := a) (b := b) (c := c) (d := d) x.1 :=
    (sqdiagBWAAdjointGraphSubmodule_mem_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) x.1).mp x.2
  let R : RootTarget n b c d :=
    sqdiagBWAAdjointGraphRootMap
      (n := n) (a := a) (b := b) (c := c) (d := d) x
  have hRRange :
      R ∈
        YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    change
      sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d)
    rw [sqdiagBWAAdjointGraphRootMap_apply]
    rw [← range_K_yw_eq_sup_YW (n := n) (a := a) (b := b) (c := c) (d := d)]
    exact ⟨x.1.1, rfl⟩
  have hRZ :
      R ∈ ZDiffSpace (n := n) (b := b) (c := c) (d := d) := by
    change
      sqdiagBWAAdjointGraphRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d) x ∈
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)
    simpa [sqdiagBWAAdjointGraphRootMap_apply] using hxGraph.1
  let rootInf :
      ↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
          WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
        ZDiffSpace (n := n) (b := b) (c := c) (d := d)) :=
    ⟨R, ⟨hRRange, hRZ⟩⟩
  rcases hsurj rootInf with ⟨z, hz⟩
  rcases z.2.1 with ⟨source, hsource⟩
  have hsourceCompat :
      source ∈
        sqdiagBWZCompatSubmodule
          (n := n) (a := a) (b := b) (c := c) (d := d) := by
    change
      SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) source ∈
        sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d)
    rw [hsource]
    exact z.2.2
  refine ⟨⟨source, hsourceCompat⟩, ?_⟩
  have hzRoot :
      z.1.1 = R := by
    have hval :=
      congrArg
        (fun u :
          ↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
              WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
            ZDiffSpace (n := n) (b := b) (c := c) (d := d)) =>
            (u : RootTarget n b c d))
        hz
    simpa [sqdiagBWZCompatImageRootMap, rootInf, R] using hval
  change
    (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d) source).1 =
      sqdiagBWAAdjointGraphRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d) x
  rw [hsource, hzRoot]

theorem sqdiagBWZCompatImageRootMap_surjective_of_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F
          (↑(LinearMap.range
              (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
            sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
              WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
            ZDiffSpace (n := n) (b := b) (c := c) (d := d)))) :
    Function.Surjective
      (sqdiagBWZCompatImageRootMap
        (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  have htop :
      LinearMap.range
          (sqdiagBWZCompatImageRootMap
            (n := n) (a := a) (b := b) (c := c) (d := d)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [
      LinearMap.finrank_range_of_inj
        (sqdiagBWZCompatImageRootMap_injective
          (n := n) (a := a) (b := b) (c := c) (d := d)),
      hfin]
  exact LinearMap.range_eq_top.mp htop

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_imageRootMap_surjective
    {n a b c d : ℕ} [NeZero n]
    (hsurj :
      Function.Surjective
        (sqdiagBWZCompatImageRootMap
          (n := n) (a := a) (b := b) (c := c) (d := d)))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  exact
    sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_compat_same_root
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (fun x =>
        sqdiagBWAAdjointGraph_compatSameRoot_of_imageRootMap_surjective
          (n := n) (a := a) (b := b) (c := c) (d := d) hsurj x)
      x hx

theorem sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_imageRootMap_finrank_eq
    {n a b c d : ℕ} [NeZero n]
    (hfin :
      Module.finrank F
          (↑(LinearMap.range
              (SquareCombined (n := n) (a := a) (b := b) (c := c) (d := d)) ⊓
            sqdiagZCompatTargetSubmodule (n := n) (a := a) (b := b) (c := c) (d := d))) =
        Module.finrank F
          (↑((YDiffSpace (n := n) (b := b) (c := c) (d := d) ⊔
              WDiffSpace (n := n) (b := b) (c := c) (d := d)) ⊓
            ZDiffSpace (n := n) (b := b) (c := c) (d := d))))
    (x : SqdiagBWAAdjointGraph n a b c d)
    (hx : x ∈ sqdiagBWAAdjointGraphLagrangian n a b c d) :
    sqdiagBWAAdjointGraphQ x = 0 := by
  exact
    sqdiagBWAAdjointGraphQ_eq_zero_of_mem_lagrangian_of_imageRootMap_surjective
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (sqdiagBWZCompatImageRootMap_surjective_of_finrank_eq
        (n := n) (a := a) (b := b) (c := c) (d := d) hfin)
      x hx

end

end SquareDiagonal
end Core4loop
