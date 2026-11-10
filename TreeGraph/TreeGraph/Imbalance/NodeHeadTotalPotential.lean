import TreeGraph.Imbalance.NodeHeadSiteShear

namespace TreeGraph
namespace Imbalance

noncomputable def copenTotalDiag
    (n : Nat) [NeZero n] (C : RTree)
    (y : Copen n C) : Rep n :=
  let coords := (rootFieldDomainCleanEquivCopen n C).symm y
  ∑ v : NonRootVertex C,
    ∑ j : Fin (NonRootVertex.weight v), coords v j

noncomputable def nonRootDomainTotalDiag
    (n : Nat) [NeZero n] (C : RTree)
    (v : NonRootVertex C)
    (dom : NonRootFieldDomainClean n C v) : Rep n :=
  (∑ i : Fin (C.rootWeight - 1), dom.rootCoord i) +
    dom.diagonal +
      ∑ u : OtherNonRootVertexClean C v,
        ∑ j : Fin (NonRootVertex.weight u.1), dom.otherCoord u j

noncomputable def otherNonRootVertexEquivSubtypeNe
    (C : RTree) (v : NonRootVertex C) :
    OtherNonRootVertexClean C v ≃ { u : NonRootVertex C // u ≠ v } where
  toFun u :=
    ⟨u.1, by
      intro h
      exact u.2 (congrArg (fun w : NonRootVertex C => w.1.1) h)⟩
  invFun u :=
    ⟨u.1, by
      intro haddr
      apply u.2
      apply Subtype.ext
      apply Subtype.ext
      exact haddr⟩
  left_inv u := by
    rfl
  right_inv u := by
    rfl

theorem sum_nonRootVertex_eq_self_add_other
    (C : RTree) (v : NonRootVertex C)
    (f : NonRootVertex C → Rep n) :
    (∑ u : NonRootVertex C, f u) =
      f v + ∑ u : OtherNonRootVertexClean C v, f u.1 := by
  classical
  let e := otherNonRootVertexEquivSubtypeNe C v
  have hother :
      (∑ u : OtherNonRootVertexClean C v, f u.1) =
        ∑ u : { u : NonRootVertex C // u ≠ v }, f u.1 := by
    exact Fintype.sum_equiv e
      (fun u : OtherNonRootVertexClean C v => f u.1)
      (fun u : { u : NonRootVertex C // u ≠ v } => f u.1)
      (by intro u; rfl)
  have hsub :
      (∑ x ∈ (Finset.univ.erase v), f x) =
        ∑ u : { u : NonRootVertex C // u ≠ v }, f u.1 := by
    refine Finset.sum_subtype (Finset.univ.erase v) ?_ f
    intro x
    simp
  have herase :
      (∑ x ∈ (Finset.univ.erase v), f x) + f v =
        ∑ x ∈ (Finset.univ : Finset (NonRootVertex C)), f x := by
    exact Finset.sum_erase_add (Finset.univ : Finset (NonRootVertex C))
      f (Finset.mem_univ v)
  rw [hother, ← hsub]
  rw [← herase]
  rw [add_comm]

theorem copenTotalDiag_rootFieldDomainCleanEquivCopen
    (n : Nat) [NeZero n] (C : RTree)
    (coords : RootFieldDomainClean n C) :
    copenTotalDiag n C ((rootFieldDomainCleanEquivCopen n C) coords) =
      ∑ v : NonRootVertex C,
        ∑ j : Fin (NonRootVertex.weight v), coords v j := by
  simp [copenTotalDiag]

theorem nonRootDomainTotalDiag_nonRootDomainOfSiteClean
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C)
    (v : NonRootVertex C) (shift : Rep n) :
    nonRootDomainTotalDiag n C v
        (nonRootDomainOfSiteClean site v shift) =
      (∑ i : Fin (C.rootWeight - 1), site.rootCoord i) +
        copenTotalDiag n C
          ((rootFieldDomainCleanEquivCopen n C) site.nonRootCoord) +
        shift := by
  classical
  rw [copenTotalDiag_rootFieldDomainCleanEquivCopen]
  unfold nonRootDomainTotalDiag nonRootDomainOfSiteClean diagonalClean
  rw [sum_nonRootVertex_eq_self_add_other C v
      (fun u : NonRootVertex C =>
        ∑ j : Fin (NonRootVertex.weight u), site.nonRootCoord u j)]
  set R : Rep n := ∑ i : Fin (C.rootWeight - 1), site.rootCoord i
  set V : Rep n := ∑ j : Fin (NonRootVertex.weight v), site.nonRootCoord v j
  set O : Rep n :=
    ∑ u : OtherNonRootVertexClean C v,
      ∑ j : Fin (NonRootVertex.weight u.1), site.nonRootCoord u.1 j
  change R + (V + shift) + O = R + (V + O) + shift
  abel

theorem nonRootDomainTotalDiag_nonRootDomainOfSiteClean_zero
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C)
    (v : NonRootVertex C) :
    nonRootDomainTotalDiag n C v
        (nonRootDomainOfSiteClean site v 0) =
      (∑ i : Fin (C.rootWeight - 1), site.rootCoord i) +
        copenTotalDiag n C
          ((rootFieldDomainCleanEquivCopen n C) site.nonRootCoord) := by
  rw [nonRootDomainTotalDiag_nonRootDomainOfSiteClean]
  simp

theorem nonRootDomainTotalDiag_nonRootDomainOfSiteClean_one
    (n : Nat) [NeZero n] (C : RTree)
    (site : NormalSiteClean n C)
    (v : NonRootVertex C) :
    nonRootDomainTotalDiag n C v
        (nonRootDomainOfSiteClean site v 1) =
      (∑ i : Fin (C.rootWeight - 1), site.rootCoord i) +
        copenTotalDiag n C
          ((rootFieldDomainCleanEquivCopen n C) site.nonRootCoord) +
        1 := by
  rw [nonRootDomainTotalDiag_nonRootDomainOfSiteClean]

end Imbalance
end TreeGraph
