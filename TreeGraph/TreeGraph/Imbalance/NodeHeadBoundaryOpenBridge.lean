import TreeGraph.Imbalance.NodeHeadBoundaryPhaseBridgeSkeleton

namespace TreeGraph
namespace Imbalance

noncomputable def headChildLocalOpenCoordOfParentSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    Copen n C :=
  (rootFieldDomainCleanEquivCopen n C)
    (headChildLocalSiteOfParent n a C rest hC site).nonRootCoord

noncomputable def headChildRootDomainFromParentSite
    {n a : Nat} [NeZero n]
    {C : RTree} {rest : List RTree}
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (s : Rep n) :
    NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) where
  rootCoord := site.rootCoord
  diagonal := s
  otherCoord := fun u => site.nonRootCoord u.1

noncomputable def headChildRootBoundaryFieldFromParentSite
    {n a : Nat} [NeZero n]
    {C : RTree} {rest : List RTree}
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest)))
    (s : Rep n) : F2 :=
  Aopen.nodeField
    (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
    (headChildRootDomainFromParentSite site s)

noncomputable def vertexCoordDomainFromBoundaryOpen
    (n : Nat) [NeZero n] (C : RTree) (y : Copen n C) :
    VertexCoordDomainClean n C := by
  cases C with
  | node b cs =>
      exact (vertexCoordDomainEquivCplus n (RTree.node b cs)).symm
        ((fun _ => 0), y)

noncomputable def headChildRootDomainFromBoundaryData
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (_hC : RTree.PositiveWeights C)
    (q : Block n (a - 1))
    (tail : CoordsList n rest)
    (s : Rep n)
    (y : Copen n C) :
    NonRootFieldDomainClean n (RTree.node a (C :: rest))
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) :=
  let childCoords := vertexCoordDomainFromBoundaryOpen n C y
  let parentCoords :=
    (parentNonRootCoordsHeadTailEquiv n a C rest).symm (childCoords, tail)
  { rootCoord := q
    diagonal := s
    otherCoord := fun u => parentCoords u.1 }

noncomputable def headChildRootBoundaryFieldFromParent
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (hC : RTree.PositiveWeights C)
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (q : Block n (a - 1))
    (tail : CoordsList n rest)
    (s : Rep n) : BoundaryField n C :=
  fun y =>
    Aopen.nodeField
      (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))
      (headChildRootDomainFromBoundaryData n a C rest hC q tail s y)

theorem ketAtPathClean_headChildRoot
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    ketAtPathClean A site [0] =
      ketAtVertexClean A site
        (headChildRootInParent (a := a) (C := C) (rest := rest)) := by
  unfold ketAtPathClean
  by_cases hp : ([0] : List Nat) ∈ RTree.addresses (RTree.node a (C :: rest))
  · rw [dif_pos hp]
    congr 1
  · exact False.elim
      (hp (headChildRootInParent (a := a) (C := C) (rest := rest)).2)

theorem braAtPathClean_headChildRoot
    {n a : Nat} [NeZero n] {C : RTree} {rest : List RTree}
    (A : NormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    braAtPathClean A site [0] =
      braAtVertexClean A site
        (headChildRootInParent (a := a) (C := C) (rest := rest)) := by
  unfold braAtPathClean
  by_cases hp : ([0] : List Nat) ∈ RTree.addresses (RTree.node a (C :: rest))
  · rw [dif_pos hp]
    congr 1
  · exact False.elim
      (hp (headChildRootInParent (a := a) (C := C) (rest := rest)).2)

theorem headBoundaryChildRootKet_eq_boundaryFamilyAtSite
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryChildRootKet
        (closeOpenNormalAssignmentClean root Aopen) site =
      headChildRootBoundaryFieldFromParentSite Aopen site
        (diagonalClean site
          (headChildRootNonRootInParent (a := a) (C := C) (rest := rest))) := by
  unfold headBoundaryChildRootKet
  rw [ketAtPathClean_headChildRoot]
  simp [headChildRootNonRootInParent, headChildRootBoundaryFieldFromParentSite,
    headChildRootDomainFromParentSite, ketAtVertexClean,
    nonRootDomainOfSiteClean, closeOpenNormalAssignmentClean]

theorem headBoundaryChildRootBra_eq_boundaryFamilyAtSite_succ
    (n a : Nat) [NeZero n]
    (C : RTree) (rest : List RTree)
    (root : RootFieldAssignmentClean n (RTree.node a (C :: rest)))
    (Aopen : OpenNormalAssignmentClean n (RTree.node a (C :: rest)))
    (site : NormalSiteClean n (RTree.node a (C :: rest))) :
    headBoundaryChildRootBra
        (closeOpenNormalAssignmentClean root Aopen) site =
      headChildRootBoundaryFieldFromParentSite Aopen site
        (diagonalClean site
          (headChildRootNonRootInParent (a := a) (C := C) (rest := rest)) + 1) := by
  unfold headBoundaryChildRootBra
  rw [braAtPathClean_headChildRoot]
  simp [headChildRootNonRootInParent, headChildRootBoundaryFieldFromParentSite,
    headChildRootDomainFromParentSite, braAtVertexClean,
    nonRootDomainOfSiteClean, closeOpenNormalAssignmentClean]

end Imbalance
end TreeGraph
