import TreeGraph.Imbalance.FinalRootIntersection

namespace TreeGraph
namespace Imbalance

private lemma numVertices_pos (T : RTree) : 0 < RTree.numVertices T := by
  cases T with
  | node a cs =>
      simp [RTree.numVertices]

private lemma numVertices_le_sum_of_mem {T : RTree} {ts : List RTree}
    (h : T ∈ ts) :
    RTree.numVertices T ≤ (ts.map RTree.numVertices).sum := by
  induction ts with
  | nil =>
      cases h
  | cons U us ih =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h
        simp
      · have hle := ih h
        simp
        omega

private lemma numVertices_lt_node_of_mem
    {C : RTree} {a : Nat} {cs : List RTree} (h : C ∈ cs) :
    RTree.numVertices C < RTree.numVertices (RTree.node a cs) := by
  have hle := numVertices_le_sum_of_mem h
  simp [RTree.numVertices]
  omega

private lemma rootWeight_pos_of_positiveWeights
    {T : RTree} (hT : RTree.PositiveWeights T) :
    0 < T.rootWeight := by
  cases T with
  | node a cs =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      simpa [RTree.rootWeight] using hnode.1

noncomputable def recursiveMessageSpace (n : Nat) [NeZero n] :
    (T : RTree) → RTree.PositiveWeights T →
      Submodule F2 (BoundaryField n T) := by
  classical
  refine WellFounded.fix (measure RTree.numVertices).wf
    (C := fun T => RTree.PositiveWeights T →
      Submodule F2 (BoundaryField n T)) ?_
  intro T rec hT
  cases T with
  | node a cs =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      let rec build
          (ds : List RTree)
          (hds : ∀ C ∈ ds, RTree.PositiveWeights C)
          (hlt : ∀ C ∈ ds,
            RTree.numVertices C < RTree.numVertices (RTree.node a cs)) :
          Submodule F2 (Field (CoordsList n ds)) :=
        match ds with
        | [] => ⊤
        | C :: rest => by
            have hC : RTree.PositiveWeights C := hds C (by simp)
            have hC_lt :
                RTree.numVertices C <
                  RTree.numVertices (RTree.node a cs) :=
              hlt C (by simp)
            have hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
              intro D hD
              exact hds D (by simp [hD])
            have hrest_lt :
                ∀ D ∈ rest,
                  RTree.numVertices D <
                    RTree.numVertices (RTree.node a cs) := by
              intro D hD
              exact hlt D (by simp [hD])
            let childSpace : Submodule F2 (BoundaryField n C) :=
              rec C hC_lt hC
            letI : FiniteDimensional F2 childSpace := inferInstance
            exact
              sliceIntersection (Cplus n C) (CoordsList n rest)
                (Kchild n C
                  (rootWeight_pos_of_positiveWeights hC)
                  childSpace)
                (build rest hrest hrest_lt)
        termination_by ds.length
      exact build cs hnode.2 (fun C hC => numVertices_lt_node_of_mem hC)

private theorem finrank_recursiveMessageSpace_build (n : Nat) [NeZero n]
    (a : Nat) (cs ds : List RTree)
    (rec : (y : RTree) →
      @WellFoundedRelation.rel RTree (measure RTree.numVertices)
        y (RTree.node a cs) →
        (fun T => RTree.PositiveWeights T →
          Submodule F2 (BoundaryField n T)) y)
    (hrec : ∀ (C : RTree)
      (hltC : @WellFoundedRelation.rel RTree (measure RTree.numVertices)
        C (RTree.node a cs))
      (hC : RTree.PositiveWeights C),
        Module.finrank F2 (rec C hltC hC) = YdimCandidate n C)
    (hds : ∀ C ∈ ds, RTree.PositiveWeights C)
    (hlt : ∀ C ∈ ds,
      RTree.numVertices C < RTree.numVertices (RTree.node a cs)) :
    Module.finrank F2
      (recursiveMessageSpace.build n a cs rec ds hds hlt) =
      (ds.map (fun C =>
        branchAllowedDim n (RTree.totalWeight C) (YdimCandidate n C))).prod := by
  induction ds with
  | nil =>
      rw [recursiveMessageSpace.build]
      rw [finrank_top]
      change Module.finrank F2 (PUnit → F2) = 1
      simp
  | cons C rest ih =>
      have hC : RTree.PositiveWeights C := hds C (by simp)
      have hC_lt :
          RTree.numVertices C < RTree.numVertices (RTree.node a cs) :=
        hlt C (by simp)
      have hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
        intro D hD
        exact hds D (by simp [hD])
      have hrest_lt : ∀ D ∈ rest,
          RTree.numVertices D < RTree.numVertices (RTree.node a cs) := by
        intro D hD
        exact hlt D (by simp [hD])
      rw [recursiveMessageSpace.build]
      let childSpace : Submodule F2 (BoundaryField n C) := rec C hC_lt hC
      have hchild_dim :
          Module.finrank F2 childSpace = YdimCandidate n C := by
        simpa [childSpace] using hrec C hC_lt hC
      have htail_dim :
          Module.finrank F2
            (recursiveMessageSpace.build n a cs rec rest hrest hrest_lt) =
            (rest.map (fun D =>
              branchAllowedDim n (RTree.totalWeight D)
                (YdimCandidate n D))).prod :=
        ih hrest hrest_lt
      calc
        Module.finrank F2
            (sliceIntersection (Cplus n C) (CoordsList n rest)
              (Kchild n C (rootWeight_pos_of_positiveWeights hC) childSpace)
              (recursiveMessageSpace.build n a cs rec rest hrest hrest_lt)) =
            Module.finrank F2
              (Kchild n C (rootWeight_pos_of_positiveWeights hC) childSpace) *
              Module.finrank F2
                (recursiveMessageSpace.build n a cs rec rest hrest hrest_lt) := by
          rw [finrank_sliceIntersection]
        _ = branchAllowedDim n (RTree.totalWeight C) (YdimCandidate n C) *
            (rest.map (fun D =>
              branchAllowedDim n (RTree.totalWeight D)
                (YdimCandidate n D))).prod := by
          rw [finrank_Kchild, hchild_dim, htail_dim]
        _ = ((C :: rest).map (fun D =>
              branchAllowedDim n (RTree.totalWeight D)
                (YdimCandidate n D))).prod := by
          simp

theorem finrank_recursiveMessageSpace (n : Nat) [NeZero n] :
    ∀ (T : RTree) (hT : RTree.PositiveWeights T),
      Module.finrank F2 (recursiveMessageSpace n T hT) =
        YdimCandidate n T := by
  classical
  intro T
  refine WellFounded.induction (measure RTree.numVertices).wf
    (C := fun T => ∀ hT : RTree.PositiveWeights T,
      Module.finrank F2 (recursiveMessageSpace n T hT) =
        YdimCandidate n T) T ?_
  intro T ih hT
  cases T with
  | node a cs =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      rw [recursiveMessageSpace, WellFounded.fix_eq]
      change Module.finrank F2
          (recursiveMessageSpace.build n a cs _ cs hnode.2
            (fun C hC => numVertices_lt_node_of_mem hC)) =
        YdimCandidate n (RTree.node a cs)
      rw [finrank_recursiveMessageSpace_build]
      · simp [YdimCandidate]
      · intro C hltC hC
        simpa [recursiveMessageSpace] using ih C hltC hC

noncomputable def Ydim (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) : Nat :=
  Module.finrank F2 (recursiveMessageSpace n T hT)

@[simp] theorem Ydim_eq_YdimCandidate (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    Ydim n T hT = YdimCandidate n T :=
  finrank_recursiveMessageSpace n T hT

theorem YdimCandidate_cast_eq_YrecInt (n : Nat) [NeZero n] :
    ∀ (T : RTree) (_hT : RTree.PositiveWeights T),
      ((YdimCandidate n T : Nat) : ℤ) = YrecInt n T := by
  classical
  intro T
  refine WellFounded.induction (measure RTree.numVertices).wf
    (C := fun T => ∀ _hT : RTree.PositiveWeights T,
      ((YdimCandidate n T : Nat) : ℤ) = YrecInt n T) T ?_
  intro T ih hT
  cases T with
  | node a cs =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      have hfactor : ∀ C ∈ cs,
          (((branchAllowedDim n (RTree.totalWeight C)
              (YdimCandidate n C) : Nat) : ℤ) =
            (nZ n) ^ RTree.totalWeight C - (tZ n) * YrecInt n C) := by
        intro C hCmem
        have hC : RTree.PositiveWeights C := hnode.2 C hCmem
        have hle0 := branchAllowedDim_subtrahend_le n C
          (rootWeight_pos_of_positiveWeights hC)
          (recursiveMessageSpace n C hC)
        have hle :
            (n - 1) * YdimCandidate n C ≤
              n ^ RTree.totalWeight C := by
          simpa [finrank_recursiveMessageSpace n C hC] using hle0
        have hcast := branchAllowedDim_cast_of_le
          (n := n) (A := RTree.totalWeight C)
          (Y := YdimCandidate n C) hle
        have hih := ih C (numVertices_lt_node_of_mem hCmem) hC
        rw [hcast, hih]
      calc
        ((YdimCandidate n (RTree.node a cs) : Nat) : ℤ) =
            ((cs.map (fun C =>
              branchAllowedDim n (RTree.totalWeight C)
                (YdimCandidate n C))).prod : ℤ) := by
          simp [YdimCandidate]
        _ = (cs.map (fun C =>
              (nZ n) ^ RTree.totalWeight C -
                (tZ n) * YrecInt n C)).prod := by
          rw [Nat.cast_list_prod]
          rw [List.map_map]
          change
            (cs.map (fun C =>
              ((branchAllowedDim n (RTree.totalWeight C)
                (YdimCandidate n C) : Nat) : ℤ))).prod =
            (cs.map (fun C =>
              (nZ n) ^ RTree.totalWeight C -
                (tZ n) * YrecInt n C)).prod
          rw [List.map_congr_left hfactor]
        _ = YrecInt n (RTree.node a cs) := by
          rw [YrecInt_node]

theorem Ydim_cast_eq_YrecInt (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Ydim n T hT : Nat) : ℤ) = YrecInt n T := by
  rw [Ydim_eq_YdimCandidate]
  exact YdimCandidate_cast_eq_YrecInt n T hT

theorem XdimCandidate_cast_eq_XrecInt (n : Nat) [NeZero n] :
    ∀ (T : RTree) (_hT : RTree.PositiveWeights T),
      ((XdimCandidate n T : Nat) : ℤ) = XrecInt n T := by
  classical
  intro T
  refine WellFounded.induction (measure RTree.numVertices).wf
    (C := fun T => ∀ _hT : RTree.PositiveWeights T,
      ((XdimCandidate n T : Nat) : ℤ) = XrecInt n T) T ?_
  intro T ih hT
  cases T with
  | node a cs =>
      have hnode : 0 < a ∧ ∀ C ∈ cs, RTree.PositiveWeights C := by
        simpa [RTree.PositiveWeights] using hT
      have hcontrib : ∀ (ds : List RTree),
          (∀ C ∈ ds, RTree.PositiveWeights C) →
          (∀ C ∈ ds,
            RTree.numVertices C < RTree.numVertices (RTree.node a cs)) →
          ∀ left : Nat,
            ((XdimChildContrib n a ds left : Nat) : ℤ) =
              childContribSum n a ds left := by
        intro ds
        induction ds with
        | nil =>
            intro hds hlt left
            simp [XdimChildContrib, childContribSum]
        | cons C rest ihrest =>
            intro hds hlt left
            have hC : RTree.PositiveWeights C := hds C (by simp)
            have hC_lt :
                RTree.numVertices C <
                  RTree.numVertices (RTree.node a cs) :=
              hlt C (by simp)
            have hrest : ∀ D ∈ rest, RTree.PositiveWeights D := by
              intro D hD
              exact hds D (by simp [hD])
            have hrest_lt : ∀ D ∈ rest,
                RTree.numVertices D <
                  RTree.numVertices (RTree.node a cs) := by
              intro D hD
              exact hlt D (by simp [hD])
            have hX :
                ((XdimCandidate n C : Nat) : ℤ) = XrecInt n C :=
              ih C hC_lt hC
            have htail :=
              ihrest hrest hrest_lt (left + RTree.totalWeight C)
            rw [XdimChildContrib_cons, childContribSum]
            simp [hX, htail, XrecInt, nZ, Nat.cast_add,
              Nat.cast_mul, Nat.cast_pow]
      calc
        ((XdimCandidate n (RTree.node a cs) : Nat) : ℤ) =
            ((YdimCandidate n (RTree.node a cs) +
              XdimChildContrib n a cs 0 : Nat) : ℤ) := by
          rw [XdimCandidate_node]
        _ = ((YdimCandidate n (RTree.node a cs) : Nat) : ℤ) +
            ((XdimChildContrib n a cs 0 : Nat) : ℤ) := by
          norm_num
        _ = YrecInt n (RTree.node a cs) +
            childContribSum n a cs 0 := by
          rw [YdimCandidate_cast_eq_YrecInt n (RTree.node a cs) hT]
          rw [hcontrib cs hnode.2
            (fun C hC => numVertices_lt_node_of_mem hC) 0]
        _ = XrecInt n (RTree.node a cs) := by
          rw [XrecInt_node]

noncomputable def Xdim (n : Nat) (T : RTree) : Nat :=
  XdimCandidate n T

@[simp] theorem Xdim_leaf (n a : Nat) :
    Xdim n (RTree.node a []) = 1 := by
  simp [Xdim]

theorem Xdim_node (n a : Nat) (cs : List RTree) :
    Xdim n (RTree.node a cs) =
      YdimCandidate n (RTree.node a cs) +
        XdimChildContrib n a cs 0 := by
  rw [Xdim, XdimCandidate_node]

theorem Xdim_node_eq_Ydim_add_childContrib
    (n : Nat) [NeZero n] (a : Nat) (cs : List RTree)
    (hT : RTree.PositiveWeights (RTree.node a cs)) :
    Xdim n (RTree.node a cs) =
      Ydim n (RTree.node a cs) hT +
        XdimChildContrib n a cs 0 := by
  rw [Xdim_node, Ydim_eq_YdimCandidate]

theorem Xdim_cast_eq_XrecInt (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Xdim n T : Nat) : ℤ) = XrecInt n T := by
  rw [Xdim]
  exact XdimCandidate_cast_eq_XrecInt n T hT

theorem Ydim_cast_eq_Ypoly (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Ydim n T hT : Nat) : ℤ) = Ypoly n T := by
  simpa [YrecInt] using Ydim_cast_eq_YrecInt n T hT

theorem Xdim_cast_eq_Xpoly (n : Nat) [NeZero n]
    (T : RTree) (hT : RTree.PositiveWeights T) :
    ((Xdim n T : Nat) : ℤ) = Xpoly n T := by
  simpa [XrecInt] using Xdim_cast_eq_XrecInt n T hT

end Imbalance
end TreeGraph
