import TreeGraph.Poly

namespace TreeGraph

structure Term where
  deg : Nat
  compWeight : Nat
  deriving Repr, DecidableEq

namespace Term

noncomputable def value (n : Nat) (t : Term) : ℤ :=
  (-1 : ℤ) ^ t.deg * (tZ n) ^ t.deg * (nZ n) ^ t.compWeight

protected def add (s t : Term) : Term :=
  { deg := s.deg + t.deg, compWeight := s.compWeight + t.compWeight }

theorem value_add (n : Nat) (s t : Term) :
    Term.value n (Term.add s t) = Term.value n s * Term.value n t := by
  simp [Term.value, Term.add, pow_add]
  ring

end Term

noncomputable def termSum (n : Nat) (xs : List Term) : ℤ :=
  (xs.map (Term.value n)).sum

noncomputable def combineTermLists : List (List Term) → List Term
  | [] => [{ deg := 0, compWeight := 0 }]
  | xs :: rest =>
      xs.flatMap (fun x =>
        (combineTermLists rest).map (fun y => Term.add x y))

noncomputable def shiftTerm (shift : Nat) (t : Term) : Term :=
  { deg := t.deg, compWeight := t.compWeight + shift }

def raiseDegree (t : Term) : Term :=
  { deg := 1 + t.deg, compWeight := t.compWeight }

theorem termSum_nil (n : Nat) :
    termSum n [] = 0 := by
  simp [termSum]

theorem termSum_cons (n : Nat) (t : Term) (xs : List Term) :
    termSum n (t :: xs) = Term.value n t + termSum n xs := by
  simp [termSum]

theorem termSum_append (n : Nat) (xs ys : List Term) :
    termSum n (xs ++ ys) = termSum n xs + termSum n ys := by
  simp [termSum]

theorem Term.value_raiseDegree (n : Nat) (t : Term) :
    Term.value n (raiseDegree t) = - (tZ n) * Term.value n t := by
  simp [raiseDegree, Term.value, pow_add]
  ring

theorem value_shiftTerm (n shift : Nat) (t : Term) :
    Term.value n (shiftTerm shift t) = (nZ n) ^ shift * Term.value n t := by
  simp [shiftTerm, Term.value, pow_add]
  ring

theorem termSum_map_raiseDegree (n : Nat) (xs : List Term) :
    termSum n (xs.map raiseDegree) =
      - (tZ n) * termSum n xs := by
  induction xs with
  | nil =>
      simp [termSum]
  | cons t ts ih =>
      simp only [List.map_cons]
      rw [termSum_cons, termSum_cons, Term.value_raiseDegree, ih]
      ring

theorem termSum_map_add_left (n : Nat) (x : Term) (ys : List Term) :
    termSum n (ys.map (fun y => Term.add x y)) =
      Term.value n x * termSum n ys := by
  induction ys with
  | nil =>
      simp [termSum]
  | cons y ys ih =>
      simp only [List.map_cons]
      rw [termSum_cons, termSum_cons, Term.value_add, ih]
      ring

theorem termSum_pairProduct (n : Nat) (xs ys : List Term) :
    termSum n (xs.flatMap (fun x => ys.map (fun y => Term.add x y))) =
      termSum n xs * termSum n ys := by
  induction xs with
  | nil =>
      simp [termSum]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [termSum_append, termSum_map_add_left, ih, termSum_cons]
      ring

theorem termSum_combine (n : Nat) (xss : List (List Term)) :
    termSum n (combineTermLists xss) = (xss.map (termSum n)).prod := by
  induction xss with
  | nil =>
      simp [combineTermLists, termSum, Term.value]
  | cons xs rest ih =>
      simp [combineTermLists, termSum_pairProduct, ih]

theorem termSum_shiftTerm (n shift : Nat) (xs : List Term) :
    termSum n (xs.map (shiftTerm shift)) = (nZ n) ^ shift * termSum n xs := by
  induction xs with
  | nil =>
      simp [termSum]
  | cons t ts ih =>
      simp only [List.map_cons]
      rw [termSum_cons, termSum_cons, value_shiftTerm, ih]
      ring

private lemma numVertices_pos (T : RTree) : 0 < RTree.numVertices T := by
  cases T with
  | node a cs =>
      simp [RTree.numVertices]

private lemma numVertices_le_sum_of_mem {T : RTree} {ts : List RTree} (h : T ∈ ts) :
    RTree.numVertices T ≤ (ts.map RTree.numVertices).sum := by
  induction ts with
  | nil =>
      cases h
  | cons U us ih =>
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst h
        simp
      · have hlt := ih h
        simp
        omega

private lemma numVertices_lt_node_of_mem {C : RTree} {a : Nat} {cs : List RTree}
    (h : C ∈ cs) :
    RTree.numVertices C < RTree.numVertices (RTree.node a cs) := by
  have hle := numVertices_le_sum_of_mem h
  simp [RTree.numVertices]
  omega

noncomputable def rootedTerms : RTree → List Term
  | RTree.node _ cs =>
      combineTermLists (cs.map (fun C =>
        [{ deg := 0, compWeight := RTree.totalWeight C }]
          ++ ((rootedTerms C).map (fun t =>
            raiseDegree t))))
termination_by T => RTree.numVertices T
decreasing_by
  exact numVertices_lt_node_of_mem (by assumption)

noncomputable def branchOptions (C : RTree) : List Term :=
  [{ deg := 0, compWeight := RTree.totalWeight C }]
    ++ ((rootedTerms C).map (fun t =>
      raiseDegree t))

noncomputable def childAllTermsShiftedFrom (subTerms : RTree → List Term)
    (a : Nat) : List RTree → Nat → List Term
  | [], _ => []
  | C :: rest, left =>
      let right := (rest.map RTree.totalWeight).sum
      let shift := a + left + right
      ((subTerms C).map (shiftTerm shift))
        ++ childAllTermsShiftedFrom subTerms a rest (left + RTree.totalWeight C)

noncomputable def allTermsFuel : Nat → RTree → List Term
  | 0, _ => []
  | fuel + 1, RTree.node a cs =>
      rootedTerms (RTree.node a cs)
        ++ childAllTermsShiftedFrom (allTermsFuel fuel) a cs 0

noncomputable def allTerms (T : RTree) : List Term :=
  allTermsFuel (RTree.numVertices T) T

noncomputable def childAllTermsShifted (a : Nat) : List RTree → Nat → List Term :=
  childAllTermsShiftedFrom allTerms a

theorem termSum_branchOptions (n : Nat) (C : RTree) :
    termSum n (branchOptions C)
      = (nZ n) ^ (RTree.totalWeight C) - (tZ n) * termSum n (rootedTerms C) := by
  rw [branchOptions, termSum_append, termSum_map_raiseDegree]
  simp [termSum, Term.value]
  ring

theorem termSum_branchOptions_inline (n : Nat) (C : RTree) :
    termSum n
        ({ deg := 0, compWeight := RTree.totalWeight C } ::
          ((rootedTerms C).map (fun t => raiseDegree t))) =
      (nZ n) ^ (RTree.totalWeight C) - (tZ n) * termSum n (rootedTerms C) := by
  simpa [branchOptions] using termSum_branchOptions n C

private theorem branchProduct_eq (n : Nat) (cs : List RTree)
    (h : ∀ C ∈ cs, Ypoly n C = termSum n (rootedTerms C)) :
    (cs.map (fun C =>
      (nZ n) ^ RTree.totalWeight C - (tZ n) * Ypoly n C)).prod =
    (cs.map (fun C =>
      termSum n
        ({ deg := 0, compWeight := RTree.totalWeight C } ::
          ((rootedTerms C).map (fun t => raiseDegree t))))).prod := by
  induction cs with
  | nil =>
      simp
  | cons C rest ih =>
      have hC : Ypoly n C = termSum n (rootedTerms C) := h C (by simp)
      have hrest : ∀ D ∈ rest, Ypoly n D = termSum n (rootedTerms D) := by
        intro D hD
        exact h D (by simp [hD])
      have hopt := termSum_branchOptions_inline n C
      simp [hC, hopt, ih hrest]

theorem Ypoly_eq_rootedTerms (n : Nat) (T : RTree) :
    Ypoly n T = termSum n (rootedTerms T) := by
  induction T using rootedTerms.induct with
  | case1 a cs ih =>
      simpa [Ypoly, rootedTerms, termSum_combine] using branchProduct_eq n cs ih

theorem childContribSum_eq_childAllTermsShiftedFrom
    (n a : Nat) (cs : List RTree) (left : Nat)
    (subTerms : RTree → List Term)
    (hsub : ∀ C ∈ cs, Xpoly n C = termSum n (subTerms C)) :
    childContribSum n a cs left =
      termSum n (childAllTermsShiftedFrom subTerms a cs left) := by
  induction cs generalizing left with
  | nil =>
      simp [childContribSum, childAllTermsShiftedFrom, termSum]
  | cons C rest ih =>
      have hC : Xpoly n C = termSum n (subTerms C) := hsub C (by simp)
      have hrest : ∀ D ∈ rest, Xpoly n D = termSum n (subTerms D) := by
        intro D hD
        exact hsub D (by simp [hD])
      simp [childContribSum, childAllTermsShiftedFrom, termSum_append,
        termSum_shiftTerm, hC, ih (left + RTree.totalWeight C) hrest]

theorem Xpoly_eq_allTermsFuel_of_le (n fuel : Nat) (T : RTree)
    (h : RTree.numVertices T ≤ fuel) :
    Xpoly n T = termSum n (allTermsFuel fuel T) := by
  induction T using rootedTerms.induct generalizing fuel with
  | case1 a cs ih =>
      cases fuel with
      | zero =>
          simp [RTree.numVertices] at h
      | succ fuel =>
          have hchild :
              ∀ C ∈ cs, Xpoly n C = termSum n (allTermsFuel fuel C) := by
            intro C hC
            apply ih C hC fuel
            have hlt := numVertices_lt_node_of_mem (C := C) (a := a) (cs := cs) hC
            omega
          simp [Xpoly, allTermsFuel, termSum_append, Ypoly_eq_rootedTerms,
            childContribSum_eq_childAllTermsShiftedFrom n a cs 0
              (allTermsFuel fuel) hchild]

theorem Xpoly_eq_allTerms (n : Nat) (T : RTree) :
    Xpoly n T = termSum n (allTerms T) := by
  induction T using rootedTerms.induct with
  | case1 a cs ih =>
      have hsub : ∀ C ∈ cs, Xpoly n C = termSum n (allTerms C) := by
        intro C hC
        exact ih C hC
      unfold allTerms
      exact Xpoly_eq_allTermsFuel_of_le n (RTree.numVertices (RTree.node a cs))
        (RTree.node a cs) le_rfl

end TreeGraph
