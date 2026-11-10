import TreeGraph.Imbalance.NodeHeadFullSignedSum

namespace TreeGraph
namespace Imbalance

def blockSplitDiagInit {b : Nat} (_hb : 0 < b) (i : Fin (b - 1)) :
    Fin b :=
  ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le b 1)⟩

def blockSplitDiagLast {b : Nat} (hb : 0 < b) : Fin b :=
  ⟨b - 1, by omega⟩

noncomputable def blockLastToDiagPairEquiv
    (n b : Nat) [NeZero n] :
    Block n (b - 1) × Rep n ≃ Block n (b - 1) × Rep n where
  toFun P := (P.1, P.2 + ∑ i : Fin (b - 1), P.1 i)
  invFun P := (P.1, P.2 - ∑ i : Fin (b - 1), P.1 i)
  left_inv P := by
    ext
    · rfl
    · simp
  right_inv P := by
    ext
    · rfl
    · simp

noncomputable def blockSplitDiagEquiv
    (n b : Nat) [NeZero n] (hb : 0 < b) :
    Block n b ≃ Block n (b - 1) × Rep n :=
  (blockSplitLastEquiv n b hb).trans (blockLastToDiagPairEquiv n b)

theorem blockSplitLastEquiv_fst_apply_eq_init
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (x : Block n b) (i : Fin (b - 1)) :
    (blockSplitLastEquiv n b hb x).1 i =
      x (blockSplitDiagInit hb i) := by
  change
    x (⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.sub_le b 1)⟩ : Fin b) =
      x (blockSplitDiagInit hb i)
  apply congrArg x
  exact Fin.ext rfl

theorem blockSplitLastEquiv_snd_eq_last
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (x : Block n b) :
    (blockSplitLastEquiv n b hb x).2 =
      x (blockSplitDiagLast hb) := by
  change x (⟨b - 1, by omega⟩ : Fin b) = x (blockSplitDiagLast hb)
  apply congrArg x
  exact Fin.ext rfl

theorem diag_eq_splitLast_sum
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (x : Block n b) :
    diag n b x =
      (∑ i : Fin (b - 1), (blockSplitLastEquiv n b hb x).1 i) +
        (blockSplitLastEquiv n b hb x).2 := by
  cases b with
  | zero =>
      omega
  | succ k =>
      rw [diag, Fin.sum_univ_castSucc]
      have hsum :
          (∑ i : Fin k,
            (blockSplitLastEquiv n (Nat.succ k) hb x).1 i) =
            ∑ i : Fin k, x (Fin.castSucc i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [blockSplitLastEquiv_fst_apply_eq_init]
        apply congrArg x
        exact Fin.ext rfl
      have hlast :
          (blockSplitLastEquiv n (Nat.succ k) hb x).2 =
            x (Fin.last k) := by
        rw [blockSplitLastEquiv_snd_eq_last]
        apply congrArg x
        exact Fin.ext rfl
      change
        (∑ i : Fin k, x (Fin.castSucc i)) + x (Fin.last k) =
          (∑ i : Fin k,
            (blockSplitLastEquiv n (Nat.succ k) hb x).1 i) +
            (blockSplitLastEquiv n (Nat.succ k) hb x).2
      rw [hsum, hlast]

theorem blockSplitDiagEquiv_fst_apply_eq_init
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (x : Block n b) (i : Fin (b - 1)) :
    (blockSplitDiagEquiv n b hb x).1 i =
      x (blockSplitDiagInit hb i) := by
  unfold blockSplitDiagEquiv blockLastToDiagPairEquiv
  simp [blockSplitLastEquiv_fst_apply_eq_init]

theorem blockSplitDiagEquiv_snd_eq_diag
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (x : Block n b) :
    (blockSplitDiagEquiv n b hb x).2 = diag n b x := by
  unfold blockSplitDiagEquiv blockLastToDiagPairEquiv
  dsimp
  rw [diag_eq_splitLast_sum n b hb x]
  abel

theorem blockSplitDiagEquiv_diag
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (u : Block n (b - 1)) (s : Rep n) :
    diag n b ((blockSplitDiagEquiv n b hb).symm (u, s)) = s := by
  have h :=
    blockSplitDiagEquiv_snd_eq_diag n b hb
      ((blockSplitDiagEquiv n b hb).symm (u, s))
  simpa using h.symm

theorem blockSplitDiagEquiv_init
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (u : Block n (b - 1)) (s : Rep n) (i : Fin (b - 1)) :
    ((blockSplitDiagEquiv n b hb).symm (u, s))
        (blockSplitDiagInit hb i) = u i := by
  have h :=
    blockSplitDiagEquiv_fst_apply_eq_init n b hb
      ((blockSplitDiagEquiv n b hb).symm (u, s)) i
  simpa using h.symm

theorem PiCoeff_eq_sum_blockSplitDiag
    (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) (s : Rep n) (y : C0) :
    PiCoeff n ha C0 h (s, y) =
      ∑ u : Block n (a - 1),
        h ((blockSplitDiagEquiv n a ha).symm (u, s), y) := by
  classical
  let e := blockSplitDiagEquiv n a ha
  rw [PiCoeff_apply]
  have hsum :
      (∑ x : Block n a,
        if diag n a x = s then h (x, y) else 0) =
        ∑ p : Block n (a - 1) × Rep n,
          if p.2 = s then h (e.symm p, y) else 0 := by
    calc
      (∑ x : Block n a,
        if diag n a x = s then h (x, y) else 0) =
          ∑ x : Block n a,
            if (e x).2 = s then h (e.symm (e x), y) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [blockSplitDiagEquiv_snd_eq_diag]
            have hx : e.symm (e x) = x := e.left_inv x
            rw [hx]
      _ =
          ∑ p : Block n (a - 1) × Rep n,
            if p.2 = s then h (e.symm p, y) else 0 := by
            exact Equiv.sum_comp e
              (fun p : Block n (a - 1) × Rep n =>
                if p.2 = s then h (e.symm p, y) else 0)
  rw [hsum]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro u _
  simp [e]

theorem PiFull_apply_eq_sum_blockSplitDiag
    (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) (s : Rep n) (μ : C0 → F2) :
    PiFull n ha C0 h s μ =
      ∑ y : C0,
        μ y *
          (∑ u : Block n (a - 1),
            h ((blockSplitDiagEquiv n a ha).symm (u, s), y)) := by
  rw [PiFull_apply]
  change
    (∑ y : C0, μ y * PiCoeff n ha C0 h (s, y)) =
      ∑ y : C0,
        μ y *
          (∑ u : Block n (a - 1),
            h ((blockSplitDiagEquiv n a ha).symm (u, s), y))
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [PiCoeff_eq_sum_blockSplitDiag]

noncomputable def blockLastToDiagShearEquiv
    (n b : Nat) [NeZero n] (hb : 0 < b) :
    Block n b ≃ Block n b :=
  ((blockSplitLastEquiv n b hb).trans
    (blockLastToDiagPairEquiv n b)).trans
      (blockSplitLastEquiv n b hb).symm

theorem blockLastToDiagShearEquiv_split_snd_eq_diag
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (x : Block n b) :
    (blockSplitLastEquiv n b hb
      ((blockLastToDiagShearEquiv n b hb) x)).2 =
      diag n b x := by
  unfold blockLastToDiagShearEquiv blockLastToDiagPairEquiv
  dsimp
  rw [Equiv.apply_symm_apply]
  rw [diag_eq_splitLast_sum n b hb x]
  abel

theorem blockLastToDiagShearEquiv_last_eq_diag
    (n b : Nat) [NeZero n] (hb : 0 < b)
    (x : Block n b) :
    (blockLastToDiagShearEquiv n b hb x) (blockSplitDiagLast hb) =
      diag n b x := by
  have hlast :=
    blockSplitLastEquiv_snd_eq_last n b hb
      ((blockLastToDiagShearEquiv n b hb) x)
  have hdiag :=
    blockLastToDiagShearEquiv_split_snd_eq_diag n b hb x
  exact hlast.symm.trans hdiag

noncomputable def PiLastCoeff (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0] :
    ((Block n a × C0 → F2) →ₗ[F2] (Rep n × C0 → F2)) where
  toFun h := fun p =>
    ∑ x : Block n a,
      if x (blockSplitDiagLast ha) = p.1 then h (x, p.2) else 0
  map_add' h k := by
    classical
    ext p
    change
      (∑ x : Block n a,
        if x (blockSplitDiagLast ha) = p.1
          then h (x, p.2) + k (x, p.2) else 0) =
        (∑ x : Block n a,
          if x (blockSplitDiagLast ha) = p.1
            then h (x, p.2) else 0) +
          ∑ x : Block n a,
            if x (blockSplitDiagLast ha) = p.1
              then k (x, p.2) else 0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases hx : x (blockSplitDiagLast ha) = p.1 <;> simp [hx]
  map_smul' r h := by
    classical
    ext p
    change
      (∑ x : Block n a,
        if x (blockSplitDiagLast ha) = p.1
          then r * h (x, p.2) else 0) =
        r * ∑ x : Block n a,
          if x (blockSplitDiagLast ha) = p.1
            then h (x, p.2) else 0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    by_cases hx : x (blockSplitDiagLast ha) = p.1 <;> simp [hx]

@[simp] theorem PiLastCoeff_apply (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) (p : Rep n × C0) :
    PiLastCoeff n ha C0 h p =
      ∑ x : Block n a,
        if x (blockSplitDiagLast ha) = p.1 then h (x, p.2) else 0 := rfl

noncomputable def PiLastFull (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0] :
    ((Block n a × C0 → F2) →ₗ[F2]
      (Rep n → Module.Dual F2 (C0 → F2))) where
  toFun h := fun s =>
    TreeGraph.dotLinear C0 (fun y => PiLastCoeff n ha C0 h (s, y))
  map_add' h k := by
    classical
    funext s
    apply LinearMap.ext
    intro m
    change
      (∑ y : C0, m y *
        (∑ x : Block n a,
          if x (blockSplitDiagLast ha) = s
            then h (x, y) + k (x, y) else 0)) =
        (∑ y : C0, m y *
          (∑ x : Block n a,
            if x (blockSplitDiagLast ha) = s then h (x, y) else 0)) +
          ∑ y : C0, m y *
            (∑ x : Block n a,
              if x (blockSplitDiagLast ha) = s then k (x, y) else 0)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro y _
    have hinner :
        (∑ x : Block n a,
          if x (blockSplitDiagLast ha) = s
            then h (x, y) + k (x, y) else 0) =
          (∑ x : Block n a,
            if x (blockSplitDiagLast ha) = s then h (x, y) else 0) +
            ∑ x : Block n a,
              if x (blockSplitDiagLast ha) = s then k (x, y) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hx : x (blockSplitDiagLast ha) = s <;> simp [hx]
    rw [hinner, mul_add]
  map_smul' r h := by
    classical
    funext s
    apply LinearMap.ext
    intro m
    change
      (∑ y : C0, m y *
        (∑ x : Block n a,
          if x (blockSplitDiagLast ha) = s
            then r * h (x, y) else 0)) =
        r * ∑ y : C0, m y *
          (∑ x : Block n a,
            if x (blockSplitDiagLast ha) = s then h (x, y) else 0)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y _
    have hinner :
        (∑ x : Block n a,
          if x (blockSplitDiagLast ha) = s
            then r * h (x, y) else 0) =
          r * ∑ x : Block n a,
            if x (blockSplitDiagLast ha) = s then h (x, y) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hx : x (blockSplitDiagLast ha) = s <;> simp [hx]
    rw [hinner]
    ring

@[simp] theorem PiLastFull_apply (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) (s : Rep n) :
    PiLastFull n ha C0 h s =
      TreeGraph.dotLinear C0 (fun y => PiLastCoeff n ha C0 h (s, y)) := rfl

theorem PiLastCoeff_eq_PiCoeff_comp_shear
    (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) :
    PiLastCoeff n ha C0 h =
      PiCoeff n ha C0
        (fun p => h ((blockLastToDiagShearEquiv n a ha) p.1, p.2)) := by
  classical
  funext p
  rw [PiLastCoeff_apply, PiCoeff_apply]
  let E := blockLastToDiagShearEquiv n a ha
  let f : Block n a → F2 := fun x =>
    if x (blockSplitDiagLast ha) = p.1 then h (x, p.2) else 0
  calc
    (∑ x : Block n a,
        if x (blockSplitDiagLast ha) = p.1 then h (x, p.2) else 0) =
        ∑ x : Block n a, f (E x) := by
          have hsum := Equiv.sum_comp E f
          simpa [f] using hsum.symm
    _ =
        ∑ x : Block n a,
          if diag n a x = p.1
            then h ((blockLastToDiagShearEquiv n a ha) x, p.2)
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          simp [f, E, blockLastToDiagShearEquiv_last_eq_diag]

theorem PiLastFull_eq_PiFull_comp_shear
    (n : Nat) {a : Nat} [NeZero n]
    (ha : 0 < a) (C0 : Type) [Fintype C0]
    (h : Block n a × C0 → F2) :
    PiLastFull n ha C0 h =
      PiFull n ha C0
        (fun p => h ((blockLastToDiagShearEquiv n a ha) p.1, p.2)) := by
  funext s
  apply LinearMap.ext
  intro m
  rw [PiLastFull_apply, PiFull_apply]
  have hcoeff :=
    congrFun (PiLastCoeff_eq_PiCoeff_comp_shear n ha C0 h)
  simp [hcoeff]

end Imbalance
end TreeGraph
