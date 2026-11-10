import Core3loop.OddCase

open scoped BigOperators

namespace Core3loop

def constProfile {n : ℕ} (a : F) : Profile n := fun _ => a

noncomputable def scalarZAgg {c n : ℕ} [NeZero n] (u : ZCoord c n → F) : I n → F :=
  fun s => ∑ z : ZCoord c n, if sumZ z = s then u z else 0

noncomputable def scalarYAggMap {b n : ℕ} [NeZero n] : (YCoord b n → F) →ₗ[F] Profile n where
  toFun := scalarYAgg
  map_add' := by
    intro u v
    funext t
    change (∑ y : YCoord b n, if sumY y = t then u y + v y else 0) =
      (∑ y : YCoord b n, if sumY y = t then u y else 0) +
        ∑ y : YCoord b n, if sumY y = t then v y else 0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hyt : sumY y = t <;> simp [hyt]
  map_smul' := by
    intro a v
    funext t
    change (∑ y : YCoord b n, if sumY y = t then a * v y else 0) =
      a * ∑ y : YCoord b n, if sumY y = t then v y else 0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro y hy
    by_cases hyt : sumY y = t <;> simp [hyt, Pi.smul_apply]

noncomputable def scalarZAggMap {c n : ℕ} [NeZero n] : (ZCoord c n → F) →ₗ[F] Profile n where
  toFun := scalarZAgg
  map_add' := by
    intro u v
    funext s
    change (∑ z : ZCoord c n, if sumZ z = s then u z + v z else 0) =
      (∑ z : ZCoord c n, if sumZ z = s then u z else 0) +
        ∑ z : ZCoord c n, if sumZ z = s then v z else 0
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z hz
    by_cases hzs : sumZ z = s <;> simp [hzs]
  map_smul' := by
    intro a v
    funext s
    change (∑ z : ZCoord c n, if sumZ z = s then a * v z else 0) =
      a * ∑ z : ZCoord c n, if sumZ z = s then v z else 0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro z hz
    by_cases hzs : sumZ z = s <;> simp [hzs, Pi.smul_apply]

noncomputable def liftProfileY {b n : ℕ} [NeZero n] (hb : 0 < b) (μ : Profile n) : YCoord b n → F :=
  fun y => if y = yOfSum (n := n) hb (sumY y) then μ (sumY y) else 0

noncomputable def liftProfileZ {c n : ℕ} [NeZero n] (hc : 0 < c) (μ : Profile n) : ZCoord c n → F :=
  fun z => if z = zOfSum (n := n) hc (sumZ z) then μ (sumZ z) else 0

lemma scalarYAgg_liftProfileY {b n : ℕ} [NeZero n] (hb : 0 < b) (μ : Profile n) :
    scalarYAgg (liftProfileY (n := n) hb μ) = μ := by
  funext t
  unfold scalarYAgg liftProfileY
  rw [Finset.sum_eq_single (yOfSum (n := n) hb t)]
  · simp
  · intro y _ hy
    by_cases hyt : sumY y = t
    · have hy' : y ≠ yOfSum (n := n) hb (sumY y) := by
        simpa [hyt] using hy
      simp [hyt, hy']
      intro hy''
      exact False.elim (hy hy'')
    · simp [hyt]
  · simp

lemma scalarZAgg_liftProfileZ {c n : ℕ} [NeZero n] (hc : 0 < c) (μ : Profile n) :
    scalarZAgg (liftProfileZ (n := n) hc μ) = μ := by
  funext s
  unfold scalarZAgg liftProfileZ
  rw [Finset.sum_eq_single (zOfSum (n := n) hc s)]
  · simp
  · intro z _ hz
    by_cases hzs : sumZ z = s
    · have hz' : z ≠ zOfSum (n := n) hc (sumZ z) := by
        simpa [hzs] using hz
      simp [hzs, hz']
      intro hz''
      exact False.elim (hz hz'')
    · simp [hzs]
  · simp

lemma scalarYAgg_surjective {b n : ℕ} [NeZero n] (hb : 0 < b) :
    Function.Surjective (scalarYAgg (b := b) (n := n)) := by
  intro μ
  exact ⟨liftProfileY (n := n) hb μ, scalarYAgg_liftProfileY (n := n) hb μ⟩

lemma scalarZAgg_surjective {c n : ℕ} [NeZero n] (hc : 0 < c) :
    Function.Surjective (scalarZAgg (c := c) (n := n)) := by
  intro μ
  exact ⟨liftProfileZ (n := n) hc μ, scalarZAgg_liftProfileZ (n := n) hc μ⟩

lemma even_card_Coord_of_even {m n : ℕ} [NeZero n] (hm : 0 < m) (hn : Even n) :
    Even (Fintype.card (Coord m n)) := by
  have hexp : m ≠ 0 := by omega
  simpa [card_Coord] using Even.pow_of_ne_zero (a := n) hn hexp

lemma sum_const_coord_eq_zero_of_even {m n : ℕ} [NeZero n] (hm : 0 < m) (hn : Even n) (x : F) :
    ∑ u : Coord m n, x = 0 := by
  have hx : x = 0 ∨ x = 1 := by
    fin_cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with rfl | rfl
  · simp
  · rcases even_card_Coord_of_even (m := m) (n := n) hm hn with ⟨k, hk⟩
    calc
      ∑ _u : Coord m n, (1 : F) = (Fintype.card (Coord m n) : F) := by simp
      _ = 0 := by
            have h2 : ((2 : ℕ) : F) = 0 := by decide
            rw [hk, Nat.cast_add]
            simpa [F_add_self] using (F_add_self (k : F))

lemma sum_sigmaCoord_eq_zero_of_even {m n : ℕ} [NeZero n] (hm2 : 1 < m) (hn : Even n)
    (f : I n → F) :
    ∑ u : Coord m n, f (sigmaCoord u) = 0 := by
  rcases Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega) with ⟨k, rfl⟩
  have hk : 0 < k := by omega
  calc
    ∑ u : Coord (k + 1) n, f (sigmaCoord u)
      = ∑ p : I n × Coord k n, f (sigmaCoord (composeCoord p.1 p.2)) := by
          refine Fintype.sum_equiv (coordSuccEquiv k n) (fun u => f (sigmaCoord u))
            (fun p => f (sigmaCoord (composeCoord p.1 p.2))) ?_
          intro u
          have hu : composeCoord (u 0) (tailCoord u) = u := (coordSuccEquiv k n).left_inv u
          simp [coordSuccEquiv, hu]
    _ = ∑ t : I n, ∑ tail : Coord k n, f (t + sigmaCoord tail) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro t ht
          refine Finset.sum_congr rfl ?_
          intro tail htail
          rw [sigmaCoord_composeCoord]
    _ = ∑ tail : Coord k n, ∑ t : I n, f (t + sigmaCoord tail) := by
          rw [Finset.sum_comm]
    _ = ∑ tail : Coord k n, ∑ t : I n, f t := by
          refine Finset.sum_congr rfl ?_
          intro tail htail
          simpa [add_comm] using sum_reindex_addLeft (n := n) (sigmaCoord tail) f
    _ = 0 := by
          exact sum_const_coord_eq_zero_of_even (m := k) (n := n) hk hn (∑ t : I n, f t)

lemma sum_sumY_eq_zero_of_even {b n : ℕ} [NeZero n] (hb2 : 1 < b) (hn : Even n)
    (f : I n → F) :
    ∑ y : YCoord b n, f (sumY y) = 0 := by
  simpa [sumY, sigmaCoord] using sum_sigmaCoord_eq_zero_of_even (m := b) (n := n) hb2 hn f

lemma sum_sumZ_eq_zero_of_even {c n : ℕ} [NeZero n] (hc2 : 1 < c) (hn : Even n)
    (f : I n → F) :
    ∑ z : ZCoord c n, f (sumZ z) = 0 := by
  simpa [sumZ, sigmaCoord] using sum_sigmaCoord_eq_zero_of_even (m := c) (n := n) hc2 hn f

lemma range_scalarYAggMap_top {b n : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.range (scalarYAggMap (b := b) (n := n)) = ⊤ := by
  ext μ
  constructor
  · intro hμ
    simp
  · intro hμ
    rcases scalarYAgg_surjective (b := b) (n := n) hb μ with ⟨u, rfl⟩
    exact ⟨u, rfl⟩

lemma range_scalarZAggMap_top {c n : ℕ} [NeZero n] (hc : 0 < c) :
    LinearMap.range (scalarZAggMap (c := c) (n := n)) = ⊤ := by
  ext μ
  constructor
  · intro hμ
    simp
  · intro hμ
    rcases scalarZAgg_surjective (c := c) (n := n) hc μ with ⟨u, rfl⟩
    exact ⟨u, rfl⟩

lemma finrank_yFunctions {b n : ℕ} [NeZero n] :
    Module.finrank F (YCoord b n → F) = n ^ b := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [card_YCoord]

lemma finrank_zFunctions {c n : ℕ} [NeZero n] :
    Module.finrank F (ZCoord c n → F) = n ^ c := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp [card_ZCoord]

lemma finrank_ker_scalarYAggMap {b n : ℕ} [NeZero n] (hb : 0 < b) :
    Module.finrank F (LinearMap.ker (scalarYAggMap (b := b) (n := n))) = n ^ b - n := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (scalarYAggMap (b := b) (n := n))
  rw [range_scalarYAggMap_top (b := b) (n := n) hb] at hdim
  have htop : Module.finrank F ↥(⊤ : Submodule F (Profile n)) = n := by
    simpa using finrank_profile (n := n)
  rw [htop, finrank_yFunctions (b := b) (n := n)] at hdim
  omega

lemma finrank_ker_scalarZAggMap {c n : ℕ} [NeZero n] (hc : 0 < c) :
    Module.finrank F (LinearMap.ker (scalarZAggMap (c := c) (n := n))) = n ^ c - n := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (scalarZAggMap (c := c) (n := n))
  rw [range_scalarZAggMap_top (c := c) (n := n) hc] at hdim
  have htop : Module.finrank F ↥(⊤ : Submodule F (Profile n)) = n := by
    simpa using finrank_profile (n := n)
  rw [htop, finrank_zFunctions (c := c) (n := n)] at hdim
  omega

abbrev ConstAggY (b n : ℕ) [NeZero n] :=
  { v : YCoord b n → F // ∃ a : F, scalarYAgg v = constProfile (n := n) a }

abbrev ConstAggZ (c n : ℕ) [NeZero n] :=
  { u : ZCoord c n → F // ∃ a : F, scalarZAgg u = constProfile (n := n) a }

noncomputable instance instFintypeConstAggY {b n : ℕ} [NeZero n] : Fintype (ConstAggY b n) := by
  classical
  exact Fintype.ofFinite (ConstAggY b n)

noncomputable instance instFintypeConstAggZ {c n : ℕ} [NeZero n] : Fintype (ConstAggZ c n) := by
  classical
  exact Fintype.ofFinite (ConstAggZ c n)

noncomputable instance instFintypeKerScalarYAggMap {b n : ℕ} [NeZero n] :
    Fintype (LinearMap.ker (scalarYAggMap (b := b) (n := n))) := by
  classical
  exact Fintype.ofFinite (LinearMap.ker (scalarYAggMap (b := b) (n := n)))

noncomputable instance instFintypeKerScalarZAggMap {c n : ℕ} [NeZero n] :
    Fintype (LinearMap.ker (scalarZAggMap (c := c) (n := n))) := by
  classical
  exact Fintype.ofFinite (LinearMap.ker (scalarZAggMap (c := c) (n := n)))

noncomputable def constAggYWitness {b n : ℕ} [NeZero n] (hb : 0 < b) (a : F) : YCoord b n → F :=
  liftProfileY (n := n) hb (constProfile (n := n) a)

noncomputable def constAggZWitness {c n : ℕ} [NeZero n] (hc : 0 < c) (a : F) : ZCoord c n → F :=
  liftProfileZ (n := n) hc (constProfile (n := n) a)

lemma scalarYAgg_constAggYWitness {b n : ℕ} [NeZero n] (hb : 0 < b) (a : F) :
    scalarYAgg (constAggYWitness (b := b) (n := n) hb a) = constProfile (n := n) a := by
  simpa [constAggYWitness] using
    scalarYAgg_liftProfileY (b := b) (n := n) hb (constProfile (n := n) a)

lemma scalarZAgg_constAggZWitness {c n : ℕ} [NeZero n] (hc : 0 < c) (a : F) :
    scalarZAgg (constAggZWitness (c := c) (n := n) hc a) = constProfile (n := n) a := by
  simpa [constAggZWitness] using
    scalarZAgg_liftProfileZ (c := c) (n := n) hc (constProfile (n := n) a)

noncomputable def constAggYToData {b n : ℕ} [NeZero n] (hb : 0 < b) :
    ConstAggY b n → F × LinearMap.ker (scalarYAggMap (b := b) (n := n))
  | ⟨v, hv⟩ =>
      let a : F := scalarYAgg v 0
      let kv : LinearMap.ker (scalarYAggMap (b := b) (n := n)) := ⟨v + constAggYWitness (b := b) (n := n) hb a, by
        rcases hv with ⟨a0, ha0⟩
        have ha : a = a0 := by
          simpa [a, ha0, constProfile] using congrFun ha0 (0 : I n)
        change scalarYAgg (v + constAggYWitness (b := b) (n := n) hb a) = 0
        calc
          scalarYAgg (v + constAggYWitness (b := b) (n := n) hb a)
              = scalarYAgg v + scalarYAgg (constAggYWitness (b := b) (n := n) hb a) := by
                  change
                    (scalarYAggMap (b := b) (n := n))
                        (v + constAggYWitness (b := b) (n := n) hb a) =
                      (scalarYAggMap (b := b) (n := n)) v +
                        (scalarYAggMap (b := b) (n := n))
                          (constAggYWitness (b := b) (n := n) hb a)
                  exact
                    (scalarYAggMap (b := b) (n := n)).map_add v
                      (constAggYWitness (b := b) (n := n) hb a)
          _ = constProfile (n := n) a0 + constProfile (n := n) a := by
                rw [ha0, scalarYAgg_constAggYWitness (b := b) (n := n) hb]
          _ = 0 := by
                ext t
                simp [constProfile, ha, F_add_self]⟩
      (a, kv)

noncomputable def dataToConstAggY {b n : ℕ} [NeZero n] (hb : 0 < b) :
    F × LinearMap.ker (scalarYAggMap (b := b) (n := n)) → ConstAggY b n
  | (a, kv) =>
      ⟨constAggYWitness (b := b) (n := n) hb a + kv.1, ⟨a, by
        have hkv : scalarYAgg kv.1 = 0 := kv.2
        calc
          scalarYAgg (constAggYWitness (b := b) (n := n) hb a + kv.1)
              = scalarYAgg (constAggYWitness (b := b) (n := n) hb a) + scalarYAgg kv.1 := by
                  change
                    (scalarYAggMap (b := b) (n := n))
                        (constAggYWitness (b := b) (n := n) hb a + kv.1) =
                      (scalarYAggMap (b := b) (n := n))
                          (constAggYWitness (b := b) (n := n) hb a) +
                        (scalarYAggMap (b := b) (n := n)) kv.1
                  exact
                    (scalarYAggMap (b := b) (n := n)).map_add
                      (constAggYWitness (b := b) (n := n) hb a) kv.1
          _ = constProfile (n := n) a + 0 := by
                rw [scalarYAgg_constAggYWitness (b := b) (n := n) hb, hkv]
          _ = constProfile (n := n) a := by simp⟩⟩

lemma dataToConstAggY_constAggYToData {b n : ℕ} [NeZero n] (hb : 0 < b) (u : ConstAggY b n) :
    dataToConstAggY (b := b) (n := n) hb (constAggYToData (b := b) (n := n) hb u) = u := by
  rcases u with ⟨u, hu⟩
  apply Subtype.ext
  funext y
  by_cases hy : y = yOfSum (n := n) hb (sumY y)
  · have hw : constAggYWitness (b := b) (n := n) hb (scalarYAgg u 0) y = scalarYAgg u 0 := by
      unfold constAggYWitness liftProfileY
      rw [if_pos hy]
      simp [constProfile]
    calc
      (dataToConstAggY (b := b) (n := n) hb (constAggYToData (b := b) (n := n) hb ⟨u, hu⟩)).1 y
          = scalarYAgg u 0 + (u y + scalarYAgg u 0) := by
              simp [dataToConstAggY, constAggYToData, hw]
      _ = u y := by
            simp [add_assoc, add_left_comm, add_comm, F_add_self]
  · have hw : constAggYWitness (b := b) (n := n) hb (scalarYAgg u 0) y = 0 := by
      unfold constAggYWitness liftProfileY
      rw [if_neg hy]
    calc
      (dataToConstAggY (b := b) (n := n) hb (constAggYToData (b := b) (n := n) hb ⟨u, hu⟩)).1 y
          = 0 + (u y + 0) := by
              simp [dataToConstAggY, constAggYToData, hw]
      _ = u y := by simp

lemma constAggYToData_dataToConstAggY {b n : ℕ} [NeZero n] (hb : 0 < b)
    (x : F × LinearMap.ker (scalarYAggMap (b := b) (n := n))) :
    constAggYToData (b := b) (n := n) hb (dataToConstAggY (b := b) (n := n) hb x) = x := by
  rcases x with ⟨a, kv⟩
  have hkv : scalarYAgg kv.1 = 0 := kv.2
  have hkv0 : scalarYAgg kv.1 0 = 0 := by
    simpa using congrFun hkv (0 : I n)
  have hfst : scalarYAgg (constAggYWitness (b := b) (n := n) hb a + kv.1) 0 = a := by
    calc
      scalarYAgg (constAggYWitness (b := b) (n := n) hb a + kv.1) 0
          = (scalarYAgg (constAggYWitness (b := b) (n := n) hb a) + scalarYAgg kv.1) 0 := by
              change
                ((scalarYAggMap (b := b) (n := n))
                    (constAggYWitness (b := b) (n := n) hb a + kv.1)) 0 =
                  (((scalarYAggMap (b := b) (n := n))
                      (constAggYWitness (b := b) (n := n) hb a)) +
                    ((scalarYAggMap (b := b) (n := n)) kv.1)) 0
              exact congrFun
                ((scalarYAggMap (b := b) (n := n)).map_add
                  (constAggYWitness (b := b) (n := n) hb a) kv.1) (0 : I n)
      _ = a := by
            simp [scalarYAgg_constAggYWitness (b := b) (n := n) hb, constProfile, hkv0]
  have hswapY : scalarYAgg (kv.1 + constAggYWitness (b := b) (n := n) hb a) 0 = a := by
    simpa [add_comm, add_left_comm, add_assoc] using hfst
  apply Prod.ext
  · simpa [constAggYToData, dataToConstAggY] using hfst
  · apply Subtype.ext
    funext y
    by_cases hy : y = yOfSum (n := n) hb (sumY y)
    · have hw : constAggYWitness (b := b) (n := n) hb a y = a := by
        unfold constAggYWitness liftProfileY
        rw [if_pos hy]
        simp [constProfile]
      have hw' :
          constAggYWitness (b := b) (n := n) hb
              (scalarYAgg (kv.1 + constAggYWitness (b := b) (n := n) hb a) 0) y = a := by
        unfold constAggYWitness liftProfileY
        rw [if_pos hy]
        simpa [constProfile] using hswapY
      calc
        (constAggYToData (b := b) (n := n) hb (dataToConstAggY (b := b) (n := n) hb (a, kv))).2.1 y
            = a + (kv.1 y + a) := by
                simp [constAggYToData, dataToConstAggY, hw, hw', add_assoc, add_left_comm,
                  add_comm]
        _ = kv.1 y := by
              calc
                a + (kv.1 y + a) = (a + a) + kv.1 y := by ac_rfl
                _ = kv.1 y := by simp [F_add_self]
    · have hw : constAggYWitness (b := b) (n := n) hb a y = 0 := by
        unfold constAggYWitness liftProfileY
        rw [if_neg hy]
      have hw' :
          constAggYWitness (b := b) (n := n) hb
              (scalarYAgg (kv.1 + constAggYWitness (b := b) (n := n) hb a) 0) y = 0 := by
        unfold constAggYWitness liftProfileY
        rw [if_neg hy]
      calc
        (constAggYToData (b := b) (n := n) hb (dataToConstAggY (b := b) (n := n) hb (a, kv))).2.1 y
            = 0 + (kv.1 y + 0) := by
                simp [constAggYToData, dataToConstAggY, hw, hw', add_assoc, add_left_comm,
                  add_comm]
        _ = kv.1 y := by simp

noncomputable def constAggYEquiv {b n : ℕ} [NeZero n] (hb : 0 < b) :
    ConstAggY b n ≃ F × LinearMap.ker (scalarYAggMap (b := b) (n := n)) where
  toFun := constAggYToData (b := b) (n := n) hb
  invFun := dataToConstAggY (b := b) (n := n) hb
  left_inv := dataToConstAggY_constAggYToData (b := b) (n := n) hb
  right_inv := constAggYToData_dataToConstAggY (b := b) (n := n) hb

lemma natCard_constAggY {b n : ℕ} [NeZero n] (hb : 0 < b) :
    Nat.card (ConstAggY b n) = 2 ^ (n ^ b - n + 1) := by
  rw [Nat.card_congr (constAggYEquiv (b := b) (n := n) hb)]
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F)]
  have hF : Fintype.card F = 2 := by
    simp [F, ZMod.card]
  rw [hF]
  simp [finrank_ker_scalarYAggMap (b := b) (n := n) hb]
  have hk : n ^ b - n + 1 = (n ^ b - n) + 1 := by
    omega
  rw [hk, pow_add, pow_one, Nat.mul_comm]

noncomputable def constAggZToData {c n : ℕ} [NeZero n] (hc : 0 < c) :
    ConstAggZ c n → F × LinearMap.ker (scalarZAggMap (c := c) (n := n))
  | ⟨u, hu⟩ =>
      let a : F := scalarZAgg u 0
      let ku : LinearMap.ker (scalarZAggMap (c := c) (n := n)) := ⟨u + constAggZWitness (c := c) (n := n) hc a, by
        rcases hu with ⟨a0, ha0⟩
        have ha : a = a0 := by
          simpa [a, ha0, constProfile] using congrFun ha0 (0 : I n)
        change scalarZAgg (u + constAggZWitness (c := c) (n := n) hc a) = 0
        calc
          scalarZAgg (u + constAggZWitness (c := c) (n := n) hc a)
              = scalarZAgg u + scalarZAgg (constAggZWitness (c := c) (n := n) hc a) := by
                  change
                    (scalarZAggMap (c := c) (n := n))
                        (u + constAggZWitness (c := c) (n := n) hc a) =
                      (scalarZAggMap (c := c) (n := n)) u +
                        (scalarZAggMap (c := c) (n := n))
                          (constAggZWitness (c := c) (n := n) hc a)
                  exact
                    (scalarZAggMap (c := c) (n := n)).map_add u
                      (constAggZWitness (c := c) (n := n) hc a)
          _ = constProfile (n := n) a0 + constProfile (n := n) a := by
                rw [ha0, scalarZAgg_constAggZWitness (c := c) (n := n) hc]
          _ = 0 := by
                ext s
                simp [constProfile, ha, F_add_self]⟩
      (a, ku)

noncomputable def dataToConstAggZ {c n : ℕ} [NeZero n] (hc : 0 < c) :
    F × LinearMap.ker (scalarZAggMap (c := c) (n := n)) → ConstAggZ c n
  | (a, ku) =>
      ⟨constAggZWitness (c := c) (n := n) hc a + ku.1, ⟨a, by
        have hku : scalarZAgg ku.1 = 0 := ku.2
        calc
          scalarZAgg (constAggZWitness (c := c) (n := n) hc a + ku.1)
              = scalarZAgg (constAggZWitness (c := c) (n := n) hc a) + scalarZAgg ku.1 := by
                  change
                    (scalarZAggMap (c := c) (n := n))
                        (constAggZWitness (c := c) (n := n) hc a + ku.1) =
                      (scalarZAggMap (c := c) (n := n))
                          (constAggZWitness (c := c) (n := n) hc a) +
                        (scalarZAggMap (c := c) (n := n)) ku.1
                  exact
                    (scalarZAggMap (c := c) (n := n)).map_add
                      (constAggZWitness (c := c) (n := n) hc a) ku.1
          _ = constProfile (n := n) a + 0 := by
                rw [scalarZAgg_constAggZWitness (c := c) (n := n) hc, hku]
          _ = constProfile (n := n) a := by simp⟩⟩

lemma dataToConstAggZ_constAggZToData {c n : ℕ} [NeZero n] (hc : 0 < c) (u : ConstAggZ c n) :
    dataToConstAggZ (c := c) (n := n) hc (constAggZToData (c := c) (n := n) hc u) = u := by
  rcases u with ⟨u, hu⟩
  apply Subtype.ext
  funext z
  by_cases hz : z = zOfSum (n := n) hc (sumZ z)
  · have hw : constAggZWitness (c := c) (n := n) hc (scalarZAgg u 0) z = scalarZAgg u 0 := by
      unfold constAggZWitness liftProfileZ
      rw [if_pos hz]
      simp [constProfile]
    calc
      (dataToConstAggZ (c := c) (n := n) hc (constAggZToData (c := c) (n := n) hc ⟨u, hu⟩)).1 z
          = scalarZAgg u 0 + (u z + scalarZAgg u 0) := by
              simp [dataToConstAggZ, constAggZToData, hw]
      _ = u z := by
            simp [add_assoc, add_left_comm, add_comm, F_add_self]
  · have hw : constAggZWitness (c := c) (n := n) hc (scalarZAgg u 0) z = 0 := by
      unfold constAggZWitness liftProfileZ
      rw [if_neg hz]
    calc
      (dataToConstAggZ (c := c) (n := n) hc (constAggZToData (c := c) (n := n) hc ⟨u, hu⟩)).1 z
          = 0 + (u z + 0) := by
              simp [dataToConstAggZ, constAggZToData, hw]
      _ = u z := by simp

lemma constAggZToData_dataToConstAggZ {c n : ℕ} [NeZero n] (hc : 0 < c)
    (x : F × LinearMap.ker (scalarZAggMap (c := c) (n := n))) :
    constAggZToData (c := c) (n := n) hc (dataToConstAggZ (c := c) (n := n) hc x) = x := by
  rcases x with ⟨a, ku⟩
  have hku : scalarZAgg ku.1 = 0 := ku.2
  have hku0 : scalarZAgg ku.1 0 = 0 := by
    simpa using congrFun hku (0 : I n)
  have hfst : scalarZAgg (constAggZWitness (c := c) (n := n) hc a + ku.1) 0 = a := by
    calc
      scalarZAgg (constAggZWitness (c := c) (n := n) hc a + ku.1) 0
          = (scalarZAgg (constAggZWitness (c := c) (n := n) hc a) + scalarZAgg ku.1) 0 := by
              change
                ((scalarZAggMap (c := c) (n := n))
                    (constAggZWitness (c := c) (n := n) hc a + ku.1)) 0 =
                  (((scalarZAggMap (c := c) (n := n))
                      (constAggZWitness (c := c) (n := n) hc a)) +
                    ((scalarZAggMap (c := c) (n := n)) ku.1)) 0
              exact congrFun
                ((scalarZAggMap (c := c) (n := n)).map_add
                  (constAggZWitness (c := c) (n := n) hc a) ku.1) (0 : I n)
      _ = a := by
            simp [scalarZAgg_constAggZWitness (c := c) (n := n) hc, constProfile, hku0]
  have hswap : scalarZAgg (ku.1 + constAggZWitness (c := c) (n := n) hc a) 0 = a := by
    simpa [add_comm, add_left_comm, add_assoc] using hfst
  apply Prod.ext
  · simpa [constAggZToData, dataToConstAggZ] using hfst
  · apply Subtype.ext
    funext z
    by_cases hz : z = zOfSum (n := n) hc (sumZ z)
    · have hw : constAggZWitness (c := c) (n := n) hc a z = a := by
        unfold constAggZWitness liftProfileZ
        rw [if_pos hz]
        simp [constProfile]
      have hw' :
          constAggZWitness (c := c) (n := n) hc
              (scalarZAgg (ku.1 + constAggZWitness (c := c) (n := n) hc a) 0) z = a := by
        unfold constAggZWitness liftProfileZ
        rw [if_pos hz]
        simpa [constProfile] using hswap
      calc
        (constAggZToData (c := c) (n := n) hc (dataToConstAggZ (c := c) (n := n) hc (a, ku))).2.1 z
            = a + (ku.1 z + a) := by
                simp [constAggZToData, dataToConstAggZ, hw, hw', add_assoc, add_left_comm,
                  add_comm]
        _ = ku.1 z := by
              calc
                a + (ku.1 z + a) = (a + a) + ku.1 z := by ac_rfl
                _ = ku.1 z := by simp [F_add_self]
    · have hw : constAggZWitness (c := c) (n := n) hc a z = 0 := by
        unfold constAggZWitness liftProfileZ
        rw [if_neg hz]
      have hw' :
          constAggZWitness (c := c) (n := n) hc
              (scalarZAgg (ku.1 + constAggZWitness (c := c) (n := n) hc a) 0) z = 0 := by
        unfold constAggZWitness liftProfileZ
        rw [if_neg hz]
      calc
        (constAggZToData (c := c) (n := n) hc (dataToConstAggZ (c := c) (n := n) hc (a, ku))).2.1 z
            = 0 + (ku.1 z + 0) := by
                simp [constAggZToData, dataToConstAggZ, hw, hw', add_assoc, add_left_comm,
                  add_comm]
        _ = ku.1 z := by simp

noncomputable def constAggZEquiv {c n : ℕ} [NeZero n] (hc : 0 < c) :
    ConstAggZ c n ≃ F × LinearMap.ker (scalarZAggMap (c := c) (n := n)) where
  toFun := constAggZToData (c := c) (n := n) hc
  invFun := dataToConstAggZ (c := c) (n := n) hc
  left_inv := dataToConstAggZ_constAggZToData (c := c) (n := n) hc
  right_inv := constAggZToData_dataToConstAggZ (c := c) (n := n) hc

lemma natCard_constAggZ {c n : ℕ} [NeZero n] (hc : 0 < c) :
    Nat.card (ConstAggZ c n) = 2 ^ (n ^ c - n + 1) := by
  rw [Nat.card_congr (constAggZEquiv (c := c) (n := n) hc)]
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F)]
  have hF : Fintype.card F = 2 := by
    simp [F, ZMod.card]
  rw [hF]
  simp [finrank_ker_scalarZAggMap (c := c) (n := n) hc]
  have hk : n ^ c - n + 1 = (n ^ c - n) + 1 := by
    omega
  rw [hk, pow_add, pow_one, Nat.mul_comm]

lemma natCard_constAggYZ_prod {b c n : ℕ} [NeZero n] (hb : 0 < b) (hc : 0 < c) :
    Nat.card (ConstAggY b n × ConstAggZ c n) =
      2 ^ ((n ^ b - n + 1) + (n ^ c - n + 1)) := by
  rw [Nat.card_prod, natCard_constAggY (b := b) (n := n) hb, natCard_constAggZ (c := c) (n := n) hc]
  exact (pow_add 2 (n ^ b - n + 1) (n ^ c - n + 1)).symm

noncomputable def BAgg {c n : ℕ} [NeZero n] (bcoef : ScalarBCoef c n) (t s : I n) : F :=
  ∑ z : ZCoord c n, if sumZ z = s then bcoef t z else 0

noncomputable def TAdjScalarFun {b c n : ℕ} [NeZero n] (bcoef : ScalarBCoef c n) : ScalarCCoef b n :=
  fun y r => BAgg (c := c) (n := n) bcoef (sumY y) r + BAgg (c := c) (n := n) bcoef (sumY y + 1) (r - 1)

noncomputable def TAdjScalar {b c n : ℕ} [NeZero n] : ScalarBCoef c n →ₗ[F] ScalarCCoef b n where
  toFun := TAdjScalarFun
  map_add' := by
    intro b₁ b₂
    funext y r
    have h1 :
        BAgg (c := c) (n := n) (b₁ + b₂) (sumY y) r =
          BAgg (c := c) (n := n) b₁ (sumY y) r + BAgg (c := c) (n := n) b₂ (sumY y) r := by
      unfold BAgg
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro z hz
      by_cases hzs : sumZ z = r <;> simp [hzs]
    have h2 :
        BAgg (c := c) (n := n) (b₁ + b₂) (sumY y + 1) (r - 1) =
          BAgg (c := c) (n := n) b₁ (sumY y + 1) (r - 1) +
            BAgg (c := c) (n := n) b₂ (sumY y + 1) (r - 1) := by
      unfold BAgg
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro z hz
      by_cases hzs : sumZ z = r - 1 <;> simp [hzs]
    unfold TAdjScalarFun
    rw [h1, h2]
    simp [Pi.add_apply, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a bcoef
    funext y r
    unfold TAdjScalarFun BAgg
    simp [Finset.mul_sum, Pi.smul_apply, mul_add]

lemma BAgg_buildScalarB_even {c n : ℕ} [NeZero n] (hn : Even n) (hc2 : 1 < c)
    (h : HRaw n) (u : ZCoord c n → F) (t s : I n) :
    BAgg (c := c) (n := n) (buildScalarB h u) t s = scalarZAgg (c := c) (n := n) u s := by
  unfold BAgg buildScalarB scalarZAgg
  let g : ZCoord c n → F := fun z => if sumZ z = s then u z + prefixT h t (sumZ z) else 0
  let g1 : ZCoord c n → F := fun z => if sumZ z = s then u z else 0
  let g2 : ZCoord c n → F := fun z => if sumZ z = s then prefixT h t (sumZ z) else 0
  have hsplit :
      (Finset.univ.sum fun z : ZCoord c n => g z) =
        Finset.univ.sum (fun z : ZCoord c n => g1 z + g2 z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          by_cases hzs : sumZ z = s <;> simp [g, g1, g2, hzs]
  have hconst :
      (Finset.univ.sum fun z : ZCoord c n => g2 z) = 0 := by
        simpa using
          sum_sumZ_eq_zero_of_even (c := c) (n := n) hc2 hn
            (fun r => if r = s then prefixT h t r else 0)
  simpa [g, g1, g2] using congrArg (fun x => x) <| by
    rw [hsplit, Finset.sum_add_distrib, hconst, add_zero]

lemma Cagg_buildScalarC_even {b n : ℕ} [NeZero n] (hn : Even n) (hb2 : 1 < b)
    (h : HRaw n) (v : YCoord b n → F) (t s : I n) :
    Cagg (b := b) (n := n) (buildScalarC h v) t s = scalarYAgg (b := b) (n := n) v t := by
  unfold Cagg buildScalarC scalarYAgg
  let g : YCoord b n → F := fun y => if sumY y = t then v y + prefixR h (sumY y) s else 0
  let g1 : YCoord b n → F := fun y => if sumY y = t then v y else 0
  let g2 : YCoord b n → F := fun y => if sumY y = t then prefixR h (sumY y) s else 0
  have hsplit :
      (Finset.univ.sum fun y : YCoord b n => g y) =
        Finset.univ.sum (fun y : YCoord b n => g1 y + g2 y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          by_cases hyt : sumY y = t <;> simp [g, g1, g2, hyt]
  have hconst :
      (Finset.univ.sum fun y : YCoord b n => g2 y) = 0 := by
        simpa using
          sum_sumY_eq_zero_of_even (b := b) (n := n) hb2 hn
            (fun r => if r = t then prefixR h r s else 0)
  simpa [g, g1, g2] using congrArg (fun x => x) <| by
    rw [hsplit, Finset.sum_add_distrib, hconst, add_zero]

lemma TAdjScalar_buildScalarB_even {b c n : ℕ} [NeZero n] (hn : Even n) (hc2 : 1 < c)
    (h : HRaw n) (u : ZCoord c n → F) (y : YCoord b n) (r : I n) :
    TAdjScalarFun (b := b) (c := c) (n := n) (buildScalarB h u) y r =
      scalarZAgg (c := c) (n := n) u r + scalarZAgg (c := c) (n := n) u (r - 1) := by
  simp [TAdjScalarFun, BAgg_buildScalarB_even (c := c) (n := n) hn hc2 h u]

lemma TScalar_buildScalarC_even {b c n : ℕ} [NeZero n] (hn : Even n) (hb2 : 1 < b)
    (h : HRaw n) (v : YCoord b n → F) (t : I n) (z : ZCoord c n) :
    TScalarFun (b := b) (c := c) (n := n) (buildScalarC h v) t z =
      scalarYAgg (b := b) (n := n) v t + scalarYAgg (b := b) (n := n) v (t - 1) := by
  simp [TScalarFun, Cagg_buildScalarC_even (b := b) (n := n) hn hb2 h v]

lemma TAdjScalar_buildScalarB_eq_zero_iff {b c n : ℕ} [NeZero n]
    (hb : 0 < b) (hn : Even n) (hc2 : 1 < c) (h : HRaw n) (u : ZCoord c n → F) :
    TAdjScalar (b := b) (c := c) (n := n) (buildScalarB h u) = 0 ↔
      ∃ a : F, scalarZAgg (c := c) (n := n) u = constProfile (n := n) a := by
  constructor
  · intro hzero
    let μ : Profile n := scalarZAgg (c := c) (n := n) u
    have hstep : ∀ s : I n, μ (s + 1) = μ s := by
      intro s
      have hs := congrFun (congrFun hzero (yOfSum (n := n) hb 0)) (s + 1)
      have hs0 : μ (s + 1) + μ s = 0 := by
        simpa [μ, TAdjScalar, TAdjScalar_buildScalarB_even (b := b) (c := c) (n := n) hn hc2 h u,
          sumY_yOfSum (n := n) hb 0] using hs
      have hs' : μ (s + 1) = -(μ s) := eq_neg_of_add_eq_zero_left hs0
      simpa [μ] using hs'
    refine ⟨μ 0, ?_⟩
    funext s
    simpa [μ, constProfile] using zmod_step_const μ hstep s
  · rintro ⟨a, ha⟩
    funext y r
    simpa [TAdjScalar, ha, constProfile, F_add_self] using
      TAdjScalar_buildScalarB_even (b := b) (c := c) (n := n) hn hc2 h u y r

lemma TScalar_buildScalarC_eq_zero_iff {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) (h : HRaw n) (v : YCoord b n → F) :
    TScalar (b := b) (c := c) (n := n) (buildScalarC h v) = 0 ↔
      ∃ a : F, scalarYAgg (b := b) (n := n) v = constProfile (n := n) a := by
  constructor
  · intro hzero
    let μ : Profile n := scalarYAgg (b := b) (n := n) v
    have hstep : ∀ s : I n, μ (s + 1) = μ s := by
      intro s
      have hs := congrFun (congrFun hzero (s + 1)) (default : ZCoord c n)
      have hs0 : μ (s + 1) + μ s = 0 := by
        simpa [μ, TScalar, TScalar_buildScalarC_even (b := b) (c := c) (n := n) hn hb2 h v] using hs
      have hs' : μ (s + 1) = -(μ s) := eq_neg_of_add_eq_zero_left hs0
      simpa [μ] using hs'
    refine ⟨μ 0, ?_⟩
    funext s
    simpa [μ, constProfile] using zmod_step_const μ hstep s
  · rintro ⟨a, ha⟩
    funext t z
    simpa [TScalar, ha, constProfile, F_add_self] using
      TScalar_buildScalarC_even (b := b) (c := c) (n := n) hn hb2 h v t z

lemma sumY_eq_apply_zero_of_b_eq_one {n : ℕ} [NeZero n] (y : YCoord 1 n) :
    sumY y = y 0 := by
  simpa [sumY, sigmaCoord, No13Migration.sumCoord]

lemma sumY_injective_of_b_eq_one {n : ℕ} [NeZero n] :
    Function.Injective (sumY (b := 1) (n := n)) := by
  intro y y' h
  ext i
  fin_cases i
  simpa [sumY_eq_apply_zero_of_b_eq_one] using h

lemma y_eq_yOfSum_of_b_eq_one {n : ℕ} [NeZero n] (y : YCoord 1 n) :
    y = yOfSum (b := 1) (n := n) (by omega) (sumY y) := by
  apply sumY_injective_of_b_eq_one (n := n)
  simpa using (sumY_yOfSum (b := 1) (n := n) (by omega) (sumY y)).symm

lemma Cagg_eq_of_b_eq_one {n : ℕ} [NeZero n] (ccoef : ScalarCCoef 1 n) (t r : I n) :
    Cagg (b := 1) (n := n) ccoef t r = ccoef (yOfSum (b := 1) (n := n) (by omega) t) r := by
  have hb : 0 < 1 := by omega
  unfold Cagg
  rw [Finset.sum_eq_single (yOfSum (b := 1) (n := n) hb t)]
  · simp
  · intro y _ hy
    by_cases hyt : sumY y = t
    · have hy' : y = yOfSum (b := 1) (n := n) hb t := by
        apply sumY_injective_of_b_eq_one (n := n)
        simpa [hyt] using (sumY_yOfSum (b := 1) (n := n) hb t).symm
      exact (hy hy').elim
    · simp [hyt]
  · simp

lemma Cagg_injective_of_b_eq_one {n : ℕ} [NeZero n] :
    Function.Injective (Cagg (b := 1) (n := n)) := by
  intro c₁ c₂ h
  funext y r
  have hy : yOfSum (b := 1) (n := n) (by omega) (sumY y) = y := by
    simpa using (y_eq_yOfSum_of_b_eq_one (n := n) y).symm
  have hs := congrFun (congrFun h (sumY y)) r
  simpa [Cagg_eq_of_b_eq_one, hy] using hs

noncomputable def diagScalarCCoefOfProfile {n : ℕ} [NeZero n] (μ : Profile n) :
    ScalarCCoef 1 n :=
  liftMatrix (b := 1) (n := n) (by omega) (diagConst μ)

lemma Cagg_diagScalarCCoefOfProfile {n : ℕ} [NeZero n] (μ : Profile n) :
    Cagg (b := 1) (n := n) (diagScalarCCoefOfProfile (n := n) μ) = diagConst μ := by
  simpa [diagScalarCCoefOfProfile] using
    Cagg_liftMatrix (b := 1) (n := n) (by omega) (diagConst μ)

lemma TScalar_diagScalarCCoefOfProfile_zero {c n : ℕ} [NeZero n] (μ : Profile n) :
    TScalar (b := 1) (c := c) (n := n) (diagScalarCCoefOfProfile (n := n) μ) = 0 := by
  ext t z
  have hz := congrFun (congrFun (Dfun_diagConst_zero μ) t) (sumZ z)
  rw [TScalar_eq_expandMatrix_comp_D_comp_CaggMap]
  simpa [LinearMap.comp_apply, D, expandMatrix, CaggMap, Cagg_diagScalarCCoefOfProfile] using hz

lemma TScalar_eq_zero_iff_exists_diagScalarCCoefOfProfile_of_b_eq_one {c n : ℕ} [NeZero n]
    (hc : 0 < c) (ccoef : ScalarCCoef 1 n) :
    TScalar (b := 1) (c := c) (n := n) ccoef = 0 ↔
      ∃ μ : Profile n, ccoef = diagScalarCCoefOfProfile (n := n) μ := by
  constructor
  · intro hzero
    have hED :
        (expandMatrix (c := c) (n := n))
          ((D (n := n)) ((CaggMap (b := 1) (n := n)) ccoef)) = 0 := by
      simpa [TScalar_eq_expandMatrix_comp_D_comp_CaggMap, LinearMap.comp_apply] using hzero
    have hD :
        (D (n := n)) ((CaggMap (b := 1) (n := n)) ccoef) = 0 := by
      exact (expandMatrix_injective (c := c) (n := n) hc) hED
    have hker : Cagg (b := 1) (n := n) ccoef ∈ LinearMap.ker (D (n := n)) := by
      simpa [CaggMap] using hD
    rcases (mem_ker_D_iff_exists_diagConst (n := n) (Cagg (b := 1) (n := n) ccoef)).mp hker with
      ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    apply Cagg_injective_of_b_eq_one (n := n)
    calc
      Cagg (b := 1) (n := n) ccoef = diagConst μ := hμ
      _ = Cagg (b := 1) (n := n) (diagScalarCCoefOfProfile (n := n) μ) := by
            symm
            exact Cagg_diagScalarCCoefOfProfile (n := n) μ
  · rintro ⟨μ, rfl⟩
    exact TScalar_diagScalarCCoefOfProfile_zero (c := c) (n := n) μ

noncomputable def kerTScalarEquivProfile_of_b_eq_one {c n : ℕ} [NeZero n] (hc : 0 < c) :
    { ccoef : ScalarCCoef 1 n // TScalar (b := 1) (c := c) (n := n) ccoef = 0 } ≃ Profile n where
  toFun := fun x => Cagg (b := 1) (n := n) x.1 0
  invFun := fun μ => ⟨diagScalarCCoefOfProfile (n := n) μ,
    TScalar_diagScalarCCoefOfProfile_zero (c := c) (n := n) μ⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply Cagg_injective_of_b_eq_one (n := n)
    rcases
      (TScalar_eq_zero_iff_exists_diagScalarCCoefOfProfile_of_b_eq_one
        (c := c) (n := n) hc x.1).mp x.2 with ⟨μ, hμ⟩
    calc
      Cagg (b := 1) (n := n)
          (diagScalarCCoefOfProfile (n := n) (Cagg (b := 1) (n := n) x.1 0)) =
          diagConst (Cagg (b := 1) (n := n) x.1 0) := by
            exact Cagg_diagScalarCCoefOfProfile (n := n) (Cagg (b := 1) (n := n) x.1 0)
      _ = diagConst μ := by
            funext t s
            have hrow : Cagg (b := 1) (n := n) x.1 0 = μ := by
              funext r
              rw [hμ, Cagg_diagScalarCCoefOfProfile]
              simp [diagConst]
            rw [hrow]
      _ = Cagg (b := 1) (n := n) x.1 := by
            rw [hμ, Cagg_diagScalarCCoefOfProfile]
  right_inv := by
    intro μ
    funext s
    have hs := congrFun (congrFun (Cagg_diagScalarCCoefOfProfile (n := n) μ) 0) s
    simpa [diagConst] using hs

lemma natCard_ker_TScalar_of_b_eq_one {c n : ℕ} [NeZero n] (hc : 0 < c) :
    Nat.card { ccoef : ScalarCCoef 1 n // TScalar (b := 1) (c := c) (n := n) ccoef = 0 } =
      2 ^ n := by
  rw [Nat.card_congr (kerTScalarEquivProfile_of_b_eq_one (c := c) (n := n) hc)]
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_profile]
  simp [F]

noncomputable def diagHRawOfProfile {n : ℕ} [NeZero n] (μ : Profile n) : HRaw n :=
  fun t s => μ (t + s) + μ (t + s + 1)

noncomputable def diagVDataOfProfile {n : ℕ} [NeZero n] (μ : Profile n) : YCoord 1 n → F :=
  fun y => μ (sumY y)

lemma rowSum_diagHRawOfProfile_zero {n : ℕ} [NeZero n] (μ : Profile n) :
    rowSum (diagHRawOfProfile (n := n) μ) = 0 := by
  funext t
  unfold rowSum diagHRawOfProfile
  rw [Finset.sum_add_distrib]
  have h1 : ∑ s : I n, μ (t + s) = sigma μ := by
    simpa [sigma] using (sum_reindex_addLeft (n := n) t μ)
  have h2 : ∑ s : I n, μ (t + s + 1) = sigma μ := by
    simpa [sigma, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (t + 1) μ)
  simpa [h1, h2] using (F_add_self (sigma μ))

lemma colSum_diagHRawOfProfile_zero {n : ℕ} [NeZero n] (μ : Profile n) :
    colSum (diagHRawOfProfile (n := n) μ) = 0 := by
  funext s
  unfold colSum diagHRawOfProfile
  rw [Finset.sum_add_distrib]
  have h1 : ∑ t : I n, μ (t + s) = sigma μ := by
    simpa [sigma, add_comm] using (sum_reindex_addLeft (n := n) s μ)
  have h2 : ∑ t : I n, μ (t + s + 1) = sigma μ := by
    simpa [sigma, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (s + 1) μ)
  simpa [h1, h2] using (F_add_self (sigma μ))

lemma diagHRawOfProfile_mem_HAdmissible {n : ℕ} [NeZero n] (μ : Profile n) :
    diagHRawOfProfile (n := n) μ ∈ HAdmissible (n := n) := by
  constructor
  · change rowSum (diagHRawOfProfile (n := n) μ) = 0
    exact rowSum_diagHRawOfProfile_zero (n := n) μ
  · change colSum (diagHRawOfProfile (n := n) μ) = 0
    exact colSum_diagHRawOfProfile_zero (n := n) μ

lemma prefixR_diagHRawOfProfile {n : ℕ} [NeZero n] (μ : Profile n) (t r : I n) :
    prefixR (diagHRawOfProfile (n := n) μ) t r = μ (t + r) + μ t := by
  let h : HRaw n := diagHRawOfProfile (n := n) μ
  have hh : h ∈ HAdmissible (n := n) := diagHRawOfProfile_mem_HAdmissible (n := n) μ
  let g : I n → F := fun s => prefixR h t s + μ (t + s) + μ t
  have hstep : ∀ s : I n, g (s + 1) = g s := by
    intro s
    have hp : prefixR h t (s + 1) = prefixR h t s + h t s := by
      have hq := prefixR_pair_eq_of_mem_HAdmissible (n := n) hh t s
      apply add_left_cancel (a := prefixR h t s)
      simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hq
    dsimp [g]
    rw [hp]
    simp [h, diagHRawOfProfile, add_assoc, add_left_comm, add_comm, F_add_self]
  have hconst := zmod_step_const g hstep r
  have hzero : g 0 = 0 := by
    simp [g, h, prefixR_zero, add_assoc, add_left_comm, add_comm, F_add_self]
  have hgr : g r = 0 := by
    simpa [hzero] using hconst
  have hsum : prefixR h t r + (μ (t + r) + μ t) = 0 := by
    simpa [g, add_assoc, add_left_comm, add_comm] using hgr
  have hEq := eq_neg_of_add_eq_zero_left hsum
  simpa [h, add_assoc, add_left_comm, add_comm] using hEq

lemma buildScalarC_diagHRawOfProfile_eq_diagScalarCCoefOfProfile {n : ℕ} [NeZero n]
    (μ : Profile n) :
    buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ) =
      diagScalarCCoefOfProfile (n := n) μ := by
  have hb : 0 < 1 := by omega
  apply Cagg_injective_of_b_eq_one (n := n)
  funext t r
  calc
    Cagg (b := 1) (n := n)
        (buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ)) t r
        =
        buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ)
          (yOfSum (b := 1) (n := n) hb t) r := by
            rw [Cagg_eq_of_b_eq_one]
    _ = μ (t + r) := by
          have hy : sumY (yOfSum (b := 1) (n := n) hb t) = t := sumY_yOfSum (b := 1) (n := n) hb t
          have hp :
              prefixR (diagHRawOfProfile (n := n) μ) t r = μ (t + r) + μ t :=
            prefixR_diagHRawOfProfile (n := n) μ t r
          calc
            buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ)
                (yOfSum (b := 1) (n := n) hb t) r
                =
                diagVDataOfProfile (n := n) μ (yOfSum (b := 1) (n := n) hb t) +
                  prefixR (diagHRawOfProfile (n := n) μ) t r := by
                      simp [buildScalarC, hy]
            _ = μ t + (μ (t + r) + μ t) := by
                  simp [diagVDataOfProfile, hy, hp]
            _ = μ (t + r) := by
                  calc
                    μ t + (μ (t + r) + μ t) = (μ t + μ t) + μ (t + r) := by ac_rfl
                    _ = μ (t + r) := by simp [F_add_self]
    _ = Cagg (b := 1) (n := n) (diagScalarCCoefOfProfile (n := n) μ) t r := by
          rw [Cagg_diagScalarCCoefOfProfile]
          simp [diagConst]

abbrev EvenVisibleKernelData (b c n : ℕ) [NeZero n] :=
  { bc : ScalarVisibleCompat b c n //
      TAdjScalar (b := b) (c := c) (n := n) bc.bcoef = 0 ∧
        TScalar (b := b) (c := c) (n := n) bc.ccoef = 0 }

abbrev EvenVisibleKernelHUVData (b c n : ℕ) [NeZero n] :=
  HAdmissible (n := n) × (ConstAggZ c n × ConstAggY b n)

noncomputable instance instFintypeEvenVisibleKernelData {b c n : ℕ} [NeZero n] :
    Fintype (EvenVisibleKernelData b c n) := by
  classical
  exact Fintype.ofFinite (EvenVisibleKernelData b c n)

noncomputable instance instFintypeEvenVisibleKernelHUVData {b c n : ℕ} [NeZero n] :
    Fintype (EvenVisibleKernelHUVData b c n) := by
  classical
  infer_instance

noncomputable def evenVisibleKernelToHUVData {b c n : ℕ} [NeZero n]
    (hb2 : 1 < b) (hc2 : 1 < c) (hn : Even n) :
    EvenVisibleKernelData b c n → EvenVisibleKernelHUVData b c n
  | ⟨bc, hbker, hcker⟩ =>
      let hb : 0 < b := by omega
      let hc : 0 < c := by omega
      let hH : HAdmissible (n := n) := ⟨visibleHData (b := b) (c := c) (n := n) hc bc,
        visibleHData_mem_HAdmissible (b := b) (c := c) (n := n) hb hc bc⟩
      let uK : ConstAggZ c n := ⟨visibleUData bc,
        (TAdjScalar_buildScalarB_eq_zero_iff (b := b) (c := c) (n := n) hb hn hc2
          (visibleHData (b := b) (c := c) (n := n) hc bc) (visibleUData bc)).1 <| by
            simpa [buildScalarB_visibleData_eq (b := b) (c := c) (n := n) hb hc bc] using hbker⟩
      let vK : ConstAggY b n := ⟨visibleVData bc,
        (TScalar_buildScalarC_eq_zero_iff (b := b) (c := c) (n := n) hn hb2
          (visibleHData (b := b) (c := c) (n := n) hc bc) (visibleVData bc)).1 <| by
            simpa [buildScalarC_visibleData_eq (b := b) (c := c) (n := n) hc bc] using hcker⟩
      (hH, (uK, vK))

noncomputable def evenVisibleKernelFromHUVData {b c n : ℕ} [NeZero n]
    (hb2 : 1 < b) (hc2 : 1 < c) (hn : Even n) :
    EvenVisibleKernelHUVData b c n → EvenVisibleKernelData b c n
  | ⟨h, uK, vK⟩ =>
      let hb : 0 < b := by omega
      let hc : 0 < c := by omega
      ⟨build_mem_scalarVisibleCompat_of_mem_HAdmissible
          (b := b) (c := c) (n := n) hb hc h uK.1 vK.1,
        (TAdjScalar_buildScalarB_eq_zero_iff (b := b) (c := c) (n := n) hb hn hc2 h.1 uK.1).2 uK.2,
        (TScalar_buildScalarC_eq_zero_iff (b := b) (c := c) (n := n) hn hb2 h.1 vK.1).2 vK.2⟩

lemma evenVisibleKernelToHUVData_from {b c n : ℕ} [NeZero n]
    (hb2 : 1 < b) (hc2 : 1 < c) (hn : Even n)
    (z : EvenVisibleKernelHUVData b c n) :
    evenVisibleKernelToHUVData (b := b) (c := c) (n := n) hb2 hc2 hn
      (evenVisibleKernelFromHUVData (b := b) (c := c) (n := n) hb2 hc2 hn z) = z := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  rcases z with ⟨⟨h, hh⟩, ⟨⟨u, hu⟩, ⟨v, hv⟩⟩⟩
  let bc : ScalarVisibleCompat b c n :=
    build_mem_scalarVisibleCompat_of_mem_HAdmissible
      (b := b) (c := c) (n := n) hb hc ⟨h, hh⟩ u v
  have hpB : TAdjScalar (b := b) (c := c) (n := n) bc.bcoef = 0 := by
    dsimp [bc]
    exact (TAdjScalar_buildScalarB_eq_zero_iff (b := b) (c := c) (n := n) hb hn hc2 h u).2 hu
  have hpC : TScalar (b := b) (c := c) (n := n) bc.ccoef = 0 := by
    dsimp [bc]
    exact (TScalar_buildScalarC_eq_zero_iff (b := b) (c := c) (n := n) hn hb2 h v).2 hv
  have hH := visibleHData_build_eq (b := b) (c := c) (n := n) hb hc ⟨h, hh⟩ u v
  have hU := visibleUData_build_eq (b := b) (c := c) (n := n) hb hc ⟨h, hh⟩ u v
  have hV := visibleVData_build_eq (b := b) (c := c) (n := n) hb hc ⟨h, hh⟩ u v
  change
    evenVisibleKernelToHUVData (b := b) (c := c) (n := n) hb2 hc2 hn
      ⟨bc, hpB, hpC⟩ = ⟨⟨h, hh⟩, ⟨⟨u, hu⟩, ⟨v, hv⟩⟩⟩
  ext x y <;> simp [evenVisibleKernelToHUVData, evenVisibleKernelFromHUVData]
  · change visibleHData (b := b) (c := c) (n := n) hc bc x y = h x y
    simpa using congrFun (congrFun hH x) y
  · change visibleUData
      bc x = u x
    simpa using congrFun hU x
  · change visibleVData
      bc x = v x
    simpa using congrFun hV x

lemma evenVisibleKernelToHUVData_injective {b c n : ℕ} [NeZero n]
    (hb2 : 1 < b) (hc2 : 1 < c) (hn : Even n) :
    Function.Injective (evenVisibleKernelToHUVData (b := b) (c := c) (n := n) hb2 hc2 hn) := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  intro x y hxy
  rcases x with ⟨bcx, hbx, hcx⟩
  rcases y with ⟨bcy, hby, hcy⟩
  have hh :
      visibleHData (b := b) (c := c) (n := n) hc bcx =
        visibleHData (b := b) (c := c) (n := n) hc bcy := by
    exact congrArg (fun z : EvenVisibleKernelHUVData b c n => z.1.1) hxy
  have hu :
      visibleUData bcx = visibleUData bcy := by
    exact congrArg (fun z : EvenVisibleKernelHUVData b c n => z.2.1.1) hxy
  have hv :
      visibleVData bcx = visibleVData bcy := by
    exact congrArg (fun z : EvenVisibleKernelHUVData b c n => z.2.2.1) hxy
  have hbcoef :
      bcx.bcoef = bcy.bcoef := by
    calc
      bcx.bcoef =
          buildScalarB
            (visibleHData (b := b) (c := c) (n := n) hc bcx) (visibleUData bcx) := by
              symm
              exact buildScalarB_visibleData_eq (b := b) (c := c) (n := n) hb hc bcx
      _ =
          buildScalarB
            (visibleHData (b := b) (c := c) (n := n) hc bcy) (visibleUData bcy) := by
              rw [hh, hu]
      _ = bcy.bcoef := by
            exact buildScalarB_visibleData_eq (b := b) (c := c) (n := n) hb hc bcy
  have hccoef :
      bcx.ccoef = bcy.ccoef := by
    calc
      bcx.ccoef =
          buildScalarC
            (visibleHData (b := b) (c := c) (n := n) hc bcx) (visibleVData bcx) := by
              symm
              exact buildScalarC_visibleData_eq (b := b) (c := c) (n := n) hc bcx
      _ =
          buildScalarC
            (visibleHData (b := b) (c := c) (n := n) hc bcy) (visibleVData bcy) := by
              rw [hh, hv]
      _ = bcy.ccoef := by
            exact buildScalarC_visibleData_eq (b := b) (c := c) (n := n) hc bcy
  apply Subtype.ext
  exact ScalarVisibleCompat.ext hbcoef hccoef

lemma evenVisibleKernelFromHUVData_to {b c n : ℕ} [NeZero n]
    (hb2 : 1 < b) (hc2 : 1 < c) (hn : Even n)
    (x : EvenVisibleKernelData b c n) :
    evenVisibleKernelFromHUVData (b := b) (c := c) (n := n) hb2 hc2 hn
      (evenVisibleKernelToHUVData (b := b) (c := c) (n := n) hb2 hc2 hn x) = x := by
  apply evenVisibleKernelToHUVData_injective (b := b) (c := c) (n := n) hb2 hc2 hn
  simpa using
    evenVisibleKernelToHUVData_from (b := b) (c := c) (n := n) hb2 hc2 hn
      (evenVisibleKernelToHUVData (b := b) (c := c) (n := n) hb2 hc2 hn x)

noncomputable def evenVisibleKernelEquivHUVData {b c n : ℕ} [NeZero n]
    (hb2 : 1 < b) (hc2 : 1 < c) (hn : Even n) :
    EvenVisibleKernelData b c n ≃ EvenVisibleKernelHUVData b c n where
  toFun := evenVisibleKernelToHUVData (b := b) (c := c) (n := n) hb2 hc2 hn
  invFun := evenVisibleKernelFromHUVData (b := b) (c := c) (n := n) hb2 hc2 hn
  left_inv := evenVisibleKernelFromHUVData_to (b := b) (c := c) (n := n) hb2 hc2 hn
  right_inv := evenVisibleKernelToHUVData_from (b := b) (c := c) (n := n) hb2 hc2 hn

lemma natCard_evenVisibleKernelHUVData {b c n : ℕ} [NeZero n]
    (hb2 : 1 < b) (hc2 : 1 < c) :
    Nat.card (EvenVisibleKernelHUVData b c n) =
      2 ^ (((n - 1) ^ 2) + ((n ^ c - n + 1) + (n ^ b - n + 1))) := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  change Nat.card (HAdmissible (n := n) × (ConstAggZ c n × ConstAggY b n)) =
    2 ^ (((n - 1) ^ 2) + ((n ^ c - n + 1) + (n ^ b - n + 1)))
  rw [Nat.card_prod, natCard_HAdmissible, Nat.card_prod,
    natCard_constAggZ (c := c) (n := n) hc, natCard_constAggY (b := b) (n := n) hb]
  simp [pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

lemma natCard_evenVisibleKernelData_closed_all_ge_two {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    Nat.card (EvenVisibleKernelData b c n) =
      2 ^ (n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
  have hb2' : 1 < b := by omega
  have hc2' : 1 < c := by omega
  rw [Nat.card_congr (evenVisibleKernelEquivHUVData (b := b) (c := c) (n := n) hb2' hc2' hn)]
  rw [natCard_evenVisibleKernelHUVData (b := b) (c := c) (n := n) hb2' hc2']
  congr 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  set B := k.succ ^ b
  set C := k.succ ^ c
  have hk1 : 1 ≤ k.succ := Nat.succ_le_succ (Nat.zero_le _)
  have hb1 : 1 ≤ b := by omega
  have hc1 : 1 ≤ c := by omega
  have hpowb : k.succ ≤ B := by
    simpa [B, pow_one] using Nat.pow_le_pow_right hk1 hb1
  have hpowc : k.succ ≤ C := by
    simpa [C, pow_one] using Nat.pow_le_pow_right hk1 hc1
  have hsubb : B - k.succ + 1 = B - k := by
    omega
  have hsubc : C - k.succ + 1 = C - k := by
    omega
  have hsplitb : B = (B - k) + k := by
    exact (Nat.sub_add_cancel (le_trans (Nat.le_succ k) hpowb)).symm
  have hsplitc : C = (C - k) + k := by
    exact (Nat.sub_add_cancel (le_trans (Nat.le_succ k) hpowc)).symm
  have hsq : k.succ * k.succ = k * k + 2 * k + 1 := by
    simp [Nat.succ_eq_add_one]
    ring
  have hfour : 4 * k.succ = 4 * k + 4 := by
    omega
  have hstep2 : B + C + k * k - 2 * k = B + C + k.succ ^ 2 - 4 * k.succ + 3 := by
    cases k with
    | zero =>
        exfalso
        simpa using hn
    | succ k' =>
        cases k' with
        | zero =>
            rw [pow_two, hsq, hfour]
            have hBC : 4 ≤ B + C := by
              omega
            omega
        | succ k'' =>
            rw [hsplitb, hsplitc, pow_two, hsq, hfour]
            set m : ℕ := k'' + 1 + 1
            change B - m + m + (C - m + m) + m * m - 2 * m =
              B - m + m + (C - m + m) + (m * m + 2 * m + 1) - (4 * m + 4) + 3
            have hm2 : 2 ≤ m := by
              dsimp [m]
              omega
            have hmleB : m ≤ B := by
              exact le_trans (Nat.le_succ m) hpowb
            have hmleC : m ≤ C := by
              exact le_trans (Nat.le_succ m) hpowc
            have hBcancel : B - m + m = B := Nat.sub_add_cancel hmleB
            have hCcancel : C - m + m = C := Nat.sub_add_cancel hmleC
            rw [hBcancel, hCcancel]
            set X : ℕ := B + C + (m * m + 2 * m + 1)
            have hm1B : m + 1 ≤ B := by
              simpa [Nat.succ_eq_add_one] using hpowb
            have hm1C : m + 1 ≤ C := by
              simpa [Nat.succ_eq_add_one] using hpowc
            have hmpos : 0 < m := by
              omega
            have hmSq : 1 ≤ m * m := by
              exact Nat.succ_le_of_lt (Nat.mul_pos hmpos hmpos)
            have hbound : 4 * m + 4 ≤ X := by
              dsimp [X]
              omega
            symm
            calc
              X - (4 * m + 4) + 3 = 3 + (X - (4 * m + 4)) := by ac_rfl
              _ = 3 + X - (4 * m + 4) := by rw [Nat.add_sub_assoc hbound]
              _ = B + C + m * m - 2 * m := by
                    dsimp [X]
                    omega
  have hlin :
      (B - k) + (C - k) + k * k = B + C + k.succ ^ 2 - 4 * k.succ + 3 := by
    calc
      (B - k) + (C - k) + k * k = B + C + k * k - 2 * k := by
        omega
      _ = B + C + k.succ ^ 2 - 4 * k.succ + 3 := hstep2
  have hexp :
      ((k.succ - 1) ^ 2) + ((C - k.succ + 1) + (B - k.succ + 1)) =
        B + C + k.succ ^ 2 - 4 * k.succ + 3 := by
    calc
      ((k.succ - 1) ^ 2) + ((C - k.succ + 1) + (B - k.succ + 1))
          = k * k + ((C - k) + (B - k)) := by
              rw [Nat.succ_sub_one, hsubb, hsubc, pow_two]
      _ = (B - k) + (C - k) + k * k := by ac_rfl
      _ = B + C + k.succ ^ 2 - 4 * k.succ + 3 := hlin
  simpa [B, C] using hexp

theorem card_evenVisibleKernelData_closed_all_ge_two {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    Fintype.card (EvenVisibleKernelData b c n) =
      2 ^ (n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_evenVisibleKernelData_closed_all_ge_two
    (b := b) (c := c) (n := n) hn hb2 hc2

lemma visibleHData_eq_of_ccoef_eq_of_b_eq_one {c n : ℕ} [NeZero n] (hc : 0 < c)
    {bc₁ bc₂ : ScalarVisibleCompat 1 c n} (hcc : bc₁.ccoef = bc₂.ccoef) :
    visibleHData (b := 1) (c := c) (n := n) hc bc₁ =
      visibleHData (b := 1) (c := c) (n := n) hc bc₂ := by
  have hb : 0 < 1 := by omega
  funext t r
  calc
    visibleHData (b := 1) (c := c) (n := n) hc bc₁ t r
        = bc₁.ccoef (yOfSum (b := 1) (n := n) hb t) (r + 1) +
            bc₁.ccoef (yOfSum (b := 1) (n := n) hb t) r := by
              simpa [sumY_yOfSum] using
                visibleH_eq_c_increment (b := 1) (c := c) (n := n) hc bc₁
                  (yOfSum (b := 1) (n := n) hb t) r
    _ =
        bc₂.ccoef (yOfSum (b := 1) (n := n) hb t) (r + 1) +
          bc₂.ccoef (yOfSum (b := 1) (n := n) hb t) r := by rw [hcc]
    _ = visibleHData (b := 1) (c := c) (n := n) hc bc₂ t r := by
          simpa [sumY_yOfSum] using
            (visibleH_eq_c_increment (b := 1) (c := c) (n := n) hc bc₂
              (yOfSum (b := 1) (n := n) hb t) r).symm

noncomputable def evenVisibleKernelToProfileConstAggZ_of_b_eq_one {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) :
    EvenVisibleKernelData 1 c n → Profile n × ConstAggZ c n
  | ⟨bc, hbker, hcker⟩ =>
      let hc : 0 < c := by omega
      let μ := (kerTScalarEquivProfile_of_b_eq_one (c := c) (n := n) hc) ⟨bc.ccoef, hcker⟩
      let uK : ConstAggZ c n := ⟨visibleUData bc,
        (TAdjScalar_buildScalarB_eq_zero_iff (b := 1) (c := c) (n := n) (by omega) hn hc2
          (visibleHData (b := 1) (c := c) (n := n) hc bc) (visibleUData bc)).1 <| by
            simpa [buildScalarB_visibleData_eq (b := 1) (c := c) (n := n) (by omega) hc bc] using hbker⟩
      (μ, uK)

noncomputable def evenVisibleKernelFromProfileConstAggZ_of_b_eq_one {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) :
    Profile n × ConstAggZ c n → EvenVisibleKernelData 1 c n
  | ⟨μ, uK⟩ =>
      let hc : 0 < c := by omega
      let h : HAdmissible (n := n) :=
        ⟨diagHRawOfProfile (n := n) μ, diagHRawOfProfile_mem_HAdmissible (n := n) μ⟩
      let bc : ScalarVisibleCompat 1 c n :=
        build_mem_scalarVisibleCompat_of_mem_HAdmissible
          (b := 1) (c := c) (n := n) (by omega) hc h uK.1 (diagVDataOfProfile (n := n) μ)
      ⟨bc,
        (TAdjScalar_buildScalarB_eq_zero_iff (b := 1) (c := c) (n := n) (by omega) hn hc2 h.1 uK.1).2
          uK.2,
        by
          change
            TScalar (b := 1) (c := c) (n := n)
              (buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ)) = 0
          rw [buildScalarC_diagHRawOfProfile_eq_diagScalarCCoefOfProfile]
          exact TScalar_diagScalarCCoefOfProfile_zero (c := c) (n := n) μ⟩

lemma evenVisibleKernelToProfileConstAggZ_of_b_eq_one_injective {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) :
    Function.Injective
      (evenVisibleKernelToProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2) := by
  have hc : 0 < c := by omega
  intro x y hxy
  rcases x with ⟨bcx, hbx, hcx⟩
  rcases y with ⟨bcy, hby, hcy⟩
  have hccsub :
      (⟨bcx.ccoef, hcx⟩ :
        { ccoef : ScalarCCoef 1 n // TScalar (b := 1) (c := c) (n := n) ccoef = 0 }) =
      ⟨bcy.ccoef, hcy⟩ := by
    exact (kerTScalarEquivProfile_of_b_eq_one (c := c) (n := n) hc).injective
      (congrArg Prod.fst hxy)
  have hcc : bcx.ccoef = bcy.ccoef := by
    exact congrArg Subtype.val hccsub
  have hu :
      visibleUData bcx = visibleUData bcy := by
    exact congrArg (fun z : Profile n × ConstAggZ c n => z.2.1) hxy
  have hh :
      visibleHData (b := 1) (c := c) (n := n) hc bcx =
        visibleHData (b := 1) (c := c) (n := n) hc bcy :=
    visibleHData_eq_of_ccoef_eq_of_b_eq_one (c := c) (n := n) hc hcc
  have hbcoef :
      bcx.bcoef = bcy.bcoef := by
    calc
      bcx.bcoef =
          buildScalarB
            (visibleHData (b := 1) (c := c) (n := n) hc bcx) (visibleUData bcx) := by
              symm
              exact buildScalarB_visibleData_eq (b := 1) (c := c) (n := n) (by omega) hc bcx
      _ =
          buildScalarB
            (visibleHData (b := 1) (c := c) (n := n) hc bcy) (visibleUData bcy) := by
              rw [hh, hu]
      _ = bcy.bcoef := by
            exact buildScalarB_visibleData_eq (b := 1) (c := c) (n := n) (by omega) hc bcy
  apply Subtype.ext
  exact ScalarVisibleCompat.ext hbcoef hcc

lemma evenVisibleKernelToProfileConstAggZ_of_b_eq_one_from {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) (z : Profile n × ConstAggZ c n) :
    evenVisibleKernelToProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2
      (evenVisibleKernelFromProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2 z) = z := by
  have hc : 0 < c := by omega
  rcases z with ⟨μ, uK⟩
  let h : HAdmissible (n := n) :=
    ⟨diagHRawOfProfile (n := n) μ, diagHRawOfProfile_mem_HAdmissible (n := n) μ⟩
  let bc : ScalarVisibleCompat 1 c n :=
    build_mem_scalarVisibleCompat_of_mem_HAdmissible
      (b := 1) (c := c) (n := n) (by omega) hc h uK.1 (diagVDataOfProfile (n := n) μ)
  have hbker : TAdjScalar (b := 1) (c := c) (n := n) bc.bcoef = 0 := by
    dsimp [bc]
    exact
      (TAdjScalar_buildScalarB_eq_zero_iff (b := 1) (c := c) (n := n) (by omega) hn hc2 h.1 uK.1).2
        uK.2
  have hcker : TScalar (b := 1) (c := c) (n := n) bc.ccoef = 0 := by
    change
      TScalar (b := 1) (c := c) (n := n)
        (buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ)) = 0
    rw [buildScalarC_diagHRawOfProfile_eq_diagScalarCCoefOfProfile]
    exact TScalar_diagScalarCCoefOfProfile_zero (c := c) (n := n) μ
  change evenVisibleKernelToProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2 ⟨bc, hbker, hcker⟩ =
    (μ, uK)
  apply Prod.ext
  · change
      (kerTScalarEquivProfile_of_b_eq_one (c := c) (n := n) hc)
        ⟨buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ), hcker⟩ = μ
    have hsub :
        (⟨buildScalarC (diagHRawOfProfile (n := n) μ) (diagVDataOfProfile (n := n) μ), hcker⟩ :
          { ccoef : ScalarCCoef 1 n // TScalar (b := 1) (c := c) (n := n) ccoef = 0 }) =
        ⟨diagScalarCCoefOfProfile (n := n) μ,
          TScalar_diagScalarCCoefOfProfile_zero (c := c) (n := n) μ⟩ := by
      apply Subtype.ext
      exact buildScalarC_diagHRawOfProfile_eq_diagScalarCCoefOfProfile (n := n) μ
    rw [hsub]
    exact (kerTScalarEquivProfile_of_b_eq_one (c := c) (n := n) hc).right_inv μ
  · apply Subtype.ext
    change visibleUData bc = ↑uK
    dsimp [bc]
    simpa [h] using
      visibleUData_build_eq (b := 1) (c := c) (n := n) (by omega) hc h uK.1
        (diagVDataOfProfile (n := n) μ)

lemma evenVisibleKernelFromProfileConstAggZ_of_b_eq_one_to {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) (x : EvenVisibleKernelData 1 c n) :
    evenVisibleKernelFromProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2
      (evenVisibleKernelToProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2 x) = x := by
  apply evenVisibleKernelToProfileConstAggZ_of_b_eq_one_injective
    (c := c) (n := n) hn hc2
  simpa using
    evenVisibleKernelToProfileConstAggZ_of_b_eq_one_from (c := c) (n := n) hn hc2
      (evenVisibleKernelToProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2 x)

noncomputable def evenVisibleKernelEquivProfileConstAggZ_of_b_eq_one {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) :
    EvenVisibleKernelData 1 c n ≃ Profile n × ConstAggZ c n where
  toFun := evenVisibleKernelToProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2
  invFun := evenVisibleKernelFromProfileConstAggZ_of_b_eq_one (c := c) (n := n) hn hc2
  left_inv := evenVisibleKernelFromProfileConstAggZ_of_b_eq_one_to (c := c) (n := n) hn hc2
  right_inv := evenVisibleKernelToProfileConstAggZ_of_b_eq_one_from (c := c) (n := n) hn hc2

lemma natCard_evenVisibleKernelData_closed_b_eq_one {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) :
    Nat.card (EvenVisibleKernelData 1 c n) = 2 ^ (n ^ c + 1) := by
  have hc : 0 < c := by omega
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  have hc1 : 1 ≤ c := by omega
  have hpow : n ≤ n ^ c := by
    simpa [pow_one] using Nat.pow_le_pow_right hn1 hc1
  rw [Nat.card_congr (evenVisibleKernelEquivProfileConstAggZ_of_b_eq_one
    (c := c) (n := n) hn hc2)]
  rw [Nat.card_prod]
  have hProf : Nat.card (Profile n) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_profile]
    simp [F]
  rw [hProf, natCard_constAggZ (c := c) (n := n) hc]
  calc
    2 ^ n * 2 ^ (n ^ c - n + 1) = 2 ^ (n + (n ^ c - n + 1)) := by
      symm
      exact pow_add 2 n (n ^ c - n + 1)
    _ = 2 ^ (n ^ c + 1) := by
      have hexp : n + (n ^ c - n + 1) = n ^ c + 1 := by
        omega
      rw [hexp]

theorem card_evenVisibleKernelData_closed_b_eq_one {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) :
    Fintype.card (EvenVisibleKernelData 1 c n) = 2 ^ (n ^ c + 1) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_evenVisibleKernelData_closed_b_eq_one
    (c := c) (n := n) hn hc2

lemma sumZ_eq_apply_zero_of_c_eq_one {n : ℕ} [NeZero n] (z : ZCoord 1 n) :
    sumZ z = z 0 := by
  simpa [sumZ, sigmaCoord, No13Migration.sumCoord]

lemma sumZ_injective_of_c_eq_one {n : ℕ} [NeZero n] :
    Function.Injective (sumZ (c := 1) (n := n)) := by
  intro z z' h
  ext i
  fin_cases i
  simpa [sumZ_eq_apply_zero_of_c_eq_one] using h

lemma z_eq_zOfSum_of_c_eq_one {n : ℕ} [NeZero n] (z : ZCoord 1 n) :
    z = zOfSum (c := 1) (n := n) (by omega) (sumZ z) := by
  apply sumZ_injective_of_c_eq_one (n := n)
  simpa using (sumZ_zOfSum (c := 1) (n := n) (by omega) (sumZ z)).symm

lemma BAgg_eq_of_c_eq_one {n : ℕ} [NeZero n] (bcoef : ScalarBCoef 1 n) (t s : I n) :
    BAgg (c := 1) (n := n) bcoef t s = bcoef t (zOfSum (c := 1) (n := n) (by omega) s) := by
  have hc : 0 < 1 := by omega
  unfold BAgg
  rw [Finset.sum_eq_single (zOfSum (c := 1) (n := n) hc s)]
  · simp
  · intro z _ hz
    by_cases hzs : sumZ z = s
    · have hz' : z = zOfSum (c := 1) (n := n) hc s := by
        apply sumZ_injective_of_c_eq_one (n := n)
        simpa [hzs] using (sumZ_zOfSum (c := 1) (n := n) hc s).symm
      exact (hz hz').elim
    · simp [hzs]
  · simp

lemma BAgg_injective_of_c_eq_one {n : ℕ} [NeZero n] :
    Function.Injective (BAgg (c := 1) (n := n)) := by
  intro b₁ b₂ h
  funext t z
  have hz : z = zOfSum (c := 1) (n := n) (by omega) (sumZ z) := by
    simpa using z_eq_zOfSum_of_c_eq_one (n := n) z
  have hs := congrFun (congrFun h t) (sumZ z)
  rw [BAgg_eq_of_c_eq_one (n := n) b₁ t (sumZ z),
    BAgg_eq_of_c_eq_one (n := n) b₂ t (sumZ z)] at hs
  rw [← hz] at hs
  exact hs

noncomputable def diagScalarBCoefOfProfile {n : ℕ} [NeZero n] (μ : Profile n) :
    ScalarBCoef 1 n :=
  fun t z => μ (t + sumZ z)

lemma BAgg_diagScalarBCoefOfProfile {n : ℕ} [NeZero n] (μ : Profile n) :
    BAgg (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) = diagConst μ := by
  funext t s
  rw [BAgg_eq_of_c_eq_one]
  simp [diagScalarBCoefOfProfile, diagConst, sumZ_zOfSum (c := 1) (n := n) (by omega) s]

lemma TAdjScalar_diagScalarBCoefOfProfile_zero {b n : ℕ} [NeZero n] (μ : Profile n) :
    TAdjScalar (b := b) (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) = 0 := by
  funext y r
  change
    BAgg (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) (sumY y) r +
      BAgg (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) (sumY y + 1) (r - 1) = 0
  rw [show BAgg (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) (sumY y) r =
      diagConst μ (sumY y) r by
        exact congrFun (congrFun (BAgg_diagScalarBCoefOfProfile (n := n) μ) (sumY y)) r]
  rw [show BAgg (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) (sumY y + 1) (r - 1) =
      diagConst μ (sumY y + 1) (r - 1) by
        exact congrFun (congrFun (BAgg_diagScalarBCoefOfProfile (n := n) μ) (sumY y + 1)) (r - 1)]
  simp [diagConst, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, F_add_self]

lemma TAdjScalar_eq_zero_iff_exists_diagScalarBCoefOfProfile_of_c_eq_one {b n : ℕ} [NeZero n]
    (hb : 0 < b) (bcoef : ScalarBCoef 1 n) :
    TAdjScalar (b := b) (c := 1) (n := n) bcoef = 0 ↔
      ∃ μ : Profile n, bcoef = diagScalarBCoefOfProfile (n := n) μ := by
  constructor
  · intro hzero
    let m : MatrixFun n := BAgg (c := 1) (n := n) bcoef
    have hD : Dfun m = 0 := by
      apply (Dfun_eq_zero_iff_step (n := n) m).2
      intro t s
      have hs := congrFun (congrFun hzero (yOfSum (b := b) (n := n) hb (t - 1))) (s + 1)
      have hs0 : m (t - 1) (s + 1) + m t s = 0 := by
        simpa [m, TAdjScalar, TAdjScalarFun, sumY_yOfSum (b := b) (n := n) hb (t - 1),
          sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs
      have hs' : m (t - 1) (s + 1) = -(m t s) := eq_neg_of_add_eq_zero_left hs0
      simpa [m] using hs'
    have hker : m ∈ LinearMap.ker (D (n := n)) := by
      change Dfun m = 0
      exact hD
    rcases (mem_ker_D_iff_exists_diagConst (n := n) m).mp hker with ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    apply BAgg_injective_of_c_eq_one (n := n)
    calc
      BAgg (c := 1) (n := n) bcoef = diagConst μ := hμ
      _ = BAgg (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) := by
            symm
            exact BAgg_diagScalarBCoefOfProfile (n := n) μ
  · rintro ⟨μ, rfl⟩
    exact TAdjScalar_diagScalarBCoefOfProfile_zero (b := b) (n := n) μ

noncomputable def kerTAdjScalarEquivProfile_of_c_eq_one {b n : ℕ} [NeZero n] (hb : 0 < b) :
    { bcoef : ScalarBCoef 1 n // TAdjScalar (b := b) (c := 1) (n := n) bcoef = 0 } ≃ Profile n where
  toFun := fun x => BAgg (c := 1) (n := n) x.1 0
  invFun := fun μ => ⟨diagScalarBCoefOfProfile (n := n) μ,
    TAdjScalar_diagScalarBCoefOfProfile_zero (b := b) (n := n) μ⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply BAgg_injective_of_c_eq_one (n := n)
    rcases
      (TAdjScalar_eq_zero_iff_exists_diagScalarBCoefOfProfile_of_c_eq_one
        (b := b) (n := n) hb x.1).mp x.2 with ⟨μ, hμ⟩
    calc
      BAgg (c := 1) (n := n)
          (diagScalarBCoefOfProfile (n := n) (BAgg (c := 1) (n := n) x.1 0)) =
          diagConst (BAgg (c := 1) (n := n) x.1 0) := by
            exact BAgg_diagScalarBCoefOfProfile (n := n) (BAgg (c := 1) (n := n) x.1 0)
      _ = diagConst μ := by
            funext t s
            have hrow : BAgg (c := 1) (n := n) x.1 0 = μ := by
              funext r
              rw [hμ, BAgg_diagScalarBCoefOfProfile]
              simp [diagConst]
            rw [hrow]
      _ = BAgg (c := 1) (n := n) x.1 := by
            rw [hμ, BAgg_diagScalarBCoefOfProfile]
  right_inv := by
    intro μ
    funext s
    have hs := congrFun (congrFun (BAgg_diagScalarBCoefOfProfile (n := n) μ) 0) s
    simpa [diagConst] using hs

noncomputable def diagUDataOfProfile {n : ℕ} [NeZero n] (μ : Profile n) : ZCoord 1 n → F :=
  fun z => μ (sumZ z)

lemma prefixT_diagHRawOfProfile {n : ℕ} [NeZero n] (μ : Profile n) (t s : I n) :
    prefixT (diagHRawOfProfile (n := n) μ) t s = μ (t + s) + μ s := by
  let h : HRaw n := diagHRawOfProfile (n := n) μ
  have hh : h ∈ HAdmissible (n := n) := diagHRawOfProfile_mem_HAdmissible (n := n) μ
  let g : I n → F := fun r => prefixT h r s + μ (r + s) + μ s
  have hstep : ∀ r : I n, g (r + 1) = g r := by
    intro r
    have hp : prefixT h (r + 1) s = prefixT h r s + h r s := by
      have hq := prefixT_pair_eq_of_mem_HAdmissible (n := n) hh r s
      apply add_left_cancel (a := prefixT h r s)
      simpa [add_assoc, add_left_comm, add_comm, F_add_self] using hq
    dsimp [g]
    rw [hp]
    simp [h, diagHRawOfProfile, add_assoc, add_left_comm, add_comm, F_add_self]
  have hconst := zmod_step_const g hstep t
  have hzero : g 0 = 0 := by
    simp [g, h, prefixT_zero, add_assoc, add_left_comm, add_comm, F_add_self]
  have hgt : g t = 0 := by
    simpa [hzero] using hconst
  have hsum : prefixT h t s + (μ (t + s) + μ s) = 0 := by
    simpa [g, add_assoc, add_left_comm, add_comm] using hgt
  have hEq := eq_neg_of_add_eq_zero_left hsum
  simpa [h, add_assoc, add_left_comm, add_comm] using hEq

lemma buildScalarB_diagHRawOfProfile_eq_diagScalarBCoefOfProfile {n : ℕ} [NeZero n]
    (μ : Profile n) :
    buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ) =
      diagScalarBCoefOfProfile (n := n) μ := by
  have hc : 0 < 1 := by omega
  apply BAgg_injective_of_c_eq_one (n := n)
  funext t r
  calc
    BAgg (c := 1) (n := n)
        (buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ)) t r
        =
        buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ)
          t (zOfSum (c := 1) (n := n) hc r) := by
            rw [BAgg_eq_of_c_eq_one]
    _ = μ (t + r) := by
          have hz : sumZ (zOfSum (c := 1) (n := n) hc r) = r := sumZ_zOfSum (c := 1) (n := n) hc r
          have hp :
              prefixT (diagHRawOfProfile (n := n) μ) t r = μ (t + r) + μ r :=
            prefixT_diagHRawOfProfile (n := n) μ t r
          calc
            buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ)
                t (zOfSum (c := 1) (n := n) hc r)
                =
                diagUDataOfProfile (n := n) μ (zOfSum (c := 1) (n := n) hc r) +
                  prefixT (diagHRawOfProfile (n := n) μ) t r := by
                      simp [buildScalarB, hz]
            _ = μ r + (μ (t + r) + μ r) := by
                  simp [diagUDataOfProfile, hz, hp]
            _ = μ (t + r) := by
                  calc
                    μ r + (μ (t + r) + μ r) = (μ r + μ r) + μ (t + r) := by ac_rfl
                    _ = μ (t + r) := by simp [F_add_self]
    _ = BAgg (c := 1) (n := n) (diagScalarBCoefOfProfile (n := n) μ) t r := by
          rw [BAgg_diagScalarBCoefOfProfile]
          simp [diagConst]

lemma visibleHData_eq_of_bcoef_eq_of_c_eq_one {b n : ℕ} [NeZero n]
    {bc₁ bc₂ : ScalarVisibleCompat b 1 n} (hbc : bc₁.bcoef = bc₂.bcoef) :
    visibleHData (b := b) (c := 1) (n := n) (by omega) bc₁ =
      visibleHData (b := b) (c := 1) (n := n) (by omega) bc₂ := by
  funext t r
  simp [visibleHData, hbc]

noncomputable def evenVisibleKernelToProfileConstAggY_of_c_eq_one {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) :
    EvenVisibleKernelData b 1 n → Profile n × ConstAggY b n
  | ⟨bc, hbker, hcker⟩ =>
      let hb : 0 < b := by omega
      let μ := (kerTAdjScalarEquivProfile_of_c_eq_one (b := b) (n := n) hb) ⟨bc.bcoef, hbker⟩
      let vK : ConstAggY b n := ⟨visibleVData bc,
        (TScalar_buildScalarC_eq_zero_iff (b := b) (c := 1) (n := n) hn hb2
          (visibleHData (b := b) (c := 1) (n := n) (by omega) bc) (visibleVData bc)).1 <| by
            simpa [buildScalarC_visibleData_eq (b := b) (c := 1) (n := n) (by omega) bc] using hcker⟩
      (μ, vK)

noncomputable def evenVisibleKernelFromProfileConstAggY_of_c_eq_one {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) :
    Profile n × ConstAggY b n → EvenVisibleKernelData b 1 n
  | ⟨μ, vK⟩ =>
      let hb : 0 < b := by omega
      let h : HAdmissible (n := n) :=
        ⟨diagHRawOfProfile (n := n) μ, diagHRawOfProfile_mem_HAdmissible (n := n) μ⟩
      let bc : ScalarVisibleCompat b 1 n :=
        build_mem_scalarVisibleCompat_of_mem_HAdmissible
          (b := b) (c := 1) (n := n) hb (by omega) h (diagUDataOfProfile (n := n) μ) vK.1
      ⟨bc,
        by
          change
            TAdjScalar (b := b) (c := 1) (n := n)
              (buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ)) = 0
          rw [buildScalarB_diagHRawOfProfile_eq_diagScalarBCoefOfProfile]
          exact TAdjScalar_diagScalarBCoefOfProfile_zero (b := b) (n := n) μ,
        (TScalar_buildScalarC_eq_zero_iff (b := b) (c := 1) (n := n) hn hb2 h.1 vK.1).2 vK.2⟩

lemma evenVisibleKernelToProfileConstAggY_of_c_eq_one_injective {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) :
    Function.Injective
      (evenVisibleKernelToProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2) := by
  have hb : 0 < b := by omega
  intro x y hxy
  rcases x with ⟨bcx, hbx, hcx⟩
  rcases y with ⟨bcy, hby, hcy⟩
  have hbsub :
      (⟨bcx.bcoef, hbx⟩ :
        { bcoef : ScalarBCoef 1 n // TAdjScalar (b := b) (c := 1) (n := n) bcoef = 0 }) =
      ⟨bcy.bcoef, hby⟩ := by
    exact (kerTAdjScalarEquivProfile_of_c_eq_one (b := b) (n := n) hb).injective
      (congrArg Prod.fst hxy)
  have hbcoef : bcx.bcoef = bcy.bcoef := by
    exact congrArg Subtype.val hbsub
  have hv :
      visibleVData bcx = visibleVData bcy := by
    exact congrArg (fun z : Profile n × ConstAggY b n => z.2.1) hxy
  have hh :
      visibleHData (b := b) (c := 1) (n := n) (by omega) bcx =
        visibleHData (b := b) (c := 1) (n := n) (by omega) bcy :=
    visibleHData_eq_of_bcoef_eq_of_c_eq_one (b := b) (n := n) hbcoef
  have hccoef :
      bcx.ccoef = bcy.ccoef := by
    calc
      bcx.ccoef =
          buildScalarC
            (visibleHData (b := b) (c := 1) (n := n) (by omega) bcx) (visibleVData bcx) := by
              symm
              exact buildScalarC_visibleData_eq (b := b) (c := 1) (n := n) (by omega) bcx
      _ =
          buildScalarC
            (visibleHData (b := b) (c := 1) (n := n) (by omega) bcy) (visibleVData bcy) := by
              rw [hh, hv]
      _ = bcy.ccoef := by
            exact buildScalarC_visibleData_eq (b := b) (c := 1) (n := n) (by omega) bcy
  apply Subtype.ext
  exact ScalarVisibleCompat.ext hbcoef hccoef

lemma evenVisibleKernelToProfileConstAggY_of_c_eq_one_from {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) (z : Profile n × ConstAggY b n) :
    evenVisibleKernelToProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2
      (evenVisibleKernelFromProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2 z) = z := by
  have hb : 0 < b := by omega
  rcases z with ⟨μ, vK⟩
  let h : HAdmissible (n := n) :=
    ⟨diagHRawOfProfile (n := n) μ, diagHRawOfProfile_mem_HAdmissible (n := n) μ⟩
  let bc : ScalarVisibleCompat b 1 n :=
    build_mem_scalarVisibleCompat_of_mem_HAdmissible
      (b := b) (c := 1) (n := n) hb (by omega) h (diagUDataOfProfile (n := n) μ) vK.1
  have hbker : TAdjScalar (b := b) (c := 1) (n := n) bc.bcoef = 0 := by
    change
      TAdjScalar (b := b) (c := 1) (n := n)
        (buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ)) = 0
    rw [buildScalarB_diagHRawOfProfile_eq_diagScalarBCoefOfProfile]
    exact TAdjScalar_diagScalarBCoefOfProfile_zero (b := b) (n := n) μ
  have hcker : TScalar (b := b) (c := 1) (n := n) bc.ccoef = 0 := by
    dsimp [bc]
    exact (TScalar_buildScalarC_eq_zero_iff (b := b) (c := 1) (n := n) hn hb2 h.1 vK.1).2 vK.2
  change evenVisibleKernelToProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2 ⟨bc, hbker, hcker⟩ =
    (μ, vK)
  apply Prod.ext
  · change
      (kerTAdjScalarEquivProfile_of_c_eq_one (b := b) (n := n) hb)
        ⟨buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ), hbker⟩ = μ
    have hsub :
        (⟨buildScalarB (diagHRawOfProfile (n := n) μ) (diagUDataOfProfile (n := n) μ), hbker⟩ :
          { bcoef : ScalarBCoef 1 n // TAdjScalar (b := b) (c := 1) (n := n) bcoef = 0 }) =
        ⟨diagScalarBCoefOfProfile (n := n) μ,
          TAdjScalar_diagScalarBCoefOfProfile_zero (b := b) (n := n) μ⟩ := by
      apply Subtype.ext
      exact buildScalarB_diagHRawOfProfile_eq_diagScalarBCoefOfProfile (n := n) μ
    rw [hsub]
    exact (kerTAdjScalarEquivProfile_of_c_eq_one (b := b) (n := n) hb).right_inv μ
  · apply Subtype.ext
    change visibleVData bc = ↑vK
    dsimp [bc]
    simpa [h] using
      visibleVData_build_eq (b := b) (c := 1) (n := n) hb (by omega) h
        (diagUDataOfProfile (n := n) μ) vK.1

lemma evenVisibleKernelFromProfileConstAggY_of_c_eq_one_to {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) (x : EvenVisibleKernelData b 1 n) :
    evenVisibleKernelFromProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2
      (evenVisibleKernelToProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2 x) = x := by
  apply evenVisibleKernelToProfileConstAggY_of_c_eq_one_injective
    (b := b) (n := n) hn hb2
  simpa using
    evenVisibleKernelToProfileConstAggY_of_c_eq_one_from (b := b) (n := n) hn hb2
      (evenVisibleKernelToProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2 x)

noncomputable def evenVisibleKernelEquivProfileConstAggY_of_c_eq_one {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) :
    EvenVisibleKernelData b 1 n ≃ Profile n × ConstAggY b n where
  toFun := evenVisibleKernelToProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2
  invFun := evenVisibleKernelFromProfileConstAggY_of_c_eq_one (b := b) (n := n) hn hb2
  left_inv := evenVisibleKernelFromProfileConstAggY_of_c_eq_one_to (b := b) (n := n) hn hb2
  right_inv := evenVisibleKernelToProfileConstAggY_of_c_eq_one_from (b := b) (n := n) hn hb2

lemma natCard_evenVisibleKernelData_closed_c_eq_one {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) :
    Nat.card (EvenVisibleKernelData b 1 n) = 2 ^ (n ^ b + 1) := by
  have hb : 0 < b := by omega
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  have hb1 : 1 ≤ b := by omega
  have hpow : n ≤ n ^ b := by
    simpa [pow_one] using Nat.pow_le_pow_right hn1 hb1
  rw [Nat.card_congr (evenVisibleKernelEquivProfileConstAggY_of_c_eq_one
    (b := b) (n := n) hn hb2)]
  rw [Nat.card_prod]
  have hProf : Nat.card (Profile n) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_profile]
    simp [F]
  rw [hProf, natCard_constAggY (b := b) (n := n) hb]
  calc
    2 ^ n * 2 ^ (n ^ b - n + 1) = 2 ^ (n + (n ^ b - n + 1)) := by
      symm
      exact pow_add 2 n (n ^ b - n + 1)
    _ = 2 ^ (n ^ b + 1) := by
      have hexp : n + (n ^ b - n + 1) = n ^ b + 1 := by
        omega
      rw [hexp]

theorem card_evenVisibleKernelData_closed_c_eq_one {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) :
    Fintype.card (EvenVisibleKernelData b 1 n) = 2 ^ (n ^ b + 1) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_evenVisibleKernelData_closed_c_eq_one
    (b := b) (n := n) hn hb2

lemma diagScalarCCoefOfProfile_apply {n : ℕ} [NeZero n] (μ : Profile n) (y : YCoord 1 n)
    (r : I n) :
    diagScalarCCoefOfProfile (n := n) μ y r = μ (sumY y + r) := by
  have hy : y = yOfSum (b := 1) (n := n) (by omega) (sumY y) :=
    y_eq_yOfSum_of_b_eq_one (n := n) y
  unfold diagScalarCCoefOfProfile liftMatrix
  rw [if_pos hy]
  simp [diagConst]

lemma diagProfile_sum_eq_const_of_visible_eq_one_eq_one {n : ℕ} [NeZero n]
    (bc : ScalarVisibleCompat 1 1 n) (μ ν : Profile n)
    (hb : bc.bcoef = diagScalarBCoefOfProfile (n := n) ν)
    (hc : bc.ccoef = diagScalarCCoefOfProfile (n := n) μ) :
    ∀ s : I n, ν s + μ s = ν 0 + μ 0 := by
  let δ : Profile n := fun s => ν s + μ s
  have hstep : ∀ s : I n, δ (s + 1) = δ s := by
    intro s
    have hcompat := bc.compat (yOfSum (b := 1) (n := n) (by omega) 0)
      (zOfSum (c := 1) (n := n) (by omega) s)
    have hs0 : ν s + ν (s + 1) + (μ s + μ (s + 1)) = 0 := by
      simpa [hb, hc, diagScalarBCoefOfProfile, diagScalarCCoefOfProfile_apply,
        sumY_yOfSum, sumZ_zOfSum, add_assoc, add_left_comm, add_comm] using hcompat
    have hs1 : (ν (s + 1) + μ (s + 1)) + (ν s + μ s) = 0 := by
      simpa [add_assoc, add_left_comm, add_comm] using hs0
    have hs2 : δ (s + 1) = -(δ s) := by
      simpa [δ] using (eq_neg_of_add_eq_zero_left hs1)
    simpa [δ, add_assoc, add_left_comm, add_comm] using hs2
  intro s
  simpa [δ] using zmod_step_const δ hstep s

lemma diagProfile_eq_add_const_of_visible_eq_one_eq_one {n : ℕ} [NeZero n]
    (bc : ScalarVisibleCompat 1 1 n) (μ ν : Profile n)
    (hb : bc.bcoef = diagScalarBCoefOfProfile (n := n) ν)
    (hc : bc.ccoef = diagScalarCCoefOfProfile (n := n) μ) :
    ν = μ + constProfile (n := n) (ν 0 + μ 0) := by
  funext s
  have hs := diagProfile_sum_eq_const_of_visible_eq_one_eq_one
    (n := n) bc μ ν hb hc s
  calc
    ν s = ν s + (μ s + μ s) := by simp [F_add_self]
    _ = (ν s + μ s) + μ s := by ac_rfl
    _ = (ν 0 + μ 0) + μ s := by rw [hs]
    _ = μ s + (ν 0 + μ 0) := by ac_rfl
    _ = (μ + constProfile (n := n) (ν 0 + μ 0)) s := by
          simp [constProfile]

noncomputable def evenVisibleKernelToProfileBit_of_eq_one_eq_one {n : ℕ} [NeZero n] :
    EvenVisibleKernelData 1 1 n → Profile n × F
  | ⟨bc, hbker, hcker⟩ =>
      let μ := (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
        ⟨bc.ccoef, hcker⟩
      let ν := (kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega))
        ⟨bc.bcoef, hbker⟩
      (μ, ν 0 + μ 0)

noncomputable def evenVisibleKernelFromProfileBit_of_eq_one_eq_one {n : ℕ} [NeZero n] :
    Profile n × F → EvenVisibleKernelData 1 1 n
  | ⟨μ, a⟩ =>
      let ν : Profile n := μ + constProfile (n := n) a
      ⟨{ bcoef := diagScalarBCoefOfProfile (n := n) ν
        , ccoef := diagScalarCCoefOfProfile (n := n) μ
        , compat := by
            intro y z
            simp [ν, diagScalarBCoefOfProfile, diagScalarCCoefOfProfile_apply, constProfile,
              add_assoc, add_left_comm, add_comm, F_add_self] },
        TAdjScalar_diagScalarBCoefOfProfile_zero (b := 1) (n := n) ν,
        TScalar_diagScalarCCoefOfProfile_zero (c := 1) (n := n) μ⟩

lemma evenVisibleKernelToProfileBit_of_eq_one_eq_one_of_diag {n : ℕ} [NeZero n]
    (μ ν : Profile n)
    (hcompat :
      ∀ y z,
        diagScalarBCoefOfProfile (n := n) ν (sumY y) z +
            diagScalarBCoefOfProfile (n := n) ν (sumY y + 1) z +
            diagScalarCCoefOfProfile (n := n) μ y (sumZ z) +
            diagScalarCCoefOfProfile (n := n) μ y (sumZ z + 1) = 0) :
    evenVisibleKernelToProfileBit_of_eq_one_eq_one (n := n)
      ⟨{ bcoef := diagScalarBCoefOfProfile (n := n) ν
        , ccoef := diagScalarCCoefOfProfile (n := n) μ
        , compat := hcompat },
        TAdjScalar_diagScalarBCoefOfProfile_zero (b := 1) (n := n) ν,
        TScalar_diagScalarCCoefOfProfile_zero (c := 1) (n := n) μ⟩ = (μ, ν 0 + μ 0) := by
  apply Prod.ext
  · change
      (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
        ⟨diagScalarCCoefOfProfile (n := n) μ,
          TScalar_diagScalarCCoefOfProfile_zero (c := 1) (n := n) μ⟩ = μ
    exact (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega)).right_inv μ
  · have hμ :
        (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
          ⟨diagScalarCCoefOfProfile (n := n) μ,
            TScalar_diagScalarCCoefOfProfile_zero (c := 1) (n := n) μ⟩ = μ :=
      (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega)).right_inv μ
    have hν :
        (kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega))
          ⟨diagScalarBCoefOfProfile (n := n) ν,
            TAdjScalar_diagScalarBCoefOfProfile_zero (b := 1) (n := n) ν⟩ = ν :=
      (kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega)).right_inv ν
    change
      (kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega))
          ⟨diagScalarBCoefOfProfile (n := n) ν,
            TAdjScalar_diagScalarBCoefOfProfile_zero (b := 1) (n := n) ν⟩ 0 +
        (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
          ⟨diagScalarCCoefOfProfile (n := n) μ,
            TScalar_diagScalarCCoefOfProfile_zero (c := 1) (n := n) μ⟩ 0 =
          ν 0 + μ 0
    rw [hν, hμ]

lemma evenVisibleKernelToProfileBit_of_eq_one_eq_one_from {n : ℕ} [NeZero n]
    (z : Profile n × F) :
    evenVisibleKernelToProfileBit_of_eq_one_eq_one (n := n)
      (evenVisibleKernelFromProfileBit_of_eq_one_eq_one (n := n) z) = z := by
  rcases z with ⟨μ, a⟩
  let ν : Profile n := μ + constProfile (n := n) a
  have hcompat :
      ∀ y z,
        diagScalarBCoefOfProfile (n := n) ν (sumY y) z +
            diagScalarBCoefOfProfile (n := n) ν (sumY y + 1) z +
            diagScalarCCoefOfProfile (n := n) μ y (sumZ z) +
            diagScalarCCoefOfProfile (n := n) μ y (sumZ z + 1) = 0 := by
    intro y z
    simp [ν, diagScalarBCoefOfProfile, diagScalarCCoefOfProfile_apply, constProfile,
      add_assoc, add_left_comm, add_comm, F_add_self]
  calc
    evenVisibleKernelToProfileBit_of_eq_one_eq_one (n := n)
        (evenVisibleKernelFromProfileBit_of_eq_one_eq_one (n := n) (μ, a))
        = (μ, μ 0 + constProfile (n := n) a 0 + μ 0) := by
            simpa [evenVisibleKernelFromProfileBit_of_eq_one_eq_one, ν, hcompat] using
              evenVisibleKernelToProfileBit_of_eq_one_eq_one_of_diag (n := n) μ ν hcompat
    _ = (μ, a) := by
          apply Prod.ext
          · rfl
          · simp [constProfile, add_assoc, add_left_comm, add_comm, F_add_self]

lemma evenVisibleKernelToProfileBit_of_eq_one_eq_one_injective {n : ℕ} [NeZero n] :
    Function.Injective (evenVisibleKernelToProfileBit_of_eq_one_eq_one (n := n)) := by
  intro x y hxy
  rcases x with ⟨bcx, hbx, hcx⟩
  rcases y with ⟨bcy, hby, hcy⟩
  let μx := (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
    ⟨bcx.ccoef, hcx⟩
  let νx := (kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega))
    ⟨bcx.bcoef, hbx⟩
  let ax : F := νx 0 + μx 0
  let μy := (kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
    ⟨bcy.ccoef, hcy⟩
  let νy := (kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega))
    ⟨bcy.bcoef, hby⟩
  let ay : F := νy 0 + μy 0
  have hμ : μx = μy := congrArg Prod.fst hxy
  have ha : ax = ay := congrArg Prod.snd hxy
  have hccx : bcx.ccoef = diagScalarCCoefOfProfile (n := n) μx := by
    change bcx.ccoef =
      diagScalarCCoefOfProfile (n := n)
        ((kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
          ⟨bcx.ccoef, hcx⟩)
    exact (congrArg Subtype.val
      ((kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega)).left_inv
        (⟨bcx.ccoef, hcx⟩ :
          { ccoef : ScalarCCoef 1 n // TScalar (b := 1) (c := 1) (n := n) ccoef = 0 }))).symm
  have hccy : bcy.ccoef = diagScalarCCoefOfProfile (n := n) μy := by
    change bcy.ccoef =
      diagScalarCCoefOfProfile (n := n)
        ((kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega))
          ⟨bcy.ccoef, hcy⟩)
    exact (congrArg Subtype.val
      ((kerTScalarEquivProfile_of_b_eq_one (c := 1) (n := n) (by omega)).left_inv
        (⟨bcy.ccoef, hcy⟩ :
          { ccoef : ScalarCCoef 1 n // TScalar (b := 1) (c := 1) (n := n) ccoef = 0 }))).symm
  have hbx' : bcx.bcoef = diagScalarBCoefOfProfile (n := n) νx := by
    change bcx.bcoef =
      diagScalarBCoefOfProfile (n := n)
        ((kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega))
          ⟨bcx.bcoef, hbx⟩)
    exact (congrArg Subtype.val
      ((kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega)).left_inv
        (⟨bcx.bcoef, hbx⟩ :
          { bcoef : ScalarBCoef 1 n // TAdjScalar (b := 1) (c := 1) (n := n) bcoef = 0 }))).symm
  have hby' : bcy.bcoef = diagScalarBCoefOfProfile (n := n) νy := by
    change bcy.bcoef =
      diagScalarBCoefOfProfile (n := n)
        ((kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega))
          ⟨bcy.bcoef, hby⟩)
    exact (congrArg Subtype.val
      ((kerTAdjScalarEquivProfile_of_c_eq_one (b := 1) (n := n) (by omega)).left_inv
        (⟨bcy.bcoef, hby⟩ :
          { bcoef : ScalarBCoef 1 n // TAdjScalar (b := 1) (c := 1) (n := n) bcoef = 0 }))).symm
  have hνx : νx = μx + constProfile (n := n) ax := by
    exact diagProfile_eq_add_const_of_visible_eq_one_eq_one
      (n := n) bcx μx νx hbx' hccx
  have hνy : νy = μy + constProfile (n := n) ay := by
    exact diagProfile_eq_add_const_of_visible_eq_one_eq_one
      (n := n) bcy μy νy hby' hccy
  have hcc : bcx.ccoef = bcy.ccoef := by
    rw [hccx, hccy, hμ]
  have hbcoef : bcx.bcoef = bcy.bcoef := by
    rw [hbx', hby', hνx, hνy, hμ, ha]
  exact Subtype.ext (ScalarVisibleCompat.ext hbcoef hcc)

lemma evenVisibleKernelFromProfileBit_of_eq_one_eq_one_to {n : ℕ} [NeZero n]
    (x : EvenVisibleKernelData 1 1 n) :
    evenVisibleKernelFromProfileBit_of_eq_one_eq_one (n := n)
      (evenVisibleKernelToProfileBit_of_eq_one_eq_one (n := n) x) = x := by
  apply evenVisibleKernelToProfileBit_of_eq_one_eq_one_injective (n := n)
  simpa using
    evenVisibleKernelToProfileBit_of_eq_one_eq_one_from (n := n)
      (evenVisibleKernelToProfileBit_of_eq_one_eq_one (n := n) x)

noncomputable def evenVisibleKernelEquivProfileBit_of_eq_one_eq_one {n : ℕ} [NeZero n] :
    EvenVisibleKernelData 1 1 n ≃ Profile n × F where
  toFun := evenVisibleKernelToProfileBit_of_eq_one_eq_one (n := n)
  invFun := evenVisibleKernelFromProfileBit_of_eq_one_eq_one (n := n)
  left_inv := evenVisibleKernelFromProfileBit_of_eq_one_eq_one_to (n := n)
  right_inv := evenVisibleKernelToProfileBit_of_eq_one_eq_one_from (n := n)

lemma natCard_evenVisibleKernelData_closed_eq_one_eq_one {n : ℕ} [NeZero n] :
    Nat.card (EvenVisibleKernelData 1 1 n) = 2 ^ (n + 1) := by
  rw [Nat.card_congr (evenVisibleKernelEquivProfileBit_of_eq_one_eq_one (n := n))]
  rw [Nat.card_prod]
  have hProf : Nat.card (Profile n) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := F), finrank_profile]
    simp [F]
  have hF : Fintype.card F = 2 := by
    simp [F, ZMod.card]
  rw [hProf, Nat.card_eq_fintype_card, hF]
  rw [Nat.pow_succ]

theorem card_evenVisibleKernelData_closed_eq_one_eq_one {n : ℕ} [NeZero n] :
    Fintype.card (EvenVisibleKernelData 1 1 n) = 2 ^ (n + 1) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_evenVisibleKernelData_closed_eq_one_eq_one (n := n)

lemma BAgg_scalarBConst {c n : ℕ} [NeZero n] (u : ZCoord c n → F) (t s : I n) :
    BAgg (c := c) (n := n) (scalarBConst (c := c) u) t s = scalarZAgg (c := c) (n := n) u s := by
  unfold BAgg scalarBConst scalarZAgg
  refine Finset.sum_congr rfl ?_
  intro z hz
  by_cases hzs : sumZ z = s <;> simp [hzs]

noncomputable def cPairScalar {b n : ℕ} [NeZero n]
    (c₁ c₂ : ScalarCCoef b n) : F :=
  ∑ y : YCoord b n, ∑ r : I n, c₁ y r * c₂ y r

lemma sum_BAgg_apply_eq {c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (t : I n) (f : I n → F) :
    ∑ r : I n, BAgg (c := c) (n := n) bcoef t r * f r =
      ∑ z : ZCoord c n, bcoef t z * f (sumZ z) := by
  unfold BAgg
  calc
    ∑ r : I n, (∑ z : ZCoord c n, if sumZ z = r then bcoef t z else 0) * f r
        = ∑ r : I n, ∑ z : ZCoord c n,
            (if sumZ z = r then bcoef t z else 0) * f r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [Finset.sum_mul]
    _ = ∑ z : ZCoord c n, ∑ r : I n,
          (if sumZ z = r then bcoef t z else 0) * f r := by
            rw [Finset.sum_comm]
    _ = ∑ z : ZCoord c n, bcoef t z * f (sumZ z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [Finset.sum_eq_single (sumZ z)]
          · simp
          · intro r hr hne
            by_cases hzr : sumZ z = r
            · exact False.elim (hne hzr.symm)
            · simp [hzr]
          · simp

lemma sum_BAgg_mul_eq {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) (y : YCoord b n) :
    ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y) r * ccoef y r =
      ∑ z : ZCoord c n, bcoef (sumY y) z * ccoef y (sumZ z) := by
  simpa using
    sum_BAgg_apply_eq (c := c) (n := n) bcoef (sumY y) (fun r : I n => ccoef y r)

lemma sum_BAgg_sub_mul_eq {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) (y : YCoord b n) :
    ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y + 1) (r - 1) * ccoef y r =
      ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
  have hreindex :
      ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y + 1) r * ccoef y (r + 1) =
        ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y + 1) (r - 1) * ccoef y r := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun r : I n => BAgg (c := c) (n := n) bcoef (sumY y + 1) (r - 1) * ccoef y r))
  calc
    ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y + 1) (r - 1) * ccoef y r
        = ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y + 1) r * ccoef y (r + 1) := by
            symm
            exact hreindex
    _ = ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
          simpa using
            sum_BAgg_apply_eq (c := c) (n := n) bcoef (sumY y + 1)
              (fun r : I n => ccoef y (r + 1))

lemma qLeftScalar_eq_sum_yz {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qLeftScalar (b := b) (c := c) (n := n) bcoef ccoef =
      ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y) z * ccoef y (sumZ z) := by
  unfold qLeftScalar Cagg
  calc
    ∑ t : I n, ∑ z : ZCoord c n, bcoef t z * (∑ y : YCoord b n,
        if sumY y = t then ccoef y (sumZ z) else 0
      )
        = ∑ t : I n, ∑ z : ZCoord c n, ∑ y : YCoord b n,
            bcoef t z * (if sumY y = t then ccoef y (sumZ z) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              refine Finset.sum_congr rfl ?_
              intro z hz
              rw [Finset.mul_sum]
    _ = ∑ z : ZCoord c n, ∑ t : I n, ∑ y : YCoord b n,
          bcoef t z * (if sumY y = t then ccoef y (sumZ z) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ z : ZCoord c n, ∑ y : YCoord b n, ∑ t : I n,
          bcoef t z * (if sumY y = t then ccoef y (sumZ z) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [Finset.sum_comm]
    _ = ∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ t : I n,
          bcoef t z * (if sumY y = t then ccoef y (sumZ z) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y) z * ccoef y (sumZ z) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          have hsingle :
              ∑ t : I n, bcoef t z * (if sumY y = t then ccoef y (sumZ z) else 0) =
                bcoef (sumY y) z * ccoef y (sumZ z) := by
            rw [Finset.sum_eq_single (sumY y)]
            · simp
            · intro t ht hne
              by_cases hyt : sumY y = t
              · exact False.elim (hne hyt.symm)
              · simp [hyt]
            · simp
          exact hsingle

lemma sumY_eq_sub_one_iff {b n : ℕ} [NeZero n] (y : YCoord b n) (t : I n) :
    sumY y = t - 1 ↔ t = sumY y + 1 := by
  constructor
  · intro h
    have h' := congrArg (fun x : I n => x + 1) h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'.symm
  · intro h
    subst t
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma qRightScalar_eq_sum_yz {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qRightScalar (b := b) (c := c) (n := n) bcoef ccoef =
      ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
  unfold qRightScalar Cagg
  calc
    ∑ t : I n, ∑ z : ZCoord c n, bcoef t z * (∑ y : YCoord b n,
        if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0
      )
        = ∑ t : I n, ∑ z : ZCoord c n, ∑ y : YCoord b n,
            bcoef t z * (if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              refine Finset.sum_congr rfl ?_
              intro z hz
              rw [Finset.mul_sum]
    _ = ∑ z : ZCoord c n, ∑ t : I n, ∑ y : YCoord b n,
          bcoef t z * (if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ z : ZCoord c n, ∑ y : YCoord b n, ∑ t : I n,
          bcoef t z * (if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            rw [Finset.sum_comm]
    _ = ∑ y : YCoord b n, ∑ z : ZCoord c n, ∑ t : I n,
          bcoef t z * (if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          refine Finset.sum_congr rfl ?_
          intro z hz
          have hsingle :
              ∑ t : I n, bcoef t z * (if sumY y = t - 1 then ccoef y (sumZ z + 1) else 0) =
                bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
            rw [Finset.sum_eq_single (sumY y + 1)]
            · simp [sumY_eq_sub_one_iff]
            · intro t ht hne
              by_cases hyt : sumY y = t - 1
              · exact False.elim (hne ((sumY_eq_sub_one_iff (b := b) (n := n) y t).1 hyt))
              · simp [hyt]
            · simp [sumY_eq_sub_one_iff]
          exact hsingle

lemma cPairScalar_TAdjScalarFun_eq_qLeft_add_qRight {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    cPairScalar (b := b) (n := n) (TAdjScalarFun (b := b) (c := c) (n := n) bcoef) ccoef =
      qLeftScalar (b := b) (c := c) (n := n) bcoef ccoef +
        qRightScalar (b := b) (c := c) (n := n) bcoef ccoef := by
  unfold cPairScalar TAdjScalarFun
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  calc
    (∑ y : YCoord b n, ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y) r * ccoef y r) +
        ∑ y : YCoord b n, ∑ r : I n, BAgg (c := c) (n := n) bcoef (sumY y + 1) (r - 1) * ccoef y r
        =
      (∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y) z * ccoef y (sumZ z)) +
        ∑ y : YCoord b n, ∑ z : ZCoord c n, bcoef (sumY y + 1) z * ccoef y (sumZ z + 1) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro y hy
            exact sum_BAgg_mul_eq (b := b) (c := c) (n := n) bcoef ccoef y
          · refine Finset.sum_congr rfl ?_
            intro y hy
            exact sum_BAgg_sub_mul_eq (b := b) (c := c) (n := n) bcoef ccoef y
    _ = qLeftScalar (b := b) (c := c) (n := n) bcoef ccoef +
          qRightScalar (b := b) (c := c) (n := n) bcoef ccoef := by
            rw [qLeftScalar_eq_sum_yz (b := b) (c := c) (n := n) bcoef ccoef,
              qRightScalar_eq_sum_yz (b := b) (c := c) (n := n) bcoef ccoef]

lemma qScalar_eq_cPair_TAdjScalarFun {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qScalar (b := b) (c := c) (n := n) bcoef ccoef =
      cPairScalar (b := b) (n := n) (TAdjScalarFun (b := b) (c := c) (n := n) bcoef) ccoef := by
  calc
    qScalar (b := b) (c := c) (n := n) bcoef ccoef =
        qLeftScalar (b := b) (c := c) (n := n) bcoef ccoef +
          qRightScalar (b := b) (c := c) (n := n) bcoef ccoef := by
            rfl
    _ =
        cPairScalar (b := b) (n := n) (TAdjScalarFun (b := b) (c := c) (n := n) bcoef) ccoef := by
          symm
          exact cPairScalar_TAdjScalarFun_eq_qLeft_add_qRight
            (b := b) (c := c) (n := n) bcoef ccoef

lemma qScalar_eq_cPair_TAdjScalar {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    qScalar (b := b) (c := c) (n := n) bcoef ccoef =
      cPairScalar (b := b) (n := n) ((TAdjScalar (b := b) (c := c) (n := n)) bcoef) ccoef := by
  simpa [TAdjScalar] using
    qScalar_eq_cPair_TAdjScalarFun (b := b) (c := c) (n := n) bcoef ccoef

noncomputable def yCoordEquivI_of_b_eq_one {n : ℕ} [NeZero n] : YCoord 1 n ≃ I n where
  toFun := sumY
  invFun := yOfSum (b := 1) (n := n) (by omega)
  left_inv := fun y => (y_eq_yOfSum_of_b_eq_one (n := n) y).symm
  right_inv := sumY_yOfSum (b := 1) (n := n) (by omega)

noncomputable def zCoordEquivI_of_c_eq_one {n : ℕ} [NeZero n] : ZCoord 1 n ≃ I n where
  toFun := sumZ
  invFun := zOfSum (c := 1) (n := n) (by omega)
  left_inv := fun z => (z_eq_zOfSum_of_c_eq_one (n := n) z).symm
  right_inv := sumZ_zOfSum (c := 1) (n := n) (by omega)

lemma scalarYAgg_eq_of_b_eq_one {n : ℕ} [NeZero n] (v : YCoord 1 n → F) (t : I n) :
    scalarYAgg (b := 1) (n := n) v t = v ((yCoordEquivI_of_b_eq_one (n := n)).symm t) := by
  have hs := Cagg_scalarCConst (b := 1) (n := n) v t (0 : I n)
  rw [Cagg_eq_of_b_eq_one] at hs
  simpa [scalarCConst, yCoordEquivI_of_b_eq_one] using hs.symm

lemma Cagg_scalarCPref_eq_of_b_eq_one {n : ℕ} [NeZero n] (h : HRaw n) (t s : I n) :
    Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) h) t s = prefixR h t s := by
  rw [Cagg_eq_of_b_eq_one]
  simp [scalarCPref, buildScalarC, yCoordEquivI_of_b_eq_one]

lemma BAgg_scalarBPref_eq_of_c_eq_one {n : ℕ} [NeZero n] (h : HRaw n) (t s : I n) :
    BAgg (c := 1) (n := n) (scalarBPref (c := 1) (n := n) h) t s = prefixT h t s := by
  rw [BAgg_eq_of_c_eq_one]
  simp [scalarBPref, buildScalarB, zCoordEquivI_of_c_eq_one]

lemma qScalar_scalarBConst_scalarCPref_eq_zero_of_eq_one_eq_one {n : ℕ} [NeZero n]
    {h : HRaw n} (hh : h ∈ HAdmissible (n := n)) (u : ZCoord 1 n → F) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBConst (c := 1) u)
      (scalarCPref (b := 1) (n := n) h) = 0 := by
  let ez : I n ≃ ZCoord 1 n := (zCoordEquivI_of_c_eq_one (n := n)).symm
  have hleft :
      qLeftScalar (b := 1) (c := 1) (n := n)
          (scalarBConst (c := 1) u)
          (scalarCPref (b := 1) (n := n) h) =
        ∑ t : I n, ∑ s : I n, u (ez s) * prefixR h t s := by
    unfold qLeftScalar scalarBConst
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          u z * Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) h) t (sumZ z)
          =
        ∑ s : I n,
          u (ez s) *
            Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) h) t (sumZ (ez s)) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    u z * Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) h) t (sumZ z))).symm)
      _ = ∑ s : I n, u (ez s) * prefixR h t s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [hsum, Cagg_scalarCPref_eq_of_b_eq_one]
  have hright_raw :
      qRightScalar (b := 1) (c := 1) (n := n)
          (scalarBConst (c := 1) u)
          (scalarCPref (b := 1) (n := n) h) =
        ∑ t : I n, ∑ s : I n, u (ez s) * prefixR h (t - 1) (s + 1) := by
    unfold qRightScalar scalarBConst
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          u z * Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) h) (t - 1) (sumZ z + 1)
          =
        ∑ s : I n,
          u (ez s) *
            Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) h) (t - 1) (sumZ (ez s) + 1) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    u z *
                      Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) h) (t - 1) (sumZ z + 1))).symm)
      _ = ∑ s : I n, u (ez s) * prefixR h (t - 1) (s + 1) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [hsum, Cagg_scalarCPref_eq_of_b_eq_one]
  have hright :
      qRightScalar (b := 1) (c := 1) (n := n)
          (scalarBConst (c := 1) u)
          (scalarCPref (b := 1) (n := n) h) =
        ∑ t : I n, ∑ s : I n, u (ez s) * prefixR h t (s + 1) := by
    rw [hright_raw]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun t : I n => ∑ s : I n, u (ez s) * prefixR h (t - 1) (s + 1))).symm
  rw [qScalar, hleft, hright]
  calc
    (∑ t : I n, ∑ s : I n, u (ez s) * prefixR h t s) +
        ∑ t : I n, ∑ s : I n, u (ez s) * prefixR h t (s + 1)
        =
      (∑ s : I n, ∑ t : I n, u (ez s) * prefixR h t s) +
        ∑ t : I n, ∑ s : I n, u (ez s) * prefixR h t (s + 1) := by
          rw [Finset.sum_comm]
    _ =
      (∑ s : I n, ∑ t : I n, u (ez s) * prefixR h t s) +
        ∑ s : I n, ∑ t : I n, u (ez s) * prefixR h t (s + 1) := by
          congr 1
          rw [Finset.sum_comm]
    _ =
      ∑ s : I n,
        ((∑ t : I n, u (ez s) * prefixR h t s) +
          ∑ t : I n, u (ez s) * prefixR h t (s + 1)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ s : I n, u (ez s) *
        (∑ t : I n, (prefixR h t s + prefixR h t (s + 1))) := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
          congr 1
          rw [Finset.sum_add_distrib]
    _ = ∑ s : I n, u (ez s) * ∑ t : I n, h t s := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          congr 1
          refine Finset.sum_congr rfl ?_
          intro t ht
          exact prefixR_pair_eq_of_mem_HAdmissible (n := n) hh t s
    _ = ∑ s : I n, u (ez s) * colSum h s := by
          refine Finset.sum_congr rfl ?_
          intro s hs
          rfl
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro s hs
          simp [colSum_eq_zero_of_mem_HAdmissible (n := n) hh s]

lemma qScalar_scalarBPref_scalarCConst_eq_zero_of_eq_one_eq_one {n : ℕ} [NeZero n]
    {h : HRaw n} (hh : h ∈ HAdmissible (n := n)) (v : YCoord 1 n → F) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) h)
      (scalarCConst (b := 1) v) = 0 := by
  let ez : I n ≃ ZCoord 1 n := (zCoordEquivI_of_c_eq_one (n := n)).symm
  have hleft :
      qLeftScalar (b := 1) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCConst (b := 1) v) =
        ∑ t : I n, ∑ s : I n, prefixT h t s * scalarYAgg (b := 1) (n := n) v t := by
    unfold qLeftScalar scalarBPref
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          buildScalarB h 0 t z * Cagg (b := 1) (n := n) (scalarCConst (b := 1) v) t (sumZ z)
          =
        ∑ s : I n,
          buildScalarB h 0 t (ez s) *
            Cagg (b := 1) (n := n) (scalarCConst (b := 1) v) t (sumZ (ez s)) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    buildScalarB h 0 t z *
                      Cagg (b := 1) (n := n) (scalarCConst (b := 1) v) t (sumZ z))).symm)
      _ = ∑ s : I n, prefixT h t s * scalarYAgg (b := 1) (n := n) v t := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [buildScalarB, hsum, Cagg_scalarCConst]
            simp
  have hright_raw :
      qRightScalar (b := 1) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCConst (b := 1) v) =
        ∑ t : I n, ∑ s : I n, prefixT h t s * scalarYAgg (b := 1) (n := n) v (t - 1) := by
    unfold qRightScalar scalarBPref
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          buildScalarB h 0 t z *
            Cagg (b := 1) (n := n) (scalarCConst (b := 1) v) (t - 1) (sumZ z + 1)
          =
        ∑ s : I n,
          buildScalarB h 0 t (ez s) *
            Cagg (b := 1) (n := n) (scalarCConst (b := 1) v) (t - 1) (sumZ (ez s) + 1) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    buildScalarB h 0 t z *
                      Cagg (b := 1) (n := n) (scalarCConst (b := 1) v) (t - 1) (sumZ z + 1))).symm)
      _ = ∑ s : I n, prefixT h t s * scalarYAgg (b := 1) (n := n) v (t - 1) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [buildScalarB, hsum, Cagg_scalarCConst]
            simp
  have hright :
      qRightScalar (b := 1) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCConst (b := 1) v) =
        ∑ t : I n, ∑ s : I n, prefixT h (t + 1) s * scalarYAgg (b := 1) (n := n) v t := by
    rw [hright_raw]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun t : I n => ∑ s : I n, prefixT h t s * scalarYAgg (b := 1) (n := n) v (t - 1))).symm
  rw [qScalar, hleft, hright]
  calc
    (∑ t : I n, ∑ s : I n, prefixT h t s * scalarYAgg (b := 1) (n := n) v t) +
        ∑ t : I n, ∑ s : I n, prefixT h (t + 1) s * scalarYAgg (b := 1) (n := n) v t
        =
      ∑ t : I n,
        ((∑ s : I n, prefixT h t s * scalarYAgg (b := 1) (n := n) v t) +
          ∑ s : I n, prefixT h (t + 1) s * scalarYAgg (b := 1) (n := n) v t) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ t : I n,
        (∑ s : I n, (prefixT h t s + prefixT h (t + 1) s)) *
          scalarYAgg (b := 1) (n := n) v t := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
          congr 1
          rw [Finset.sum_add_distrib]
    _ = ∑ t : I n, scalarYAgg (b := 1) (n := n) v t *
        (∑ s : I n, (prefixT h t s + prefixT h (t + 1) s)) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [mul_comm]
    _ = ∑ t : I n, scalarYAgg (b := 1) (n := n) v t * ∑ s : I n, h t s := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact prefixT_pair_eq_of_mem_HAdmissible (n := n) hh t s
    _ = ∑ t : I n, scalarYAgg (b := 1) (n := n) v t * rowSum h t := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rfl
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro t ht
          simp [rowSum_eq_zero_of_mem_HAdmissible (n := n) hh t]

lemma qScalar_build_eq_prefpref_of_eq_one_eq_one {n : ℕ} [NeZero n]
    {h : HRaw n} (hh : h ∈ HAdmissible (n := n))
    (u : ZCoord 1 n → F) (v : YCoord 1 n → F) :
    qScalar (b := 1) (c := 1) (n := n)
      (buildScalarB h u) (buildScalarC h v) =
      qScalar (b := 1) (c := 1) (n := n)
        (scalarBPref (c := 1) (n := n) h)
        (scalarCPref (b := 1) (n := n) h) := by
  rw [buildScalarB_eq_scalarBConst_add_scalarBPref, buildScalarC_eq_scalarCConst_add_scalarCPref]
  rw [qScalar_add_left, qScalar_add_right, qScalar_add_right]
  rw [qScalar_scalarBConst_scalarCConst_eq_zero (b := 1) (c := 1) (n := n)]
  rw [qScalar_scalarBConst_scalarCPref_eq_zero_of_eq_one_eq_one (n := n) hh u]
  rw [qScalar_scalarBPref_scalarCConst_eq_zero_of_eq_one_eq_one (n := n) hh v]
  simp [add_assoc, add_left_comm, add_comm, F_add_self]

lemma qScalar_scalarBPref_scalarCPref_formula_mixed_of_eq_one_eq_one {n : ℕ} [NeZero n]
    {h k : HRaw n} (hh : h ∈ HAdmissible (n := n)) (hk : k ∈ HAdmissible (n := n)) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) h)
      (scalarCPref (b := 1) (n := n) k) =
      (∑ t : I n, ∑ s : I n, h t s * prefixR k t s) +
        (∑ t : I n, ∑ s : I n, prefixT h t s * k t s) +
        ∑ t : I n, ∑ s : I n, h t s * k t s := by
  let ez : I n ≃ ZCoord 1 n := (zCoordEquivI_of_c_eq_one (n := n)).symm
  have hleft :
      qLeftScalar (b := 1) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCPref (b := 1) (n := n) k) =
        ∑ t : I n, ∑ s : I n, prefixT h t s * prefixR k t s := by
    unfold qLeftScalar scalarBPref
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          buildScalarB h 0 t z *
            Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) k) t (sumZ z)
          =
        ∑ s : I n,
          buildScalarB h 0 t (ez s) *
            Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) k) t (sumZ (ez s)) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    buildScalarB h 0 t z *
                      Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) k) t (sumZ z))).symm)
      _ = ∑ s : I n, prefixT h t s * prefixR k t s := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [buildScalarB, hsum, Cagg_scalarCPref_eq_of_b_eq_one]
            simp
  have hright_raw :
      qRightScalar (b := 1) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCPref (b := 1) (n := n) k) =
        ∑ t : I n, ∑ s : I n, prefixT h t s * prefixR k (t - 1) (s + 1) := by
    unfold qRightScalar scalarBPref
    refine Finset.sum_congr rfl ?_
    intro t ht
    calc
      ∑ z : ZCoord 1 n,
          buildScalarB h 0 t z *
            Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) k) (t - 1) (sumZ z + 1)
          =
        ∑ s : I n,
          buildScalarB h 0 t (ez s) *
            Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) k) (t - 1) (sumZ (ez s) + 1) := by
              simpa [ez] using
                ((Equiv.sum_comp ez
                  (fun z : ZCoord 1 n =>
                    buildScalarB h 0 t z *
                      Cagg (b := 1) (n := n) (scalarCPref (b := 1) (n := n) k) (t - 1) (sumZ z + 1))).symm)
      _ = ∑ s : I n, prefixT h t s * prefixR k (t - 1) (s + 1) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            have hsum : sumZ (ez s) = s := by
              exact (zCoordEquivI_of_c_eq_one (n := n)).apply_symm_apply s
            rw [buildScalarB, hsum, Cagg_scalarCPref_eq_of_b_eq_one]
            simp
  have hright :
      qRightScalar (b := 1) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) h)
          (scalarCPref (b := 1) (n := n) k) =
        ∑ t : I n, ∑ s : I n, prefixT h (t + 1) s * prefixR k t (s + 1) := by
    rw [hright_raw]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (sum_reindex_addLeft (n := n) (a := (1 : I n))
        (f := fun t : I n => ∑ s : I n, prefixT h t s * prefixR k (t - 1) (s + 1))).symm
  have hterm :
      ∀ t s : I n,
        prefixT h t s * prefixR k t s +
            prefixT h (t + 1) s * prefixR k t (s + 1) =
          h t s * prefixR k t s + prefixT h t s * k t s + h t s * k t s := by
    intro t s
    have hpr : prefixR k t (s + 1) = prefixR k t s + k t s := by
      apply add_left_cancel (a := prefixR k t s)
      simpa [add_assoc, add_left_comm, add_comm, F_add_self] using
        prefixR_pair_eq_of_mem_HAdmissible (n := n) hk t s
    have hpt : prefixT h (t + 1) s = prefixT h t s + h t s := by
      apply add_left_cancel (a := prefixT h t s)
      simpa [add_assoc, add_left_comm, add_comm, F_add_self] using
        prefixT_pair_eq_of_mem_HAdmissible (n := n) hh t s
    simp [hpr, hpt, mul_add, add_mul, add_assoc, add_left_comm, add_comm, F_add_self]
  rw [qScalar, hleft, hright]
  calc
    (∑ t : I n, ∑ s : I n, prefixT h t s * prefixR k t s) +
        ∑ t : I n, ∑ s : I n, prefixT h (t + 1) s * prefixR k t (s + 1)
        =
      ∑ t : I n,
        ((∑ s : I n, prefixT h t s * prefixR k t s) +
          ∑ s : I n, prefixT h (t + 1) s * prefixR k t (s + 1)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ t : I n, ∑ s : I n,
        (prefixT h t s * prefixR k t s +
          prefixT h (t + 1) s * prefixR k t (s + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [← Finset.sum_add_distrib]
    _ = ∑ t : I n, ∑ s : I n,
        (h t s * prefixR k t s + prefixT h t s * k t s + h t s * k t s) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          refine Finset.sum_congr rfl ?_
          intro s hs
          exact hterm t s
    _ =
      (∑ t : I n, ∑ s : I n, h t s * prefixR k t s) +
        (∑ t : I n, ∑ s : I n, prefixT h t s * k t s) +
        ∑ t : I n, ∑ s : I n, h t s * k t s := by
          calc
            ∑ t : I n, ∑ s : I n, (h t s * prefixR k t s + prefixT h t s * k t s + h t s * k t s)
                =
              ∑ t : I n,
                ((∑ s : I n, h t s * prefixR k t s) +
                  ∑ s : I n, prefixT h t s * k t s +
                  ∑ s : I n, h t s * k t s) := by
                    refine Finset.sum_congr rfl ?_
                    intro t ht
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            _ =
              (∑ t : I n, ∑ s : I n, h t s * prefixR k t s) +
                (∑ t : I n, ∑ s : I n, prefixT h t s * k t s) +
                ∑ t : I n, ∑ s : I n, h t s * k t s := by
                    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

lemma qScalar_scalarBPref_scalarCPref_rect_formula_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (i j : OddRectIndex n) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) (oddRectVec (n := n) i).1)
      (scalarCPref (b := 1) (n := n) (oddRectVec (n := n) j).1) =
      ((if i.2.1.val ≤ j.2.1.val then 1 else 0) +
        (if i.1.1 = j.1.1 then (if i.2.1.val ≤ j.2.1.val then 1 else 0) else 0)) +
      (((if j.1.1.val ≤ i.1.1.val then 1 else 0) +
        (if i.2.1 = j.2.1 then (if j.1.1.val ≤ i.1.1.val then 1 else 0) else 0)) +
        (1 + (if i.2.1 = j.2.1 then 1 else 0) + (if i.1.1 = j.1.1 then 1 else 0) +
          (if i.1.1 = j.1.1 ∧ i.2.1 = j.2.1 then 1 else 0))) := by
  rcases i with ⟨⟨a, ha⟩, ⟨b0, hb0⟩⟩
  rcases j with ⟨⟨c0, hc0⟩, ⟨d, hd⟩⟩
  have hha : rect a b0 ∈ HAdmissible (n := n) := rect_mem_HAdmissible (n := n) a b0
  have hhc : rect c0 d ∈ HAdmissible (n := n) := rect_mem_HAdmissible (n := n) c0 d
  simp_rw [oddRectVec_val_eq_rect]
  rw [qScalar_scalarBPref_scalarCPref_formula_mixed_of_eq_one_eq_one
    (n := n) hha hhc]
  rw [sum_rect_mul_prefixR_rect_eq (a := a) (b := b0) (c := c0) (d := d) ha hb0 hc0 hd]
  rw [sum_prefixT_rect_mul_rect_eq (a := a) (b := b0) (c := c0) (d := d) ha hb0 hc0 hd]
  rw [sum_rect_mul_rect_eq_indicator (a := a) (b := b0) (c := c0) (d := d) ha hb0 hc0 hd]
  simpa [add_assoc, add_left_comm, add_comm]

lemma qScalar_scalarBPref_scalarCPref_rect_symm_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (i j : OddRectIndex n) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) (oddRectVec (n := n) i).1)
      (scalarCPref (b := 1) (n := n) (oddRectVec (n := n) j).1) =
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) (oddRectVec (n := n) j).1)
      (scalarCPref (b := 1) (n := n) (oddRectVec (n := n) i).1) := by
  rw [qScalar_scalarBPref_scalarCPref_rect_formula_of_eq_one_eq_one (n := n) i j,
    qScalar_scalarBPref_scalarCPref_rect_formula_of_eq_one_eq_one (n := n) j i]
  rcases i with ⟨⟨a, ha⟩, ⟨b0, hb0⟩⟩
  rcases j with ⟨⟨c0, hc0⟩, ⟨d, hd⟩⟩
  by_cases hac : a = c0
  · subst hac
    by_cases hbd : b0 = d
    · subst hbd
      simp [F_add_self, add_assoc, add_left_comm, add_comm]
    · by_cases hbdle : b0.val ≤ d.val
      · have hbdv : b0.val ≠ d.val := by
          intro hv
          apply hbd
          exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdble : ¬ d.val ≤ b0.val := by omega
        simp [hbd, hdb, hbdle, hdble, F_add_self, add_assoc, add_left_comm, add_comm]
      · have hbdv : b0.val ≠ d.val := by
          intro hv
          apply hbd
          exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdble : d.val ≤ b0.val := by omega
        simp [hbd, hdb, hbdle, hdble, F_add_self, add_assoc, add_left_comm, add_comm]
  · by_cases hbd : b0 = d
    · subst hbd
      by_cases hcale : c0.val ≤ a.val
      · have hacv : a.val ≠ c0.val := by
          intro hv
          apply hac
          exact ZMod.val_injective _ hv
        have hca : ¬ c0 = a := by simpa [eq_comm] using hac
        have hacle : ¬ a.val ≤ c0.val := by omega
        simp [hac, hca, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
      · have hacv : a.val ≠ c0.val := by
          intro hv
          apply hac
          exact ZMod.val_injective _ hv
        have hca : ¬ c0 = a := by simpa [eq_comm] using hac
        have hacle : a.val ≤ c0.val := by omega
        simp [hac, hca, hcale, hacle, F_add_self, add_assoc, add_left_comm, add_comm]
    · by_cases hbdle : b0.val ≤ d.val
      · have hbdv : b0.val ≠ d.val := by
          intro hv
          apply hbd
          exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdble : ¬ d.val ≤ b0.val := by omega
        by_cases hcale : c0.val ≤ a.val
        · have hacv : a.val ≠ c0.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : ¬ a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]
        · have hacv : a.val ≠ c0.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]
      · have hbdv : b0.val ≠ d.val := by
          intro hv
          apply hbd
          exact ZMod.val_injective _ hv
        have hdb : ¬ d = b0 := by simpa [eq_comm] using hbd
        have hdble : d.val ≤ b0.val := by omega
        by_cases hcale : c0.val ≤ a.val
        · have hacv : a.val ≠ c0.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : ¬ a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]
        · have hacv : a.val ≠ c0.val := by
            intro hv
            apply hac
            exact ZMod.val_injective _ hv
          have hca : ¬ c0 = a := by simpa [eq_comm] using hac
          have hacle : a.val ≤ c0.val := by omega
          simp [hac, hca, hbd, hdb, hbdle, hdble, hcale, hacle,
            F_add_self, add_assoc, add_left_comm, add_comm]

lemma qScalar_scalarBPref_scalarCPref_rect_eq_zero_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (i : OddRectIndex n) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) (oddRectVec (n := n) i).1)
      (scalarCPref (b := 1) (n := n) (oddRectVec (n := n) i).1) = 0 := by
  rw [qScalar_scalarBPref_scalarCPref_rect_formula_of_eq_one_eq_one (n := n) i i]
  rcases i with ⟨⟨a, ha⟩, ⟨b0, hb0⟩⟩
  simp [F_add_self, add_assoc, add_left_comm, add_comm]

lemma qScalar_scalarBPref_scalarCPref_symm_oddRectVec_right_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (h : HAdmissible (n := n)) (i : OddRectIndex n) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) h.1)
      (scalarCPref (b := 1) (n := n) (oddRectVec (n := n) i).1) =
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) (oddRectVec (n := n) i).1)
      (scalarCPref (b := 1) (n := n) h.1) := by
  rw [qScalar_scalarBPref_scalarCPref_eq_sum_oddRectPair (b := 1) (c := 1) (n := n) h
    (oddRectVec (n := n) i)]
  rw [qScalar_scalarBPref_scalarCPref_eq_sum_oddRectPair (b := 1) (c := 1) (n := n)
    (oddRectVec (n := n) i) h]
  simp only [oddRectSupport_oddRectVec, Finset.sum_singleton]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact qScalar_scalarBPref_scalarCPref_rect_symm_of_eq_one_eq_one (n := n) j i

lemma qScalar_scalarBPref_scalarCPref_add_oddRectVec_eq_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (h : HAdmissible (n := n)) (i : OddRectIndex n) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) (h + oddRectVec (n := n) i).1)
      (scalarCPref (b := 1) (n := n) (h + oddRectVec (n := n) i).1) =
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) h.1)
      (scalarCPref (b := 1) (n := n) h.1) := by
  have hadd :
      qScalar (b := 1) (c := 1) (n := n)
          (scalarBPref (c := 1) (n := n) (h + oddRectVec (n := n) i).1)
          (scalarCPref (b := 1) (n := n) (h + oddRectVec (n := n) i).1) =
        qScalar (b := 1) (c := 1) (n := n)
            (scalarBPref (c := 1) (n := n) h.1)
            (scalarCPref (b := 1) (n := n) h.1) +
          qScalar (b := 1) (c := 1) (n := n)
            (scalarBPref (c := 1) (n := n) h.1)
            (scalarCPref (b := 1) (n := n) (oddRectVec (n := n) i).1) +
          qScalar (b := 1) (c := 1) (n := n)
            (scalarBPref (c := 1) (n := n) (oddRectVec (n := n) i).1)
            (scalarCPref (b := 1) (n := n) h.1) +
          qScalar (b := 1) (c := 1) (n := n)
            (scalarBPref (c := 1) (n := n) (oddRectVec (n := n) i).1)
            (scalarCPref (b := 1) (n := n) (oddRectVec (n := n) i).1) := by
    change
      qScalar (b := 1) (c := 1) (n := n)
        (scalarBPref (c := 1) (n := n) (h.1 + (oddRectVec (n := n) i).1))
        (scalarCPref (b := 1) (n := n) (h.1 + (oddRectVec (n := n) i).1)) = _
    rw [scalarBPref_add, scalarCPref_add, qScalar_add_left, qScalar_add_right, qScalar_add_right]
    ac_rfl
  rw [hadd,
    qScalar_scalarBPref_scalarCPref_symm_oddRectVec_right_of_eq_one_eq_one (n := n) h i,
    qScalar_scalarBPref_scalarCPref_rect_eq_zero_of_eq_one_eq_one (n := n) i]
  simp [F_add_self, add_assoc, add_left_comm, add_comm]

lemma qScalar_scalarBPref_scalarCPref_sum_oddRectVec_eq_zero_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (S : Finset (OddRectIndex n)) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) (Finset.sum S (fun i => (oddRectVec (n := n) i).1)))
      (scalarCPref (b := 1) (n := n) (Finset.sum S (fun i => (oddRectVec (n := n) i).1))) = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [qScalar, qLeftScalar, qRightScalar, scalarBPref, scalarCPref,
        buildScalarB, buildScalarC, prefixT, prefixR]
  | @insert i S hi ih =>
      have hstep :
          qScalar (b := 1) (c := 1) (n := n)
              (scalarBPref (c := 1) (n := n)
                (Finset.sum (insert i S) (fun j => (oddRectVec (n := n) j).1)))
              (scalarCPref (b := 1) (n := n)
                (Finset.sum (insert i S) (fun j => (oddRectVec (n := n) j).1))) =
            qScalar (b := 1) (c := 1) (n := n)
              (scalarBPref (c := 1) (n := n) (Finset.sum S (fun j => (oddRectVec (n := n) j).1)))
              (scalarCPref (b := 1) (n := n) (Finset.sum S (fun j => (oddRectVec (n := n) j).1))) := by
        simpa [Finset.sum_insert, hi, add_assoc, add_left_comm, add_comm] using
          qScalar_scalarBPref_scalarCPref_add_oddRectVec_eq_of_eq_one_eq_one (n := n)
            (h := Finset.sum S (fun j => oddRectVec (n := n) j)) (i := i)
      rw [hstep]
      exact ih

theorem qScalar_scalarBPref_scalarCPref_eq_zero_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (h : HAdmissible (n := n)) :
    qScalar (b := 1) (c := 1) (n := n)
      (scalarBPref (c := 1) (n := n) h.1)
      (scalarCPref (b := 1) (n := n) h.1) = 0 := by
  let S : Finset (OddRectIndex n) := oddRectSupport (n := n) h
  have hs :
      Finset.sum S (fun i => (oddRectVec (n := n) i).1) = h.1 := by
    simpa [S] using congrArg Subtype.val (oddRect_sum_support (n := n) h)
  have hzero :
      qScalar (b := 1) (c := 1) (n := n)
        (scalarBPref (c := 1) (n := n) (Finset.sum S (fun i => (oddRectVec (n := n) i).1)))
        (scalarCPref (b := 1) (n := n) (Finset.sum S (fun i => (oddRectVec (n := n) i).1))) = 0 := by
    simpa [S] using
      qScalar_scalarBPref_scalarCPref_sum_oddRectVec_eq_zero_of_eq_one_eq_one (n := n) S
  rw [← hs]
  exact hzero

theorem qScalar_eq_zero_on_visible_of_eq_one_eq_one {n : ℕ} [NeZero n]
    (bc : ScalarVisibleCompat 1 1 n) :
    qScalar (b := 1) (c := 1) (n := n) bc.bcoef bc.ccoef = 0 := by
  have hh :
      visibleHData (b := 1) (c := 1) (n := n) (by omega) bc ∈ HAdmissible (n := n) := by
    exact visibleHData_mem_HAdmissible (b := 1) (c := 1) (n := n) (by omega) (by omega) bc
  rw [← buildScalarB_visibleData_eq (b := 1) (c := 1) (n := n) (by omega) (by omega) bc]
  rw [← buildScalarC_visibleData_eq (b := 1) (c := 1) (n := n) (by omega) bc]
  rw [qScalar_build_eq_prefpref_of_eq_one_eq_one (n := n) hh (visibleUData bc) (visibleVData bc)]
  exact qScalar_scalarBPref_scalarCPref_eq_zero_of_eq_one_eq_one (n := n)
    ⟨visibleHData (b := 1) (c := 1) (n := n) (by omega) bc, hh⟩

abbrev ScalarCIndex (b n : ℕ) := YCoord b n × I n

noncomputable def toggleAtScalarCCoef {b n : ℕ} [NeZero n]
    (u0 : ScalarCIndex b n) (ccoef : ScalarCCoef b n) : ScalarCCoef b n :=
  fun y r => ccoef y r + if (y, r) = u0 then 1 else 0

noncomputable def toggleEquivScalarCCoef {b n : ℕ} [NeZero n]
    (u0 : ScalarCIndex b n) : ScalarCCoef b n ≃ ScalarCCoef b n where
  toFun := toggleAtScalarCCoef u0
  invFun := toggleAtScalarCCoef u0
  left_inv := by
    intro ccoef
    funext y r
    by_cases h : (y, r) = u0
    · subst h
      have h11 : (1 : F) + 1 = 0 := by decide
      simp [toggleAtScalarCCoef, add_assoc, h11]
    · simp [toggleAtScalarCCoef, h]
  right_inv := by
    intro ccoef
    funext y r
    by_cases h : (y, r) = u0
    · subst h
      have h11 : (1 : F) + 1 = 0 := by decide
      simp [toggleAtScalarCCoef, add_assoc, h11]
    · simp [toggleAtScalarCCoef, h]

lemma toggleAtScalarCCoef_apply {b n : ℕ} [NeZero n]
    (u0 : ScalarCIndex b n) (ccoef : ScalarCCoef b n) (y : YCoord b n) (r : I n) :
    toggleAtScalarCCoef u0 ccoef y r = ccoef y r + if (y, r) = u0 then 1 else 0 := by
  rfl

lemma cPairScalar_toggleAtScalarCCoef {b n : ℕ} [NeZero n]
    (u0 : ScalarCIndex b n) (ccoef m : ScalarCCoef b n) (hm : m u0.1 u0.2 = 1) :
    cPairScalar (b := b) (n := n) m (toggleAtScalarCCoef u0 ccoef) =
      cPairScalar (b := b) (n := n) m ccoef + 1 := by
  rcases u0 with ⟨y0, r0⟩
  unfold cPairScalar
  simp_rw [toggleAtScalarCCoef_apply, mul_add, Finset.sum_add_distrib]
  have hs :
      ∑ y : YCoord b n, ∑ r : I n, m y r * (if (y, r) = (y0, r0) then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single y0]
    · rw [Finset.sum_eq_single r0]
      · simpa using hm
      · intro r hr hne
        simp [hne]
      · simp
    · intro y hy hne
      simp [hne]
    · simp
  rw [hs]

lemma sum_bitSign_cPairScalar {b n : ℕ} [NeZero n] (m : ScalarCCoef b n) :
    ∑ ccoef : ScalarCCoef b n, bitSign (cPairScalar (b := b) (n := n) m ccoef) =
      if m = 0 then Fintype.card (ScalarCCoef b n) else 0 := by
  classical
  by_cases hm : m = 0
  · simp [hm, cPairScalar, No13Migration.bitSign_zero]
  · have hex : ∃ u0 : ScalarCIndex b n, m u0.1 u0.2 ≠ 0 := by
      by_contra h
      apply hm
      funext y r
      by_cases hyr : m y r = 0
      · exact hyr
      · exact False.elim (h ⟨(y, r), hyr⟩)
    rcases hex with ⟨u0, hu0⟩
    have hm1 : m u0.1 u0.2 = 1 := F_ne_zero_eq_one _ hu0
    let S : ℤ := ∑ ccoef : ScalarCCoef b n, bitSign (cPairScalar (b := b) (n := n) m ccoef)
    have htoggle :
        S = ∑ ccoef : ScalarCCoef b n,
          bitSign (cPairScalar (b := b) (n := n) m (toggleAtScalarCCoef u0 ccoef)) := by
      simpa [S] using
        (((toggleEquivScalarCCoef (b := b) (n := n) u0).symm.sum_comp
          (fun ccoef : ScalarCCoef b n =>
            bitSign (cPairScalar (b := b) (n := n) m ccoef))).symm)
    have hneg :
        ∑ ccoef : ScalarCCoef b n,
          bitSign (cPairScalar (b := b) (n := n) m (toggleAtScalarCCoef u0 ccoef)) = -S := by
      calc
        ∑ ccoef : ScalarCCoef b n,
            bitSign (cPairScalar (b := b) (n := n) m (toggleAtScalarCCoef u0 ccoef))
            = ∑ ccoef : ScalarCCoef b n,
                -bitSign (cPairScalar (b := b) (n := n) m ccoef) := by
                  refine Finset.sum_congr rfl ?_
                  intro ccoef hccoef
                  rw [cPairScalar_toggleAtScalarCCoef (b := b) (n := n) u0 ccoef m hm1]
                  simpa using No13Migration.bitSign_add_one
                    (cPairScalar (b := b) (n := n) m ccoef)
        _ = -S := by
              simp [S]
    have hs : S = -S := by
      calc
        S = ∑ ccoef : ScalarCCoef b n,
            bitSign (cPairScalar (b := b) (n := n) m (toggleAtScalarCCoef u0 ccoef)) := htoggle
        _ = -S := hneg
    have hzero : S = 0 := by
      linarith
    simp [S, hm, hzero]

lemma sum_bitSign_qScalar_right {b c n : ℕ} [NeZero n] (bcoef : ScalarBCoef c n) :
    ∑ ccoef : ScalarCCoef b n, bitSign (qScalar (b := b) (c := c) (n := n) bcoef ccoef) =
      if (TAdjScalar (b := b) (c := c) (n := n)) bcoef = 0 then
        Fintype.card (ScalarCCoef b n) else 0 := by
  simpa [qScalar_eq_cPair_TAdjScalar] using
    sum_bitSign_cPairScalar (b := b) (n := n)
      (m := (TAdjScalar (b := b) (c := c) (n := n)) bcoef)

lemma card_scalarCCoef {b n : ℕ} [NeZero n] :
    Fintype.card (ScalarCCoef b n) = 2 ^ (n ^ (b + 1)) := by
  rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F)]
  simp [F, finrank_scalarCCoef (b := b) (n := n)]

lemma sum_evenVisible_weight_eq_indicator {b c n : ℕ} [NeZero n]
    (bcoef : ScalarBCoef c n) (ccoef : ScalarCCoef b n) :
    ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
      bitSign
        (qScalar (b := b) (c := c) (n := n) bcoef c₂ +
          qScalar (b := b) (c := c) (n := n) b₂ ccoef) =
      (((if (TAdjScalar (b := b) (c := c) (n := n)) bcoef = 0 then
          Fintype.card (ScalarCCoef b n) else 0 : ℕ) : ℤ) *
        ((if (TScalar (b := b) (c := c) (n := n)) ccoef = 0 then
          Fintype.card (ScalarBCoef c n) else 0 : ℕ) : ℤ)) := by
  calc
    ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
        bitSign
          (qScalar (b := b) (c := c) (n := n) bcoef c₂ +
            qScalar (b := b) (c := c) (n := n) b₂ ccoef)
      =
        ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
          bitSign (qScalar (b := b) (c := c) (n := n) bcoef c₂) *
            bitSign (qScalar (b := b) (c := c) (n := n) b₂ ccoef) := by
              refine Finset.sum_congr rfl ?_
              intro c₂ hc₂
              refine Finset.sum_congr rfl ?_
              intro b₂ hb₂
              simpa using
                No13Migration.bitSign_add
                  (qScalar (b := b) (c := c) (n := n) bcoef c₂)
                  (qScalar (b := b) (c := c) (n := n) b₂ ccoef)
    _ =
        ∑ c₂ : ScalarCCoef b n,
          bitSign (qScalar (b := b) (c := c) (n := n) bcoef c₂) *
            ∑ b₂ : ScalarBCoef c n,
              bitSign (qScalar (b := b) (c := c) (n := n) b₂ ccoef) := by
                refine Finset.sum_congr rfl ?_
                intro c₂ hc₂
                simpa using
                  (Finset.mul_sum
                    (s := (Finset.univ : Finset (ScalarBCoef c n)))
                    (a := bitSign (qScalar (b := b) (c := c) (n := n) bcoef c₂))
                    (f := fun b₂ : ScalarBCoef c n =>
                      bitSign (qScalar (b := b) (c := c) (n := n) b₂ ccoef))).symm
    _ =
        (∑ c₂ : ScalarCCoef b n,
          bitSign (qScalar (b := b) (c := c) (n := n) bcoef c₂)) *
          ∑ b₂ : ScalarBCoef c n,
            bitSign (qScalar (b := b) (c := c) (n := n) b₂ ccoef) := by
              rw [Finset.sum_mul]
    _ = (((if (TAdjScalar (b := b) (c := c) (n := n)) bcoef = 0 then
            Fintype.card (ScalarCCoef b n) else 0 : ℕ) : ℤ) *
          ((if (TScalar (b := b) (c := c) (n := n)) ccoef = 0 then
            Fintype.card (ScalarBCoef c n) else 0 : ℕ) : ℤ)) := by
              rw [sum_bitSign_qScalar_right (b := b) (c := c) (n := n) bcoef,
                sum_bitSign_qScalar (b := b) (c := c) (n := n) ccoef]

lemma sum_evenVisible_eq_kernel_visible_count {b c n : ℕ} [NeZero n] :
    ∑ bc : ScalarVisibleCompat b c n,
      ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
        bitSign
          (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
            qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) =
      ((((Fintype.card (ScalarCCoef b n) : ℕ) : ℤ) * (((Fintype.card (ScalarBCoef c n) : ℕ) : ℤ))) *
        Fintype.card (EvenVisibleKernelData b c n)) := by
  classical
  let K : ℤ := (((Fintype.card (ScalarCCoef b n) : ℕ) : ℤ) *
    (((Fintype.card (ScalarBCoef c n) : ℕ) : ℤ)))
  let s : Finset (ScalarVisibleCompat b c n) :=
    Finset.univ.filter
      (fun bc : ScalarVisibleCompat b c n =>
        (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
          (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0)
  have hterm :
      ∀ bc : ScalarVisibleCompat b c n,
        ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
            bitSign
              (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
                qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)
          =
            if h :
              (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
                (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0 then
              K else 0 := by
    intro bc
    have hprod :=
      sum_evenVisible_weight_eq_indicator (b := b) (c := c) (n := n) bc.bcoef bc.ccoef
    by_cases hb :
        (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0
    · by_cases hc :
          (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0
      · have hh :
            (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
              (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0 := ⟨hb, hc⟩
        rw [hprod]
        simp [K, hb, hc, hh]
      · have hh :
            ¬ ((TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
                (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0) := by
                  simp [hb, hc]
        rw [hprod]
        simp [K, hb, hc, hh]
    · have hh :
          ¬ ((TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
              (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0) := by
                simp [hb]
      rw [hprod]
      simp [K, hb, hh]
  calc
    ∑ bc : ScalarVisibleCompat b c n,
        ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
          bitSign
            (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
              qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef)
      =
        ∑ bc : ScalarVisibleCompat b c n,
          if h :
            (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
              (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0 then
            K else 0 := by
              refine Finset.sum_congr rfl ?_
              intro bc hbc
              exact hterm bc
    _ = s.sum (fun _ => K) := by
          have hdep :
              (∑ bc : ScalarVisibleCompat b c n,
                  if h :
                    (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
                      (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0 then
                    K else 0)
                =
                  ∑ bc : ScalarVisibleCompat b c n,
                    if (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
                        (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0 then
                      K else 0 := by
                        refine Finset.sum_congr rfl ?_
                        intro bc hbc
                        by_cases hh :
                            (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
                              (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0 <;>
                          simp [hh]
          rw [hdep]
          rw [← Finset.sum_filter]
    _ = K * Fintype.card (EvenVisibleKernelData b c n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          rw [← Fintype.card_of_subtype
            (p := fun bc : ScalarVisibleCompat b c n =>
              (TAdjScalar (b := b) (c := c) (n := n)) bc.bcoef = 0 ∧
                (TScalar (b := b) (c := c) (n := n)) bc.ccoef = 0)
            (s := s)]
          · ring
          · intro bc
            simp [s]
    _ =
        ((((Fintype.card (ScalarCCoef b n) : ℕ) : ℤ) * (((Fintype.card (ScalarBCoef c n) : ℕ) : ℤ))) *
          Fintype.card (EvenVisibleKernelData b c n)) := by
            rfl

lemma sum_evenVisible_eq_kernel_visible_factor {b c n : ℕ} [NeZero n] :
    ∑ bc : ScalarVisibleCompat b c n,
      ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
        bitSign
          (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
            qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) =
      (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1)) * Fintype.card (EvenVisibleKernelData b c n) := by
  rw [sum_evenVisible_eq_kernel_visible_count (b := b) (c := c) (n := n)]
  have hC : (((Fintype.card (ScalarCCoef b n) : ℕ) : ℤ)) = (2 : ℤ) ^ (n ^ (b + 1)) := by
    rw [card_scalarCCoef (b := b) (n := n)]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ (b + 1)))
  have hB : (((Fintype.card (ScalarBCoef c n) : ℕ) : ℤ)) = (2 : ℤ) ^ (n ^ (c + 1)) := by
    rw [card_scalarBCoef (c := c) (n := n)]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ (c + 1)))
  rw [hC, hB]
  calc
    (2 : ℤ) ^ (n ^ (b + 1)) * (2 : ℤ) ^ (n ^ (c + 1)) * Fintype.card (EvenVisibleKernelData b c n)
        = (((2 : ℤ) ^ (n ^ (b + 1))) * (2 : ℤ) ^ (n ^ (c + 1))) *
            Fintype.card (EvenVisibleKernelData b c n) := by
              ac_rfl
    _ = (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1)) * Fintype.card (EvenVisibleKernelData b c n) := by
          rw [← pow_add]

theorem sum_evenVisible_eq_kernel_visible_closed_form_all_ge_two {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    ∑ bc : ScalarVisibleCompat b c n,
      ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
        bitSign
          (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
            qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) =
      (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
  rw [sum_evenVisible_eq_kernel_visible_factor (b := b) (c := c) (n := n)]
  have hK : (Fintype.card (EvenVisibleKernelData b c n) : ℤ) =
      (2 : ℤ) ^ (n ^ b + n ^ c + n ^ 2 - 4 * n + 3) := by
    rw [card_evenVisibleKernelData_closed_all_ge_two (b := b) (c := c) (n := n) hn hb2 hc2]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ b + n ^ c + n ^ 2 - 4 * n + 3))
  rw [hK]
  rw [← pow_add]
  congr 1
  rw [Nat.pow_succ, Nat.pow_succ]
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hn
    have hmpos : 0 < m := by
      apply Nat.pos_of_ne_zero
      intro hm0
      apply NeZero.ne n
      simp [hm, hm0]
    omega
  have hbpow : n ^ 2 ≤ n ^ b := by
    exact Nat.pow_le_pow_right hn1 hb2
  have hcpow : n ^ 2 ≤ n ^ c := by
    exact Nat.pow_le_pow_right hn1 hc2
  have hquad : 4 * n ≤ n ^ 2 + n ^ 2 := by
    have h2n_sq : 2 * n ≤ n ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right n hn2
    calc
      4 * n = 2 * n + 2 * n := by omega
      _ ≤ n ^ 2 + n ^ 2 := add_le_add h2n_sq h2n_sq
  have htwo : n ^ 2 + n ^ 2 ≤ n ^ b + n ^ c := by
    simpa [two_mul] using (show 2 * n ^ 2 ≤ n ^ b + n ^ c by omega)
  have hbound : 4 * n ≤ n ^ b + n ^ c + n ^ 2 := by
    exact le_trans (le_trans hquad htwo) (Nat.le_add_right _ _)
  rw [Nat.mul_comm (n ^ b) n, Nat.mul_comm (n ^ c) n]
  calc
    n * n ^ b + n * n ^ c + (n ^ b + n ^ c + n ^ 2 - 4 * n + 3)
        = (n * n ^ b + n * n ^ c) + (n ^ b + n ^ c + n ^ 2 - 4 * n) + 3 := by
            ac_rfl
    _ = ((n * n ^ b + n * n ^ c) + (n ^ b + n ^ c + n ^ 2) - 4 * n) + 3 := by
          rw [← Nat.add_sub_assoc hbound]
    _ = n * n ^ b + n * n ^ c + n ^ b + n ^ c + n ^ 2 - 4 * n + 3 := by
          ac_rfl

theorem sum_evenVisible_eq_kernel_visible_closed_form_b_eq_one {c n : ℕ} [NeZero n]
    (hn : Even n) (hc2 : 1 < c) :
    ∑ bc : ScalarVisibleCompat 1 c n,
      ∑ c₂ : ScalarCCoef 1 n, ∑ b₂ : ScalarBCoef c n,
        bitSign
          (qScalar (b := 1) (c := c) (n := n) bc.bcoef c₂ +
            qScalar (b := 1) (c := c) (n := n) b₂ bc.ccoef) =
      (2 : ℤ) ^ (n ^ 2 + n ^ (c + 1) + n ^ c + 1) := by
  rw [sum_evenVisible_eq_kernel_visible_factor (b := 1) (c := c) (n := n)]
  have hK : (Fintype.card (EvenVisibleKernelData 1 c n) : ℤ) =
      (2 : ℤ) ^ (n ^ c + 1) := by
    rw [card_evenVisibleKernelData_closed_b_eq_one (c := c) (n := n) hn hc2]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ c + 1))
  rw [hK, ← pow_add]
  rw [show n ^ (1 + 1) = n ^ 2 by norm_num]
  ac_rfl

theorem sum_evenVisible_eq_kernel_visible_closed_form_c_eq_one {b n : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 1 < b) :
    ∑ bc : ScalarVisibleCompat b 1 n,
      ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef 1 n,
        bitSign
          (qScalar (b := b) (c := 1) (n := n) bc.bcoef c₂ +
            qScalar (b := b) (c := 1) (n := n) b₂ bc.ccoef) =
      (2 : ℤ) ^ (n ^ (b + 1) + n ^ 2 + n ^ b + 1) := by
  rw [sum_evenVisible_eq_kernel_visible_factor (b := b) (c := 1) (n := n)]
  have hK : (Fintype.card (EvenVisibleKernelData b 1 n) : ℤ) =
      (2 : ℤ) ^ (n ^ b + 1) := by
    rw [card_evenVisibleKernelData_closed_c_eq_one (b := b) (n := n) hn hb2]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n ^ b + 1))
  rw [hK, ← pow_add]
  rw [show n ^ (1 + 1) = n ^ 2 by norm_num]
  ac_rfl

theorem sum_evenVisible_eq_kernel_visible_closed_form_eq_one_eq_one
    {n : ℕ} [NeZero n] :
    ∑ bc : ScalarVisibleCompat 1 1 n,
      ∑ c₂ : ScalarCCoef 1 n, ∑ b₂ : ScalarBCoef 1 n,
        bitSign
          (qScalar (b := 1) (c := 1) (n := n) bc.bcoef c₂ +
            qScalar (b := 1) (c := 1) (n := n) b₂ bc.ccoef) =
      (2 : ℤ) ^ (n ^ 2 + n ^ 2 + n + 1) := by
  rw [sum_evenVisible_eq_kernel_visible_factor (b := 1) (c := 1) (n := n)]
  have hK : (Fintype.card (EvenVisibleKernelData 1 1 n) : ℤ) =
      (2 : ℤ) ^ (n + 1) := by
    rw [card_evenVisibleKernelData_closed_eq_one_eq_one (n := n)]
    simpa using (Nat.cast_pow (R := ℤ) 2 (n + 1))
  rw [hK, ← pow_add]
  rw [show n ^ (1 + 1) = n ^ 2 by norm_num, show n ^ (1 + 1) = n ^ 2 by norm_num]
  congr 1

theorem card_evenVisibleKernelData_closed_min_eq_one {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hdeg : b = 1 ∨ c = 1) :
    Fintype.card (EvenVisibleKernelData b c n) = 2 ^ (n ^ b + n ^ c - n + 1) := by
  rcases hdeg with rfl | rfl
  · have hc' : c = 1 ∨ 1 < c := by omega
    rcases hc' with rfl | hc2
    · have hexp : n ^ 1 + n ^ 1 - n + 1 = n + 1 := by
        simpa [pow_one] using (show n + n - n + 1 = n + 1 by omega)
      rw [hexp]
      exact card_evenVisibleKernelData_closed_eq_one_eq_one (n := n)
    · have hexp : n ^ 1 + n ^ c - n + 1 = n ^ c + 1 := by
        rw [pow_one]
        omega
      rw [hexp]
      exact card_evenVisibleKernelData_closed_b_eq_one (c := c) (n := n) hn hc2
  · have hb' : b = 1 ∨ 1 < b := by omega
    rcases hb' with rfl | hb2
    · have hexp : n ^ 1 + n ^ 1 - n + 1 = n + 1 := by
        simpa [pow_one] using (show n + n - n + 1 = n + 1 by omega)
      rw [hexp]
      exact card_evenVisibleKernelData_closed_eq_one_eq_one (n := n)
    · have hexp : n ^ b + n ^ 1 - n + 1 = n ^ b + 1 := by
        rw [pow_one]
        omega
      rw [hexp]
      exact card_evenVisibleKernelData_closed_c_eq_one (b := b) (n := n) hn hb2

theorem sum_evenVisible_eq_kernel_visible_closed_form_min_eq_one
    {b c n : ℕ} [NeZero n]
    (hn : Even n) (hb : 0 < b) (hc : 0 < c) (hdeg : b = 1 ∨ c = 1) :
    ∑ bc : ScalarVisibleCompat b c n,
      ∑ c₂ : ScalarCCoef b n, ∑ b₂ : ScalarBCoef c n,
        bitSign
          (qScalar (b := b) (c := c) (n := n) bc.bcoef c₂ +
            qScalar (b := b) (c := c) (n := n) b₂ bc.ccoef) =
      (2 : ℤ) ^ (n ^ (b + 1) + n ^ (c + 1) + n ^ b + n ^ c - n + 1) := by
  rcases hdeg with rfl | rfl
  · have hc' : c = 1 ∨ 1 < c := by omega
    rcases hc' with rfl | hc2
    · have hexp :
          n ^ (1 + 1) + n ^ (1 + 1) + n ^ 1 + n ^ 1 - n + 1 =
            n ^ 2 + n ^ 2 + n + 1 := by
        have hpow : n ^ (1 + 1) = n ^ 2 := by norm_num
        rw [hpow, hpow]
        simpa [pow_one] using
          (show n ^ 2 + n ^ 2 + n + n - n + 1 = n ^ 2 + n ^ 2 + n + 1 by omega)
      rw [hexp]
      exact sum_evenVisible_eq_kernel_visible_closed_form_eq_one_eq_one (n := n)
    · have hexp :
          n ^ (1 + 1) + n ^ (c + 1) + n ^ 1 + n ^ c - n + 1 =
            n ^ 2 + n ^ (c + 1) + n ^ c + 1 := by
        rw [show n ^ (1 + 1) = n ^ 2 by norm_num, pow_one]
        omega
      rw [hexp]
      exact sum_evenVisible_eq_kernel_visible_closed_form_b_eq_one (c := c) (n := n) hn hc2
  · have hb' : b = 1 ∨ 1 < b := by omega
    rcases hb' with rfl | hb2
    · have hexp :
          n ^ (1 + 1) + n ^ (1 + 1) + n ^ 1 + n ^ 1 - n + 1 =
            n ^ 2 + n ^ 2 + n + 1 := by
        have hpow : n ^ (1 + 1) = n ^ 2 := by norm_num
        rw [hpow, hpow]
        simpa [pow_one] using
          (show n ^ 2 + n ^ 2 + n + n - n + 1 = n ^ 2 + n ^ 2 + n + 1 by omega)
      rw [hexp]
      exact sum_evenVisible_eq_kernel_visible_closed_form_eq_one_eq_one (n := n)
    · have hexp :
          n ^ (b + 1) + n ^ (1 + 1) + n ^ b + n ^ 1 - n + 1 =
            n ^ (b + 1) + n ^ 2 + n ^ b + 1 := by
        rw [show n ^ (1 + 1) = n ^ 2 by norm_num, pow_one]
        omega
      rw [hexp]
      exact sum_evenVisible_eq_kernel_visible_closed_form_c_eq_one (b := b) (n := n) hn hb2

end Core3loop
