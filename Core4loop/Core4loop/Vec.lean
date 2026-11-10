import Core4loop.Basic

open scoped BigOperators

namespace Core4loop

abbrev Vec (n k : ℕ) := Fin k → I n
abbrev PVec (n a : ℕ) := Vec n (a - 1)
abbrev YVec (n b : ℕ) := Vec n b
abbrev ZVec (n c : ℕ) := Vec n c
abbrev WVec (n d : ℕ) := Vec n d

noncomputable def vecSum {n k : ℕ} [NeZero n] (v : Vec n k) : I n :=
  ∑ i : Fin k, v i

def zeroVec {n k : ℕ} : Vec n k := fun _ => 0

def vecSingle {n k : ℕ} [NeZero n] (hk : 0 < k) (s : I n) : Vec n k :=
  fun i => if i = ⟨0, hk⟩ then s else 0

lemma card_vec (n k : ℕ) [NeZero n] :
    Fintype.card (Vec n k) = n ^ k := by
  change Fintype.card (Fin k → ZMod n) = n ^ k
  rw [Fintype.card_fun]
  simp [ZMod.card]

lemma card_fun_vec_to_F (n k : ℕ) [NeZero n] :
    Fintype.card (Vec n k → F) = 2 ^ (n ^ k) := by
  rw [Fintype.card_fun, card_vec]
  simp [F]

lemma card_vec3 (n b c d : ℕ) [NeZero n] :
    Fintype.card (YVec n b × ZVec n c × WVec n d) = n ^ (b + c + d) := by
  simp only [YVec, ZVec, WVec]
  rw [Fintype.card_prod, Fintype.card_prod, card_vec, card_vec, card_vec]
  rw [← pow_add, ← pow_add]
  congr 1
  omega

lemma vecSum_vecSingle {n k : ℕ} [NeZero n] (hk : 0 < k) (s : I n) :
    vecSum (vecSingle hk s) = s := by
  classical
  unfold vecSum vecSingle
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

lemma vecSum_surjective {n k : ℕ} [NeZero n] (hk : 0 < k) :
    Function.Surjective (vecSum : Vec n k → I n) := by
  intro s
  exact ⟨vecSingle hk s, vecSum_vecSingle hk s⟩

noncomputable def vecSumRep {n k : ℕ} [NeZero n] (hk : 0 < k) (s : I n) : Vec n k :=
  Classical.choose (vecSum_surjective (n := n) (k := k) hk s)

lemma vecSum_vecSumRep {n k : ℕ} [NeZero n] (hk : 0 < k) (s : I n) :
    vecSum (vecSumRep (n := n) (k := k) hk s) = s :=
  Classical.choose_spec (vecSum_surjective (n := n) (k := k) hk s)

def shiftVec {n k : ℕ} (v : Vec n k) (i : Fin k) (t : I n) : Vec n k :=
  fun j => if j = i then v j + t else v j

lemma sum_update_add {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] (f : ι → M) (i : ι) (t : M) :
    (∑ j : ι, (if j = i then f j + t else f j)) = (∑ j : ι, f j) + t := by
  classical
  have hsplit :
      (∑ j : ι, (if j = i then f j + t else f j)) =
        (∑ j : ι, f j) + ∑ j : ι, (if j = i then t else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases h : j = i
    · simp [h]
    · simp [h]
  have hsingle : (∑ j : ι, (if j = i then t else 0)) = t := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [hsplit, hsingle]

lemma vecSum_shiftVec {n k : ℕ} [NeZero n]
    (v : Vec n k) (i : Fin k) (t : I n) :
    vecSum (shiftVec v i t) = vecSum v + t := by
  unfold vecSum shiftVec
  simpa using sum_update_add (fun j : Fin k => v j) i t

def shiftVecEquiv {n k : ℕ} (i : Fin k) (t : I n) : Vec n k ≃ Vec n k where
  toFun v := shiftVec v i t
  invFun v := shiftVec v i (-t)
  left_inv v := by
    funext j
    by_cases h : j = i
    · subst h
      simp [shiftVec, add_assoc]
    · simp [shiftVec, h]
  right_inv v := by
    funext j
    by_cases h : j = i
    · subst h
      simp [shiftVec, add_assoc]
    · simp [shiftVec, h]

lemma sum_vec_shift_invariant {n k : ℕ} [NeZero n] (i : Fin k) (t : I n)
    (f : Vec n k → F) :
    (∑ v : Vec n k, f (shiftVec v i t)) = ∑ v : Vec n k, f v := by
  simpa using ((shiftVecEquiv (n := n) (k := k) i t).sum_comp f)

lemma sum_cyclic_difference_over_vecSum_zero {n k : ℕ} [NeZero n]
    (hk : 0 < k) (g : I n → F) :
    (∑ v : Vec n k, (g (vecSum v) + g (vecSum v + 1))) = 0 := by
  classical
  let i : Fin k := ⟨0, hk⟩
  rw [Finset.sum_add_distrib]
  have hshift :
      (∑ v : Vec n k, g (vecSum v + 1)) = ∑ v : Vec n k, g (vecSum v) := by
    calc
      (∑ v : Vec n k, g (vecSum v + 1))
          = ∑ v : Vec n k, g (vecSum (shiftVec v i (1 : I n))) := by
              refine Finset.sum_congr rfl ?_
              intro v _
              rw [vecSum_shiftVec]
      _ = ∑ v : Vec n k, g (vecSum v) := by
              exact sum_vec_shift_invariant i (1 : I n) (fun v => g (vecSum v))
  rw [hshift]
  exact F_add_self _

def vecCons {n k : ℕ} (head : I n) (tail : Vec n k) : Vec n (k + 1)
  | ⟨0, _⟩ => head
  | ⟨i + 1, hi⟩ => tail ⟨i, Nat.lt_of_succ_lt_succ hi⟩

def vecTail {n k : ℕ} (v : Vec n (k + 1)) : Vec n k :=
  fun i => v i.succ

@[simp]
theorem vecTail_vecCons {n k : ℕ}
    (head : I n) (tail : Vec n k) :
    vecTail (vecCons head tail) = tail := by
  funext i
  rfl

@[simp]
theorem vecCons_head_tail {n k : ℕ}
    (v : Vec n (k + 1)) :
    vecCons (v 0) (vecTail v) = v := by
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ _ => rfl

def vecSuccEquiv (n k : ℕ) : Vec n (k + 1) ≃ I n × Vec n k where
  toFun v := (v 0, vecTail v)
  invFun X := vecCons X.1 X.2
  left_inv := by
    intro v
    exact vecCons_head_tail v
  right_inv := by
    intro X
    rcases X with ⟨head, tail⟩
    ext <;> rfl

theorem vecSum_vecCons {n k : ℕ} [NeZero n]
    (head : I n) (tail : Vec n k) :
    vecSum (vecCons head tail) = head + vecSum tail := by
  unfold vecSum
  simpa [vecCons] using
    (Fin.sum_univ_succ (f := fun i : Fin (k + 1) => vecCons head tail i))

theorem sum_zmod_add_left {n : ℕ} [NeZero n]
    (a : I n) (f : I n → F) :
    (∑ x : I n, f (a + x)) = ∑ x : I n, f x := by
  simpa using (Equiv.sum_comp (Equiv.addLeft a) f)

theorem sum_zmod_add_right {n : ℕ} [NeZero n]
    (a : I n) (f : I n → F) :
    (∑ x : I n, f (x + a)) = ∑ x : I n, f x := by
  simpa [add_comm] using sum_zmod_add_left (n := n) a f

theorem sum_vecSum_succ_eq_card_tail_mul
    {n k : ℕ} [NeZero n] (f : I n → F) :
    (∑ w : Vec n (k + 1), f (vecSum w))
      =
      (Fintype.card (Vec n k) : F) * ∑ s : I n, f s := by
  calc
    (∑ w : Vec n (k + 1), f (vecSum w))
        =
        ∑ X : I n × Vec n k, f (vecSum (vecCons X.1 X.2)) := by
          refine Fintype.sum_equiv (vecSuccEquiv n k)
            (fun w : Vec n (k + 1) => f (vecSum w))
            (fun X : I n × Vec n k => f (vecSum (vecCons X.1 X.2))) ?_
          intro w
          simp [vecSuccEquiv]
    _ =
        ∑ s : I n, ∑ tail : Vec n k, f (s + vecSum tail) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro s _
          refine Finset.sum_congr rfl ?_
          intro tail _
          rw [vecSum_vecCons]
    _ =
        ∑ tail : Vec n k, ∑ s : I n, f (s + vecSum tail) := by
          rw [Finset.sum_comm]
    _ =
        ∑ tail : Vec n k, ∑ s : I n, f s := by
          refine Finset.sum_congr rfl ?_
          intro tail _
          exact sum_zmod_add_right (n := n) (vecSum tail) f
    _ =
        (Fintype.card (Vec n k) : F) * ∑ s : I n, f s := by
          simp [Finset.sum_const, nsmul_eq_mul]

theorem sum_vecSum_eq_card_tail_mul
    {n d : ℕ} [NeZero n] (hd : 0 < d) (f : I n → F) :
    (∑ w : Vec n d, f (vecSum w))
      =
      (Fintype.card (Vec n (d - 1)) : F) * ∑ s : I n, f s := by
  rcases Nat.exists_eq_succ_of_ne_zero hd.ne' with ⟨k, rfl⟩
  simpa using
    sum_vecSum_succ_eq_card_tail_mul (n := n) (k := k) f

lemma natCast_odd_eq_one_F {m : ℕ} (hm : Odd m) :
    ((m : ℕ) : F) = 1 := by
  rcases hm with ⟨k, rfl⟩
  have h2 : ((2 : ℕ) : F) = 0 := by decide
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, h2, zero_mul, zero_add]

lemma natCast_even_eq_zero_F {m : ℕ} (hm : Even m) :
    ((m : ℕ) : F) = 0 := by
  rcases hm with ⟨k, rfl⟩
  rw [Nat.cast_add]
  exact F_add_self (k : F)

theorem natCast_card_vec_eq_one_of_odd
    {n k : ℕ} [NeZero n] (hn : Odd n) :
    ((Fintype.card (Vec n k) : ℕ) : F) = 1 := by
  rw [card_vec]
  exact natCast_odd_eq_one_F (Odd.pow (a := n) (n := k) hn)

theorem natCast_card_vec_eq_zero_of_even_pos
    {n k : ℕ} [NeZero n] (hn : Even n) (hk : 0 < k) :
    ((Fintype.card (Vec n k) : ℕ) : F) = 0 := by
  rw [card_vec]
  exact natCast_even_eq_zero_F
    (Even.pow_of_ne_zero (a := n) hn (Nat.ne_of_gt hk))

end Core4loop
