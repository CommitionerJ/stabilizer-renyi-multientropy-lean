import Core4loop.TriangleLeaf.PassiveDot

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

def vecCons {n k : ℕ} (head : I n) (tail : Vec n k) : Vec n (k + 1)
  | ⟨0, _⟩ => head
  | ⟨i + 1, hi⟩ => tail ⟨i, Nat.lt_of_succ_lt_succ hi⟩

def vecTail {n k : ℕ} (v : Vec n (k + 1)) : Vec n k :=
  fun i => v i.succ

@[simp] theorem vecTail_vecCons {n k : ℕ}
    (head : I n) (tail : Vec n k) :
    vecTail (vecCons head tail) = tail := by
  funext i
  rfl

@[simp] theorem vecCons_head_tail {n k : ℕ}
    (v : Vec n (k + 1)) :
    vecCons (v 0) (vecTail v) = v := by
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ j => rfl

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
    (∑ w : WVec n d, f (vecSum w))
      =
      (Fintype.card (Vec n (d - 1)) : F) * ∑ s : I n, f s := by
  rcases Nat.exists_eq_succ_of_ne_zero hd.ne' with ⟨k, rfl⟩
  simpa [WVec] using
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

theorem passiveDot_diffEmbed_diffEmbed_eq_card_tail_mul
    {n d : ℕ} [NeZero n] (hd : 0 < d)
    (R S : ZeroSumProfile n) :
    passiveDot (n := n) (d := d)
        (PassiveDiffEmbed (n := n) (d := d) R)
        (PassiveDiffEmbed (n := n) (d := d) S)
      =
      (Fintype.card (Vec n (d - 1)) : F) *
        ∑ s : I n, R.1 s * S.1 s := by
  simpa [passiveDot, PassiveDiffEmbed] using
    sum_vecSum_eq_card_tail_mul (n := n) (d := d) hd
      (fun s : I n => R.1 s * S.1 s)

theorem passiveDot_diffEmbed_diffEmbed_eq_sum_of_odd
    {n d : ℕ} [NeZero n] (hd : 0 < d) (hn : Odd n)
    (R S : ZeroSumProfile n) :
    passiveDot (n := n) (d := d)
        (PassiveDiffEmbed (n := n) (d := d) R)
        (PassiveDiffEmbed (n := n) (d := d) S)
      =
      ∑ s : I n, R.1 s * S.1 s := by
  rw [passiveDot_diffEmbed_diffEmbed_eq_card_tail_mul
    (n := n) (d := d) hd R S]
  rw [natCast_card_vec_eq_one_of_odd (n := n) (k := d - 1) hn]
  simp

theorem passiveDot_diffEmbed_diffEmbed_eq_zero_of_even_two_le
    {n d : ℕ} [NeZero n] (hn : Even n) (hd2 : 2 ≤ d)
    (R S : ZeroSumProfile n) :
    passiveDot (n := n) (d := d)
        (PassiveDiffEmbed (n := n) (d := d) R)
        (PassiveDiffEmbed (n := n) (d := d) S)
      =
      0 := by
  have hd : 0 < d := by omega
  have htail : 0 < d - 1 := by omega
  rw [passiveDot_diffEmbed_diffEmbed_eq_card_tail_mul
    (n := n) (d := d) hd R S]
  rw [natCast_card_vec_eq_zero_of_even_pos
    (n := n) (k := d - 1) hn htail]
  simp

end

end TriangleLeaf
end Core4loop
