import Core4loop.TriangleLeaf.E6ShearedCoeffCore

open scoped BigOperators

namespace Core4loop
namespace TriangleLeaf

noncomputable section

/-!
Explicit sparse-source and compatibility witnesses for the corrected
TriangleLeaf sheared-S1 image theorem.
-/

noncomputable def triangleLeafE6BFiber
    {n a c d : ℕ} [NeZero n] :
    BFun4 n a c d →ₗ[F]
      (PVec n a → I n → I n → WVec n d → F) where
  toFun B := fun p s r w =>
    ∑ z : ZVec n c, if vecSum z = r then B p s z w else 0
  map_add' B D := by
    funext p s r w
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = r <;> simp [hz]
  map_smul' x B := by
    funext p s r w
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro z _
    by_cases hz : vecSum z = r <;> simp [hz, mul_zero]

@[simp]
theorem triangleLeafE6BFiber_apply
    {n a c d : ℕ} [NeZero n]
    (B : BFun4 n a c d)
    (p : PVec n a) (s r : I n) (w : WVec n d) :
    triangleLeafE6BFiber
        (n := n) (a := a) (c := c) (d := d) B p s r w =
      ∑ z : ZVec n c, if vecSum z = r then B p s z w else 0 :=
  rfl

noncomputable def triangleLeafE6BfromC
    {n a b c d : ℕ} [NeZero n] (hc : 0 < c) :
    CFun4 n a b d →ₗ[F] BFun4 n a c d where
  toFun C := fun p s z w =>
    if z = vecSingle hc (vecSum z) then
      triangleLeafE6CFiber
        (n := n) (a := a) (b := b) (d := d)
        C p (vecSum z) s w
    else 0
  map_add' C D := by
    funext p s z w
    change
      (if z = vecSingle hc (vecSum z) then
          triangleLeafE6CFiber (C + D) p (vecSum z) s w
        else 0) =
        (if z = vecSingle hc (vecSum z) then
            triangleLeafE6CFiber C p (vecSum z) s w
          else 0) +
          if z = vecSingle hc (vecSum z) then
            triangleLeafE6CFiber D p (vecSum z) s w
          else 0
    by_cases hz : z = vecSingle hc (vecSum z)
    · simp only [if_pos hz]
      exact
        congrFun
          (congrFun
            (congrFun
              (congrFun
                ((triangleLeafE6CFiber
                  (n := n) (a := a) (b := b) (d := d)).map_add C D) p)
              (vecSum z)) s) w
    · simp only [if_neg hz, add_zero]
  map_smul' x C := by
    funext p s z w
    change
      (if z = vecSingle hc (vecSum z) then
          triangleLeafE6CFiber (x • C) p (vecSum z) s w
        else 0) =
        x •
          if z = vecSingle hc (vecSum z) then
            triangleLeafE6CFiber C p (vecSum z) s w
          else 0
    by_cases hz : z = vecSingle hc (vecSum z)
    · simp only [if_pos hz]
      exact
        congrFun
          (congrFun
            (congrFun
              (congrFun
                ((triangleLeafE6CFiber
                  (n := n) (a := a) (b := b) (d := d)).map_smul x C) p)
              (vecSum z)) s) w
    · simp only [if_neg hz, smul_zero]

@[simp]
theorem triangleLeafE6BfromC_apply
    {n a b c d : ℕ} [NeZero n] (hc : 0 < c)
    (C : CFun4 n a b d)
    (p : PVec n a) (s : I n) (z : ZVec n c) (w : WVec n d) :
    triangleLeafE6BfromC
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hc C p s z w =
      if z = vecSingle hc (vecSum z) then
        triangleLeafE6CFiber
          (n := n) (a := a) (b := b) (d := d)
          C p (vecSum z) s w
      else 0 :=
  rfl

noncomputable def triangleLeafE6CfromB
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    BFun4 n a c d →ₗ[F] CFun4 n a b d where
  toFun B := fun p y r w =>
    if y = vecSingle hb (vecSum y) then
      triangleLeafE6BFiber
        (n := n) (a := a) (c := c) (d := d)
        B p r (vecSum y) w
    else 0
  map_add' B D := by
    funext p y r w
    change
      (if y = vecSingle hb (vecSum y) then
          triangleLeafE6BFiber (B + D) p r (vecSum y) w
        else 0) =
        (if y = vecSingle hb (vecSum y) then
            triangleLeafE6BFiber B p r (vecSum y) w
          else 0) +
          if y = vecSingle hb (vecSum y) then
            triangleLeafE6BFiber D p r (vecSum y) w
          else 0
    by_cases hy : y = vecSingle hb (vecSum y)
    · simp only [if_pos hy]
      exact
        congrFun
          (congrFun
            (congrFun
              (congrFun
                ((triangleLeafE6BFiber
                  (n := n) (a := a) (c := c) (d := d)).map_add B D) p) r)
              (vecSum y)) w
    · simp only [if_neg hy, add_zero]
  map_smul' x B := by
    funext p y r w
    change
      (if y = vecSingle hb (vecSum y) then
          triangleLeafE6BFiber (x • B) p r (vecSum y) w
        else 0) =
        x •
          if y = vecSingle hb (vecSum y) then
            triangleLeafE6BFiber B p r (vecSum y) w
          else 0
    by_cases hy : y = vecSingle hb (vecSum y)
    · simp only [if_pos hy]
      exact
        congrFun
          (congrFun
            (congrFun
              (congrFun
                ((triangleLeafE6BFiber
                  (n := n) (a := a) (c := c) (d := d)).map_smul x B) p) r)
              (vecSum y)) w
    · simp only [if_neg hy, smul_zero]

@[simp]
theorem triangleLeafE6CfromB_apply
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b)
    (B : BFun4 n a c d)
    (p : PVec n a) (y : YVec n b) (r : I n) (w : WVec n d) :
    triangleLeafE6CfromB
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb B p y r w =
      if y = vecSingle hb (vecSum y) then
        triangleLeafE6BFiber
          (n := n) (a := a) (c := c) (d := d)
          B p r (vecSum y) w
      else 0 :=
  rfl

theorem triangleLeafE6BFiber_BfromC
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (C : CFun4 n a b d)
    (p : PVec n a) (s r : I n) (w : WVec n d) :
    triangleLeafE6BFiber
        (n := n) (a := a) (c := c) (d := d)
        (triangleLeafE6BfromC
          (n := n) (a := a) (b := b) (c := c) (d := d) hc C)
        p s r w =
      triangleLeafE6CFiber
        (n := n) (a := a) (b := b) (d := d) C p r s w := by
  classical
  change
    (∑ z : ZVec n c,
      if vecSum z = r then
        triangleLeafE6BfromC hc C p s z w
      else 0) =
      triangleLeafE6CFiber C p r s w
  rw [Finset.sum_eq_single (vecSingle hc r)]
  · simp [triangleLeafE6BfromC, vecSum_vecSingle]
  · intro z _ hz
    by_cases hsum : vecSum z = r <;>
      simp [hsum, triangleLeafE6BfromC, hz]
  · simp

theorem triangleLeafE6CFiber_CfromB
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (B : BFun4 n a c d)
    (p : PVec n a) (s r : I n) (w : WVec n d) :
    triangleLeafE6CFiber
        (n := n) (a := a) (b := b) (d := d)
        (triangleLeafE6CfromB
          (n := n) (a := a) (b := b) (c := c) (d := d) hb B)
        p s r w =
      triangleLeafE6BFiber
        (n := n) (a := a) (c := c) (d := d) B p r s w := by
  classical
  change
    (∑ y : YVec n b,
      if vecSum y = s then
        triangleLeafE6CfromB hb B p y r w
      else 0) =
      triangleLeafE6BFiber B p r s w
  rw [Finset.sum_eq_single (vecSingle hb s)]
  · simp [triangleLeafE6CfromB, vecSum_vecSingle]
  · intro y _ hy
    by_cases hsum : vecSum y = s <;>
      simp [hsum, triangleLeafE6CfromB, hy]
  · simp

theorem triangleLeafE6BDiagOfB_BfromC_point
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (C : CFun4 n a b d)
    (p : PVec n a) (w : WVec n d) (s u : I n) :
    (BDiagOfB
        (n := n) (a := a) (c := c) (d := d)
        (triangleLeafE6BfromC
          (n := n) (a := a) (b := b) (c := c) (d := d) hc C)
        p w).1 s u =
      (triangleLeafE6AlphaShearCoeff
        (n := n) (a := a) (b := b) (d := d) C p w).1 s u := by
  change
    triangleLeafE6BFiber
          (triangleLeafE6BfromC hc C) p s (u - s) w +
        triangleLeafE6BFiber
          (triangleLeafE6BfromC hc C) p (s + 1) (u - (s + 1)) w =
      triangleLeafE6CFiber C p (u - s - 1) (u - (u - s - 1)) w +
        triangleLeafE6CFiber C p (u - s + 1 - 1)
          (u - (u - s + 1 - 1)) w
  rw [triangleLeafE6BFiber_BfromC, triangleLeafE6BFiber_BfromC]
  have h1 : u - (s + 1) = u - s - 1 := by abel
  have h2 : u - s + 1 - 1 = u - s := by abel
  have h3 : u - (u - s - 1) = s + 1 := by abel
  have h4 : u - (u - s) = s := by abel
  rw [h1, h2, h3, h4]
  exact add_comm _ _

theorem triangleLeafE6BDiagOfB_BfromC
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (C : CFun4 n a b d) :
    BDiagOfB
        (n := n) (a := a) (c := c) (d := d)
        (triangleLeafE6BfromC
          (n := n) (a := a) (b := b) (c := c) (d := d) hc C) =
      triangleLeafE6AlphaShearCoeff
        (n := n) (a := a) (b := b) (d := d) C := by
  funext p w
  apply Subtype.ext
  funext s u
  exact triangleLeafE6BDiagOfB_BfromC_point hc C p w s u

theorem triangleLeafE6AlphaShearCoeff_CfromB_point
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (B : BFun4 n a c d)
    (p : PVec n a) (w : WVec n d) (s u : I n) :
    (triangleLeafE6AlphaShearCoeff
        (n := n) (a := a) (b := b) (d := d)
        (triangleLeafE6CfromB
          (n := n) (a := a) (b := b) (c := c) (d := d) hb B)
        p w).1 s u =
      (BDiagOfB (n := n) (a := a) (c := c) (d := d) B p w).1 s u := by
  change
    triangleLeafE6CFiber (triangleLeafE6CfromB hb B)
          p (u - s - 1) (u - (u - s - 1)) w +
        triangleLeafE6CFiber (triangleLeafE6CfromB hb B)
          p (u - s + 1 - 1) (u - (u - s + 1 - 1)) w =
      triangleLeafE6BFiber B p s (u - s) w +
        triangleLeafE6BFiber B p (s + 1) (u - (s + 1)) w
  rw [triangleLeafE6CFiber_CfromB, triangleLeafE6CFiber_CfromB]
  have h1 : u - (s + 1) = u - s - 1 := by abel
  have h2 : u - s + 1 - 1 = u - s := by abel
  have h3 : u - (u - s - 1) = s + 1 := by abel
  have h4 : u - (u - s) = s := by abel
  rw [h1, h2, h3, h4]
  exact add_comm _ _

theorem triangleLeafE6AlphaShearCoeff_CfromB
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (B : BFun4 n a c d) :
    triangleLeafE6AlphaShearCoeff
        (n := n) (a := a) (b := b) (d := d)
        (triangleLeafE6CfromB
          (n := n) (a := a) (b := b) (c := c) (d := d) hb B) =
      BDiagOfB (n := n) (a := a) (c := c) (d := d) B := by
  funext p w
  apply Subtype.ext
  funext s u
  exact triangleLeafE6AlphaShearCoeff_CfromB_point hb B p w s u

theorem triangleLeafE6_sum_if_vecSum_eq_const
    {n k : ℕ} [NeZero n] (hk : 0 < k) (s : I n) (x : F) :
    (∑ v : Vec n k, if vecSum v = s then x else 0) =
      (Fintype.card (Vec n (k - 1)) : F) * x := by
  classical
  calc
    (∑ v : Vec n k, if vecSum v = s then x else 0) =
        ∑ v : Vec n k,
          (fun q : I n => if q = s then x else 0) (vecSum v) := rfl
    _ =
        (Fintype.card (Vec n (k - 1)) : F) *
          ∑ q : I n, (if q = s then x else 0) := by
      exact
        sum_vecSum_eq_card_tail_mul
          (n := n) (d := k) hk
          (fun q : I n => if q = s then x else 0)
    _ = (Fintype.card (Vec n (k - 1)) : F) * x := by
      congr 1
      rw [Finset.sum_eq_single s]
      · simp
      · intro q _ hq
        simp [hq]
      · simp

theorem triangleLeafE6_sum_if_vecSum_eq_const_zero
    {n k : ℕ} [NeZero n]
    (hn : Even n) (hk2 : 2 ≤ k) (s : I n) (x : F) :
    (∑ v : Vec n k, if vecSum v = s then x else 0) = 0 := by
  rw [triangleLeafE6_sum_if_vecSum_eq_const
    (n := n) (k := k) (by omega)]
  rw [natCast_card_vec_eq_zero_of_even_pos
    (n := n) (k := k - 1) hn (by omega)]
  simp

theorem triangleLeafE6KBMap_BfromC_point
    {n a b c d : ℕ} [NeZero n]
    (hc : 0 < c) (C : CFun4 n a b d)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6BfromC
          (n := n) (a := a) (b := b) (c := c) (d := d) hc C)
        y z w =
      if z = vecSingle hc (vecSum z) then
        ∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
              C y' (vecSingle hc (vecSum y)) w
          else 0
      else 0 := by
  classical
  by_cases hz : z = vecSingle hc (vecSum z)
  · rw [if_pos hz]
    have hB (p : PVec n a) (s : I n) :
        triangleLeafE6BfromC hc C p s z w =
          triangleLeafE6CFiber C p (vecSum z) s w := by
      change
        (if z = vecSingle hc (vecSum z) then
            triangleLeafE6CFiber C p (vecSum z) s w
          else 0) =
          triangleLeafE6CFiber C p (vecSum z) s w
      exact if_pos hz
    change
      (∑ p : PVec n a,
          (triangleLeafE6BfromC hc C p (vecSum y) z w +
            triangleLeafE6BfromC hc C p (vecSum y + 1) z w)) =
        ∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            ∑ p : PVec n a,
              (C p y' (vecSum (vecSingle hc (vecSum y))) w +
                C p y' (vecSum (vecSingle hc (vecSum y)) + 1) w)
          else 0
    simp_rw [hB]
    rw [vecSum_vecSingle]
    change
      (∑ p : PVec n a,
          (triangleLeafE6CFiber C p (vecSum z) (vecSum y) w +
            triangleLeafE6CFiber C p (vecSum z) (vecSum y + 1) w)) =
        ∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            ∑ p : PVec n a,
              (C p y' (vecSum y) w + C p y' (vecSum y + 1) w)
          else 0
    unfold triangleLeafE6CFiber
    calc
      (∑ p : PVec n a,
          ((∑ y' : YVec n b,
              if vecSum y' = vecSum z then C p y' (vecSum y) w else 0) +
            ∑ y' : YVec n b,
              if vecSum y' = vecSum z then
                C p y' (vecSum y + 1) w
              else 0)) =
          ∑ p : PVec n a, ∑ y' : YVec n b,
            if vecSum y' = vecSum z then
              C p y' (vecSum y) w + C p y' (vecSum y + 1) w
            else 0 := by
              refine Finset.sum_congr rfl ?_
              intro p _
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro y' _
              by_cases hy : vecSum y' = vecSum z <;> simp [hy]
      _ = ∑ y' : YVec n b, ∑ p : PVec n a,
            if vecSum y' = vecSum z then
              C p y' (vecSum y) w + C p y' (vecSum y + 1) w
            else 0 := by
              exact Finset.sum_comm
      _ = ∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            ∑ p : PVec n a,
              (C p y' (vecSum y) w + C p y' (vecSum y + 1) w)
          else 0 := by
              refine Finset.sum_congr rfl ?_
              intro y' _
              by_cases hy : vecSum y' = vecSum z <;> simp [hy]
  · rw [if_neg hz]
    have hB (p : PVec n a) (s : I n) :
        triangleLeafE6BfromC hc C p s z w = 0 := by
      change
        (if z = vecSingle hc (vecSum z) then
            triangleLeafE6CFiber C p (vecSum z) s w
          else 0) = 0
      exact if_neg hz
    change
      (∑ p : PVec n a,
          (triangleLeafE6BfromC hc C p (vecSum y) z w +
            triangleLeafE6BfromC hc C p (vecSum y + 1) z w)) = 0
    simp_rw [hB]
    simp

noncomputable def triangleLeafE6WfromC
    {n b c : ℕ} [NeZero n] (hc : 0 < c)
    (R : WCoeff n b c) : WCoeff n b c :=
  fun y z =>
    if z = vecSingle hc (vecSum z) then
      ∑ y' : YVec n b,
        if vecSum y' = vecSum z then
          R y' (vecSingle hc (vecSum y))
        else 0
    else 0

noncomputable def triangleLeafE6WfromB
    {n b c : ℕ} [NeZero n] (hb : 0 < b)
    (R : WCoeff n b c) : WCoeff n b c :=
  fun y z =>
    if y = vecSingle hb (vecSum y) then
      ∑ z' : ZVec n c,
        if vecSum z' = vecSum y then
          R (vecSingle hb (vecSum z)) z'
        else 0
    else 0

theorem triangleLeafE6KBMap_BfromC_eq_WDiffEmbed
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c)
    (C : CFun4 n a b d) (A : YCoeff n c d) (R : WCoeff n b c)
    (hdecomp :
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C =
        YDiffEmbed (n := n) (b := b) (c := c) (d := d) A +
          WDiffEmbed (n := n) (b := b) (c := c) (d := d) R) :
    KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6BfromC
          (n := n) (a := a) (b := b) (c := c) (d := d) hc C) =
      WDiffEmbed (n := n) (b := b) (c := c) (d := d)
        (triangleLeafE6WfromC hc R) := by
  classical
  funext y z w
  rw [triangleLeafE6KBMap_BfromC_point]
  by_cases hz : z = vecSingle hc (vecSum z)
  · rw [if_pos hz]
    change
      (∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
              C y' (vecSingle hc (vecSum y)) w
          else 0) =
        (triangleLeafE6WfromC hc R y z).1 (vecSum w)
    have hpoint (y' : YVec n b) :
        KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
            C y' (vecSingle hc (vecSum y)) w =
          (A (vecSingle hc (vecSum y)) w).1 (vecSum y') +
            (R y' (vecSingle hc (vecSum y))).1 (vecSum w) := by
      exact
        congrFun
          (congrFun
            (congrFun hdecomp y')
            (vecSingle hc (vecSum y))) w
    have hYzero :
        (∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            (A (vecSingle hc (vecSum y)) w).1 (vecSum y')
          else 0) = 0 := by
      calc
        (∑ y' : YVec n b,
            if vecSum y' = vecSum z then
              (A (vecSingle hc (vecSum y)) w).1 (vecSum y')
            else 0) =
            ∑ y' : YVec n b,
              if vecSum y' = vecSum z then
                (A (vecSingle hc (vecSum y)) w).1 (vecSum z)
              else 0 := by
                refine Finset.sum_congr rfl ?_
                intro y' _
                by_cases hy : vecSum y' = vecSum z
                · rw [if_pos hy, if_pos hy, hy]
                · rw [if_neg hy, if_neg hy]
        _ = 0 :=
          triangleLeafE6_sum_if_vecSum_eq_const_zero
            hn hb2 (vecSum z)
              ((A (vecSingle hc (vecSum y)) w).1 (vecSum z))
    calc
      (∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
              C y' (vecSingle hc (vecSum y)) w
          else 0) =
          (∑ y' : YVec n b,
            if vecSum y' = vecSum z then
              (A (vecSingle hc (vecSum y)) w).1 (vecSum y')
            else 0) +
          ∑ y' : YVec n b,
            if vecSum y' = vecSum z then
              (R y' (vecSingle hc (vecSum y))).1 (vecSum w)
            else 0 := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro y' _
              by_cases hy : vecSum y' = vecSum z
              · rw [if_pos hy, if_pos hy, if_pos hy, hpoint]
              · rw [if_neg hy, if_neg hy, if_neg hy, zero_add]
      _ = ∑ y' : YVec n b,
          if vecSum y' = vecSum z then
            (R y' (vecSingle hc (vecSum y))).1 (vecSum w)
          else 0 := by rw [hYzero, zero_add]
      _ = (triangleLeafE6WfromC hc R y z).1 (vecSum w) := by
        unfold triangleLeafE6WfromC
        rw [if_pos hz]
        change
          (∑ y' : YVec n b,
              if vecSum y' = vecSum z then
                (R y' (vecSingle hc (vecSum y))).1 (vecSum w)
              else 0) =
            (Submodule.subtype (ZeroSumProfile n)
              (∑ y' : YVec n b,
                if vecSum y' = vecSum z then
                  R y' (vecSingle hc (vecSum y))
                else 0)) (vecSum w)
        rw [map_sum]
        simp only [Finset.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro y' _
        by_cases hy : vecSum y' = vecSum z <;> simp [hy]
  · rw [if_neg hz]
    change 0 = (triangleLeafE6WfromC hc R y z).1 (vecSum w)
    unfold triangleLeafE6WfromC
    rw [if_neg hz]
    rfl

theorem triangleLeafE6_pair_BfromC_zero_mem_compatible
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c)
    (C : CFun4 n a b d)
    (hC : C ∈ triangleLeafCCompat n a b c d) :
    (triangleLeafE6BfromC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc C,
      (0 : CFun4 n a b d)) ∈
        triangleLeafCompatibleSubmodule n a b c d := by
  have hroot :=
    (mem_triangleLeafCCompat_iff_KCMap_mem_sup
      (n := n) (a := a) (b := b) (c := c) (d := d) C).mp hC
  rcases Submodule.mem_sup.mp hroot with
    ⟨yRoot, hyRoot, wRoot, hwRoot, hyw⟩
  rcases hyRoot with ⟨A, hA⟩
  rcases hwRoot with ⟨R, hR⟩
  have hdecomp :
      KCMap (n := n) (a := a) (b := b) (c := c) (d := d) C =
        YDiffEmbed (n := n) (b := b) (c := c) (d := d) A +
          WDiffEmbed (n := n) (b := b) (c := c) (d := d) R := by
    rw [hA, hR]
    exact hyw.symm
  have hKB :=
    triangleLeafE6KBMap_BfromC_eq_WDiffEmbed
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hn hb2 hc C A R hdecomp
  apply
    (triangleLeafCompatibleSubmodule_carrier_iff
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (triangleLeafE6BfromC hc C, 0)).mpr
  rw [(KCMap
    (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero, add_zero]
  exact ⟨triangleLeafE6WfromC hc R, hKB.symm⟩

theorem triangleLeafE6_exists_BOnly_BfromC
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c)
    (C : CFun4 n a b d)
    (hC : C ∈ triangleLeafCCompat n a b c d) :
    ∃ Y : triangleLeafBOnly n a b c d,
      Y.1.1.1 =
        triangleLeafE6BfromC
          (n := n) (a := a) (b := b) (c := c) (d := d) hc C := by
  let X : triangleLeafCompatibleSubmodule n a b c d :=
    ⟨(triangleLeafE6BfromC
        (n := n) (a := a) (b := b) (c := c) (d := d) hc C,
      (0 : CFun4 n a b d)),
      triangleLeafE6_pair_BfromC_zero_mem_compatible
        hn hb2 hc C hC⟩
  let Y : triangleLeafBOnly n a b c d :=
    ⟨X, LinearMap.mem_ker.mpr rfl⟩
  exact ⟨Y, rfl⟩

theorem triangleLeafE6KCMap_CfromB_point
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (B : BFun4 n a c d)
    (y : YVec n b) (z : ZVec n c) (w : WVec n d) :
    KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6CfromB
          (n := n) (a := a) (b := b) (c := c) (d := d) hb B)
        y z w =
      if y = vecSingle hb (vecSum y) then
        ∑ z' : ZVec n c,
          if vecSum z' = vecSum y then
            KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
              B (vecSingle hb (vecSum z)) z' w
          else 0
      else 0 := by
  classical
  by_cases hy : y = vecSingle hb (vecSum y)
  · rw [if_pos hy]
    have hC (p : PVec n a) (r : I n) :
        triangleLeafE6CfromB hb B p y r w =
          triangleLeafE6BFiber B p r (vecSum y) w := by
      change
        (if y = vecSingle hb (vecSum y) then
            triangleLeafE6BFiber B p r (vecSum y) w
          else 0) =
          triangleLeafE6BFiber B p r (vecSum y) w
      exact if_pos hy
    change
      (∑ p : PVec n a,
          (triangleLeafE6CfromB hb B p y (vecSum z) w +
            triangleLeafE6CfromB hb B p y (vecSum z + 1) w)) =
        ∑ z' : ZVec n c,
          if vecSum z' = vecSum y then
            ∑ p : PVec n a,
              (B p (vecSum (vecSingle hb (vecSum z))) z' w +
                B p (vecSum (vecSingle hb (vecSum z)) + 1) z' w)
          else 0
    simp_rw [hC]
    rw [vecSum_vecSingle]
    change
      (∑ p : PVec n a,
          (triangleLeafE6BFiber B p (vecSum z) (vecSum y) w +
            triangleLeafE6BFiber B p (vecSum z + 1) (vecSum y) w)) =
        ∑ z' : ZVec n c,
          if vecSum z' = vecSum y then
            ∑ p : PVec n a,
              (B p (vecSum z) z' w + B p (vecSum z + 1) z' w)
          else 0
    unfold triangleLeafE6BFiber
    calc
      (∑ p : PVec n a,
          ((∑ z' : ZVec n c,
              if vecSum z' = vecSum y then B p (vecSum z) z' w else 0) +
            ∑ z' : ZVec n c,
              if vecSum z' = vecSum y then
                B p (vecSum z + 1) z' w
              else 0)) =
          ∑ p : PVec n a, ∑ z' : ZVec n c,
            if vecSum z' = vecSum y then
              B p (vecSum z) z' w + B p (vecSum z + 1) z' w
            else 0 := by
              refine Finset.sum_congr rfl ?_
              intro p _
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro z' _
              by_cases hz' : vecSum z' = vecSum y <;> simp [hz']
      _ = ∑ z' : ZVec n c, ∑ p : PVec n a,
            if vecSum z' = vecSum y then
              B p (vecSum z) z' w + B p (vecSum z + 1) z' w
            else 0 := by
              exact Finset.sum_comm
      _ = ∑ z' : ZVec n c,
          if vecSum z' = vecSum y then
            ∑ p : PVec n a,
              (B p (vecSum z) z' w + B p (vecSum z + 1) z' w)
          else 0 := by
              refine Finset.sum_congr rfl ?_
              intro z' _
              by_cases hz' : vecSum z' = vecSum y <;> simp [hz']
  · rw [if_neg hy]
    have hC (p : PVec n a) (r : I n) :
        triangleLeafE6CfromB hb B p y r w = 0 := by
      change
        (if y = vecSingle hb (vecSum y) then
            triangleLeafE6BFiber B p r (vecSum y) w
          else 0) = 0
      exact if_neg hy
    change
      (∑ p : PVec n a,
          (triangleLeafE6CfromB hb B p y (vecSum z) w +
            triangleLeafE6CfromB hb B p y (vecSum z + 1) w)) = 0
    simp_rw [hC]
    simp

theorem triangleLeafE6KCMap_CfromB_eq_WDiffEmbed
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (B : BFun4 n a c d) (R : WCoeff n b c)
    (hdecomp :
      KBMap (n := n) (a := a) (b := b) (c := c) (d := d) B =
        WDiffEmbed (n := n) (b := b) (c := c) (d := d) R) :
    KCMap (n := n) (a := a) (b := b) (c := c) (d := d)
        (triangleLeafE6CfromB
          (n := n) (a := a) (b := b) (c := c) (d := d) hb B) =
      WDiffEmbed (n := n) (b := b) (c := c) (d := d)
        (triangleLeafE6WfromB hb R) := by
  classical
  funext y z w
  rw [triangleLeafE6KCMap_CfromB_point]
  by_cases hy : y = vecSingle hb (vecSum y)
  · rw [if_pos hy]
    change
      (∑ z' : ZVec n c,
          if vecSum z' = vecSum y then
            KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
              B (vecSingle hb (vecSum z)) z' w
          else 0) =
        (triangleLeafE6WfromB hb R y z).1 (vecSum w)
    have hpoint (z' : ZVec n c) :
        KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
            B (vecSingle hb (vecSum z)) z' w =
          (R (vecSingle hb (vecSum z)) z').1 (vecSum w) := by
      exact
        congrFun
          (congrFun
            (congrFun hdecomp (vecSingle hb (vecSum z))) z') w
    calc
      (∑ z' : ZVec n c,
          if vecSum z' = vecSum y then
            KBMap (n := n) (a := a) (b := b) (c := c) (d := d)
              B (vecSingle hb (vecSum z)) z' w
          else 0) =
          ∑ z' : ZVec n c,
            if vecSum z' = vecSum y then
              (R (vecSingle hb (vecSum z)) z').1 (vecSum w)
            else 0 := by
              refine Finset.sum_congr rfl ?_
              intro z' _
              by_cases hz' : vecSum z' = vecSum y
              · rw [if_pos hz', if_pos hz', hpoint]
              · rw [if_neg hz', if_neg hz']
      _ = (triangleLeafE6WfromB hb R y z).1 (vecSum w) := by
        unfold triangleLeafE6WfromB
        rw [if_pos hy]
        change
          (∑ z' : ZVec n c,
              if vecSum z' = vecSum y then
                (R (vecSingle hb (vecSum z)) z').1 (vecSum w)
              else 0) =
            (Submodule.subtype (ZeroSumProfile n)
              (∑ z' : ZVec n c,
                if vecSum z' = vecSum y then
                  R (vecSingle hb (vecSum z)) z'
                else 0)) (vecSum w)
        rw [map_sum]
        simp only [Finset.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro z' _
        by_cases hz' : vecSum z' = vecSum y <;> simp [hz']
  · rw [if_neg hy]
    change 0 = (triangleLeafE6WfromB hb R y z).1 (vecSum w)
    unfold triangleLeafE6WfromB
    rw [if_neg hy]
    rfl

theorem triangleLeafE6CfromB_mem_CCompat
    {n a b c d : ℕ} [NeZero n]
    (hb : 0 < b) (Y : triangleLeafBOnly n a b c d) :
    triangleLeafE6CfromB
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb Y.1.1.1 ∈
      triangleLeafCCompat n a b c d := by
  have hCzero : Y.1.1.2 = 0 := by
    have h := LinearMap.mem_ker.mp Y.2
    change Y.1.1.2 = 0 at h
    exact h
  have hKB :=
    (triangleLeafCompatibleSubmodule_carrier_iff
      (n := n) (a := a) (b := b) (c := c) (d := d) Y.1).mp Y.1.2
  rw [hCzero,
    (KCMap (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero,
    add_zero] at hKB
  rcases hKB with ⟨R, hR⟩
  have hKC :=
    triangleLeafE6KCMap_CfromB_eq_WDiffEmbed
      (n := n) (a := a) (b := b) (c := c) (d := d)
      hb Y.1.1.1 R hR.symm
  apply
    (mem_triangleLeafCCompat_iff_exists_compatibleB
      (n := n) (a := a) (b := b) (c := c) (d := d)
      (triangleLeafE6CfromB hb Y.1.1.1)).mpr
  refine ⟨0, ?_⟩
  rw [(KBMap
    (n := n) (a := a) (b := b) (c := c) (d := d)).map_zero, zero_add]
  exact ⟨triangleLeafE6WfromB hb R, hKC.symm⟩

theorem map_triangleLeafE6AlphaShearCoeff_CCompat_le_range_BOnlyBDiag
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) :
    Submodule.map
        (triangleLeafE6AlphaShearCoeff
          (n := n) (a := a) (b := b) (d := d))
        (triangleLeafCCompat n a b c d) ≤
      LinearMap.range
        (triangleLeafBOnlyBDiagMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  rintro U ⟨C, hC, rfl⟩
  rcases
      triangleLeafE6_exists_BOnly_BfromC
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hn hb2 hc C hC with
    ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  rw [triangleLeafBOnlyBDiagMap_apply, hY,
    triangleLeafE6BDiagOfB_BfromC]

theorem range_BOnlyBDiag_le_map_triangleLeafE6AlphaShearCoeff_CCompat
    {n a b c d : ℕ} [NeZero n] (hb : 0 < b) :
    LinearMap.range
        (triangleLeafBOnlyBDiagMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) ≤
      Submodule.map
        (triangleLeafE6AlphaShearCoeff
          (n := n) (a := a) (b := b) (d := d))
        (triangleLeafCCompat n a b c d) := by
  rintro U ⟨Y, rfl⟩
  refine
    ⟨triangleLeafE6CfromB
        (n := n) (a := a) (b := b) (c := c) (d := d)
        hb Y.1.1.1,
      triangleLeafE6CfromB_mem_CCompat hb Y, ?_⟩
  rw [triangleLeafBOnlyBDiagMap_apply,
    triangleLeafE6AlphaShearCoeff_CfromB]

theorem map_triangleLeafE6AlphaShearCoeff_CCompat_eq_range_BOnlyBDiag
    {n a b c d : ℕ} [NeZero n]
    (hn : Even n) (hb2 : 2 ≤ b) (hc : 0 < c) :
    Submodule.map
        (triangleLeafE6AlphaShearCoeff
          (n := n) (a := a) (b := b) (d := d))
        (triangleLeafCCompat n a b c d) =
      LinearMap.range
        (triangleLeafBOnlyBDiagMap
          (n := n) (a := a) (b := b) (c := c) (d := d)) := by
  apply le_antisymm
  · exact
      map_triangleLeafE6AlphaShearCoeff_CCompat_le_range_BOnlyBDiag
        hn hb2 hc
  · exact
      range_BOnlyBDiag_le_map_triangleLeafE6AlphaShearCoeff_CCompat
        (by omega)

end

end TriangleLeaf
end Core4loop
