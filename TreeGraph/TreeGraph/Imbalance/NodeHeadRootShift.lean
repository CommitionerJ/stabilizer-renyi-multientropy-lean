import TreeGraph.Imbalance.NodeHeadOpenData

namespace TreeGraph
namespace Imbalance

noncomputable def headChildIndexRootShiftEquiv
    (n a : Nat) [NeZero n] (rest : List RTree) (δ : Rep n) :
    HeadChildIndex n a rest ≃ HeadChildIndex n a rest :=
  Equiv.prodCongr (Equiv.refl (Block n (a - 1)))
    (Equiv.prodCongr (Equiv.refl (CoordsList n rest))
      (Equiv.addRight δ))

noncomputable def headChildIndexRootSuccEquiv
    (n a : Nat) [NeZero n] (rest : List RTree) :
    HeadChildIndex n a rest ≃ HeadChildIndex n a rest :=
  headChildIndexRootShiftEquiv n a rest (1 : Rep n)

@[simp] theorem headChildIndexRootShiftEquiv_parentRoot
    (n a : Nat) [NeZero n] (rest : List RTree) (δ : Rep n)
    (idx : HeadChildIndex n a rest) :
    headChildIndexParentRoot
        ((headChildIndexRootShiftEquiv n a rest δ) idx) =
      headChildIndexParentRoot idx := by
  rfl

@[simp] theorem headChildIndexRootShiftEquiv_tail
    (n a : Nat) [NeZero n] (rest : List RTree) (δ : Rep n)
    (idx : HeadChildIndex n a rest) :
    headChildIndexTail
        ((headChildIndexRootShiftEquiv n a rest δ) idx) =
      headChildIndexTail idx := by
  rfl

@[simp] theorem headChildIndexRootShiftEquiv_rootDiag
    (n a : Nat) [NeZero n] (rest : List RTree) (δ : Rep n)
    (idx : HeadChildIndex n a rest) :
    headChildIndexRootDiag
        ((headChildIndexRootShiftEquiv n a rest δ) idx) =
      headChildIndexRootDiag idx + δ := by
  rfl

@[simp] theorem headChildIndexRootSuccEquiv_parentRoot
    (n a : Nat) [NeZero n] (rest : List RTree)
    (idx : HeadChildIndex n a rest) :
    headChildIndexParentRoot
        ((headChildIndexRootSuccEquiv n a rest) idx) =
      headChildIndexParentRoot idx := by
  rfl

@[simp] theorem headChildIndexRootSuccEquiv_tail
    (n a : Nat) [NeZero n] (rest : List RTree)
    (idx : HeadChildIndex n a rest) :
    headChildIndexTail
        ((headChildIndexRootSuccEquiv n a rest) idx) =
      headChildIndexTail idx := by
  rfl

@[simp] theorem headChildIndexRootSuccEquiv_rootDiag
    (n a : Nat) [NeZero n] (rest : List RTree)
    (idx : HeadChildIndex n a rest) :
    headChildIndexRootDiag
        ((headChildIndexRootSuccEquiv n a rest) idx) =
      headChildIndexRootDiag idx + 1 := by
  rfl

noncomputable def headChildOpenDataRootSuccEquiv
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree) :
    HeadChildOpenData n a C rest ≃ HeadChildOpenData n a C rest where
  toFun data := fun idx => data ((headChildIndexRootSuccEquiv n a rest) idx)
  invFun data := fun idx => data ((headChildIndexRootSuccEquiv n a rest).symm idx)
  left_inv data := by
    funext idx
    exact congrArg data ((headChildIndexRootSuccEquiv n a rest).right_inv idx)
  right_inv data := by
    funext idx
    exact congrArg data ((headChildIndexRootSuccEquiv n a rest).left_inv idx)

@[simp] theorem headChildOpenDataRootSuccEquiv_apply
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest) :
    (headChildOpenDataRootSuccEquiv n a C rest data) idx =
      data ((headChildIndexRootSuccEquiv n a rest) idx) := by
  rfl

@[simp] theorem headChildOpenDataRootSuccEquiv_apply_fst
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest) :
    ((headChildOpenDataRootSuccEquiv n a C rest data) idx).1 =
      (data ((headChildIndexRootSuccEquiv n a rest) idx)).1 := by
  rfl

@[simp] theorem headChildOpenDataRootSuccEquiv_apply_snd
    (n a : Nat) [NeZero n] (C : RTree) (rest : List RTree)
    (data : HeadChildOpenData n a C rest)
    (idx : HeadChildIndex n a rest) :
    ((headChildOpenDataRootSuccEquiv n a C rest data) idx).2 =
      (data ((headChildIndexRootSuccEquiv n a rest) idx)).2 := by
  rfl

end Imbalance
end TreeGraph
