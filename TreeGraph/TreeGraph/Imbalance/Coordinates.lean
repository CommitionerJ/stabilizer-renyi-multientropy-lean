import TreeGraph.Imbalance.Projection

namespace TreeGraph
namespace Imbalance

mutual
  def Cplus (n : Nat) : RTree → Type
    | RTree.node a cs => Block n a × CoordsList n cs

  def CoordsList (n : Nat) : List RTree → Type
    | [] => PUnit
    | c :: cs => Cplus n c × CoordsList n cs
end

def Copen (n : Nat) : RTree → Type
  | RTree.node _ cs => CoordsList n cs

@[simp] theorem Cplus_node (n a : Nat) (cs : List RTree) :
    Cplus n (RTree.node a cs) = (Block n a × CoordsList n cs) := rfl

@[simp] theorem CoordsList_nil (n : Nat) :
    CoordsList n [] = PUnit := rfl

@[simp] theorem CoordsList_cons (n : Nat) (c : RTree) (cs : List RTree) :
    CoordsList n (c :: cs) = (Cplus n c × CoordsList n cs) := rfl

@[simp] theorem Copen_node (n a : Nat) (cs : List RTree) :
    Copen n (RTree.node a cs) = CoordsList n cs := rfl

mutual
  noncomputable instance fintypeCplus (n : Nat) [NeZero n] :
      (T : RTree) → Fintype (Cplus n T)
    | RTree.node a cs => by
        dsimp [Cplus]
        letI : Fintype (CoordsList n cs) := fintypeCoordsList n cs
        infer_instance

  noncomputable instance fintypeCoordsList (n : Nat) [NeZero n] :
      (cs : List RTree) → Fintype (CoordsList n cs)
    | [] => by
        dsimp [CoordsList]
        infer_instance
    | c :: cs => by
        dsimp [CoordsList]
        letI : Fintype (Cplus n c) := fintypeCplus n c
        letI : Fintype (CoordsList n cs) := fintypeCoordsList n cs
        infer_instance
end

noncomputable instance fintypeCopen (n : Nat) [NeZero n] (T : RTree) :
    Fintype (Copen n T) := by
  cases T with
  | node a cs =>
      dsimp [Copen]
      infer_instance

mutual
  theorem card_Cplus (n : Nat) [NeZero n] :
      (T : RTree) → Fintype.card (Cplus n T) = n ^ RTree.totalWeight T
    | RTree.node a cs => by
        dsimp [Cplus]
        calc
          Fintype.card (Block n a × CoordsList n cs) =
              Fintype.card (Block n a) * Fintype.card (CoordsList n cs) :=
            Fintype.card_prod (Block n a) (CoordsList n cs)
          _ = n ^ a * n ^ (cs.map RTree.totalWeight).sum := by
            rw [card_Block, card_CoordsList n cs]
          _ = n ^ (a + (cs.map RTree.totalWeight).sum) := by
            rw [Nat.pow_add]
          _ = n ^ (RTree.node a cs).totalWeight := by
            simp [RTree.totalWeight]

  theorem card_CoordsList (n : Nat) [NeZero n] :
      (cs : List RTree) →
        Fintype.card (CoordsList n cs) =
          n ^ (cs.map RTree.totalWeight).sum
    | [] => by
        simp [CoordsList]
    | c :: cs => by
        change Fintype.card (Cplus n c × CoordsList n cs) =
          n ^ (RTree.totalWeight c + (cs.map RTree.totalWeight).sum)
        calc
          Fintype.card (Cplus n c × CoordsList n cs) =
              Fintype.card (Cplus n c) * Fintype.card (CoordsList n cs) :=
            Fintype.card_prod (Cplus n c) (CoordsList n cs)
          _ = n ^ RTree.totalWeight c *
                n ^ (cs.map RTree.totalWeight).sum := by
            rw [card_Cplus n c, card_CoordsList n cs]
          _ = n ^ (RTree.totalWeight c + (cs.map RTree.totalWeight).sum) := by
            rw [Nat.pow_add]
end

theorem card_Copen (n : Nat) [NeZero n] (a : Nat) (cs : List RTree) :
    Fintype.card (Copen n (RTree.node a cs)) =
      n ^ (cs.map RTree.totalWeight).sum := by
  change Fintype.card (CoordsList n cs) = n ^ (cs.map RTree.totalWeight).sum
  exact card_CoordsList n cs

theorem Cplus_eq_root_open (n : Nat) (T : RTree) :
    Cplus n T = (Block n T.rootWeight × Copen n T) := by
  cases T with
  | node a cs =>
      rfl

end Imbalance
end TreeGraph
