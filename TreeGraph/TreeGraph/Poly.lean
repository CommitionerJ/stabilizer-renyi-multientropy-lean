import TreeGraph.RTree

namespace TreeGraph

abbrev nZ (n : Nat) : ℤ := (n : ℤ)
abbrev tZ (n : Nat) : ℤ := (n : ℤ) - 1

mutual
  noncomputable def Ypoly (n : Nat) : RTree → ℤ
    | RTree.node _ cs =>
        (cs.map (fun C =>
          (nZ n) ^ (RTree.totalWeight C) - (tZ n) * Ypoly n C)).prod

  noncomputable def Xpoly (n : Nat) : RTree → ℤ
    | RTree.node a cs =>
        Ypoly n (RTree.node a cs) + childContribSum n a cs 0

  noncomputable def childContribSum (n : Nat) (a : Nat) : List RTree → Nat → ℤ
    | [], _ => 0
    | C :: rest, left =>
        let right := (rest.map RTree.totalWeight).sum
        let shift := a + left + right
        (nZ n) ^ shift * Xpoly n C
          + childContribSum n a rest (left + RTree.totalWeight C)
end

@[simp] theorem Ypoly_leaf (n a : Nat) :
    Ypoly n (RTree.node a []) = 1 := by
  simp [Ypoly]

@[simp] theorem childContribSum_nil (n a left : Nat) :
    childContribSum n a [] left = 0 := by
  simp [childContribSum]

@[simp] theorem Xpoly_leaf (n a : Nat) :
    Xpoly n (RTree.node a []) = 1 := by
  simp [Xpoly, childContribSum]

end TreeGraph
