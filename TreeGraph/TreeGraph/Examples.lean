import TreeGraph.MainTheorem

namespace TreeGraph

def vertex1 (a : Nat) : RTree := RTree.node a []

theorem Xpoly_vertex1 (n a : Nat) : Xpoly n (vertex1 a) = 1 := by
  simp [vertex1]

def edgeTree (a b : Nat) : RTree :=
  RTree.node a [RTree.node b []]

def core3Star (a b c : Nat) : RTree :=
  RTree.node a [RTree.node b [], RTree.node c []]

def star4 (a b c d : Nat) : RTree :=
  RTree.node a [RTree.node b [], RTree.node c [], RTree.node d []]

def path4 (a b c d : Nat) : RTree :=
  RTree.node a [RTree.node b [RTree.node c [RTree.node d []]]]

theorem Xpoly_edgeTree (n a b : Nat) :
    Xpoly n (edgeTree a b) =
      (n : ℤ)^a + (n : ℤ)^b - ((n : ℤ) - 1) := by
  simp [edgeTree, Xpoly, Ypoly, childContribSum, RTree.totalWeight, nZ, tZ]
  ring_nf

theorem Xpoly_core3Star (n a b c : Nat) :
    Xpoly n (core3Star a b c) =
      (n : ℤ)^(a+b) + (n : ℤ)^(a+c) + (n : ℤ)^(b+c)
      - ((n : ℤ)-1) * ((n : ℤ)^b + (n : ℤ)^c)
      + ((n : ℤ)-1)^2 := by
  simp [core3Star, Xpoly, Ypoly, childContribSum, RTree.totalWeight, nZ, tZ, pow_add]
  ring_nf

theorem Xpoly_star4 (n a b c d : Nat) :
    Xpoly n (star4 a b c d) =
      (n : ℤ)^(b+c+d) + (n : ℤ)^(a+c+d) + (n : ℤ)^(a+b+d) + (n : ℤ)^(a+b+c)
      - ((n : ℤ)-1) * ((n : ℤ)^(b+c) + (n : ℤ)^(b+d) + (n : ℤ)^(c+d))
      + ((n : ℤ)-1)^2 * ((n : ℤ)^b + (n : ℤ)^c + (n : ℤ)^d)
      - ((n : ℤ)-1)^3 := by
  simp [star4, Xpoly, Ypoly, childContribSum, RTree.totalWeight, nZ, tZ, pow_add]
  ring_nf

theorem Xpoly_path4 (n a b c d : Nat) :
    Xpoly n (path4 a b c d) =
      (n : ℤ)^(b+c+d) + (n : ℤ)^(a+c+d) + (n : ℤ)^(a+b+d) + (n : ℤ)^(a+b+c)
      - ((n : ℤ)-1) * ((n : ℤ)^(c+d) + (n : ℤ)^(a+d) + (n : ℤ)^(a+b))
      + ((n : ℤ)-1)^2 * ((n : ℤ)^a + (n : ℤ)^d)
      - ((n : ℤ)-1)^3 := by
  simp [path4, Xpoly, Ypoly, childContribSum, RTree.totalWeight, nZ, tZ, pow_add]
  ring_nf

end TreeGraph
