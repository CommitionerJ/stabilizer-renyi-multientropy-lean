import Core4loop.Arithmetic

namespace Core4loop

inductive CoreGraph where
  | triangleLeaf
  | square
  | squareDiagonal
  | complete
  deriving DecidableEq, Fintype, Repr

open CoreGraph

def disc (G : CoreGraph) (x y z t : F) : F :=
  match G with
  | .triangleLeaf => x * y + y * z + z * x + x * t
  | .square => x * y + y * z + z * t + x * t
  | .squareDiagonal => x * y + y * z + z * t + x * t + x * z
  | .complete => x * y + x * z + x * t + y * z + y * t + z * t

end Core4loop
