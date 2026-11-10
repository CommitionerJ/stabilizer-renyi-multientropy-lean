import Core4loop.TriangleLeaf.CorrectedExponent
import Core4loop.SquareDiagonal.CorrectedProvenance.Definitions

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_one_d_one
    {n : Nat}
    (hn : Even n) :
    X1CorrectedZ 1 1 1 1 n =
      X3PaperOldZ 1 1 1 1 n +
        DiamondCorrectionZ n 1 1 1 1 := by
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ, hn]
  ring

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_one_d_ge_two
    {n d : Nat}
    (hn : Even n) (hd2 : 2 ≤ d) :
    X1CorrectedZ 1 1 d 1 n =
      X3PaperOldZ 1 1 1 d n +
        DiamondCorrectionZ n 1 1 1 d := by
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ, hn, hd2,
    pow_add, pow_one]
  ring

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_ge_two_d_one
    {n b : Nat}
    (hn : Even n) (hb2 : 2 ≤ b) :
    X1CorrectedZ 1 b 1 1 n =
      X3PaperOldZ 1 b 1 1 n +
        DiamondCorrectionZ n 1 b 1 1 := by
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ, hn, hb2,
    pow_add, pow_one]
  ring

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_one_b_ge_two_d_ge_two
    {n b d : Nat}
    (hn : Even n)
    (hb2 : 2 ≤ b) (hd2 : 2 ≤ d) :
    X1CorrectedZ 1 b d 1 n =
      X3PaperOldZ 1 b 1 d n +
        DiamondCorrectionZ n 1 b 1 d := by
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ, hn, hb2, hd2,
    pow_add, pow_one]
  ring

end Core4loop
