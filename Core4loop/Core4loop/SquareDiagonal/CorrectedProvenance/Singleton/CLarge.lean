import Core4loop.TriangleLeaf.CorrectedExponent
import Core4loop.SquareDiagonal.CorrectedProvenance.Definitions

set_option autoImplicit false
set_option warningAsError true

namespace Core4loop

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_one_d_one
    {n c : Nat}
    (hn : Even n) (hc2 : 2 ≤ c) :
    X1CorrectedZ 1 1 1 c n =
      X3PaperOldZ 1 1 c 1 n +
        DiamondCorrectionZ n 1 1 c 1 := by
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ, hn, hc2,
    pow_add, pow_one]
  ring

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_one_d_ge_two
    {n c d : Nat}
    (hn : Even n) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    X1CorrectedZ 1 1 d c n =
      X3PaperOldZ 1 1 c d n +
        DiamondCorrectionZ n 1 1 c d := by
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ, hn, hc2, hd2,
    pow_add, pow_one]
  ring

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_one
    {n b c : Nat}
    (hn : Even n) (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) :
    X1CorrectedZ 1 b 1 c n =
      X3PaperOldZ 1 b c 1 n +
        DiamondCorrectionZ n 1 b c 1 := by
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ, hn, hb2, hc2,
    pow_add, pow_one]
  ring

theorem X1CorrectedZ_relabel_eq_old_add_correction_of_even_c_ge_two_b_ge_two_d_ge_two
    {n b c d : Nat}
    (hn : Even n)
    (hb2 : 2 ≤ b) (hc2 : 2 ≤ c) (hd2 : 2 ≤ d) :
    X1CorrectedZ 1 b d c n =
      X3PaperOldZ 1 b c d n +
        DiamondCorrectionZ n 1 b c d := by
  have hcne : c ≠ 1 := by omega
  have hcplus : 2 ≤ 1 + c := by omega
  simp [X1CorrectedZ, X1PaperOldZ, TriangleLeafCorrectionZ,
    TriangleLeafExceptional, X3PaperOldZ, X3Z,
    DiamondCorrectionZ, DiamondOverlapKappaZ, ThetaZ,
    Sigma1Z, Sigma2_1Z, Sigma2_3Z, nPowZ, mZ,
    hn, hb2, hc2, hd2, hcne, hcplus,
    pow_add, pow_one]
  ring

end Core4loop
