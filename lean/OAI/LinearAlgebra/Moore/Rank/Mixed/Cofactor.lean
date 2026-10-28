import OAI.LinearAlgebra.Moore.Rank.Mixed.Definition

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix

/-- Inclusion-exclusion polarization of the actual Moore cofactor. The
factorial normalization makes a repeated argument the ordinary cofactor. -/
def mixedCofactor (m : ℕ)
    (A : Fin (m - 1) → Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    Matrix (Fin m) (Fin m) (Quaternion ℝ) :=
  ((m - 1).factorial : ℝ)⁻¹ •
    ∑ S : Finset (Fin (m - 1)),
      ((-1 : ℝ) ^ (m - 1 - S.card)) • mooreCofactor m (∑ i ∈ S, A i)

theorem mixedCofactor_eq_sum (m : ℕ)
    (A : Fin (m - 1) → Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    mixedCofactor m A =
      ((m - 1).factorial : ℝ)⁻¹ •
        ∑ S : Finset (Fin (m - 1)),
          ((-1 : ℝ) ^ (m - 1 - S.card)) • mooreCofactor m (∑ i ∈ S, A i) := rfl

end OAI.LinearAlgebra.Moore
