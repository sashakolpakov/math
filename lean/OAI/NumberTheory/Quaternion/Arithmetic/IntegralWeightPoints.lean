import OAI.NumberTheory.Quaternion.Arithmetic.MappedWeightCurves
import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm
import OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedWeightCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.BaseChange

/-! # Integral Weight Points -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntegralWeightPoints

noncomputable section

/-! Integer-weight infinitesimal directions over a coefficient field
give actual points of the original algebraic group over that field. -/

open scoped Classical
open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E] {n : ℕ}

def integralWeightPoint (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (m : Fin n → ℤ)
    (h : MappedWeightCurves.integerWeightMatrix B m ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)))
    (u : Eˣ) : G.Points (algebraMap F E) := by
  let hsum := ArithmeticGroups.Lattices.ConjugatedWeightCoordinates.Construction.conjugated_integer_diagonal_trace_zero_weights
    (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)) B m h
  refine ⟨B * ArithmeticGroups.Lattices.DiagonalWeightIntegration.Construction.diagonalWeightSL E m hsum u * B⁻¹, ?_⟩
  have hp := ArithmeticGroups.Lattices.ConjugatedWeightCoordinates.Construction.conjugate_diagonalWeightSL_mem_group (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E))
    B m hsum h (RingHom.id E) u
  have hB : SpecialLinearGroup.map (RingHom.id E) B = B := by ext i j; rfl
  simpa only [hB, ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange, RingHom.id_comp] using hp

theorem integralWeightPoint_matrix (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (B : ArithmeticGroups.Lattices.Algebraic.SL n E) (m : Fin n → ℤ)
    (h : MappedWeightCurves.integerWeightMatrix B m ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer (ArithmeticGroups.Lattices.BaseChange.Construction.matrixGroupBaseChange G (algebraMap F E)))
    (u : Eˣ) :
    PolynomialGaloisNorm.matrixPointsHom G (algebraMap F E) (integralWeightPoint G B m h u) =
      (B : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i => ((u ^ m i : Eˣ) : E)) *
        ((B⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n E) : Matrix (Fin n) (Fin n) E) := rfl

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntegralWeightPoints
