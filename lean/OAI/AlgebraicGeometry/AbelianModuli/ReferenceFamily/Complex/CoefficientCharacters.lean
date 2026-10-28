import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientDerivationMapSemilinear
import Mathlib.Basic.Complex.Basic

/-! # Coefficient Characters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientCharacters.ComplexCoefficientCharacter

noncomputable section

/-! An actual complex character of the coefficient algebra induces
the corresponding chart point and a coefficient-algebra homomorphism. -/

variable (B C : Type) [CommRing B] [CommRing C] [Algebra ℂ B] [Algebra ℂ C]
    [Algebra B C] [IsScalarTower ℂ B C] (q : C →ₐ[ℂ] ℂ)

abbrev algebra : Algebra B ℂ := (q.comp (IsScalarTower.toAlgHom ℂ B C)).toRingHom.toAlgebra

theorem scalarTower :
    letI := algebra B C q
    IsScalarTower ℂ B ℂ := by
  let := algebra B C q
  exact IsScalarTower.of_algebraMap_eq (fun r => (q.comp (IsScalarTower.toAlgHom ℂ B C)).commutes r |>.symm)

def map :
    letI := algebra B C q
    C →ₐ[B] ℂ := by
  let := algebra B C q
  exact { toRingHom := q.toRingHom, commutes' := fun _ => rfl }

theorem map_apply (c : C) :
    letI := algebra B C q
    map B C q c = q c := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientCharacters.ComplexCoefficientCharacter
