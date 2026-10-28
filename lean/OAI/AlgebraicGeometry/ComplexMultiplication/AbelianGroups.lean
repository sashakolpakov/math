import OAI.AlgebraicGeometry.ComplexMultiplication.IntegralProducts
import OAI.AlgebraicGeometry.ComplexMultiplication.RationalGroupEndomorphisms
import Mathlib.AlgebraicGeometry.Group.Abelian
import OAI.AlgebraicGeometry.Foundations.ProjectiveSpaceIs
import Mathlib.NumberTheory.NumberField.CMField

/-! # Abelian Groups -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.AbelianGroups

noncomputable section

/-! # Commutativity from the original geometric assumptions

The group law remains the given algebraic group law. Commutativity is proved,
so constructing its endomorphism ring requires no additional hypothesis.
-/

open _root_.CategoryTheory MonoidalCategory _root_.AlgebraicGeometry

universe u

/-- A proper integral group scheme over an algebraically closed field is commutative. -/
theorem properIntegralGroup_commutative {K : Type u} [Field K] [IsAlgClosed K]
    (X : Over (Spec (.of K))) [IsIntegral X.left] [IsProper X.hom] [GrpObj X] :
    IsCommMonObj X := by
  have : IsIntegral (X ⊗ X).left := IntegralProducts.integralSchemeProduct X.hom X.hom
  exact isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed X

/-- The original projective-group assumptions supply the needed commutativity. -/
instance abelianVariety_commutative (X : Over (Spec (.of ℂ)))
    [IsIntegral X.left] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X] : IsCommMonObj X :=
  properIntegralGroup_commutative X

/-- The actual rational algebraic group-endomorphism algebra under the original assumptions. -/
abbrev abelianVarietyEnd0 (X : Over (Spec (.of ℂ)))
    [IsIntegral X.left] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X] := RationalGroupEndomorphisms.RationalGroupEndomorphism X

end

end OAI.AlgebraicGeometry.ComplexMultiplication.AbelianGroups
