import OAI.AlgebraicGeometry.SheafCohomology.Projective.DominantFunctionField
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteFlatChartModule
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormalSectionsIn
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-! # Finite Function Field -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteFunctionField.Dimension

noncomputable section

/-! The actual function-field extension of a finite dominant map is finite, with compatible affine scalar towers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

@[instance_reducible]
def dominantSectionFunctionFieldAlgebra (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] : Algebra Γ(Y, U) X.functionField :=
  ((DominantFunctionField.Dimension.dominantFunctionFieldMap f).hom.comp (Y.germToFunctionField U).hom).toAlgebra

theorem dominantSectionFunctionField_tower (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] :
    letI := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
    letI := dominantSectionFunctionFieldAlgebra f U
    IsScalarTower Γ(Y, U) Y.functionField X.functionField := by
  let := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
  let := dominantSectionFunctionFieldAlgebra f U
  apply IsScalarTower.of_algebraMap_eq'
  rfl

theorem dominantPreimageSectionFunctionField_tower (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    letI := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
    letI := dominantSectionFunctionFieldAlgebra f U
    IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField := by
  let := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
  let := dominantSectionFunctionFieldAlgebra f U
  apply IsScalarTower.of_algebraMap_eq'
  exact congrArg CommRingCat.Hom.hom (DominantFunctionField.Dimension.dominantFunctionFieldMap_germ f U)

theorem finite_dominant_functionField_finite
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    letI := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
    Module.Finite Y.functionField X.functionField := by
  let := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
  let := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
  let := dominantSectionFunctionFieldAlgebra f U
  have := dominantSectionFunctionField_tower f U
  have := dominantPreimageSectionFunctionField_tower f U
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  have := FiniteFlatChartModule.Dimension.affinePreimageSectionModule_finite f U hU
  have := Quotients.FiniteDescent.NormalSectionsIn.Construction.NormalSections.affine hX (f ⁻¹ᵁ U) (hU.preimage f)
  have : IsIntegralClosure Γ(X, f ⁻¹ᵁ U) Γ(Y, U) X.functionField :=
    IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have : Algebra.IsAlgebraic Y.functionField X.functionField :=
    isAlgebraic_of_isFractionRing Γ(Y, U) Γ(X, f ⁻¹ᵁ U) Y.functionField X.functionField
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ U) (nonZeroDivisors Γ(Y, U)))
      X.functionField :=
    IsIntegralClosure.isLocalization Γ(Y, U) Y.functionField X.functionField Γ(X, f ⁻¹ᵁ U)
  exact Module.Finite.of_isLocalization Γ(Y, U) Γ(X, f ⁻¹ᵁ U) (nonZeroDivisors Γ(Y, U))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteFunctionField.Dimension
