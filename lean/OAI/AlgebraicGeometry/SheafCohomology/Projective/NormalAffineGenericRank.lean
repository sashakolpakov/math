import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteFunctionField
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.Localization.BaseChange

/-! # Normal Affine Generic Rank -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalAffineGenericRank.Dimension

noncomputable section

/-! The generic rank of actual affine finite pushforward sections is the function-field degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem dominant_affineSection_injective (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    Function.Injective (f.app U) := by
  intro a b hab
  apply Y.germToFunctionField_injective U
  apply (DominantFunctionField.Dimension.dominantFunctionFieldMap f).hom.injective
  have h := DominantFunctionField.Dimension.dominantFunctionFieldMap_germ f U
  have ha := ConcreteCategory.congr_hom h a
  have hb := ConcreteCategory.congr_hom h b
  exact ha.trans ((congrArg (X.germToFunctionField (f ⁻¹ᵁ U)) hab).trans hb.symm)

theorem affinePreimageSectionModule_torsionFree (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    letI := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
    Module.IsTorsionFree Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
  refine ⟨fun r hr => ?_⟩
  have hne : f.app U r ≠ 0 := by
    intro h
    apply (isRegular_iff_ne_zero.mp hr)
    apply dominant_affineSection_injective f U
    exact h.trans (map_zero (f.app U).hom).symm
  intro x y hxy
  exact mul_left_cancel₀ hne hxy

def finiteNormalAffineFunctionFieldIso
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    letI := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
    letI := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
    Y.functionField ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U) ≃ₗ[Y.functionField] X.functionField := by
  let := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
  let := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
  let := FiniteFunctionField.Dimension.dominantSectionFunctionFieldAlgebra f U
  have := FiniteFunctionField.Dimension.dominantSectionFunctionField_tower f U
  have := FiniteFunctionField.Dimension.dominantPreimageSectionFunctionField_tower f U
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
  exact (IsLocalizedModule.isBaseChange (nonZeroDivisors Γ(Y, U)) Y.functionField
    (IsScalarTower.toAlgHom Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField).toLinearMap).equiv

theorem affinePreimageSectionModule_genericRank
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    letI := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
    letI := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
    Module.finrank Y.functionField (Y.functionField ⊗[Γ(Y, U)] Γ(X, f ⁻¹ᵁ U)) =
      Module.finrank Y.functionField X.functionField := by
  let := DominantFunctionField.Dimension.dominantFunctionFieldAlgebra f
  let := FiniteFlatChartModule.Dimension.affinePreimageSectionAlgebra f U
  exact (finiteNormalAffineFunctionFieldIso f hX U hU).finrank_eq

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalAffineGenericRank.Dimension
