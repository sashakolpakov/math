import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CoordinateTransform
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoefficientTransformations

/-! # Evaluation Coordinate Transform -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EvaluationCoordinateTransform

noncomputable section

/-! The contragredient coefficient change transforms every actual
linear evaluation of the section family by the prescribed point map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type v} [Fintype ι]
variable (c : R →+* Γ(X, ⊤)) (M : X.Modules)

theorem transformedSectionEvaluation
    (s : ι → (Line.Bundles.structureModule X ⟶ M))
    (ev : (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor c).obj M →ₗ[R] R)
    (T : (ι → R) ≃ₗ[R] (ι → R)) (i : ι) :
    ev (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M
      (CoefficientTransformations.transformSectionFamily c M s (HilbertConstruction.Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap i)) =
        T (fun j => ev (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M (s j))) i := by
  let φ : Module.Dual R (ι →₀ R) := ev.comp (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s)
  have hv : (Finsupp.llift R R R ι).symm φ =
      (fun j => ev (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M (s j))) := by
    funext j
    change ev (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s (Finsupp.single j 1)) = _
    rw [Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_single]
  change ev (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv c M
    (CoefficientTransformations.coefficientSectionCombination c M s
      (HilbertConstruction.Dual.CoordinateTransform.pointCoordinateCoefficientTransform T (Finsupp.single i 1)))) = _
  rw [CoefficientTransformations.coefficientSectionCombination_value]
  change φ (HilbertConstruction.Dual.CoordinateTransform.pointCoordinateCoefficientTransform T (Finsupp.single i 1)) = _
  have h := HilbertConstruction.Dual.CoordinateTransform.pointCoordinateCoefficientTransform_values T ((Finsupp.llift R R R ι).symm φ) i
  rw [LinearEquiv.apply_symm_apply, hv] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EvaluationCoordinateTransform
