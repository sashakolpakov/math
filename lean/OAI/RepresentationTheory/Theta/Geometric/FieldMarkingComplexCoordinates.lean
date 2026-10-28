import OAI.RepresentationTheory.Theta.Geometric.Family.ComplexCoordinates
import OAI.RepresentationTheory.Theta.Geometric.StandardComplexCoordinates

/-! # Field Marking Complex Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingComplexCoordinates

noncomputable section

/-! Any actual field marking of a family fiber acts in complex
embedding coordinates by its coefficientwise embedded field matrix. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s) (hg : g = 3 * s)
    (hdegree : Module.finrank ℚ E = 2 * s)
    (m : let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety)

def fieldMarkingCoordinates : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  exact m.trans (Family.PELCoordinates.familyPELCoordinates A ρ x s hs hg hdegree)

theorem fieldMarkingCoordinates_apply (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    fieldMarkingCoordinates A ρ x s hs hg hdegree m v = Family.PELCoordinates.familyPELCoordinates A ρ x s hs hg hdegree (m v) := rfl

theorem fieldMarking_complexCoordinates (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (τ : E →ₐ[ℚ] ℂ) :
    let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
    let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
    Family.ComplexCoordinates.familyComplexCoordinates A ρ x s hs hg hdegree ((m.restrictScalars ℚ).toLinearMap.baseChange ℂ u) τ =
      ((LinearMap.toMatrix' (fieldMarkingCoordinates A ρ x s hs hg hdegree m).toLinearMap).map τ).mulVec
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.standardRankThreeComplexCoordinates E u τ) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
  have h := AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport.rankThreeComplexCoordinates_map (LinearEquiv.refl E (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E))
    (Family.PELCoordinates.familyPELCoordinates A ρ x s hs hg hdegree) (m.restrictScalars ℚ).toLinearMap
    (fieldMarkingCoordinates A ρ x s hs hg hdegree m).toLinearMap
    (fun v => (fieldMarkingCoordinates_apply A ρ x s hs hg hdegree m v).symm) u τ
  rw [StandardComplexCoordinates.rankThreeComplexCoordinates_refl] at h
  exact h

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingComplexCoordinates
