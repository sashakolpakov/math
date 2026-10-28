import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingComplexCoordinates
import OAI.RepresentationTheory.Theta.Geometric.Family.MarkedPolarization

/-! # Field Marking Polarization -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPolarization

noncomputable section

/-! A full field marking computes the original marked polarization
form exactly in its associated field coordinates. -/

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

theorem fieldMarkingCoordinates_polarization (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Family.MarkedPolarization.familyMarkedPolarizationForm A ρ x s hs hg hdegree
      (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m v)
      (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree m w) =
        PolarizedCanonicalForm.familyPolarizationForm A x (m v) (m w) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
  let c := Family.PELCoordinates.familyPELCoordinates A ρ x s hs hg hdegree
  change PolarizedCanonicalForm.familyPolarizationForm A x (c.symm (c (m v))) (c.symm (c (m w))) = _
  rw [c.symm_apply_apply, c.symm_apply_apply]

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPolarization
