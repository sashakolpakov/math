import OAI.RepresentationTheory.Theta.Geometric.Family.PELCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking

/-! # Marked Polarization -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The constructed coordinate transport preserves the literal marked
polarization forms of the actual polarized fibers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking

variable {E : Type} [Field E] [NumberField E] {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)

def Family.MarkedPolarization.familyMarkedPolarizationForm (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ] ℚ := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ y
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ y
  let c := Family.PELCoordinates.familyPELCoordinates A ρ y s hs hg hdegree
  exact (PolarizedCanonicalForm.familyPolarizationForm A y).compl₁₂ (c.symm.restrictScalars ℚ).toLinearMap
    (c.symm.restrictScalars ℚ).toLinearMap

theorem Family.MarkedPolarization.familyMarkedPolarizationForm_original (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) :
    Family.MarkedPolarization.familyMarkedPolarizationForm A ρ y s hs hg hdegree =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm (A.pullback y.left) (ρ.pullback y.left) s hs hg hdegree := rfl

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation PolarizedCanonicalForm.familyPolarizationForm Family.FieldActions.familyFieldPeriodAction Family.PELCoordinates.familyPELCoordinates

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateTransport_polarization (z : D.neighborhood) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Family.MarkedPolarization.familyMarkedPolarizationForm A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree
      (D.coordinateTransport A ρ s hs hg hdegree z v) (D.coordinateTransport A ρ s hs hg hdegree z w) =
      Family.MarkedPolarization.familyMarkedPolarizationForm A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree v w := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ (Intrinsic.FamilyFrames.familyChartParameter C z)
  let c₀ := Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree
  let c := Family.PELCoordinates.familyPELCoordinates A ρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree
  change PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C z)
    (c.symm (c (D.fieldEquiv A ρ z (c₀.symm v))))
    (c.symm (c (D.fieldEquiv A ρ z (c₀.symm w)))) =
      PolarizedCanonicalForm.familyPolarizationForm A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) (c₀.symm v) (c₀.symm w)
  rw [c.symm_apply_apply, c.symm_apply_apply, D.fieldEquiv_apply, D.fieldEquiv_apply]
  exact (D.polarization z (c₀.symm v) (c₀.symm w)).symm

end

end OAI.RepresentationTheory.Theta.Geometric
