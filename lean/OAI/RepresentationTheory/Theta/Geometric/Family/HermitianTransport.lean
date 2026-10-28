import OAI.RepresentationTheory.Theta.Geometric.Family.MarkedPolarization
import OAI.RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

/-! # Hermitian Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The same constructed period transport is an exact isometry between
the original fibers' reconstructed Hermitian forms. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RosatiBaseChange

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)

def Family.HermitianTransport.familyHermitianMatrix (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (s : ℕ) (hs : 0 < s)
    (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s) (ξ : E) : Matrix (Fin 3) (Fin 3) E :=
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix (A.pullback y.left) (ρ.pullback y.left) s hs hg hdegree
    (hρ.pullback A ρ y.left) ξ

attribute [local irreducible] Family.MarkedPolarization.familyMarkedPolarizationForm

variable {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.coordinateTransport_hermitian (z : D.neighborhood) (ξ : E) (hξ : ξ ≠ 0) (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian
      (Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C z) s hs hg hdegree ξ)
      (D.coordinateTransport A ρ s hs hg hdegree z v) (D.coordinateTransport A ρ s hs hg hdegree z w) =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian
        (Family.HermitianTransport.familyHermitianMatrix A ρ hρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)) s hs hg hdegree ξ) v w := by
  apply MarkedPolarizationIsometry.markedPolarization_isometry_hermitian
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)).left)
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)).left)
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left) s hs hg hdegree
    (hρ.pullback A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)).left)
    (hρ.pullback A ρ (Intrinsic.FamilyFrames.familyChartParameter C z).left) ξ hξ
    (D.coordinateTransport A ρ s hs hg hdegree z)
  intro a b
  rw [← Family.MarkedPolarization.familyMarkedPolarizationForm_original A ρ (Intrinsic.FamilyFrames.familyChartParameter C z),
    ← Family.MarkedPolarization.familyMarkedPolarizationForm_original A ρ (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))]
  exact D.coordinateTransport_polarization A ρ s hs hg hdegree z a b

end

end OAI.RepresentationTheory.Theta.Geometric
