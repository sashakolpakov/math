import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientCoordinates
import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicPeriodHodge
import OAI.AlgebraicGeometry.PELModuli.CMPoints.TypeTransport

/-! # Intrinsic Coefficient Realization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientRealization

noncomputable section

/-! The coefficient Hodge structure obtained from the original native
periods is realized on that same abelian variety's actual H1. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)

def nativeCoefficientHodgeStructure : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Fin 3 → E) :=
  (AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).transport
    (IntrinsicCoefficientCoordinates.nativeRationalCoefficientCoordinates A ρ s hs hg hdegree)

def nativeCoefficientRealization : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (nativeCoefficientHodgeStructure A ρ s hs hg hdegree) :=
  TypeTransport.hodgeRealizationAlongEquiv (IntrinsicCoefficientCoordinates.nativeRationalCoefficientCoordinates A ρ s hs hg hdegree).symm
    ((AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).transport_symm_isHodgeMap _)
    ((AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))).transport_isHodgeMap _)
    (IntrinsicPeriodHodge.nativePeriodH1Realization (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))
      (AbelianModuli.ReferenceFamily.Intrinsic.PeriodPolarization.nativePeriodPolarization (AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A))
        (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle A) (AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.polarizationLineBundle_ample A)))

theorem nativeCoefficientRealization_abelianVariety :
    (nativeCoefficientRealization A ρ s hs hg hdegree).abelianVariety =
      AbelianModuli.ReferenceFamily.Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation A) := rfl

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicCoefficientRealization
