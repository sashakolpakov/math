import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization

/-! # Hermitian Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.HermitianTransport.IntrinsicHermitianMarking

noncomputable section

/-! An isometry between the reconstructed Hermitian matrices preserves
the actual rational polarization forms under the constructed period
markings. This follows from the exact field-trace reconstruction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hρ : ActionData.RosatiConjugation A ρ) (hσ : ActionData.RosatiConjugation B σ)
    (ξ : E) (hξ : ξ ≠ 0) (u : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)

include hξ in
theorem markedHermitian_isometry_preserves_markedForm
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B σ s hs hg hdegree hσ ξ) (u x) (u y) =
        Datum.RankThreePELDatum.matrixHermitian (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y)
    (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm B σ s hs hg hdegree (u x) (u y) =
      Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm A ρ s hs hg hdegree x y := by
  have ht := congrArg (fun z : E => Algebra.trace ℚ E (ξ * z)) (hu x y)
  exact (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_trace B σ s hs hg hdegree hσ ξ hξ (u x) (u y)).symm.trans
    (ht.trans (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_trace A ρ s hs hg hdegree hρ ξ hξ x y))

include hξ in
theorem markedHermitian_isometry_preserves_polarization
    (hu : ∀ x y, Datum.RankThreePELDatum.matrixHermitian
      (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix B σ s hs hg hdegree hσ ξ) (u x) (u y) =
        Datum.RankThreePELDatum.matrixHermitian (Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A ρ s hs hg hdegree hρ ξ) x y)
    (v w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (Abelian.IntrinsicAdapter.AbelianIntrinsicAdapter.native A.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A))) :
    Intrinsic.ChernPairing.nativePolarizationForm B
      (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
        (Polarized.Projectivity.polarizedNativeProjectivePresentation B) ρ σ s hs hg hdegree u v)
      (PeriodTransport.IntrinsicPELMarking.markedPeriodTransport A.abelian B.abelian (Polarized.Projectivity.polarizedNativeProjectivePresentation A)
        (Polarized.Projectivity.polarizedNativeProjectivePresentation B) ρ σ s hs hg hdegree u w) =
      Intrinsic.ChernPairing.nativePolarizationForm A v w := by
  let PA := Polarized.Projectivity.polarizedNativeProjectivePresentation A
  let PB := Polarized.Projectivity.polarizedNativeProjectivePresentation B
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule A.abelian PA ρ
  let := Intrinsic.NumberFieldAction.IntrinsicNumberFieldAction.fieldModule B.abelian PB σ
  let cA := Intrinsic.PELMarking.IntrinsicPELMarking.coordinates A.abelian PA ρ s hs hg hdegree
  let cB := Intrinsic.PELMarking.IntrinsicPELMarking.coordinates B.abelian PB σ s hs hg hdegree
  have h := markedHermitian_isometry_preserves_markedForm A B ρ σ s hs hg hdegree
    hρ hσ ξ hξ u hu (cA v) (cA w)
  change Intrinsic.ChernPairing.nativePolarizationForm B (cB.symm (u (cA v))) (cB.symm (u (cA w))) =
    Intrinsic.ChernPairing.nativePolarizationForm A (cA.symm (cA v)) (cA.symm (cA w)) at h
  rw [cA.symm_apply_apply, cA.symm_apply_apply] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.HermitianTransport.IntrinsicHermitianMarking
