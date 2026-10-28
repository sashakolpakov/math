import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway

/-! # Rational Test -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTest.Intrinsic

noncomputable section

/-! A retained source level with its proved rational scalar calibration.
This interface carries the actual test and coordinates and has no prime parameter. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway.Approximation

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3))

structure RationalTestCalibration where
  sourceLevel : OpenSubgroup (CM.FiniteAway.Approximation.CMFiniteSU E P hP)
  calibrated : ∀ γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b, CM.FiniteAway.Approximation.cmRationalFiniteSU E P hP γ ∈ sourceLevel → ∀ a : ℂ,
    W.finite.action (Intrinsic.RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv e he W γ) φ = a • φ → a = 1

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTest.Intrinsic
