import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarCalibration
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTest

/-! # Coordinate Calibration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateCalibration.Multiplicity

noncomputable section

/-! Retain an explicitly identified rational coordinate basis in the same-test scalar calibration. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalTest.Intrinsic OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

attribute [local instance] Intrinsic.PeriodAction.Multiplicity.nativeDomainAction Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))
  (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
  (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
  (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1)
  (S : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1
    (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
    C (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))

variable {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)

include hCoord hGeometry S in
theorem retained_coordinate_rational_scalar_one
    (hCovariance : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))
    (hB : e = Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
    (T : Intrinsic.NonzeroTest.NativeThetaTest E P hP hμ v hv
      e
      he)
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (hfixed : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (maximalRealSubfield E)
      (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
      C (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v) S
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ)) (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test) =
      Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test)
    (a : ℂ)
    (ha : W.finite.action (Intrinsic.RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv
      e
      he W γ) T.test = a • T.test) :
    a = 1 := by
  subst e
  exact ScalarCalibration.Multiplicity.native_retained_rational_scalar_one E P hP hμ hs v hv B hCoord hGeometry C S W
    hCovariance T γ hfixed a ha

def retainedCoordinateCalibration
    (hCovariance : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S)
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))
    (hB : e = Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
    (T : Intrinsic.NonzeroTest.NativeThetaTest E P hP hμ v hv
      e
      he)
    (K₀ : OpenSubgroup (CM.FiniteAway.Approximation.CMFiniteSU E P hP))
    (hsource : ∀ g ∈ K₀, RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (maximalRealSubfield E)
      (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
      C (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v) S g (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test) =
        Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test) :
    RationalTest.Intrinsic.RationalTestCalibration E P hP hμ v hv e he W T.test where
  sourceLevel := K₀
  calibrated γ hγ a ha := retained_coordinate_rational_scalar_one E P hP hμ hs v hv B hCoord
    hGeometry C S W hCovariance e he hB T γ (hsource _ hγ) a ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateCalibration.Multiplicity
