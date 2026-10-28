import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FormCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CotangentCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest

/-! # Scalar Calibration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarCalibration.Multiplicity

noncomputable section

/-! The same normalized nonzero theta form calibrates a rational finite scalar to one. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
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

include hGeometry in
theorem native_retained_rational_scalar_one
    (hCovariance : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S)
    (T : Intrinsic.NonzeroTest.NativeThetaTest E P hP hμ v hv
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord))
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (hfixed : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (maximalRealSubfield E)
      (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
      C (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v) S
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ)) (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test) =
      Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test)
    (a : ℂ)
    (ha : W.finite.action (Intrinsic.RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord) W γ) T.test = a • T.test) :
    a = 1 := by
  let e := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let he := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord
  let z := Intrinsic.PeriodDomain.Multiplicity.nativeOrigin E P hP
  let w : Fin 2 → ℂ := Pi.single 0 1
  have hsource := FormCovariance.Multiplicity.native_retained_form_covariance E P hP hμ hs v hv B hCoord hGeometry C S
    hCovariance T.test γ hfixed z
  have hsourceValue := congrArg (fun L : (Fin 2 → ℂ) →L[ℂ] ℂ => L w) hsource
  have hsourceOne : Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he T.test
      (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ z.val) (fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ) z.val w) = 1 :=
    hsourceValue.trans T.value
  have hnative := Intrinsic.CotangentCovariance.nativeCotangentTheta_covariance E P hP hμ v hv e he W γ T.test z
  rw [ha, map_smul] at hnative
  have hn := congrArg (fun L : (Fin 2 → ℂ) →L[ℂ] ℂ => L w) hnative
  change a * Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he T.test
      (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ z.val) (fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ) z.val w) =
    Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv e he T.test z.val w at hn
  rw [hsourceOne, mul_one] at hn
  exact hn.trans T.value

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarCalibration.Multiplicity
