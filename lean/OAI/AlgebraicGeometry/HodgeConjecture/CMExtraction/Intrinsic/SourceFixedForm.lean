import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SourceFixedForm
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallAction

/-! # Source Fixed Form -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceFixedForm.Multiplicity

noncomputable section

/-! Express exact source-form covariance in the original native ball coordinates. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SourceFixedForm.TestTransport OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

attribute [local instance] PeriodAction.Multiplicity.nativeDomainAction Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))
  (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
  (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
  (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1)
  (S : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1
    (OneTheta.Multiplicity.nativeOneHermitian E P hP) (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
    C (OneTheta.Multiplicity.nativeOneFrames E P hP v))

include hGeometry in
theorem native_source_fixed_form_covariance
    (hCovariance : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B (OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S)
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield E) (3 * 1))
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (hfixed : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (maximalRealSubfield E)
      (OneTheta.Multiplicity.nativeOneHermitian E P hP) (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
      C (OneTheta.Multiplicity.nativeOneFrames E P hP v) S
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ)) f = f)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ (γ • z))).comp
      (fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ) z.val) =
        RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B f (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z) := by
  have ht := SourceFixedForm.TestTransport.source_fixed_form_covariance B (OneTheta.Multiplicity.nativeOneFrames E P hP v)
    (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S hGeometry hCovariance
    (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ) f hfixed (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z)
  rw [OneBallAction.Multiplicity.nativeOneBallPoint_action E P hP hμ hs v hv B hGeometry,
    OneBallAction.Multiplicity.nativeOneBallPoint_derivative E P hP hμ hs v hv B hGeometry] at ht
  exact ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceFixedForm.Multiplicity
