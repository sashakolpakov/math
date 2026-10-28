import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedForm
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceFixedForm

/-! # Form Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FormCovariance.Multiplicity

noncomputable section

/-! Source fixedness of the same transported finite test gives exact
invariance of its original native cotangent theta form. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedForm.TestTransport OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
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

include hGeometry in
theorem native_retained_form_covariance
    (hCovariance : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (hfixed : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (maximalRealSubfield E)
      (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
      C (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v) S
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ)) (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B φ) =
      Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B φ)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord) φ
      (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ z.val)).comp (fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ) z.val) =
    Intrinsic.CotangentTheta.Multiplicity.nativeCotangentThetaOneForm E P hP hμ v hv
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
      (Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord) φ z.val := by
  exact SourceFixedForm.TestTransport.covector_invariance_of_scalar_comparison _ _ _ _ _
    (Intrinsic.TransportedForm.Multiplicity.nativeOneThetaFactor E P hP hμ hs v hv B hCoord)
    (Intrinsic.TransportedForm.Multiplicity.nativeOneThetaFactor_ne_zero E P hP hμ hs v hv B hCoord hGeometry)
    (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest_thetaOneForm E P hP hμ hs v hv B hCoord hGeometry φ (γ • z))
    (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest_thetaOneForm E P hP hμ hs v hv B hCoord hGeometry φ z)
    (Intrinsic.SourceFixedForm.Multiplicity.native_source_fixed_form_covariance E P hP hμ hs v hv B hGeometry C S hCovariance
      (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B φ) γ hfixed z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.FormCovariance.Multiplicity
