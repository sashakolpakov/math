import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicOne

/-! # One Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneTheta.Multiplicity

noncomputable section

/-! The full one-line AdelicTheta/ThetaOneForms construction for the actual native PEL
coefficients. All arithmetic signatures and global/local frames are
constructed. The comparison and theta clauses use the same witnesses. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneTheta.Quadratic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem nativeOneDeltaImaginary : IsCMField.complexConj E P.imaginaryScalar = -P.imaginaryScalar :=
  hP.2.2.2.2.2.2.2.1

include hP in
theorem nativeOneDeltaNonzero : P.imaginaryScalar ≠ 0 := hP.2.2.2.2.2.2.1

variable [IsGalois ℚ E]
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s)
  (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

def nativeOneParameter : maximalRealSubfield E :=
  ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E P.imaginaryScalar (nativeOneDeltaImaginary E P hP)

omit [IsGalois ℚ E] in
theorem nativeOneParameterNonzero : nativeOneParameter E P hP ≠ 0 :=
  ThetaCycle.QuadraticModel.CM.cm_quadratic_parameter_ne_zero E P.imaginaryScalar
    (nativeOneDeltaImaginary E P hP) (nativeOneDeltaNonzero E P hP)

def nativeOneHermitian : (Matrix (Fin 3) (Fin 3)
    (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (nativeOneParameter E P hP)))ˣ :=
  ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E P.imaginaryScalar (nativeOneDeltaImaginary E P hP)
    P.b hP.2.1 hP.2.2.1

def nativeOneSkew : (Matrix (Fin 1) (Fin 1)
    (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (nativeOneParameter E P hP)))ˣ :=
  Multiplicity.MultiplicityOne.Quadratic.directSkewUnit E P.imaginaryScalar (nativeOneDeltaImaginary E P hP)
    (nativeOneDeltaNonzero E P hP) (Multiplicity.nativeCoefficient E P v)
    (Multiplicity.nativeCoefficient_real E P hP v) (Multiplicity.nativeCoefficient_ne_zero E P hP v)

def nativeOneFrames : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield E) (nativeOneParameter E P hP) 3 1
    (nativeOneHermitian E P hP) (nativeOneSkew E P hP v) :=
  Multiplicity.MultiplicityOne.Quadratic.directGlobalFrames E P.imaginaryScalar (nativeOneDeltaImaginary E P hP)
    (nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1
    (Multiplicity.nativeCoefficient E P v) (Multiplicity.nativeCoefficient_real E P hP v)
    (Multiplicity.nativeCoefficient_ne_zero E P hP v)

def nativeOneBall : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield E) (nativeOneParameter E P hP) 1
    (nativeOneHermitian E P hP) (nativeOneSkew E P hP v) :=
  Multiplicity.MultiplicityOne.Quadratic.directBallArithmeticData E (Representatives.Multiplicity.nativePlaces E P hP hμ)
    P.imaginaryScalar (nativeOneDeltaImaginary E P hP) (nativeOneDeltaNonzero E P hP)
    P.b hP.2.1 hP.2.2.1
    (Multiplicity.nativeCoefficient E P v) (Multiplicity.nativeCoefficient_real E P hP v)
    (Multiplicity.nativeCoefficient_ne_zero E P hP v)
    (IntrinsicOne.Multiplicity.native_single_ball_negative E P hP hμ) (IntrinsicOne.Multiplicity.native_single_ball_compact E P hP hμ)
    (IntrinsicOne.Multiplicity.native_single_active_skew E P hP hμ v hv)
    (IntrinsicOne.Multiplicity.native_single_other_place E P hP hμ hs)

theorem native_one_theta_from_complete_AdelicTheta (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement) :
    let F := maximalRealSubfield E
    let d := nativeOneParameter E P hP
    let hd := nativeOneParameterNonzero E P hP
    let H := nativeOneHermitian E P hP
    let K := nativeOneSkew E P hP v
    let frames := nativeOneFrames E P hP v
    let A := nativeOneBall E P hP hμ hs v hv
    ∃ C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1,
      C.ψ = ThetaCycle.FieldAdelicCharacter.CM.fieldAdelicCharacter F ∧ RepresentationTheory.Theta.Adelic.Data.CharacterConclusion F d 3 1 C ∧
      ∃ D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C frames,
        RepresentationTheory.Theta.Adelic.Data.AdelicConclusion F d 3 1 H K hd C frames D ∧
        RepresentationTheory.Theta.Adelic.Data.FiniteConclusion F d 3 1 H K hd C frames D ∧
        ∃ B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A,
          RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B frames ∧ RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B ∧
          RepresentationTheory.Theta.Adelic.DataTheta.OscillatorIdentification B frames hd C D ∧ RepresentationTheory.Theta.Adelic.SiegelBranchData.SiegelBranchExtension B frames hd C D ∧
          RepresentationTheory.Theta.Adelic.SiegelBranchData.ArchimedeanLiftUniqueness frames hd C D ∧ RepresentationTheory.Theta.Adelic.DataTheta.Descent.ThetaConstruction B ∧
          RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B frames hd C D ∧ RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent B frames hd C D ∧
          RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic.NativeConclusion B frames hd C D := by
  exact Multiplicity.OneTheta.Quadratic.direct_theta_from_complete_AdelicTheta hAdelicTheta E (Representatives.Multiplicity.nativePlaces E P hP hμ)
    P.imaginaryScalar (nativeOneDeltaImaginary E P hP) (nativeOneDeltaNonzero E P hP)
    P.b hP.2.1 hP.2.2.1 (IntrinsicOne.Multiplicity.native_single_ball_negative E P hP hμ)
    (IntrinsicOne.Multiplicity.native_single_ball_compact E P hP hμ)
    (Multiplicity.nativeCoefficient E P v) (Multiplicity.nativeCoefficient_real E P hP v)
    (Multiplicity.nativeCoefficient_ne_zero E P hP v) (IntrinsicOne.Multiplicity.native_single_active_skew E P hP hμ v hv)
    (IntrinsicOne.Multiplicity.native_single_other_place E P hP hμ hs)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneTheta.Multiplicity
