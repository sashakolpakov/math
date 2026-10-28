import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.MultiplicityOne
import OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization

/-! # One Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneTheta.Quadratic

noncomputable section

/-! Instantiate native ThetaOneForms in the original CM embedding coordinates,
compatible rational/local frames and the actual standard adelic character.
The entire AdelicTheta prerequisite and every one of its output clauses are kept. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCharacterNormalization.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData
open OAI.RepresentationTheory.Theta.Adelic.Data OAI.RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic

theorem direct_theta_from_complete_AdelicTheta
    (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement)
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [IsCMField E]
    (places : HeckeCycles.GeometricSource.CM.Places E)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
    (hball : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re < 0)
    (hcompact : ∀ i, i ≠ places.distinguished → 0 < (HeckeCycles.ReferenceDatum.CM.embeddings E places i b).re)
    (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)
    (hactive : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished (δ * a)).im < 0)
    (hother : ∃ i : Fin places.count, i ≠ places.distinguished) :
    let F := maximalRealSubfield E
    let d := ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ
    let hd := ThetaCycle.QuadraticModel.CM.cm_quadratic_parameter_ne_zero E δ hδ hδ0
    let H := ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0
    let K := MultiplicityOne.Quadratic.directSkewUnit E δ hδ hδ0 a ha ha0
    let P := MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0
    let A := MultiplicityOne.Quadratic.directBallArithmeticData E places δ hδ hδ0 b hb hb0 a ha ha0 hball hcompact hactive hother
    ∃ C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 1,
      C.ψ = ThetaCycle.FieldAdelicCharacter.CM.fieldAdelicCharacter F ∧ RepresentationTheory.Theta.Adelic.Data.CharacterConclusion F d 3 1 C ∧
      ∃ D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 1 H K hd C P,
        RepresentationTheory.Theta.Adelic.Data.AdelicConclusion F d 3 1 H K hd C P D ∧
        RepresentationTheory.Theta.Adelic.Data.FiniteConclusion F d 3 1 H K hd C P D ∧
        ∃ B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H K A,
          RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B P ∧ RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B ∧
          RepresentationTheory.Theta.Adelic.DataTheta.OscillatorIdentification B P hd C D ∧ RepresentationTheory.Theta.Adelic.SiegelBranchData.SiegelBranchExtension B P hd C D ∧
          RepresentationTheory.Theta.Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D ∧ RepresentationTheory.Theta.Adelic.DataTheta.Descent.ThetaConstruction B ∧
          RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B P hd C D ∧ RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent B P hd C D ∧
          RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic.NativeConclusion B P hd C D := by
  let F := maximalRealSubfield E
  let d := ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ
  let H := ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0
  let K := MultiplicityOne.Quadratic.directSkewUnit E δ hδ hδ0 a ha ha0
  let P := MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0
  let A := MultiplicityOne.Quadratic.directBallArithmeticData E places δ hδ hδ0 b hb hb0 a ha ha0 hball hcompact hactive hother
  have hq : d ≠ 0 ∧ ¬IsSquare d :=
    ⟨ThetaCycle.QuadraticModel.CM.cm_quadratic_parameter_ne_zero E δ hδ hδ0, ThetaCycle.QuadraticModel.CM.cm_quadratic_parameter_not_isSquare E δ hδ hδ0⟩
  exact RepresentationTheory.Theta.OneFormsIntrinsicOf.Intrinsic.theta_one_forms_of_complete_AdelicTheta hAdelicTheta F d hq H K
    (ThetaCycle.DiagonalFrame.CM.diagonal_hermitian_conjugateTranspose d (ThetaCycle.UnitaryFrame.CM.realHermitianCoefficients E b hb))
    (OneFrames.Quadratic.singleSkewUnit_conjTranspose E δ hδ hδ0 (-a)
      (MultiplicityOne.Quadratic.singleNegCoefficient_real E a ha) (neg_ne_zero.mpr ha0))
    (ThetaCycle.FieldAdelicCharacter.CM.fieldAdelicCharacter F) (ThetaCycle.FieldAdelicCharacter.CM.field_adelic_character_continuous F)
    (ThetaCycle.FieldAdelicCharacter.CM.field_adelic_character_unitary F) (ThetaCycle.FieldAdelicCharacter.CM.field_adelic_character_nontrivial F)
    (ThetaCycle.FieldAdelicCharacter.CM.field_adelic_character_principal F) P A
    (fun v t => ThetaCycle.RealCharacterNormalization.CM.field_adelic_character_standard_real_coordinate F (A.enumerate v) (A.real v) t)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneTheta.Quadratic
