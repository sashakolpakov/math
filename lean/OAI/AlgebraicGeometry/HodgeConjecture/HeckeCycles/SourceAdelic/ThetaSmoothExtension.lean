import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalIntertwining
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaBall
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.WeilData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaBall

/-! # Theta Smooth Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaSmoothExtension.CM

noncomputable section

/-! The full named AdelicTheta prerequisite produces a smooth representation
of the actual finite unitary group extending the original source action. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem exists_extension (hAdelicTheta : Adelic.ThetaBall.CM.AdelicThetaInput)
    (inputs : RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0}) :
    ∃ ρ : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (Source.QuadraticConjugation.CM.Field.RealField E)
        (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates)) →*
          (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)),
      (∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ}) ∧
      ρ.comp (ThetaRationalTheta.CM.rational E L) = Source.WeilData.CM.finiteAction E L := by
  apply Adelic.ThetaBall.CM.Elimination.finite_representation (Source.QuadraticConjugation.CM.Field.RealField E) _ 1 _ _ _ _ _ _
    (ThetaBall.CM.source_output E L hAdelicTheta inputs)
  intro C D hD T hT hG hO hCov
  refine ⟨ThetaIntrinsicAction.CM.Intrinsic.action E L T hT (Source.WeilData.CM.weilData E places) C D,
    ThetaIntrinsicAction.CM.Intrinsic.smooth E L T hT (Source.WeilData.CM.weilData E places) C D hD, ?_⟩
  exact ThetaRationalIntertwining.CM.hom E L T hT hG (Source.WeilData.CM.weilData E places)
    C D hO hCov EstablishedPoissonAutomorphy.CM.full_input

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaSmoothExtension.CM
