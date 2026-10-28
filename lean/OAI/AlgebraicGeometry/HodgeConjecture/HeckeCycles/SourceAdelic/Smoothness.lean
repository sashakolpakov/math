import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorSmoothness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SmoothExtensionElimination

/-! # Smoothness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Smoothness.CM

noncomputable section

/-! The full named AdelicTheta prerequisite supplies smoothness of the original
source active/away action, with no representation or matching field added
to the source ball-theta family. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FactorTheta.CM.RationalWeilFactorization

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (hAdelicTheta : Adelic.ThetaBall.CM.AdelicThetaInput) (inputs : RepresentationTheory.Theta.Adelic.Prerequisites.Inputs.{0, 0})
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

include hAdelicTheta inputs in
theorem product (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {g : Matrix.SpecialLinearGroup (Fin 3) ℚ_[q] × Source.FactorTheta.CM.RationalWeilFactorization.Away E L f |
      Source.FactorTheta.CM.action E L f g φ = φ} :=
  SmoothExtensionElimination.CM.apply (ThetaRationalTheta.CM.rational E L)
    (Source.WeilData.CM.finiteAction E L)
    (ThetaSmoothExtension.CM.exists_extension E L hAdelicTheta inputs)
    (fun ρ hρ hr => Source.FactorSmoothness.CM.product_smooth E L ρ hρ hr f φ)

include hAdelicTheta inputs in
theorem away (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {b : Source.FactorTheta.CM.RationalWeilFactorization.Away E L f | Source.FactorTheta.CM.action E L f (1, b) φ = φ} :=
  (product E L hAdelicTheta inputs f φ).preimage (continuous_const.prodMk continuous_id)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Smoothness.CM
