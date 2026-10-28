import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RestrictedSmoothUnramified
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaSmoothExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceFinite.Product

/-! # Unramified Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnramifiedExtension.CM

noncomputable section

/-! The smooth extension of the source action fixes each prescribed
input under integral local unitary groups outside finitely many places. -/

open scoped Classical _root_.NumberField
open Filter OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
  (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})

include hρ in
theorem eventually_fixed (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ∀ᶠ v : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FinitePlace (QuadraticConjugation.CM.Field.RealField E) in Filter.cofinite,
      ∀ g ∈ SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates) v,
        ρ (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
          (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates)) v g) φ = φ :=
  RestrictedSmoothUnramified.CM.eventually_fixed
    (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates)) ρ hρ φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnramifiedExtension.CM
