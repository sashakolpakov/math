import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnramifiedExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PlaceExclusion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace

/-! # Unramified Bound -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnramifiedBound.CM

noncomputable section

/-! One positive integer excludes every source place where the prescribed
finite Schwartz input is ramified, uniformly over the q-adic embeddings. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  (ρ : SourceFinite.Product.CM.FiniteGroup E (OppositeCoordinates.CM.coordinates E L.coordinates) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)))
  (hρ : ∀ φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places), IsOpen {g | ρ g φ = φ})

include hρ in
theorem exists_bound (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime q N →
      ∀ (f : E →+* ℚ_[q])
        (g) (_ : g ∈ SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates)
          (QadicPlace.CM.place E f)),
        ρ (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace
          (SourceFinite.Product.CM.levels E (OppositeCoordinates.CM.coordinates E L.coordinates))
          (QadicPlace.CM.place E f) g) φ = φ := by
  exact Finite.PlaceExclusion.CM.exists_embedding_bound
    (QuadraticConjugation.CM.Field.RealField E) (algebraMap (QuadraticConjugation.CM.Field.RealField E) E) _
    (UnramifiedExtension.CM.eventually_fixed E L ρ hρ φ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnramifiedBound.CM
