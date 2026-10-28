import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType
import OAI.AlgebraicGeometry.Albanese.Definitions
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Definitions -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Definitions.CM

noncomputable section

/-! Definitions used in the HeckeCycles statement. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

/--
Concrete geometric interface, defined in Proofs/Geometry.lean.

For positive multiples N of Nbase:
* X N is the source's compact smooth projective ball quotient, from
 a rank-three E-Hermitian space with signature (2,1) at the
 distinguished place and definite signatures elsewhere;
* the multiplicity line has signature function d;
* Θ N is the cohomology class of the source's projected theta
 one-form for a fixed finite input;
* all levels use that same finite input and the same theta form on
 the covering ball, with the literal principal-level orbit relation.

No rational Hodge-map spanning condition belongs in this predicate.
-/
abbrev IsSourceBallThetaFamily
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (d : Gal(E/ℚ) → Bool)
    (Nbase : ℕ)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Θ : ∀ N : ℕ,
      ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1)) : Prop :=
  GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Definitions.CM
