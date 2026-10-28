import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameSemilinearExt

/-! # Real Structure -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealStructure.CM

noncomputable section

/-! The real structure on the source exchanges conjugate CM components.
Its given complex symplectic frame sends it to ordinary conjugation. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

def conjugate : GeometricSource.CM.Ambient E →ₗ⋆[ℂ] GeometricSource.CM.Ambient E where
  toFun w τ i := star (w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) i)
  map_add' x y := by
    funext τ i
    exact star_add _ _
  map_smul' c x := by
    funext τ i
    change star (c * x (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) i) = star c * star (x (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) i)
    exact map_mul (starRingEnd ℂ) c (x (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) i)

theorem rational (x : GeometricSource.CM.Vec E) : conjugate E (GeometricSource.CM.embeddingCoordinates E x) = GeometricSource.CM.embeddingCoordinates E x := by
  funext τ i
  change star ((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (τ (x i)) : E) : ℂ) = (τ (x i) : ℂ)
  rw [ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe, star_star]

variable {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem frame (x : GeometricSource.CM.Ambient E) : ComplexAction.CM.complexFrame E C (conjugate E x) =
    fun i => star (ComplexAction.CM.complexFrame E C x i) := by
  let A := (ComplexAction.CM.complexFrame E C).toLinearMap.comp (conjugate E)
  let D := (starLinearEquiv ℂ (A := (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ)).toLinearMap.comp
    (ComplexAction.CM.complexFrame E C).toLinearMap
  have he : A = D := by
    apply Rational.FrameSemilinearExt.CM.ext (ComplexAction.CM.Symplectic.frame E C)
      (ComplexAction.CM.complexFrame E C) (GeometricSource.CM.embeddingCoordinates E) (ComplexAction.CM.complexFrame_rational E C)
    intro y
    change ComplexAction.CM.complexFrame E C (conjugate E (GeometricSource.CM.embeddingCoordinates E y)) =
      star (ComplexAction.CM.complexFrame E C (GeometricSource.CM.embeddingCoordinates E y))
    rw [rational, ComplexAction.CM.complexFrame_rational]
    ext i
    simp
  exact LinearMap.congr_fun he x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealStructure.CM
