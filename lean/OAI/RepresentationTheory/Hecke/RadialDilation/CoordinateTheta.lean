import OAI.RepresentationTheory.Hecke.RadialDilation.GeometricSpecs

/-! # Coordinate Theta -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.CoordinateTheta.Realization

noncomputable section

/-! The determinant and theta inputs in a fixed rational trace coordinate system. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

universe up ur uf ua
variable {Place : Type up} [Fintype Place]
variable {MpR : Type ur} {MpF : Type uf} {MpA : Type ua}
  [Group MpR] [Group MpF] [Group MpA]

theorem geometric_theta_inputs_for_coordinates
    (hPoissonAutomorphy : Prerequisites.Core.PoissonAutomorphy.Proposition.{up,ur,uf,ua})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ t : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ht : NumberField.IsCMField.complexConj E t = t)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) → ℚ))
    (he : ∀ x y, FramePositivity.Realization.coordinatePairing (e x) (e y) = SymplecticBasis.Realization.rationalTraceForm E (δ * t) H x y)
    (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hq : Geometry.ComplexBall.PrescribedSignsB.matrixB σ H μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0)
    (hpositive : ∀ τ u, u ∈ LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z τ) → u ≠ 0 →
      0 < (σ τ (δ * t) * Geometry.ComplexBall.PrescribedSignsB.metricValue (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H τ) u / Complex.I).re)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex Place) MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ) (hγ : γ.val = RationalCoordinates.Realization.rationalScalarMatrix E e (r : E)) :
    ∃ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex Place),
      GeometricSpecs.Realization.ThetaScalarRealization D γ μ d (fun τ => σ τ (r : E))
        (FramePositivity.Realization.upperFrame (RationalCoordinates.Realization.rationalCoordinates E σ hσ e) (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z)
        (FramePositivity.Realization.lowerFrame (RationalCoordinates.Realization.rationalCoordinates E σ hσ e) (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z) Z := by
  let ψ := Geometry.ComplexBall.PrescribedSignsB.tracePairing (Geometry.ComplexBall.PrescribedSignsB.localB σ H) (fun τ => σ τ (δ * t))
  have hpair : ∀ u v, FramePositivity.Realization.coordinatePairing (RationalCoordinates.Realization.rationalCoordinates E σ hσ e u)
      (RationalCoordinates.Realization.rationalCoordinates E σ hσ e v) = ψ u v :=
    PairingTransport.Realization.rationalCoordinates_preserves_pairing E σ hσ δ t hδ ht H hHerm e he
  have hp : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place) ψ Geometry.ComplexBall.PrescribedSignsB.realConj
      (LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z)) := by
    have hp' := Geometry.ComplexBall.PrescribedSignsB.globalFrame_positivePeriod (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) (Geometry.ComplexBall.PrescribedSignsB.matrixB_hermitian σ H hHerm)
      μ d z hq (fun τ => σ τ (δ * t))
      (fun τ => Geometry.ComplexBall.PrescribedSignsB.coefficient_real_zero (σ τ) δ t hδ ht) hpositive
    simpa only [Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] using hp'
  exact GeometricTheta.Realization.rational_period_theta_characters hPoissonAutomorphy E r hr σ hσ e (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H)
    μ d z ψ hpair hp D γ hγ

end

end OAI.RepresentationTheory.Hecke.RadialDilation.CoordinateTheta.Realization
