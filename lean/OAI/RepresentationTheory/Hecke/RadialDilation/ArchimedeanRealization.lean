import OAI.RepresentationTheory.Hecke.RadialDilation.GeometricTheta
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis
import OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport

/-! # Archimedean Realization -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ArchimedeanRealization.Realization

noncomputable section

/-! Construction of the archimedean inputs of RadialDilation from the trace geometry. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

universe up ur uf ua
variable {Place : Type up} [Fintype Place]
variable {MpR : Type ur} {MpF : Type uf} {MpA : Type ua}
  [Group MpR] [Group MpF] [Group MpA]

/-- A positive trace-form frame determines a rational symplectic scalar,
a Siegel period, the half-determinant square, and the first-theta character.
No symplectic basis, determinant identity, or theta eigenrelation is assumed. -/
theorem geometric_archimedean_inputs
    (hPoissonAutomorphy :
      Prerequisites.Core.PoissonAutomorphy.Proposition.{up, ur, uf, ua})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (δ a : E) (hδ : NumberField.IsCMField.complexConj E δ = -δ)
    (ha : NumberField.IsCMField.complexConj E a = a) (hδa : δ * a ≠ 0)
    (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ j k, H j k = NumberField.IsCMField.complexConj E (H k j))
    (hH : H.det ≠ 0)
    (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hq : Geometry.ComplexBall.PrescribedSignsB.matrixB σ H μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0)
    (hpositive : ∀ τ u, u ∈ LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z τ) → u ≠ 0 →
      0 < (σ τ (δ * a) * Geometry.ComplexBall.PrescribedSignsB.metricValue (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H τ) u / Complex.I).re)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex Place) MpR MpF MpA) :
    ∃ (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) → ℚ))
      (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex Place)),
      γ.val = RationalCoordinates.Realization.rationalScalarMatrix E e (r : E) ∧
      (let Q := FramePositivity.Realization.lowerFrame (RationalCoordinates.Realization.rationalCoordinates E σ hσ e) (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z
       Z.matrix * Q = FramePositivity.Realization.upperFrame (RationalCoordinates.Realization.rationalCoordinates E σ hσ e) (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z ∧
       Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z ^ 2 = (σ μ (r : E))⁻¹ *
         ∏ τ ∈ Finset.univ.erase μ, σ τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
       ∀ Φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex Place),
         GeometricTheta.Realization.projectedFrameTheta μ Q Z (D.finiteAction γ Φ) =
           (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z * (σ μ (r : E))⁻¹) • GeometricTheta.Realization.projectedFrameTheta μ Q Z Φ) := by
  obtain ⟨e, he⟩ := SymplecticBasis.Realization.exists_rational_symplectic_coordinates E σ hσ δ a hδ ha hδa H hHerm hH
  let γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ := ⟨RationalCoordinates.Realization.rationalScalarMatrix E e (r : E),
    PairingTransport.Realization.rationalScalarMatrix_symplectic E σ hσ δ a hδ ha H hHerm e he r hr⟩
  let ψ := Geometry.ComplexBall.PrescribedSignsB.tracePairing (Geometry.ComplexBall.PrescribedSignsB.localB σ H) (fun τ => σ τ (δ * a))
  have hpair : ∀ u v, FramePositivity.Realization.coordinatePairing (RationalCoordinates.Realization.rationalCoordinates E σ hσ e u)
      (RationalCoordinates.Realization.rationalCoordinates E σ hσ e v) = ψ u v :=
    PairingTransport.Realization.rationalCoordinates_preserves_pairing E σ hσ δ a hδ ha H hHerm e he
  have hp : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place) ψ Geometry.ComplexBall.PrescribedSignsB.realConj
      (LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) μ d z)) := by
    have hp' := Geometry.ComplexBall.PrescribedSignsB.globalFrame_positivePeriod (Geometry.ComplexBall.PrescribedSignsB.matrixB σ H) (Geometry.ComplexBall.PrescribedSignsB.matrixB_hermitian σ H hHerm)
      μ d z hq (fun τ => σ τ (δ * a))
      (fun τ => Geometry.ComplexBall.PrescribedSignsB.coefficient_real_zero (σ τ) δ a hδ ha) hpositive
    simpa only [Geometry.ComplexBall.PrescribedSignsB.matrixB_apply] using hp'
  obtain ⟨Z, hZ⟩ :=
    GeometricTheta.Realization.rational_period_theta_characters
      (hPoissonAutomorphy := hPoissonAutomorphy) (E := E) (r := r) (hr := hr)
      (σ := σ) (hσ := hσ) (e := e)
      (B := Geometry.ComplexBall.PrescribedSignsB.matrixB σ H)
      (μ := μ) (d := d) (z := z) (ψ := ψ) (hpair := hpair) (hp := hp)
      (D := D) (γ := γ) (hγ := rfl)
  exact ⟨e, γ, Z, rfl, hZ⟩

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ArchimedeanRealization.Realization
