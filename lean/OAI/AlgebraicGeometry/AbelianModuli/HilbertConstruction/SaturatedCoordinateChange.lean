import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.FrameRankInvariance
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates

/-! # Saturated Coordinate Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Coordinate substitution preserves actual saturated flat
Hilbert ideals. Flatness is transported through the high-degree
quotient equivalences; residue Hilbert polynomials are transported
through their coefficient extensions. -/
open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert
universe u v
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {P : Polynomial ℚ}
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P)

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coordinateChange (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) :
    SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R n P where
  ideal := Linear.CoordinateIdeals.linearCoordinateIdeal e I.ideal
  saturated := Linear.CoordinateIdeals.linearCoordinateIdeal_saturated e I.ideal I.saturated
  flat := by
    apply HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveQuotient_flat_of_eventually_flat _ (HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P)
    intro d hd
    have : Module.Flat R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.ideal.toIdeal d) :=
      HilbertScheme.Presentations.Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_flat I.ideal I.saturated P I.hilbert d hd
    exact Module.Flat.of_linearEquiv (Linear.CoordinateIdeals.linearCoordinateIdealDegreeQuotientEquiv e I.ideal d)
  hilbert p := by
    rw [HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff,
      Linear.CoordinateIdeals.linearCoordinateIdealExtended_hilbertPolynomial_iff,
      ← HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff]
    exact I.hilbert p

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coordinateChange_degreeRelations
    (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (I.coordinateChange e).ideal.toIdeal d =
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal d).comap (HilbertConstruction.Polynomial.CoordinateChangeEvaluation.polynomialLinearDegreeEquiv e d).toLinearMap :=
  Linear.CoordinateIdeals.linearCoordinateIdeal_degreeRelations e I.ideal d

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coordinateChange_configuration_kernel {ι : Type v}
    (w : ι → Fin (n + 1) → R) (d : ℕ)
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (s : ι → Rˣ)
    (h : (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.ideal.toIdeal d) :
    (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c j => (s c : R) * T (w c) j) d).ker =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (I.coordinateChange (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T)).ideal.toIdeal d := by
  rw [Configuration.FrameRankInvariance.homogeneousConfigurationEvaluation_kernel_frameChange, SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.coordinateChange_degreeRelations, h]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
