import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IdealCoefficientTests
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.CoefficientContainment

/-! # Affine Source Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AffineSourceCoefficients

noncomputable section

/-! An affine source with projective coordinate module has an actual
coefficient ideal for each of its ideal sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R B : CommRingCat.{u}) [Algebra R B] [Module.Projective R B]

theorem projective_affine_source_coefficients (K : (Spec B).IdealSheafData) :
    ∃ I : Ideal R, Affine.IdealCoefficientTests.IsAffineIdealCoefficient R
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) K I := by
  refine ⟨AlgebraIdealCoefficients.projectiveAlgebraIdealCoefficients R B (SpectrumIdealCoordinates.spectrumIdealCoordinates B K), ?_⟩
  intro J
  rw [← (SpectrumIdealCoordinates.spectrumIdealCoordinates B).le_iff_le,
    SpectrumIdealCoordinates.spectrumIdealCoordinates_comap, OrderIso.apply_symm_apply]
  exact (CoefficientContainment.projectiveAlgebraIdealCoefficients_containment B (SpectrumIdealCoordinates.spectrumIdealCoordinates B K) J).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AffineSourceCoefficients
