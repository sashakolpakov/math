import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialSpecialization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsRingMap

/-! # Polynomial Ideal Ring Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialIdealRingMap.GradedHilbert

noncomputable section

/-! Coefficient base change for the actual normalized polynomial ideal. -/

universe u
variable {R A : Type u} [CommRing R] [CommRing A]
variable {n N : ℕ} {ι : Type u} [Fintype ι]

theorem normalizedPolynomialIdeal_map (φ : R →+* A)
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) :
    (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) =
      PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Q.map φ) := by
  exact (Homogeneous.GeneratorsRingMap.GradedHilbert.homogeneousGeneratorsIdeal_map_ringHom φ (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a Q) N
    (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator_homogeneous a Q)).trans
      (PolynomialSpecialization.GradedHilbert.normalizedPolynomialIdeal_specialization φ a Q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialIdealRingMap.GradedHilbert
