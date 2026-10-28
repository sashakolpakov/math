import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialTransitions

/-! # Polynomial Specialization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialSpecialization.GradedHilbert

noncomputable section

/-! Explicit specialization of normalized polynomial generators identifies
their actual ideals and degree quotients. -/

open _root_.MvPolynomial

universe u
variable {R S : Type u} [CommRing R] [CommRing S] {n N : ℕ} {ι : Type u} [Fintype ι]

theorem normalizedPolynomialIdeal_specialization (φ : R →+* S)
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) :
    Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (fun j => MvPolynomial.map φ (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a Q j)) N
      (fun j => (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator_homogeneous a Q j).map φ) =
        PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Q.map φ) := by
  apply HomogeneousIdeal.ext
  change Ideal.span (Set.range (fun j => MvPolynomial.map φ (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a Q j))) =
    Ideal.span (Set.range (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a (Q.map φ)))
  congr 2
  funext j
  exact PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator_map φ a Q j

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialSpecialization.GradedHilbert
