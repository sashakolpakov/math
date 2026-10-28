import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.ConfigurationDeterminesIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasisEvaluationMatrices

/-! # Configuration Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ConfigurationEvaluation

noncomputable section

/-! A normalized configuration gives an explicit linear polynomial
evaluation map. For a detecting family of embedded scheme sections,
its kernel is exactly the homogeneous ideal component. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R] {n d : ℕ} {ι : Type v}

def homogeneousConfigurationEvaluation (v : ι → Fin (n + 1) → R) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d →ₗ[R] (ι → R) :=
  LinearMap.pi (fun c => (MvPolynomial.aeval (v c)).toLinearMap.comp (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d).subtype)

theorem homogeneousConfigurationEvaluation_kernel
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (x : ι → (Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (hx : Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d) x)
    (v : ι → Fin (n + 1) → R) (i : ι → Fin (n + 1)) (hi : ∀ c, v c (i c) = 1)
    (hv : ∀ c, x c ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R (v c) (i c) (hi c)) :
    (homogeneousConfigurationEvaluation v d).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  ext p
  change homogeneousConfigurationEvaluation v d p = 0 ↔ p.val ∈ I
  rw [Family.ConfigurationDeterminesIdeal.homogeneousPolynomial_mem_iff_detectingFamily I hI x hx]
  constructor
  · intro hp c
    apply (Normalized.PolynomialSectionEvaluation.polynomialSection_pullback_zero_iff_normalized_evaluation I p (x c) (v c) (i c) (hi c) (hv c)).mpr
    exact congrFun hp c
  · intro hp
    funext c
    exact (Normalized.PolynomialSectionEvaluation.polynomialSection_pullback_zero_iff_normalized_evaluation I p (x c) (v c) (i c) (hi c) (hv c)).mp (hp c)

def homogeneousConfigurationMatrix {ν : Type w} [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν] (b : Module.Basis ν R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d))
    (v : ι → Fin (n + 1) → R) : Matrix ι ν R :=
  BasisEvaluationMatrices.basisEvaluationMatrix b (homogeneousConfigurationEvaluation v d)

theorem homogeneousConfigurationMatrix_linearMap {ν : Type w} [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν] (b : Module.Basis ν R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d))
    (v : ι → Fin (n + 1) → R) :
    Matrix.toLin' (homogeneousConfigurationMatrix b v) =
      (homogeneousConfigurationEvaluation v d).comp b.equivFun.symm.toLinearMap :=
  BasisEvaluationMatrices.basisEvaluationMatrix_linearMap b _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ConfigurationEvaluation
