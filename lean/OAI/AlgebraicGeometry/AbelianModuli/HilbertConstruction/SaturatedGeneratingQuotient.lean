import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeDetermination
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.QuotientRankDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IdealBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Saturated Generating Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A retained finite flat quotient agrees with the saturated degree quotient whenever their ranks agree. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation.GradedHilbert

universe u

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.retainedQuotient_eq_of_saturated_coordinates
    {R : Type u} [CommRing R] {n B : ℕ} {r : ℕ → ℕ}
    (D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r) (d : Fin (B + 1))
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation D.generatedIdeal = I)
    (Q : Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (r d))
    (hQ : Q.toSubmodule = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d) : D.quotient d = Q := by
  apply Module.Grassmannian.ext
  have hle : (D.quotient d).toSubmodule ≤ Q.toSubmodule := by
    rw [hQ, ← D.generatedIdeal_degree d]
    intro x hx
    change x.val ∈ I.toIdeal
    rw [← hI]
    exact (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.le_projectiveSaturation D.generatedIdeal) hx
  exact Flat.QuotientRankDetection.submodule_eq_of_flat_quotient_ranks (D.quotient d).toSubmodule Q.toSubmodule hle
    (fun p => ((D.quotient d).rankAtStalk_eq p).trans (Q.rankAtStalk_eq p).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
