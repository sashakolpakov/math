import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechIntersectionCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms

/-! # Module Cech Term Ext -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ModuleCechTermExt

noncomputable section

/-! Ordered projective intersection values determine every homogeneous Čech term. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveModuleCechTerm_ext (d : ℤ) (q : ℕ)
    (f g : HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1))
    (h : ∀ a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q,
      f.val (CechIntersectionCoordinates.projectiveCechIndexFinset a) = g.val (CechIntersectionCoordinates.projectiveCechIndexFinset a)) : f = g := by
  apply (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)).injective
  funext s
  apply Subtype.ext
  let e : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q ≃
      {s : Finset (Fin (n + 1)) // s.card = q + 1} := OrderedCech.LiftedIndices.orderedCechLiftedFinsetEquiv (Fin (n + 1)) q
  obtain ⟨a, rfl⟩ := e.surjective s
  exact h a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ModuleCechTermExt
