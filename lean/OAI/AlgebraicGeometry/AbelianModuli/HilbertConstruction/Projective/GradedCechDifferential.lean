import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.GradedCechDifferential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CechRestrictionIndexEquality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechCofaces

/-! # Graded Cech Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GradedCechDifferential

noncomputable section

/-! The graded projective Čech differential is expressed with the exact deleted indices of the actual projective cover. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveModuleCechDifferential_ordered {q : ℕ}
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) (q + 1))
    (f : HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)) :
    HilbertScheme.Presentations.ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) f (CechIntersectionCoordinates.projectiveCechIndexFinset a) =
      ∑ k : Fin (q + 2), (-1 : R) ^ k.val •
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k)
          (f (CechIntersectionCoordinates.projectiveCechIndexFinset (a.delete k))) := by
  have hs := Ordered.GradedCechDifferential.moduleCechDifferential_ordered (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (OrderedCech.LiftedIndices.orderedCechIndexULiftEquiv (Fin (n + 1)) (q + 1) a) f
  apply hs.trans
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun x ↦ (-1 : R) ^ k.val • x)
    (Module.CechRestrictionIndexEquality.moduleChartRestriction_family_congr (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) f
      (CechIntersectionCoordinates.projectiveCechIndexFinset_delete a k).symm (Finset.erase_subset _ _)
      (NegativeTwist.CechCofaces.projectiveCechIndexFinset_delete_subset a k))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GradedCechDifferential
