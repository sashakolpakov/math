import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalCoefficientRing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChangeObstructionFlatness

/-! # Local Projective Flat Model -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalProjectiveFlatModel

noncomputable section

/-! A projective quotient which becomes flat over a local ring already
becomes flat over a Noetherian local coefficient ring mapping to it. -/

open _root_.AlgebraicGeometry

universe u
variable {B A : Type u} [CommRing B] [CommRing A] [IsLocalRing A] [Algebra B A]

instance localCoefficientRing_targetLocalHom (E : Subalgebra B A) :
    IsLocalHom (algebraMap (LocalCoefficientRing.localCoefficientRing E) A) :=
  Local.CoefficientLocalization.localCoefficientLocalizationMap_isLocalHom E.val.toRingHom

namespace GradedHilbert

variable [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap B A)] {n : ℕ}

theorem projective_flat_local_coefficient_model
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading B n))
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)))]
    (C : Subalgebra B A) [Algebra.FiniteType B C] :
    ∃ E : Subalgebra B A, C ≤ E ∧ Algebra.FiniteType B E ∧
      Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap
        (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := LocalCoefficientRing.localCoefficientRing E) I))) := by
  obtain ⟨E, hCE, hE, hflat⟩ := Projective.BaseChangeObstructionFlatness.GradedHilbert.projective_flat_finite_coefficient_criterion I C
    (IsLocalRing.maximalIdeal B)
  let : Algebra.FiniteType B E := hE
  refine ⟨E, hCE, hE, hflat (LocalCoefficientRing.localCoefficientRing E) ?_⟩
  exact (IsLocalRing.map_maximalIdeal_lt_top (algebraMap B (LocalCoefficientRing.localCoefficientRing E))).ne

end GradedHilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalProjectiveFlatModel
