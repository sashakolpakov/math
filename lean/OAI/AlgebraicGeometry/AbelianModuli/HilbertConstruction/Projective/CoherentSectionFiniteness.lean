import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentCechFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.SectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

/-! # Coherent Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentSectionFiniteness

noncomputable section

/-! Actual global sections of finite-type quasicoherent projective sheaves are finite over the Noetherian base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projective_coherent_sections_finite (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj M) := by
  have : Module.Finite R ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex
      (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) M
      (CechCover.projectiveCechOpens I)).homology 0) := @CoherentCechFiniteness.projectiveCoherentCech_homology_finite R _ _ n I M
        ‹M.IsQuasicoherent› ‹M.IsFiniteType› 0
  exact OrderedCech.SectionFiniteness.coefficient_sections_finite_of_cech _ M (CechCover.projectiveCechOpens I) (CechCover.projectiveCechOpens_cover I)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentSectionFiniteness
