import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentCechFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiDegreeZeroFiniteness

/-! # Zariski Cohomology Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiCohomologyFiniteness.ZariskiCohomology

noncomputable section

/-! Genuine Zariski cohomology of a coherent sheaf on a projective coordinate quotient is finite over the Noetherian coefficient ring in every degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem projective_zariski_cohomology_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) q).obj M) := by
  cases q with
  | zero => exact ZariskiDegreeZeroFiniteness.ZariskiCohomology.projective_zariski_zero_finite I M
  | succ q =>
      have : Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).homology (q + 1)) :=
        @CoherentCechFiniteness.projectiveCoherentCech_homology_finite R _ _ n I M
          ‹M.IsQuasicoherent› ‹M.IsFiniteType› (q + 1)
      exact Module.Finite.equiv (CechZariskiComparison.projectiveCechZariskiModuleIso I M q).toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiCohomologyFiniteness.ZariskiCohomology
