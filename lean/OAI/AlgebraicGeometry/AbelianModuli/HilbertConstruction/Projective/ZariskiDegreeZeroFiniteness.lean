import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.DegreeZero
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveCoherentSectionFiniteness

/-! # Zariski Degree Zero Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiDegreeZeroFiniteness.ZariskiCohomology

noncomputable section

/-! Actual Ext-based degree-zero cohomology of coherent projective sheaves is finite over the Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem projective_zariski_zero_finite {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) 0).obj M) := by
  have : Module.Finite R ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))).obj M) :=
    CoherentSectionFiniteness.projective_coherent_sections_finite I M
  exact Module.Finite.equiv (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv _ M).symm

theorem projectivePresentation_zariski_zero_finite {X : Over (Spec (.of R))}
    (P : ProjectivePresentations.ProjectivePresentation X) (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) 0).obj M) := by
  have : Module.Finite R ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom)).obj M) :=
    P.coherentSections_finite M
  exact Module.Finite.equiv (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv _ M).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiDegreeZeroFiniteness.ZariskiCohomology
