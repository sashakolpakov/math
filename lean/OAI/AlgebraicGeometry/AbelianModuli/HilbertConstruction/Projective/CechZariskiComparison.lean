import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCech

/-! # Cech Zariski Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechZariskiComparison

noncomputable section

/-! Coordinate Čech cohomology of a projective quotient agrees with genuine coefficient-linear Zariski cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCechOpens_iSup : ⨆ i, CechCover.projectiveCechOpens I i = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨i, hi⟩ := CechCover.projectiveCechOpens_cover I x
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

def projectiveCechZariskiModuleIso
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent] (q : ℕ) :
    ((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).homology (q + 1) ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) (q + 1)).obj M := by
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let : IsProper p := HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper I
  let : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  exact OrderedCech.ZariskiComparison.orderedCechZariskiModuleIso _ M (CechCover.projectiveCechOpens I)
    (projectiveCechOpens_iSup I) (CechCover.projectiveCechOpens_affine I) q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechZariskiComparison
