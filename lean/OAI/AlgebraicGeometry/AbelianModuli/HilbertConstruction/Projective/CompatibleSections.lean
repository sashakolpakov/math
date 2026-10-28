import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleCoordinateSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionCover

/-! # Compatible Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CompatibleSections

noncomputable section

/-! Every quasicoherent section on an actual projective coordinate chart extends to a family of chart sections satisfying one common twisting-degree compatibility equation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projective_quasicoherent_compatible_section_extension
    (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) [M.IsQuasicoherent]
    (j : Fin (n + 1)) (s : Γ(M, ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {j})) :
    ∃ (d : ℕ) (t : ∀ i : Fin (n + 1), Γ(M, ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i})),
      t j = s ∧ ∀ i k : Fin (n + 1),
        M.presheaf.map (homOfLE ((SectionCover.projectiveCoordinateSectionCover I).overlap_le_left i k)).op (t i) =
          ((SectionCover.projectiveCoordinateSectionCover I).transition i k) ^ d •
            M.presheaf.map (homOfLE ((SectionCover.projectiveCoordinateSectionCover I).overlap_le_right i k)).op (t k) :=
  (SectionCover.projectiveCoordinateSectionCover I).exists_compatible_coordinateCoefficients M j s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CompatibleSections
