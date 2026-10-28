import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.DegreeOneGenerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeOneProjectivePresentation

/-! # Veronese Projective Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.VeroneseProjectivePresentation

noncomputable section

/-! A positive Veronese of the actual balanced determinant algebra
has a constructed projective presentation over the coefficient spectrum. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem presentation_of_degree_one_generators
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (g : ℕ → Submodule R A) [GradedAlgebra g]
    (h : ∃ (n : ℕ) (D : Fin (n + 1) → A),
      (∀ j, D j ∈ g 1) ∧ Algebra.adjoin R (Set.range D) = ⊤) :
    Nonempty (Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap g))) := by
  obtain ⟨n, D, hD, hgen⟩ := h
  exact ⟨DegreeOneProjectivePresentation.degreeOneProjectivePresentation g D hD hgen⟩

private theorem veronese_presentation_of_degree_one_generators
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (g : ℕ → Submodule R A) [GradedAlgebra g]
    (h : ∃ N : ℕ, 0 < N ∧ ∃ (n : ℕ) (D : Fin (n + 1) → Veronese.Subalgebra.veroneseSubalgebra g N),
      (∀ j, D j ∈ Veronese.Grading.veroneseGrading g N 1) ∧ Algebra.adjoin R (Set.range D) = ⊤) :
    ∃ N : ℕ+, Nonempty (Projective.ProjectivePresentations.ProjectivePresentation
      (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Veronese.Grading.veroneseGrading g (N : ℕ))))) := by
  obtain ⟨N, hN, hgen⟩ := h
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact ⟨⟨N, hN⟩, presentation_of_degree_one_generators (Veronese.Grading.veroneseGrading g N) hgen⟩

theorem balancedDeterminant_veronese_projective_presentation
    (R : Type u) [CommRing R] {r m : ℕ} (hr : 0 < r) (i : Fin m) :
    ∃ N : ℕ+, Nonempty (Projective.ProjectivePresentations.ProjectivePresentation
      (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Veronese.Grading.veroneseGrading (DeterminantGrading.balancedDeterminantGrading R r m i) (N : ℕ))))) := by
  exact veronese_presentation_of_degree_one_generators (DeterminantGrading.balancedDeterminantGrading R r m i)
    (Veronese.DegreeOneGenerators.balancedDeterminant_veronese_degree_one_generators R hr i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.VeroneseProjectivePresentation
