import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PresentationProper
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveCharts

/-! # Base Projective Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseProjectivePresentation.Core

noncomputable section

/-! The base scheme has a chosen projective presentation via a constant
projective point. This supplies the empty-product case for finite parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def baseProjectivePresentation (S : Scheme.{u}) : Has.Core.ProjectivePresentation (Over.mk (𝟙 S)) := by
  let f : Over.mk (𝟙 S) ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S 0 :=
    AbelianModuli.HilbertConstruction.Section.ProjectiveCharts.projectiveChartMapOver (𝟙 S) (fun _ : Fin 1 => 1) 0 rfl
  have hf : IsClosedImmersion f.left := by
    have h : f.left ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S 0).hom = 𝟙 S := f.w
    let : IsClosedImmersion (f.left ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S 0).hom) :=
      h.symm ▸ inferInstanceAs (IsClosedImmersion (𝟙 S))
    exact IsClosedImmersion.of_comp f.left (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S 0).hom
  exact Has.Core.ProjectivePresentation.ofHilbertConstruction ⟨0, f, hf⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BaseProjectivePresentation.Core
