import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Has
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.PolynomialAmbient

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectivePresentation.GradedHilbert

noncomputable section

/-! The canonical projective presentation of relative polynomial projective
space, in the exact native geometry used by the Presentations statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def canonicalProjectivePresentation (M : Scheme.{u}) (n : ℕ) :
    Has.Core.ProjectivePresentation (PolynomialAmbient.GradedHilbert.relativeProjectiveOver M n) where
  dimension := n
  embedding := 𝟙 (Has.Core.projectiveSpace M n)
  closed := by
    change IsClosedImmersion (𝟙 (Has.Core.projectiveSpace M n))
    infer_instance
  over_base := Category.id_comp _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ProjectivePresentation.GradedHilbert
