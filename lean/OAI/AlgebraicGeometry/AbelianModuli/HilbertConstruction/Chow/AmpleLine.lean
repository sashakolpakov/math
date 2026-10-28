import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectiveChowModification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationAmpleBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.OverSeparatedBase

/-! # Ample Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

noncomputable section

/-! The constructed Chow modification has an actual line bundle ample over its base and target. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

def Modification.ChowModification.Model.ampleLineBundle (D : Modification.ChowModification.Model f) : Line.Bundles.LineBundle D.scheme :=
  D.projectivePresentation.ampleLineBundle

theorem Modification.ChowModification.Model.ampleLineBundle_isAmple (D : Modification.ChowModification.Model f) : D.ampleLineBundle.IsAmple :=
  D.projectivePresentation.ampleLineBundle_isAmple

theorem Modification.ChowModification.Model.ampleLineBundle_relative_to_base (D : Modification.ChowModification.Model f) :
    D.ampleLineBundle.IsRelativelyAmple (D.projection ≫ f) :=
  Ample.OverSeparatedBase.ample_isRelativelyAmple_over_separated (D.projection ≫ f) D.ampleLineBundle_isAmple

theorem Modification.ChowModification.Model.ampleLineBundle_relative_to_target (D : Modification.ChowModification.Model f) [IsProper f] :
    D.ampleLineBundle.IsRelativelyAmple D.projection := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact Ample.OverSeparatedBase.ample_isRelativelyAmple_over_separated D.projection D.ampleLineBundle_isAmple

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow
