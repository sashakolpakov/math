import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.GeometricAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Ampleness

/-! # Field Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every polarized full-level abelian object over an arbitrary field has an ample canonical graph bundle and an actual projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_isAmple_overField : A.graphBundle.IsAmple :=
  A.graphBundle.isAmple_of_geometric_fibers_overField A.abelian.scheme.hom
    A.graphBundle_ample_geometricFiber

def PolarizationData.PolarizedAbelianWithFullLevel.projectivePresentation_overField : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme :=
  A.graphBundle_isAmple_overField.projectivePresentation A.abelian.scheme.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
