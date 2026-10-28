import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.BundleGraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorAmpleness

/-! # External Square Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ExternalSquareEmbedding

noncomputable section

/-! Construct a power embedding of the external square of an ample bundle on a proper scheme over an affine base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsAffine S] {A : Over S} [IsProper A.hom]

def ampleExternalSquarePowerEmbedding (L : Line.Bundles.LineBundle A.left) (hL : L.IsAmple) :
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle L L) (A ⊗ A).hom := by
  have hT : (Graph.ExternalTensorBundle.externalTensorBundle L L).IsAmple :=
    Line.Bundles.LineBundle.IsAmple.externalTensor A.hom A.hom hL hL
  have : IsProper (A ⊗ A).hom :=
    inferInstanceAs (IsProper (Limits.pullback.fst A.hom A.hom ≫ A.hom))
  exact (hT.exists_powerProjectiveEmbedding (A ⊗ A).hom).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ExternalSquareEmbedding
