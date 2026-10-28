import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.NoetherianAffineProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.GraphTwisting

/-! # Product Power Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ProductPowerEmbedding

noncomputable section

/-! The canonical polarization bundles construct an actual external-power product embedding for every pair of polarized objects over a Noetherian affine base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u

def polarizedProductPowerEmbedding
    {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    {g N : ℕ} {δ : Fin g → ℕ} (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) :
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle A.graphBundle B.graphBundle)
      (A.abelian.scheme ⊗ B.abelian.scheme).hom := by
  have hL : (Graph.ExternalTensorBundle.externalTensorBundle A.graphBundle B.graphBundle).IsAmple :=
    Line.Bundles.LineBundle.IsAmple.externalTensor A.abelian.scheme.hom B.abelian.scheme.hom
      A.graphBundle_isAmple_of_noetherian_affine B.graphBundle_isAmple_of_noetherian_affine
  have : IsProper (A.abelian.scheme ⊗ B.abelian.scheme).hom :=
    inferInstanceAs (IsProper (Limits.pullback.fst A.abelian.scheme.hom B.abelian.scheme.hom ≫ A.abelian.scheme.hom))
  exact (hL.exists_powerProjectiveEmbedding (A.abelian.scheme ⊗ B.abelian.scheme).hom).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ProductPowerEmbedding
