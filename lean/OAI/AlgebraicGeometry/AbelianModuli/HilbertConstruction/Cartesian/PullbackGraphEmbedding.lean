import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackReembedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ProjectedGraphRecovery

/-! # Pullback Graph Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PullbackGraphEmbedding

noncomputable section

/-! The base-changed product embedding is transported into any specified Cartesian ambient model, with exact comparison to the categorical pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S T : Scheme.{u}} {A B P : Over S} {Q : Over T}
variable (p : Q.left ⟶ P.left) (f : T ⟶ S) (hp : IsPullback p Q.hom P.hom f)
variable (j : A ⊗ B ⟶ P)

def cartesianPullbackGraphEmbedding :
    (Over.pullback f).obj A ⊗ (Over.pullback f).obj B ⟶ Q :=
  Pullback.ProjectedGraphRecovery.pullbackProductEmbedding f j ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).inv

instance cartesianPullbackGraphEmbedding_closed [IsClosedImmersion j.left] :
    IsClosedImmersion (cartesianPullbackGraphEmbedding p f hp j).left := by
  have : IsClosedImmersion (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).inv.left :=
    Grassmann.ProjectivePresentation.overIso_closedImmersion (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).symm
  change IsClosedImmersion ((Pullback.ProjectedGraphRecovery.pullbackProductEmbedding f j).left ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).inv.left)
  infer_instance

theorem cartesianPullbackGraphEmbedding_comp :
    cartesianPullbackGraphEmbedding p f hp j ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom =
      Pullback.ProjectedGraphRecovery.pullbackProductEmbedding f j := by
  simp only [cartesianPullbackGraphEmbedding, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PullbackGraphEmbedding
