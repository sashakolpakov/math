import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingCartesian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBaseChange

/-! # Product Embedding Twisting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual Cartesian product embedding and the native product of the
base-changed presentations have isomorphic pulled-back O(1) bundles. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

def Relative.ProductEmbeddingTwisting.relativeProjectiveGraphEmbedding_twistingBundleIso
    {S T : Scheme.{u}} {X Y : Over S} {n : ℕ} (f : T ⟶ S)
    (j : X ⊗ Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T n).pullback (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).left).sheaf ≅
      (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback j.left).pullback
        (Graph.FamilyNaturality.overProductBaseChangeMap f X Y)).sheaf := by
  let O := RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n
  let j' := RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j
  let c := Graph.FamilyNaturality.overProductBaseChangeMap f X Y
  exact (Scheme.Modules.pullback j'.left).mapIso
      (RelativeProjective.TwistingBaseChange.relativeProjectiveTwistingBundle_baseChangeIso f n).symm ≪≫
    (Scheme.Modules.pullbackComp j'.left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n)).app O.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (Relative.GraphEmbeddingCartesian.relativeProjectiveGraphEmbedding_over f j)).app O.sheaf ≪≫
    (Scheme.Modules.pullbackComp c j.left).symm.app O.sheaf

def Projective.ProjectivePresentations.ProjectivePresentation.relativeProductEmbeddingTwistingIso
    {S T : Scheme.{u}} {X Y : Over S}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y) (f : T ⟶ S) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T (P.product Q).dimension).pullback
      (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f (P.product Q).embedding).left).sheaf ≅
      ((P.baseChange f).product (Q.baseChange f)).ampleLineBundle.sheaf :=
  Relative.ProductEmbeddingTwisting.relativeProjectiveGraphEmbedding_twistingBundleIso f (P.product Q).embedding ≪≫
    (P.productBaseChangeTwistingBundleIso Q f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
