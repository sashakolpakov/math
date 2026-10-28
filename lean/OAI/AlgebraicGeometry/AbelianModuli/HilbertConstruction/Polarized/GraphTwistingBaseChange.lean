import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.GraphBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphBundles

/-! # Graph Twisting Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphTwistingBaseChange

noncomputable section

/-! In an external-power embedding of canonical polarization bundles, every base-changed graph has the expected actual tensor bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u

variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle A.graphBundle B.graphBundle)
  (A.abelian.scheme ⊗ B.abelian.scheme).hom) (f : T ⟶ S)

def polarizedGraphTwistingBundleIso
    (p : (A.pullback f).abelian.scheme ⟶ (B.pullback f).abelian.scheme) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).pullback
      (MorphismGraphFamilies.familyGraph p ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f
        (E.relativeMorphism A.graphBundle B.graphBundle)).left).sheaf ≅
      (((A.pullback f).graphBundle.tensor ((B.pullback f).graphBundle.pullback p.left)).tensorPower E.degree).sheaf :=
  E.graphTwistingBundle_baseChangeIso A.graphBundle B.graphBundle f p ≪≫
    (TensorPower.Maps.tensorPowerFunctor _ E.degree).mapIso (Tensor.Bifunctor.tensorModuleMapIso
      (A.graphBundle_baseChangeIso f).symm
      ((Scheme.Modules.pullback p.left).mapIso (B.graphBundle_baseChangeIso f).symm))

def polarizedIsoGraphTwistingBundleIso
    (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback f) (B.pullback f)) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).pullback
      (MorphismGraphFamilies.familyGraph e.abelian.hom ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f
        (E.relativeMorphism A.graphBundle B.graphBundle)).left).sheaf ≅
      (((A.pullback f).graphBundle.tensor (A.pullback f).graphBundle).tensorPower E.degree).sheaf :=
  polarizedGraphTwistingBundleIso A B E f e.abelian.hom ≪≫
    (TensorPower.Maps.tensorPowerFunctor _ E.degree).mapIso (Tensor.Bifunctor.tensorModuleMapIso (Iso.refl _) e.graphBundleIso)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.GraphTwistingBaseChange
