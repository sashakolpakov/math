import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.GraphTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingCartesian

/-! # Graph Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual twisting bundle of a base-changed external-power embedding, and of every graph in it, is computed by the pulled-back factor bundles. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u

variable {S T : Scheme.{u}} {A B : Over S} (L : Line.Bundles.LineBundle A.left) (M : Line.Bundles.LineBundle B.left)
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (Graph.ExternalTensorBundle.externalTensorBundle L M) (A ⊗ B).hom) (f : T ⟶ S)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.twistingBundle_baseChangeIso :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).pullback
      (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f (E.relativeMorphism L M)).left).sheaf ≅
      ((Graph.ExternalTensorBundle.externalTensorBundle (A := (Over.pullback f).obj A) (B := (Over.pullback f).obj B)
        (L.pullback (Limits.pullback.fst A.hom f))
        (M.pullback (Limits.pullback.fst B.hom f))).tensorPower E.degree).sheaf := by
  let O := RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S E.dimension
  let j := E.relativeMorphism L M
  let j' := RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j
  let c := Graph.FamilyNaturality.overProductBaseChangeMap f A B
  exact (Scheme.Modules.pullback j'.left).mapIso
      (RelativeProjective.TwistingBaseChange.relativeProjectiveTwistingBundle_baseChangeIso f E.dimension).symm ≪≫
    (Scheme.Modules.pullbackComp j'.left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f E.dimension)).app O.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (Relative.GraphEmbeddingCartesian.relativeProjectiveGraphEmbedding_over f j)).app O.sheaf ≪≫
    (Scheme.Modules.pullbackComp c j.left).symm.app O.sheaf ≪≫
    (Scheme.Modules.pullback c).mapIso
      (E.twistingBundleIso (A ⊗ B).hom ≪≫ E.externalPowerIso L M) ≪≫
    (Graph.ExternalTensorBundle.externalTensorBundle L M).powerBaseChangeIso c E.degree ≪≫
    (TensorPower.Maps.tensorPowerFunctor _ E.degree).mapIso (External.TensorBaseChange.externalTensorBundle_baseChangeIso f L M)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.graphTwistingBundle_baseChangeIso
    (p : (Over.pullback f).obj A ⟶ (Over.pullback f).obj B) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).pullback
      (MorphismGraphFamilies.familyGraph p ≫ RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f (E.relativeMorphism L M)).left).sheaf ≅
      (((L.pullback (Limits.pullback.fst A.hom f)).tensor
        ((M.pullback (Limits.pullback.fst B.hom f)).pullback p.left)).tensorPower E.degree).sheaf := by
  let g := (MorphismGraphFamilies.familyGraph p).left
  let j := (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f (E.relativeMorphism L M)).left
  let L' := L.pullback (Limits.pullback.fst A.hom f)
  let M' := M.pullback (Limits.pullback.fst B.hom f)
  exact (Scheme.Modules.pullbackComp g j).symm.app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle T E.dimension).sheaf ≪≫
    (Scheme.Modules.pullback g).mapIso (E.twistingBundle_baseChangeIso L M f) ≪≫
    (Graph.ExternalTensorBundle.externalTensorBundle (A := (Over.pullback f).obj A) (B := (Over.pullback f).obj B)
      L' M').powerBaseChangeIso g E.degree ≪≫
    (TensorPower.Maps.tensorPowerFunctor _ E.degree).mapIso (Graph.ExternalTensorBundle.graphExternalTensorBundleIso p L' M')

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
