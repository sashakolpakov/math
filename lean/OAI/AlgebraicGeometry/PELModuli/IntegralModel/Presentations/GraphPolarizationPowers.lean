import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GraphPolarizationPowers
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.HomFunctor

/-! # Graph Polarization Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphPolarizationPowers

noncomputable section

/-! Graph polarization on Presentations's chosen categorical product. Its actual
source pullbacks agree with those of the native monoidal graph. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u
variable {S : Scheme.{u}} (X : Over S) (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)

def e34Graph (f : X ⟶ X) : X ⟶ X ⨯ X := prod.lift (𝟙 X) f

theorem e34Graph_closed [IsSeparated X.hom] (f : X ⟶ X) : IsClosedImmersion (e34Graph X f).left := by
  have h : (e34Graph X f).left ≫ (prod.fst : X ⨯ X ⟶ X).left = 𝟙 X.left :=
    congrArg Over.Hom.left (prod.lift_fst (𝟙 X) f)
  have : IsClosedImmersion ((e34Graph X f).left ≫ (prod.fst : X ⨯ X ⟶ X).left) := by
    rw [h]
    infer_instance
  have : IsSeparated (prod.fst : X ⨯ X ⟶ X).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (e34Graph X f).left (prod.fst : X ⨯ X ⟶ X).left

def e34ProductLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (X ⨯ X).left :=
  (P.pullback (prod.fst : X ⨯ X ⟶ X).left).tensor (P.pullback (prod.snd : X ⨯ X ⟶ X).left)

theorem e34Graph_product_class (f : X ⟶ X) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (e34Graph X f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (e34ProductLine X P)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) := by
  have hf : (e34Graph X f).left ≫ (prod.fst : X ⨯ X ⟶ X).left = 𝟙 X.left :=
    congrArg Over.Hom.left (prod.lift_fst (𝟙 X) f)
  have hs : (e34Graph X f).left ≫ (prod.snd : X ⨯ X ⟶ X).left = f.left :=
    congrArg Over.Hom.left (prod.lift_snd (𝟙 X) f)
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (e34Graph X f).left
    (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (prod.fst : X ⨯ X ⟶ X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) *
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (prod.snd : X ⨯ X ⟶ X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)) = _
  rw [map_mul]
  have h₁ := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e34Graph X f).left
    (prod.fst : X ⨯ X ⟶ X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)).symm.trans
      ((congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)) hf).trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)))
  have h₂ := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (e34Graph X f).left
    (prod.snd : X ⨯ X ⟶ X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)).symm.trans
      (congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)) hs)
  exact congrArg₂ (fun a b : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X.left => a * b) h₁ h₂

theorem e34Graph_power_comparison (f : X ⟶ X) (m : ℕ) :
    Nonempty ((((e34ProductLine X P).tensorPower m).pullback (e34Graph X f).left).sheaf ≅
      (((GraphPolarizationPowers.GraphPolarization.productLine X P).tensorPower m).pullback
        (GraphPolarizationPowers.GraphPolarization.graph X f).left).sheaf) := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((e34ProductLine X P).tensorPower m).pullback (e34Graph X f).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((GraphPolarizationPowers.GraphPolarization.productLine X P).tensorPower m).pullback
        (GraphPolarizationPowers.GraphPolarization.graph X f).left) := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (e34Graph X f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((e34ProductLine X P).tensorPower m)) =
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (GraphPolarizationPowers.GraphPolarization.graph X f).left
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((GraphPolarizationPowers.GraphPolarization.productLine X P).tensorPower m))
    rw [AmpleTensor.PolarizationAmpleness.tensorPower_class, AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow, map_pow,
      e34Graph_product_class, GraphPolarizationPowers.GraphPolarization.graph_product_class]
  exact Quotient.exact h

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphPolarizationPowers
