import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphPolarizationPowers
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismHom

/-! # Graph Polarization Powers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.GraphPolarizationPowers

noncomputable section

/-! The product-polarization identity on the actual relative Hom graph,
with its source identified with the pulled-back abelian scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.EndomorphismHom.EndomorphismFamilies
universe u

theorem schemePicardPullback_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Z) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (f ≫ g) q = Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback f (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback g q) :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp f g q

theorem e34ProductLine_pullback_class {S : Scheme.{u}} (X : Over S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) {Y : Scheme.{u}} (w : Y ⟶ (X ⨯ X).left)
    (a b : Y ⟶ X.left)
    (ha : w ≫ (prod.fst : X ⨯ X ⟶ X).left = a)
    (hb : w ≫ (prod.snd : X ⨯ X ⟶ X).left = b) :
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback w (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine X P)) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) * Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback b (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) := by
  change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback w
    (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (prod.fst : X ⨯ X ⟶ X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) *
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (prod.snd : X ⨯ X ⟶ X).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)) = _
  rw [map_mul, ← schemePicardPullback_comp_apply, ← schemePicardPullback_comp_apply, ha, hb]

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (T : Over S)
    (v : (A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme)

def relativeGraphToProduct : (A.pullback T.hom).scheme.left ⟶ (A.scheme ⨯ A.scheme).left :=
  (EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso A T).inv ≫
    (prod.lift (prod.snd : T ⨯ A.scheme ⟶ A.scheme) (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T v)).left

theorem relativeGraphToProduct_fst :
    relativeGraphToProduct A T v ≫ (prod.fst : A.scheme ⨯ A.scheme ⟶ A.scheme).left =
      pullback.fst A.scheme.hom T.hom := by
  rw [relativeGraphToProduct, Category.assoc, ← Over.comp_left, prod.lift_fst]
  rw [← EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso_fst A T, Iso.inv_hom_id_assoc]

theorem relativeGraphToProduct_snd :
    relativeGraphToProduct A T v ≫ (prod.snd : A.scheme ⨯ A.scheme ⟶ A.scheme).left =
      v.left ≫ pullback.fst A.scheme.hom T.hom := by
  rw [relativeGraphToProduct, Category.assoc, ← Over.comp_left, prod.lift_snd,
    EndomorphismHom.EndomorphismFamilies.relativeHomEquiv_left, Iso.inv_hom_id_assoc]

theorem relativeGraphToProduct_power (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (r m : ℕ)
    (hv : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback v.left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (P.pullback (pullback.fst A.scheme.hom T.hom))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (P.pullback (pullback.fst A.scheme.hom T.hom)) ^ r) :
    Nonempty ((((Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine A.scheme P).tensorPower m).pullback
      (relativeGraphToProduct A T v)).sheaf ≅
        ((P.tensorPower ((r + 1) * m)).pullback (pullback.fst A.scheme.hom T.hom)).sheaf) := by
  let c : (A.pullback T.hom).scheme.left ⟶ A.scheme.left := pullback.fst A.scheme.hom T.hom
  have hv' : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback v.left (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P)) =
      Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf P) ^ r := hv
  have hp := e34ProductLine_pullback_class A.scheme P (relativeGraphToProduct A T v)
    c (v.left ≫ c) (relativeGraphToProduct_fst A T v) (relativeGraphToProduct_snd A T v)
  rw [schemePicardPullback_comp_apply] at hp
  rw [hv'] at hp
  have he : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine A.scheme P).tensorPower m).pullback
      (relativeGraphToProduct A T v)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (((P.tensorPower ((r + 1) * m)).pullback c)) := by
    change Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (relativeGraphToProduct A T v)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((Presentations.GraphPolarizationPowers.PolarizationEmbedding.e34ProductLine A.scheme P).tensorPower m)) =
        Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback c (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (P.tensorPower ((r + 1) * m)))
    rw [AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow, hp, ← pow_succ', ← pow_mul, AmpleTensor.PolarizationAmpleness.tensorPower_class, map_pow]
  exact Quotient.exact he

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.GraphPolarizationPowers
