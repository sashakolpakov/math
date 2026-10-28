import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineContinuous
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology

/-! # Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map.Comparison

noncomputable section

/-!
# IntegralComparison: the natural map from big to small crystalline cohomology

Restriction is proved exact using continuity and cocontinuity of the
actual inclusion. It preserves the constant and structure sheaves, so it
induces a linear map to the previously defined small-site Ext cohomology.
Bijectivity of this comparison map is not asserted here.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction (Coeff ModuleSheaf)

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

abbrev SmallModuleSheaf :=
  Sheaf (Site.AffineThickening.topology (p := p) (J := J) (δB := δ) (f := f))
    (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))

abbrev restriction : ExactRestriction.ModuleSheaf (p := p) (J := J) (δ := δ) f ⥤
    SmallModuleSheaf (p := p) (J := J) (δ := δ) f :=
  BigCrystallineSite.fromSmall.sheafPushforwardContinuous (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))
    Site.AffineThickening.topology BigCrystallineSite.Object.topology

instance restriction_additive : (restriction (p := p) (J := J) (δ := δ) f).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction (p := p) (J := J) (δ := δ) f).Linear (ExactRestriction.Coeff (B := B)) where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction (p := p) (J := J) (δ := δ) f).IsLeftAdjoint :=
  (BigCrystallineSite.fromSmall.sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))
    Site.AffineThickening.topology BigCrystallineSite.Object.topology).isLeftAdjoint

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (restriction (p := p) (J := J) (δ := δ) f) := by infer_instance

instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction (p := p) (J := J) (δ := δ) f) := by infer_instance

def presheafTransport :
    BigCrystallineSite.fromSmall.op ⋙ BigCrystallineCohomology.largePresheaf
        (p := p) (J := J) (δ := δ) f ≅
      Site.AffineThickening.structureModulePresheafLarge (p := p) (J := J) (δB := δ) (f := f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

def structureTransport :
    (restriction f).obj (BigCrystallineCohomology.structureSheaf
        (p := p) (J := J) (δ := δ) f) ≅
      Site.AffineThickening.structureModuleSheaf (p := p) (J := J) (δB := δ) (f := f) :=
  (BigCrystallineSite.fromSmall.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B))) Site.AffineThickening.topology BigCrystallineSite.Object.topology).symm.app
      (BigCrystallineCohomology.largePresheaf f) ≪≫
    (presheafToSheaf Site.AffineThickening.topology (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B)))).mapIso (presheafTransport f)

def constantTransport :
    (restriction f).obj (BigCrystallineCohomology.constantUnit
        (p := p) (J := J) (δ := δ) f) ≅
      Site.AffineThickening.constantBaseSheaf (p := p) (J := J) (δB := δ) (f := f) :=
  (BigCrystallineSite.fromSmall.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B))) Site.AffineThickening.topology BigCrystallineSite.Object.topology).symm.app
      ((Functor.const _).obj (ModuleCat.of (ExactRestriction.Coeff (B := B)) (ExactRestriction.Coeff (B := B))))

def integralComparison (n : ℕ) :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n →ₗ[ExactRestriction.Coeff (B := B)]
      Site.AffineThickening.IntegralModuleCohomology (p := p) (J := J) (δB := δ) (f := f) n :=
  (Etale.Frobenius.extIsoCongr (ExactRestriction.Coeff (B := B))
    (constantTransport f) (structureTransport f) n).toLinearMap.comp
      ((restriction f).mapExtLinearMap (ExactRestriction.Coeff (B := B))
        (BigCrystallineCohomology.constantUnit f)
        (BigCrystallineCohomology.structureSheaf f) n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map.Comparison
