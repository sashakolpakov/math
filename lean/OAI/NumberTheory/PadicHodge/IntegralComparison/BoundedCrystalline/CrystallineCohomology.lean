import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Extension
import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution

/-! # Crystalline Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology

noncomputable section

/-!
# IntegralComparison: restriction of original crystalline cohomology to a bounded level

The level coefficient sheaf is restriction of the original structure
sheaf. Exact restriction preserves the original constant source and
injectives, and therefore gives both the actual map on Ext and a
restricted injective resolution.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

abbrev structureSheaf : Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  (Site.restriction f n).obj (BigCrystallineCohomology.structureSheaf f)

abbrev constantUnit : Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  (constantSheaf (Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))).obj
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))

instance hasExt : HasExt.{u + 2} (Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) :=
  HasExt.standard _

instance restriction_linear :
    (Site.restriction (p := p) (J := J) (δ := δ) f n).Linear (Crystalline.ExactRestriction.Coeff (B := B)) where
  map_smul := by intros; rfl

def constantUnitIso : (Site.restriction f n).obj
    (BigCrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f) ≅ constantUnit f n :=
  ((Site.inclusion f n).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) (Site.topology f n) BigCrystallineSite.Object.topology).symm.app
      ((Functor.const (BigCrystallineSite.Object p B J δ f)ᵒᵖ).obj (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))))

abbrev Cohomology (i : ℕ) := Abelian.Ext.{u + 2} (constantUnit (p := p) (J := J) (δ := δ) f n)
  (structureSheaf f n) i

def restriction (i : ℕ) : BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i →ₗ[Crystalline.ExactRestriction.Coeff (B := B)]
    Cohomology (p := p) (J := J) (δ := δ) f n i :=
  (Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := B)) (constantUnitIso f n) (Iso.refl _) i).toLinearMap.comp
    ((Site.restriction f n).mapExtLinearMap (Crystalline.ExactRestriction.Coeff (B := B))
      (BigCrystallineCohomology.constantUnit f) (BigCrystallineCohomology.structureSheaf f) i)

def resolution (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f)) :
    InjectiveResolution (structureSheaf (p := p) (J := J) (δ := δ) f n) :=
  ExactInjectiveResolution.map (Site.restriction f n) I

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
