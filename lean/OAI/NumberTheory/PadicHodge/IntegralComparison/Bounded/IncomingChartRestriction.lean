import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricOpenSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

/-! # Incoming Chart Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingChartRestriction

noncomputable section

/-! The original incoming crystalline section complex restricts between nested chart images. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} (fZ : Z ⟶ Spec (CommRingCat.of B))
  (g : X ⟶ Y) (h : Y ⟶ Z) (n : ℕ)

theorem property_le : BoundedOpen.Subsite.property (p := p) (J := J) (δ := δ) fZ (g ≫ h) n ≤
    BoundedOpen.Subsite.property fZ h n := by
  intro U hU
  obtain ⟨t, ht⟩ := hU
  exact ⟨t ≫ g, (Category.assoc _ _ _).trans ht⟩

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) fZ n))

def map : BoundedOpen.Resolution.complex fZ h n I ⟶
    BoundedOpen.Resolution.complex fZ (g ≫ h) n I where
  f i := (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).map
    (ModuleCat.ofHom (Incoming.SectionRestriction.restrict (Crystalline.ExactRestriction.Coeff (B := B))
      (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))
      (BoundedOpen.Subsite.property fZ (g ≫ h) n) (BoundedOpen.Subsite.property fZ h n)
      (I.cocomplex.X i).obj (property_le fZ g h n)))
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

variable {fZ} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY)

def comparison (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n) :
    (ObjectProperty.ιOfLE (property_le (p := p) (J := J) (δ := δ) fZ g h n)).obj
      ((BoundedOpen.Equivalence.openFunctor (g ≫ h)
        (Crystalline.PostcomposeComposition.overBase g h hg hh) n).obj U) ⟶
    (BoundedOpen.Equivalence.openFunctor h hh n).obj
      ((BoundedOpen.Equivalence.postcompose g hg n).obj U) :=
  ObjectProperty.homMk ((Crystalline.PostcomposeComposition.boundedIso g h hg hh n).inv.app U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingChartRestriction
