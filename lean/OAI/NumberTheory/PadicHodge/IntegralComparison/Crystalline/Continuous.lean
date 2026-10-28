import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Lifts
import OAI.NumberTheory.PadicHodge.IntegralComparison.SiteLifts

/-! # Continuous -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Continuous

noncomputable section

/-!
# IntegralComparison: continuity of big crystalline postcomposition

The incoming lifts and triangle lifts are the explicit constructions on
divided-power thickenings. This proves continuity for the topology generated
by the actual cartesian Zariski covering families.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Lifts
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Coverings OAI.NumberTheory.PadicHodge.IntegralComparison.SiteLifts

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable {fY : Y ⟶ Spec (CommRingCat.of B)}
variable (g : X ⟶ Y) (hg : g ≫ fY = f)

def incomingLifts : SiteLifts.IncomingLifts (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg) where
  object α := Lifts.liftedObject g hg α
  iso α := Lifts.liftedIso g hg α
  hom α := Lifts.liftedHom g hg α
  map_hom α := Lifts.liftedHom_map g hg α
  fullTriangle a b c h :=
    ⟨Lifts.liftTriangle g hg a b c h, Lifts.liftTriangle_map g hg a b c h, Lifts.liftTriangle_comp g hg a b c h⟩

instance postcompose_continuous :
    (BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg).IsContinuous
      BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology :=
  (incomingLifts g hg).continuous BigCrystallineSite.Object.precoverage BigCrystallineSite.Object.precoverage
    (Coverings.postcompose_preserves_coverings g hg)

variable (A : Type*) [Category A]

/-- Restriction of actual sheaves along crystalline postcomposition. -/
def sheafRestriction :
    Sheaf (BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := fY)) A ⥤
      Sheaf (BigCrystallineSite.Object.topology (p := p) (J := J) (δ := δ) (f := f)) A :=
  (BigCrystallineSite.postcompose g hg).sheafPushforwardContinuous A BigCrystallineSite.Object.topology BigCrystallineSite.Object.topology

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Continuous
