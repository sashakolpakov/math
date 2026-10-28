import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionComposition

/-! # Resolution Congr -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionCongr

noncomputable section

/-! Original crystalline resolution restriction respects equality of geometric chart maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g g' : X ⟶ Y) [Mono g] [Mono g'] (hg : g ≫ fY = fX) (hg' : g' ≫ fY = fX) (e : g = g') (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))

def iso : (GeometricResolution.resolution g hg n I).cocomplex ≅
    (GeometricResolution.resolution g' hg' n I).cocomplex := by
  cases e
  exact Iso.refl _

theorem augmentation : (GeometricResolution.resolution g hg n I).ι ≫
    (iso g g' hg hg' e n I).hom = (GeometricResolution.resolution g' hg' n I).ι := by
  cases e
  exact Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionCongr
