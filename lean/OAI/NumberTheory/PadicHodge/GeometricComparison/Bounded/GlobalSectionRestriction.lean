import OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

/-! # Global Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction

noncomputable section

/-! Original global presheaf sections restrict naturally to the
original bounded crystalline Zariski open-section functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
abbrev globalSections := IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2}
  R (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n)

def transformation : globalSections (p := p) (J := J) (δ := δ) f n ⋙ Functor.const Y.Opensᵒᵖ ⟶
    IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) f n :=
  Functor.whiskerLeft (sheafToPresheaf (IntegralComparison.BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} R))
    (IncomingGlobal.IncomingGlobalSectionRestriction.lifted.{u + 1, u, u + 1, u, u + 2} R (ModuleCat.of R R)
      (IntegralComparison.BoundedOpen.SectionPresheaf.property f n) (IntegralComparison.BoundedOpen.SectionPresheaf.monotone f n))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction
