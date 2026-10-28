import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricOpenSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartOpenImage

/-! # Chart Section Functor Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso.BoundedChartSectionFunctorIso

noncomputable section

/-! Actual geometric chart sections agree naturally with the original
Zariski open-section functor for arbitrary sheaf complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

abbrev subsiteSections := IntegralComparison.BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) fY g n ⋙
  IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedOpen.Subsite.topology (p := p) (J := J) (δ := δ) fY g n)

def geometricIso : subsiteSections (p := p) (J := J) (δ := δ) g n ≅
    IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n ⋙
      IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n) :=
  NatIso.ofComponents (fun F => (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapIso
    (IntegralComparison.Bounded.GeometricOpenSections.linearEquiv g hg n F).toModuleIso) (by
      intro F H a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

def imageIso : subsiteSections (p := p) (J := J) (δ := δ) g n ≅
    IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n ⋙
      IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := B) g.opensRange :=
  NatIso.ofComponents (fun F => (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapIso
    (IntegralComparison.Bounded.ChartOpenImage.linearEquiv fY g n F).toModuleIso) (by
      intro F H a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

def iso : IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n ⋙
      IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n) ≅
    IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n ⋙
      IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := B) g.opensRange :=
  (geometricIso g hg n).symm ≪≫ imageIso g n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso.BoundedChartSectionFunctorIso
