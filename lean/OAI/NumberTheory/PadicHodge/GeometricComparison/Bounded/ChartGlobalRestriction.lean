import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartSectionFunctorIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction

/-! # Chart Global Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartGlobalRestriction.BoundedChartGlobalRestriction

noncomputable section

/-! The geometric-chart section identification carries actual global
restriction to the original Zariski image-open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

abbrev subsiteMap := IntegralComparison.Sheaf.PresheafSectionRestriction.map.{u + 1, u, u + 2}
  (IntegralComparison.BoundedOpen.Subsite.inclusion (p := p) (J := J) (δ := δ) fY g n) R
    (IntegralComparison.BoundedOpen.Subsite.topology fY g n) (IntegralComparison.BoundedCrystalline.Site.topology fY n)

abbrev geometricMap := IntegralComparison.Sheaf.PresheafSectionRestriction.map.{u + 1, u, u + 2}
  (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n) R
    (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology fY n)

def imageMap : GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections (p := p) (J := J) (δ := δ) fY n ⟶
    IntegralComparison.BoundedOpen.SectionComplex.functor fY n ⋙ IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := B) g.opensRange where
  app F := ((GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fY n).app F).app (op g.opensRange)
  naturality _ _ a := congrArg (fun η => η.app (op g.opensRange))
    ((GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fY n).naturality a)

theorem subsite_geometric : subsiteMap (p := p) (J := J) (δ := δ) g n ≫
    (ChartSectionFunctorIso.BoundedChartSectionFunctorIso.geometricIso g hg n).hom = geometricMap g hg n := by
  apply NatTrans.ext
  funext F
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem subsite_image : subsiteMap (p := p) (J := J) (δ := δ) (fY := fY) g n ≫
    (ChartSectionFunctorIso.BoundedChartSectionFunctorIso.imageIso g n).hom = imageMap g n := by
  apply NatTrans.ext
  funext F
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem square : geometricMap (p := p) (J := J) (δ := δ) g hg n ≫
    (ChartSectionFunctorIso.BoundedChartSectionFunctorIso.iso g hg n).hom = imageMap g n := by
  rw [← subsite_geometric, ChartSectionFunctorIso.BoundedChartSectionFunctorIso.iso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact subsite_image (fY := fY) g n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartGlobalRestriction.BoundedChartGlobalRestriction
