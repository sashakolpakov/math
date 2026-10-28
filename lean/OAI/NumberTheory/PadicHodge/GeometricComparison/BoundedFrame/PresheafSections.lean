import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PulledMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.NatIso

/-! # Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PresheafSections.BoundedFrameGeometricPresheafSections

noncomputable section

/-! Original frame section maps commute with geometric restriction
in presheaf-section coordinates, retaining the actual frame morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n
local notation "KY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fY n FY
local notation "KX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n FX
local notation "DY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.frameComplex fY n FY
local notation "DX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f n FX
local notation "aY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.sheafMap fY n FY
local notation "aX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f n FX
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricMap.map g hg n α
abbrev localSections := IntegralComparison.Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2}
  R (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n)

abbrev sectionIso := IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R
  (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n)

abbrev pulledSections := IntegralComparison.ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2}
  R (IntegralComparison.BoundedCrystalline.Site.topology f n) DY _ (IntegralComparison.BoundedFrame.PulledMap.map g hg n (FY := FY))

omit [IsSeparated f] [Mono g] in
theorem restriction_component (i : ℕ) :
    (IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fY n) DY KY aY).f i ≫
      (IntegralComparison.Sheaf.PresheafSectionRestriction.complexMap G R (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology fY n) KY).f i =
    (pulledSections g hg n (FY := FY)).f i ≫
      ((sectionIso (f := f) n).app
        ((((IntegralComparison.Bounded.PostcomposeTopology.restriction g hg n).mapHomologicalComplex (.up ℕ)).obj KY).X i)).hom :=
  congrArg (fun a => a.f i)
    (IntegralComparison.ConstantSection.ComplexRestriction.naturality.{u + 1, u, u + 2} G R
      (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology fY n) DY KY aY)

theorem component (i : ℕ) :
    (IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fY n) DY KY aY).f i ≫
      (IntegralComparison.Sheaf.PresheafSectionRestriction.complexMap G R (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology fY n) KY).f i ≫
        (localSections (f := f) n).map ((b).f i) =
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).map ((IntegralComparison.BoundedFrame.SectionChange.frameMap α).f i) ≫
      (IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n) DX KX aX).f i :=
  NatIso.NatIsoSectionSquare.square (sectionIso (f := f) n) ((b).f i) _ _ ((pulledSections g hg n (FY := FY)).f i) _ _
    (restriction_component g hg n (FY := FY) i) (IntegralComparison.BoundedFrame.PulledMap.sections_component g hg n α i)

theorem square : IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fY n) DY KY aY ≫
    IntegralComparison.Sheaf.PresheafSectionRestriction.complexMap G R (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology fY n) KY ≫
      ((localSections (p := p) (J := J) (δ := δ) (f := f) n).mapHomologicalComplex (.up ℕ)).map b =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap α) ≫
        IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n) DX KX aX := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component g hg n α i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PresheafSections.BoundedFrameGeometricPresheafSections
