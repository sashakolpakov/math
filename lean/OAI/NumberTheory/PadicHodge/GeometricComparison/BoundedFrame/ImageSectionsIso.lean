import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RestrictedSectionsIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.ChartGlobalRestriction

/-! # Image Sections Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ImageSectionsIso.BoundedFrameImageSectionsIso

noncomputable section

/-! The original frame section map on a geometric chart is invertible
in the original Zariski image-open coordinates whenever the local section map is. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ fY = f) (n : ℕ)
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
abbrev globalMap := IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2}
  R (IntegralComparison.BoundedCrystalline.Site.topology fY n) DY KY aY

def comparisonIso := (NatIso.mapHomologicalComplex
  (Bounded.ChartSectionFunctorIso.BoundedChartSectionFunctorIso.iso (p := p) (J := J) (δ := δ) g hg n) (.up ℕ)).app KY

def map := globalMap n (FY := FY) ≫
  (NatTrans.mapHomologicalComplex (Bounded.ChartGlobalRestriction.BoundedChartGlobalRestriction.imageMap
    (p := p) (J := J) (δ := δ) (fY := fY) g n) (.up ℕ)).app KY

omit [IsSeparated f] in
theorem map_eq : map g n (FY := FY) =
    RestrictedSectionsIso.BoundedFrameRestrictedSectionsIso.map g hg n (FY := FY) ≫ (comparisonIso g hg n (FY := FY)).hom := by
  have h := congrArg (fun a => (NatTrans.mapHomologicalComplex a (.up ℕ)).app KY)
    (Bounded.ChartGlobalRestriction.BoundedChartGlobalRestriction.square (p := p) (J := J) (δ := δ) g hg n)
  rw [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app] at h
  exact ((Category.assoc _ _ _).trans (congrArg (fun a => globalMap n (FY := FY) ≫ a) h)).symm

variable [IsIso α] (hlocal : IsIso (IntegralComparison.BoundedFrame.DeRhamSections.sectionsMap f n FX))

include hlocal α in
theorem isIso : IsIso (map g n (FY := FY)) := by
  let h : IsIso (RestrictedSectionsIso.BoundedFrameRestrictedSectionsIso.map g hg n (FY := FY)) :=
    RestrictedSectionsIso.BoundedFrameRestrictedSectionsIso.isIso g hg n α hlocal
  let e := comparisonIso g hg n (FY := FY)
  have he : IsIso e.hom := inferInstance
  rw [map_eq g hg n]
  exact (isIso_comp_right_iff _ e.hom).mpr h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ImageSectionsIso.BoundedFrameImageSectionsIso
