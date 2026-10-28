import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PresheafSections
import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.FunctorIsomorphisms
import OAI.NumberTheory.PadicHodge.GeometricComparison.IsIso

/-! # Restricted Sections Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RestrictedSectionsIso.BoundedFrameRestrictedSectionsIso

noncomputable section

/-! An invertible local frame section map makes the original global
frame section map invertible after actual geometric chart restriction. -/

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

abbrev localMap := IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2}
  R (IntegralComparison.BoundedCrystalline.Site.topology f n) DX KX aX

def map := IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fY n) DY KY aY ≫
  IntegralComparison.Sheaf.PresheafSectionRestriction.complexMap G R (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology fY n) KY

variable [IsIso α] (hlocal : IsIso (IntegralComparison.BoundedFrame.DeRhamSections.sectionsMap f n FX))

include hlocal in
theorem local_isIso : IsIso (localMap (f := f) n (FX := FX)) := by
  let := hlocal
  change IsIso (IntegralComparison.BoundedFrame.DeRhamSections.sectionsMap f n FX ≫
    (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R (IntegralComparison.BoundedCrystalline.Site.topology f n) KX).hom)
  infer_instance

include hlocal α in
theorem isIso : IsIso (BoundedFrameRestrictedSectionsIso.map g hg n (FY := FY)) := by
  let := Frame.FunctorIsomorphisms.FrameFunctorIsomorphisms.geometricMap n g hg α
  let := Frame.FunctorIsomorphisms.FrameFunctorIsomorphisms.frameMap n α
  have hpost : IsIso (((localSections (f := f) n).mapHomologicalComplex (.up ℕ)).map b) := inferInstance
  have hsource : IsIso (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap α)) := inferInstance
  have hsquare := (Category.assoc _ _ _).trans (PresheafSections.BoundedFrameGeometricPresheafSections.square g hg n α)
  exact GeometricComparison.IsIso.IsIsoSquare.left (BoundedFrameRestrictedSectionsIso.map g hg n (FY := FY)) _ _ _ hsquare hpost hsource (local_isIso n hlocal)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RestrictedSectionsIso.BoundedFrameRestrictedSectionsIso
