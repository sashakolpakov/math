import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureTransportComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution

/-! # Resolution Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionComposition

noncomputable section

/-! The original injective resolution restricts compatibly along nested geometric charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (h : Y ⟶ Z) [Mono g] [Mono h]
  (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fZ n))

local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition.overBase g h hg hh
local notation "Rg" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "Rh" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) h hh n
local notation "Rc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) (g ≫ h) hc n
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution g hg n
  (GeometricResolution.resolution h hh n I)
local notation "IC" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution (g ≫ h) hc n I

def iso : (IX).cocomplex ≅ (IC).cocomplex :=
  (NatIso.mapHomologicalComplex (RestrictionComposition.iso g h hg hh n) (.up ℕ)).app I.cocomplex

theorem augmentation : (IX).ι ≫ (iso g h hg hh n I).hom = (IC).ι :=
  Single.ComplexTransportComposition.map Rh Rg Rc
    (RestrictionComposition.iso g h hg hh n)
    (BoundedOpen.Sheaves.structureTransport h hh n)
    (BoundedOpen.Sheaves.structureTransport g hg n)
    (BoundedOpen.Sheaves.structureTransport (g ≫ h) hc n)
    (StructureTransportComposition.hom g h hg hh n) I.ι

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionComposition
