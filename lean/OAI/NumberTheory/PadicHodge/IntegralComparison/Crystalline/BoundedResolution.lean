import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSheafSectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Reconstruction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafInjectives

/-! # Bounded Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison

noncomputable section

/-!
# IntegralComparison: original crystalline cohomology from all bounded resolution sections

This uses a genuine injective resolution of the original structure sheaf.
Each term is reconstructed from its compatible sections on all original
bounded crystalline levels, retaining the original coefficient action.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f

def resolution : InjectiveResolution O := injectiveResolution O

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ExhaustiveSheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R BigCrystallineSite.Object.topology
    (BoundedCrystalline.Site.property (p := p) (J := J) (δ := δ) f)
    (BoundedSection.Reconstruction.monotone_property f) (resolution f).cocomplex

def homologyIso (i : ℕ) : (complex (p := p) (J := J) (δ := δ) f).homology i ≅
    ModuleCat.of R (BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f i) :=
  ExhaustiveSheafSectionComplex.homologyIso.{u + 1, u, u + 1, u + 2} R BigCrystallineSite.Object.topology (BoundedCrystalline.Site.property f)
    (BoundedSection.Reconstruction.monotone_property f) (BoundedCrystalline.Site.exists_level f) (resolution f) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison
