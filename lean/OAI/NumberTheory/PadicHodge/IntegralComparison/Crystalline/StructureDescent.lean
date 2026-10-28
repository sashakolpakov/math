import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RingDescent
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map

/-! # Structure Descent -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent

noncomputable section

/-!
# IntegralComparison: the original crystalline structure sheaves have ambient-ring sections

The large module presheaves satisfy sheaf descent. Therefore their
canonical maps to the original sheafifications are isomorphisms, on both
the big and small crystalline sites.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction (Coeff)
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RingDescent

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

def largeUnderlyingIso :
    BigCrystallineCohomology.largePresheaf (p := p) (J := J) (δ := δ) f ⋙ forget (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B))) ≅
      RingDescent.ringPresheaf f ⋙ forget CommRingCat.{u} ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

lemma largePresheaf_isSheaf : Presheaf.IsSheaf BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf (p := p) (J := J) (δ := δ) f) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)
    (forget (ModuleCat.{u + 1} (ExactRestriction.Coeff (B := B))))).mpr
  apply (Presheaf.isSheaf_of_iso_iff (largeUnderlyingIso f)).mpr
  exact Presheaf.isSheaf_comp_of_isSheaf BigCrystallineSite.Object.topology (RingDescent.ringPresheaf f)
    (forget CommRingCat.{u} ⋙ uliftFunctor.{u + 1}) (RingDescent.ringPresheaf_isSheaf f)

def structurePresheafIso : BigCrystallineCohomology.largePresheaf (p := p) (J := J) (δ := δ) f ≅ (BigCrystallineCohomology.structureSheaf f).obj :=
  isoSheafify BigCrystallineSite.Object.topology (largePresheaf_isSheaf f)

def smallPresheafIso : BigCrystallineSite.fromSmall.op ⋙ BigCrystallineCohomology.largePresheaf (p := p) (J := J) (δ := δ) f ≅
    Site.AffineThickening.structureModulePresheafLarge (p := p) (B := B) (J := J) (δB := δ) (f := f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

lemma smallPresheaf_isSheaf : Presheaf.IsSheaf Site.AffineThickening.topology
    (Site.AffineThickening.structureModulePresheafLarge (p := p) (B := B) (J := J) (δB := δ) (f := f)) :=
  (Presheaf.isSheaf_of_iso_iff (smallPresheafIso f)).mp
    (BigCrystallineSite.fromSmall.op_comp_isSheaf_of_isSheaf Site.AffineThickening.topology BigCrystallineSite.Object.topology
      (BigCrystallineCohomology.largePresheaf f) (largePresheaf_isSheaf f))

def smallStructurePresheafIso :
    Site.AffineThickening.structureModulePresheafLarge (p := p) (B := B) (J := J) (δB := δ) (f := f) ≅
      (Site.AffineThickening.structureModuleSheaf (p := p) (B := B) (J := J) (δB := δ) (f := f)).obj :=
  isoSheafify Site.AffineThickening.topology (smallPresheaf_isSheaf f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent
