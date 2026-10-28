import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.SectionsExcision
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex

/-! # Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Sections

noncomputable section

/-! Forgetting local support lands in the original bounded
crystalline Ext group, through its actual open-section resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n)) (O U : Y.Opens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

def complex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((Supported.SectionsExcision.supported U (U ⊓ O) inf_le_left).mapHomologicalComplex
    (.up ℕ)).obj K

def extension (hcover : U ⊔ O = ⊤) : complex fY n I O U ⟶
    ((BoundedOpen.SectionComplex.evaluation (B := B) (⊤ : Y.Opens)).mapHomologicalComplex
      (.up ℕ)).obj (BoundedOpen.SectionComplex.complex fY n I) :=
  Supported.SectionsExcision.extensionComplex O U hcover K

def forgetSupport (hcover : U ⊔ O = ⊤) (i : ℕ) :
    (complex fY n I O U).homology i ⟶
      ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology
        (p := p) (J := J) (δ := δ) fY n i) :=
  HomologicalComplex.homologyMap (extension fY n I O U hcover) i ≫
    (BoundedOpen.SectionGlobal.homologyIso fY n I i).hom

abbrev extension_restriction (hcover : U ⊔ O = ⊤) (j : ℕ) :=
  Supported.SectionsExcision.extension_restriction O U hcover ((K).X j)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Sections
