import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Topology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Sheaves -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves

noncomputable section

/-!
# IntegralComparison: the actual bounded chart sheaf equivalence retains both cohomology coefficients
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "JX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n
local notation "JY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fY n
local notation "JO" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.topology (p := p) (J := J) (δ := δ) fY g n
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.openFunctor (p := p) (J := J) (δ := δ) g hg n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n

def equivalence : Subsite.ModuleSheaf (p := p) (J := J) (δ := δ) fY g n ≌
    BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n := by
  let e := BoundedOpen.Equivalence.equivalence (p := p) (J := J) (δ := δ) g hg n
  letI : e.symm.inverse.IsDenseSubsite JX JO := Topology.dense g hg n
  exact e.symm.sheafCongr JO JX (ModuleCat.{u + 1} R)

instance equivalence_additive : (equivalence (p := p) (J := J) (δ := δ) g hg n).functor.Additive where
  map_add := by intros; rfl

instance equivalence_linear : (equivalence (p := p) (J := J) (δ := δ) g hg n).functor.Linear R where
  map_smul := by intros; rfl

def restrictionIso : Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n ≅
    Subsite.restriction fY g n ⋙ (equivalence g hg n).functor := Iso.refl _

omit [Mono g] in
def levelRestrictionIso : BoundedCrystalline.Site.restriction (p := p) (J := J) (δ := δ) fY n ⋙
    Bounded.PostcomposeTopology.restriction g hg n ≅
      Crystalline.ExactRestriction.restriction g hg ⋙ BoundedCrystalline.Site.restriction f n := Iso.refl _

omit [Mono g] in
def structureTransport : (Bounded.PostcomposeTopology.restriction g hg n).obj
    (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY n) ≅
      BoundedCrystalline.CrystallineCohomology.structureSheaf f n :=
  (levelRestrictionIso g hg n).app (BigCrystallineCohomology.structureSheaf fY) ≪≫
    (BoundedCrystalline.Site.restriction f n).mapIso (BigCrystallineCohomology.structureTransport g hg)

variable (fY)

abbrev constantUnit : Subsite.ModuleSheaf (p := p) (J := J) (δ := δ) fY g n :=
  (constantSheaf JO (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R)

abbrev structureSheaf : Subsite.ModuleSheaf (p := p) (J := J) (δ := δ) fY g n :=
  (Subsite.restriction fY g n).obj (BoundedCrystalline.CrystallineCohomology.structureSheaf fY n)

variable {fY}

def constantUnitIso : (equivalence g hg n).functor.obj (constantUnit (p := p) (J := J) (δ := δ) fY g n) ≅
    BoundedCrystalline.CrystallineCohomology.constantUnit f n :=
  ((E).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R) JX JO).symm.app
    ((Functor.const (Subsite.Objects (p := p) (J := J) (δ := δ) fY g n)ᵒᵖ).obj (ModuleCat.of R R))

def structureSheafIso : (equivalence g hg n).functor.obj (structureSheaf (p := p) (J := J) (δ := δ) fY g n) ≅
    BoundedCrystalline.CrystallineCohomology.structureSheaf f n :=
  ((restrictionIso g hg n).app (BoundedCrystalline.CrystallineCohomology.structureSheaf fY n)).symm ≪≫
    structureTransport g hg n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves
