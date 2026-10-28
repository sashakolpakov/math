import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RestrictionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction

/-! # Restriction Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.RestrictionComposition

noncomputable section

/-! Actual presheaf sections respect the canonical composition of crystalline restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (h : Y ⟶ Z) (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) h hh n
local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ)
  (g ≫ h) (Crystalline.PostcomposeComposition.overBase g h hg hh) n
local notation "Rh" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) h hh n

theorem component (M : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fZ n) :
    (Sheaf.PresheafSectionRestriction.map.{u + 1, u, u + 2} H R (BoundedCrystalline.Site.topology fY n) (BoundedCrystalline.Site.topology fZ n)).app M ≫
      (Sheaf.PresheafSectionRestriction.map G R (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fY n)).app ((Rh).obj M) ≫
        (Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2}
          R (BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fX n)).map (Bounded.RestrictionComposition.objectIso g h hg hh n M).hom =
    (Sheaf.PresheafSectionRestriction.map C R (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fZ n)).app M := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  apply NatTrans.ext
  funext U
  change x.down.app ((H).op.obj ((G).op.obj U)) ≫
    (Bounded.RestrictionComposition.objectIso g h hg hh n M).hom.hom.app U = _
  exact (congrArg (fun a => x.down.app ((H).op.obj ((G).op.obj U)) ≫ a)
    (Bounded.RestrictionComposition.component g h hg hh n M U)).trans
      ((x.down.naturality ((Crystalline.PostcomposeComposition.boundedIso g h hg hh n).inv.app U.unop).op).symm.trans
        (Category.id_comp _))

theorem complexes (L : CochainComplex (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fZ n) ℕ) :
    Sheaf.PresheafSectionRestriction.complexMap.{u + 1, u, u + 2} H R (BoundedCrystalline.Site.topology fY n) (BoundedCrystalline.Site.topology fZ n) L ≫
      Sheaf.PresheafSectionRestriction.complexMap G R (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fY n)
        (((Rh).mapHomologicalComplex (.up ℕ)).obj L) ≫
          ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2}
          R (BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fX n)).mapHomologicalComplex (.up ℕ)).map
            (((NatIso.mapHomologicalComplex (Bounded.RestrictionComposition.iso g h hg hh n) (.up ℕ)).app L).hom) =
    Sheaf.PresheafSectionRestriction.complexMap C R (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fZ n) L := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component g h hg hh n (L.X i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.RestrictionComposition
