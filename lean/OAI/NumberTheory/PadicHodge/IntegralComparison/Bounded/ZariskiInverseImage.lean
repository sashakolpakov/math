import OAI.NumberTheory.PadicHodge.IntegralComparison.NeighborhoodInverseImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.NeighborhoodValues
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSheaf

/-! # Zariski Inverse Image -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ZariskiInverseImage

noncomputable section

/-!
# IntegralComparison: the actual neighborhood inverse-image construction preserves monomorphisms of Zariski sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def presheaves : (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ⥤
    ((BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)ᵒᵖ ⥤
      ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  NeighborhoodInverseImage.functor (BoundedOpen.SectionPresheaf.property fY n)
    (fun V {_ _} α => BoundedOpen.SectionPresheaf.incoming fY n V α)

instance presheaves_preservesMonomorphisms : (presheaves (p := p) (J := J) (δ := δ) fY n).PreservesMonomorphisms :=
  NeighborhoodInverseImage.preservesMonomorphisms (BoundedOpen.SectionPresheaf.property fY n)
    (fun V {_ _} α => BoundedOpen.SectionPresheaf.incoming fY n V α)

def sheaves : Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ⥤
    BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n :=
  sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ⋙
    presheaves fY n ⋙ presheafToSheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

instance sheaves_preservesMonomorphisms : (sheaves (p := p) (J := J) (δ := δ) fY n).PreservesMonomorphisms := by
  let L := sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
  let M := presheaves (p := p) (J := J) (δ := δ) fY n
  let S := presheafToSheaf (BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) fY n)
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
  have : L.PreservesMonomorphisms := by infer_instance
  have : M.PreservesMonomorphisms := presheaves_preservesMonomorphisms fY n
  have : S.PreservesMonomorphisms := by infer_instance
  exact inferInstanceAs ((L ⋙ M ⋙ S).PreservesMonomorphisms)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ZariskiInverseImage
