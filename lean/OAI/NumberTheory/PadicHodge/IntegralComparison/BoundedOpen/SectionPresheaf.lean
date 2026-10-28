import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionPresheaf

/-! # Section Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf

noncomputable section

/-!
# IntegralComparison: sections of the original bounded crystalline resolution over geometric opens
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

abbrev property (V : Y.Opens) : ObjectProperty
    (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) :=
  Subsite.property fY V.ι n

theorem monotone : Monotone (property (p := p) (J := J) (δ := δ) fY n) := by
  intro U V h T hT
  obtain ⟨t, ht⟩ := hT
  refine ⟨t ≫ Y.homOfLE h, ?_⟩
  rw [Category.assoc, Scheme.homOfLE_ι, ht]

theorem incoming (V : Y.Opens) {U T : BoundedCrystalline.Site.Objects
    (p := p) (J := J) (δ := δ) fY n} (α : U ⟶ T) : property fY n V T → property fY n V U :=
  Subsite.incoming fY V.ι n α

def functor : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n ⥤
    (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  sheafToPresheaf (BoundedCrystalline.Site.topology fY n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ⋙
    Incoming.SectionPresheaf.functor (Crystalline.ExactRestriction.Coeff (B := B)) (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))
      (property fY n) (monotone fY n)

instance functor_additive : (functor (p := p) (J := J) (δ := δ) fY n).Additive := by
  dsimp only [functor]
  infer_instance

theorem restriction_surjective (F : BoundedCrystalline.Site.ModuleSheaf
    (p := p) (J := J) (δ := δ) fY n) [Injective F] {U V : Y.Opensᵒᵖ} (α : U ⟶ V) :
    Function.Surjective (((functor fY n).obj F).map α) :=
  Incoming.SectionPresheaf.sheaf_map_surjective (Crystalline.ExactRestriction.Coeff (B := B))
    (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))) (property fY n) (monotone fY n)
    (fun V {_ _} α => incoming fY n V α) (BoundedCrystalline.Site.topology fY n) F α

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf
