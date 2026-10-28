import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support

/-! # Neighborhoods -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Neighborhoods

noncomputable section

/-!
# IntegralComparison: filtered Zariski neighborhoods of the actual bounded crystalline closed image
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.property (p := p) (J := J) (δ := δ) fY n

abbrev Objects (T : Site.Objects (p := p) (J := J) (δ := δ) fY n) :=
  Incoming.Neighborhoods.Objects P T

instance cofiltered (T : Site.Objects (p := p) (J := J) (δ := δ) fY n) :
    IsCofiltered (Objects fY n T) :=
  Incoming.Neighborhoods.cofiltered P (BoundedOpen.Support.property_top fY n)
    (fun U V T hU hV => (BoundedOpen.Support.property_inf fY n T U V).mpr ⟨hU, hV⟩) T

def change {T U : Site.Objects (p := p) (J := J) (δ := δ) fY n} (α : T ⟶ U) :
    Objects fY n U ⥤ Objects fY n T :=
  Incoming.Neighborhoods.change P (fun V {_ _} β => BoundedOpen.SectionPresheaf.incoming fY n V β) α

theorem membership (T : Site.Objects (p := p) (J := J) (δ := δ) fY n) (V : Y.Opens) :
    Incoming.Neighborhoods.property P T V ↔ Set.range T.obj.mapToX ⊆ (V : Set Y) :=
  BoundedOpen.Support.property_iff_range_subset fY n T V

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Neighborhoods
