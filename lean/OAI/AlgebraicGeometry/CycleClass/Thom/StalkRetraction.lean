import Mathlib.AlgebraicGeometry.Scheme

/-! # Stalk Retraction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetraction.Constructions

noncomputable section

/-! An actual scheme retraction gives an actual retraction of local rings,
with the point transport explicitly included in the section map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme} (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X) (x : X)

def retractionStalkPointIso : X.presheaf.stalk (r (i x)) ≅ X.presheaf.stalk x :=
  X.presheaf.stalkCongr (.of_eq (congrArg (fun f : X ⟶ X => f x) h))

def retractionStalkSection : X.presheaf.stalk x ⟶ Y.presheaf.stalk (i x) :=
  (retractionStalkPointIso i r h x).inv ≫ r.stalkMap (i x)

theorem retractionStalkSection_retract :
    retractionStalkSection i r h x ≫ i.stalkMap x = 𝟙 (X.presheaf.stalk x) := by
  have hc : (i ≫ r).stalkMap x = (retractionStalkPointIso i r h x).hom := by
    rw [Scheme.Hom.stalkMap_congr_hom (i ≫ r) (𝟙 X) h x, Scheme.Hom.stalkMap_id]
    change (retractionStalkPointIso i r h x).hom ≫ 𝟙 _ = _
    exact Category.comp_id _
  unfold retractionStalkSection
  rw [Category.assoc, ← Scheme.Hom.stalkMap_comp, hc]
  exact (retractionStalkPointIso i r h x).inv_hom_id

end

end OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetraction.Constructions
