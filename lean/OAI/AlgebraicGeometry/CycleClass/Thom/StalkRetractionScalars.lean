import OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetraction
import OAI.AlgebraicGeometry.CycleClass.Thom.FormalSmoothRetract

/-! # Stalk Retraction Scalars -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetractionScalars.Constructions

noncomputable section

/-! Actual scheme retractions respect scalar constants in local rings.
Formal smoothness of the global-base stalk map therefore descends. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetraction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.FormalSmoothRetract.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y S : Scheme.{0}}

def stalkBaseMap (f : X ⟶ S) (x : X) : Γ(S, ⊤) ⟶ X.presheaf.stalk x :=
  f.appTop ≫ X.presheaf.germ ⊤ x (by trivial)

@[reassoc]
theorem stalkBaseMap_natural (i : Y ⟶ X) (f : X ⟶ S) (y : Y) :
    stalkBaseMap f (i y) ≫ i.stalkMap y = stalkBaseMap (i ≫ f) y := by
  unfold stalkBaseMap
  rw [Category.assoc, i.germ_stalkMap ⊤ y (by trivial), Scheme.Hom.comp_appTop, Category.assoc]
  rfl

variable (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
  (f : X ⟶ S) (g : Y ⟶ S) (hr : r ≫ f = g) (x : X)

include hr in
@[reassoc]
theorem retractionStalkSection_base :
    stalkBaseMap f x ≫ StalkRetraction.Constructions.retractionStalkSection i r h x = stalkBaseMap g (i x) := by
  have ht : stalkBaseMap f x ≫ (StalkRetraction.Constructions.retractionStalkPointIso i r h x).inv = stalkBaseMap f (r (i x)) := by
    simp only [stalkBaseMap, StalkRetraction.Constructions.retractionStalkPointIso, TopCat.Presheaf.stalkCongr_inv, Category.assoc,
      TopCat.Presheaf.germ_stalkSpecializes]
  unfold StalkRetraction.Constructions.retractionStalkSection
  rw [← Category.assoc, ht, stalkBaseMap_natural, hr]

include hr h in
theorem stalkBaseMap_formallySmooth_of_retract (hi : i ≫ g = f)
    (hg : (stalkBaseMap g (i x)).hom.FormallySmooth) : (stalkBaseMap f x).hom.FormallySmooth := by
  have hI := retractionStalkSection_base i r h f g hr x
  have hR : stalkBaseMap g (i x) ≫ i.stalkMap x = stalkBaseMap f x := by
    rw [stalkBaseMap_natural, hi]
  have hIR := StalkRetraction.Constructions.retractionStalkSection_retract i r h x
  exact FormalSmoothRetract.Constructions.ringHom_formallySmooth_of_retract (stalkBaseMap f x).hom (stalkBaseMap g (i x)).hom
    (StalkRetraction.Constructions.retractionStalkSection i r h x).hom (i.stalkMap x).hom
    (congrArg CommRingCat.Hom.hom hI) (congrArg CommRingCat.Hom.hom hR)
    (congrArg CommRingCat.Hom.hom hIR) hg

end

end OAI.AlgebraicGeometry.CycleClass.Thom.StalkRetractionScalars.Constructions
