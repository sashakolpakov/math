import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover
import Mathlib.CategoryTheory.Sites.Over

/-! # Etale Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.EtaleRestriction.Construction

noncomputable section

/-!
# Completion: restriction of actual sheaves along weakly étale maps

Composition of structure maps gives the functor from the smaller site's
objects to the original site. It preserves covering pullbacks and coverings,
so objectwise restriction takes actual sheaves to actual sheaves.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

local instance : MorphismProperty.IsStableUnderComposition (@WeaklyEtale.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@WeaklyEtale.{u})).toIsStableUnderComposition

local instance (X : Scheme.{u}) : Precoverage.IsStableUnderBaseChange (Scheme.ProEt.precoverage X) :=
  inferInstanceAs (Precoverage.IsStableUnderBaseChange
    (Scheme.proetalePrecoverage.comap (Scheme.ProEt.forget X ⋙ Over.forget X)))

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : WeaklyEtale f)

/-- Composition with the actual weakly étale structure map. -/
def proEtCompose : Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ hf

instance proEtCompose_preservesPullbacks : PreservesLimitsOfShape WalkingCospan (proEtCompose f hf) := by
  have : PreservesLimitsOfShape WalkingCospan
      (proEtCompose f hf ⋙ Scheme.ProEt.forget X ⋙ Over.forget X) := by
    change PreservesLimitsOfShape WalkingCospan (Scheme.ProEt.forget Y ⋙ Over.forget Y)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (proEtCompose f hf) (Scheme.ProEt.forget X ⋙ Over.forget X)

instance proEtCompose_continuous :
    (proEtCompose f hf).IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
    (proEtCompose f hf) (Scheme.ProEt.precoverage Y) (Scheme.ProEt.precoverage X)
  intro U P hP
  change (P.map (proEtCompose f hf)).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
    Scheme.proetalePrecoverage U.left
  obtain ⟨ι, V, g, rfl⟩ := P.exists_eq_ofArrows
  change (Presieve.ofArrows V g).map (Scheme.ProEt.forget Y ⋙ Over.forget Y) ∈
    Scheme.proetalePrecoverage U.left at hP
  simpa only [Presieve.map_ofArrows] using! hP

/-- Restriction of an actual sheaf is given by its original values on the composed objects. -/
def proEtSheafRestriction (A : Type v) [Category.{w} A] :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf (Scheme.ProEt.topology Y) A :=
  (proEtCompose f hf).sheafPushforwardContinuous A (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.EtaleRestriction.Construction
