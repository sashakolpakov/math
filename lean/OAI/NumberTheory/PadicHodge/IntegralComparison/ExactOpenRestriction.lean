import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleHomology
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Algebra.Category.Grp.Limits

/-! # Exact Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactOpenRestriction

noncomputable section

/-! Restriction of module sheaves to an open subscheme preserves genuine
homology: it preserves limits as a sheaf pushforward and colimits as the
left adjoint to extension along the open immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance additive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := rfl

instance preservesFiniteLimits : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  let G := Scheme.Modules.toPresheaf X
  let H := Scheme.Modules.toPresheaf Y
  have : PreservesLimits H := inferInstanceAs (PreservesLimits (Scheme.Modules.toPresheaf Y))
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft X.Opensᵒᵖ Y.Opensᵒᵖ AddCommGrpCat.{u}).obj f.opensFunctor.op) :=
    inferInstance
  have : ReflectsFiniteLimits G :=
    { reflects := fun _ => reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f ⋙ G) := by
    change PreservesFiniteLimits (H ⋙ (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

instance preservesFiniteColimits : PreservesFiniteColimits (Scheme.Modules.restrictFunctor f) :=
  inferInstance

instance preservesHomology : (Scheme.Modules.restrictFunctor f).PreservesHomology := inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactOpenRestriction
