import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Large Limit Reflection -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.LargeLimitReflection.ModuleLargeLimitReflection

noncomputable section

/-!
# Reflection of existing large limits by the module forgetful functor

If a diagram of modules has a limiting cone on underlying sets, its
compatible sections are small enough to carry the usual module limit.
The original cone is therefore limiting in modules as well. No size
bound on the indexing category is assumed.
-/

open _root_.CategoryTheory Limits

universe u v w t

variable (R : Type u) [Ring R] {J : Type w} [Category.{t} J]

theorem reflectsLimit (F : J ⥤ ModuleCat.{v} R) : ReflectsLimit F (forget (ModuleCat.{v} R)) where
  reflects {c} hc := ⟨by
    have : HasLimit (F ⋙ forget (ModuleCat.{v} R)) := ⟨_, hc⟩
    have : Small.{v} (F ⋙ forget (ModuleCat.{v} R)).sections :=
      (Types.hasLimit_iff_small_sections _).mp inferInstance
    have : PreservesLimit F (forget (ModuleCat.{v} R)) :=
      preservesLimit_of_preserves_limit_cone (ModuleCat.HasLimits.limitConeIsLimit F)
        (Types.Small.limitConeIsLimit _)
    have : ReflectsLimit F (forget (ModuleCat.{v} R)) :=
      reflectsLimit_of_reflectsIsomorphisms F (forget (ModuleCat.{v} R))
    exact isLimitOfReflects _ hc⟩

theorem reflectsLimitsOfSize : ReflectsLimitsOfSize.{t, w} (forget (ModuleCat.{v} R)) where
  reflectsLimitsOfShape := ⟨fun {F} => reflectsLimit R F⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.LargeLimitReflection.ModuleLargeLimitReflection
