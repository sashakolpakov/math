import OAI.NumberTheory.PadicHodge.IntegralComparison.SliceKanComponents
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Slice Exact Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SliceExactExtension

noncomputable section

/-!
# IntegralComparison: exact extension from a slice and preservation of injectives

Pointwise left extension from the slice is a coproduct. Exactness of
module coproducts and sheafification proves exactness of the native
left adjoint to restriction. Hence restriction to the slice preserves
injective module sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C]
  (R : Type (max u v)) [Ring R] (U : C)

theorem preservesFiniteLimits : PreservesFiniteLimits
    ((Over.forget U).op.lan : ((Over U)ᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Cᵒᵖ ⥤ ModuleCat.{max u v} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max u v}
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
    ((Over.forget U).op.lan : ((Over U)ᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Cᵒᵖ ⥤ ModuleCat.{max u v} R) K
  intro X
  have := SliceKanComponents.exact_colimits U X R
  exact preservesLimitsOfShape_of_natIso
    (FlatModuleKanExtension.evaluationIso R (Over.forget U).op X).symm

variable (J : GrothendieckTopology C)

theorem sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits ((Over.forget U).sheafPullback (ModuleCat.{max u v} R) (J.over U) J) := by
  have := preservesFiniteLimits R U
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U)
        (ModuleCat.{max u v} R) (J.over U) J) := by
    change PreservesFiniteLimits (sheafToPresheaf (J.over U) (ModuleCat.{max u v} R) ⋙
      (Over.forget U).op.lan ⋙ presheafToSheaf J (ModuleCat.{max u v} R))
    have : PreservesFiniteLimits
        ((Over.forget U).op.lan ⋙ presheafToSheaf J (ModuleCat.{max u v} R)) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Over.forget U)
      (ModuleCat.{max u v} R) (J.over U) J).symm

theorem restriction_preservesInjectives :
    (J.overPullback (ModuleCat.{max u v} R) U).PreservesInjectiveObjects := by
  have := sheafPullback_preservesFiniteLimits R U J
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Over.forget U).sheafAdjunctionContinuous (ModuleCat.{max u v} R) (J.over U) J)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SliceExactExtension
