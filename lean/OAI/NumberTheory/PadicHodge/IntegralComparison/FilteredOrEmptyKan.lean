import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatFromNonemptyLimits

/-! # Filtered Or Empty Kan -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredOrEmptyKan

noncomputable section

/-!
# IntegralComparison: exact module extension when incoming categories may be empty

Filtered module colimits are exact. The empty case is also exact because
an empty coproduct is the zero module. Consequently products and
equalizers suffice for exact module-valued Kan extension, even before
local existence of incoming crystalline presentations is established.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable (R : Type (max u v)) [Ring R]

lemma exact_colimits (J : Type u) [Category.{v} J] [IsFilteredOrEmpty J] :
    HasExactColimitsOfShape J (ModuleCat.{max u v} R) := by
  classical
  by_cases h : Nonempty J
  · have : IsFiltered J := { nonempty := h }
    have : AB5OfSize.{v, u} (ModuleCat.{max u v} R) := AB5OfSize_of_univLE (ModuleCat.{max u v} R)
    infer_instance
  · have : IsEmpty J := not_nonempty_iff.mp h
    exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{max u v} R)
      (equivalenceOfIsEmpty (Discrete PEmpty.{1}) J)

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (F : C ⥤ D) [HasBinaryProducts C] [HasEqualizers C]
variable [PreservesLimitsOfShape (Discrete WalkingPair) F]
variable [PreservesLimitsOfShape WalkingParallelPair F]

lemma preservesFiniteLimits :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max u v} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max u v}
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
    (F.op.lan : (Cᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Dᵒᵖ ⥤ ModuleCat.{max u v} R) K
  intro X
  have := FlatFromNonemptyLimits.cofilteredOrEmpty F (unop X)
  have : IsFilteredOrEmpty (CostructuredArrow F.op X) :=
    IsFilteredOrEmpty.of_equivalence (structuredArrowOpEquivalence F (unop X))
  have := exact_colimits R (CostructuredArrow F.op X)
  exact preservesLimitsOfShape_of_natIso (FlatModuleKanExtension.evaluationIso R F.op X).symm

lemma sheafPullback_preservesFiniteLimits (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] : PreservesFiniteLimits (F.sheafPullback (ModuleCat.{max u v} R) J K) := by
  have := preservesFiniteLimits R F
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{max u v} R) J K) := by
    change PreservesFiniteLimits (sheafToPresheaf J (ModuleCat.{max u v} R) ⋙
      F.op.lan ⋙ presheafToSheaf K (ModuleCat.{max u v} R))
    have : PreservesFiniteLimits (F.op.lan ⋙ presheafToSheaf K (ModuleCat.{max u v} R)) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso F (ModuleCat.{max u v} R) J K).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredOrEmptyKan
