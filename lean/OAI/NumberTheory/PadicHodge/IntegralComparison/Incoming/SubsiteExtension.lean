import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Subsite
import OAI.NumberTheory.PadicHodge.IntegralComparison.FilteredOrEmptyKan

/-! # Subsite Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SubsiteExtension

noncomputable section

/-!
# IntegralComparison: exact module extension from a full subsite closed under incoming maps

The pointwise Kan category is empty outside the subsite and has a
terminal object inside it. Its module colimits are exact, hence the
native left adjoint to sheaf restriction preserves finite limits.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] (P : ObjectProperty C)
  (hP : ∀ {X Y : C}, (X ⟶ Y) → P Y → P X)

include hP in
theorem index_filteredOrEmpty (X : Cᵒᵖ) : IsFilteredOrEmpty (CostructuredArrow P.ι.op X) := by
  classical
  by_cases h : Nonempty (CostructuredArrow P.ι.op X)
  · obtain ⟨Y⟩ := h
    have hX : P X.unop := hP Y.hom.unop Y.left.unop.property
    let Z : P.FullSubcategory := ⟨X.unop, hX⟩
    have : IsFiltered (CostructuredArrow P.ι.op X) :=
      IsFiltered.of_isTerminal _ (CostructuredArrow.mkIdTerminal (S := P.ι.op) (Y := op Z))
    infer_instance
  · have : IsEmpty (CostructuredArrow P.ι.op X) := not_nonempty_iff.mp h
    exact { cocone_objs := fun Y => isEmptyElim Y, cocone_maps := fun {Y} => isEmptyElim Y }

variable (R : Type (max u v)) [Ring R]

include hP in
theorem preservesFiniteLimits : PreservesFiniteLimits
    (P.ι.op.lan : (P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Cᵒᵖ ⥤ ModuleCat.{max u v} R) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{max u v}
  intro K _ _
  apply preservesLimitsOfShape_of_evaluation
    (P.ι.op.lan : (P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{max u v} R) ⥤ Cᵒᵖ ⥤ ModuleCat.{max u v} R) K
  intro X
  have := index_filteredOrEmpty P hP X
  have := FilteredOrEmptyKan.exact_colimits R (CostructuredArrow P.ι.op X)
  exact preservesLimitsOfShape_of_natIso (FlatModuleKanExtension.evaluationIso R P.ι.op X).symm

variable (J : GrothendieckTopology C) [P.ι.IsContinuous (P.ι.restrictedTopology J) J]

include hP in
theorem sheafPullback_preservesFiniteLimits : PreservesFiniteLimits
    (P.ι.sheafPullback (ModuleCat.{max u v} R) (P.ι.restrictedTopology J) J) := by
  have := preservesFiniteLimits P hP R
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback P.ι
      (ModuleCat.{max u v} R) (P.ι.restrictedTopology J) J) := by
    change PreservesFiniteLimits
      (sheafToPresheaf (P.ι.restrictedTopology J) (ModuleCat.{max u v} R) ⋙
        P.ι.op.lan ⋙ presheafToSheaf J (ModuleCat.{max u v} R))
    have : PreservesFiniteLimits (P.ι.op.lan ⋙ presheafToSheaf J (ModuleCat.{max u v} R)) :=
      comp_preservesFiniteLimits _ _
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (Functor.sheafPullbackConstruction.sheafPullbackIso
    P.ι (ModuleCat.{max u v} R) (P.ι.restrictedTopology J) J).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SubsiteExtension
