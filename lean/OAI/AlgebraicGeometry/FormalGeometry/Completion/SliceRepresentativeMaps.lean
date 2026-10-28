import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Slice Representative Maps -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceRepresentativeMaps.Construction

noncomputable section

/-!
# Completion: transition maps between representatives on slices

The universal sections determine the transition maps uniquely. These maps
preserve the original sections and obey identity and composition laws.
-/

open _root_.CategoryTheory Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)
  {U V W : C} {T : Over U} {S : Over V} {Q : Over W}
  (rT : ((Over.forget U).op ⋙ F).RepresentableBy T)
  (rS : ((Over.forget V).op ⋙ F).RepresentableBy S)

/-- The universal section of a representative in a slice. -/
def sliceUniversalSection : F.obj (op T.left) := rT.homEquiv (𝟙 T)

/-- The unique transition morphism determined by the first representative's universal section. -/
def sliceRepresentativeMap (h : U ⟶ V) : T.left ⟶ S.left :=
  ((rS.homEquiv (X := Over.mk (T.hom ≫ h))).symm
    (sliceUniversalSection F (U := U) (T := T) rT)).left

theorem sliceRepresentativeMap_over (h : U ⟶ V) :
    sliceRepresentativeMap F rT rS h ≫ S.hom = T.hom ≫ h :=
  Over.w _

/-- Transition morphisms identify the original universal sections. -/
theorem sliceRepresentativeMap_section (h : U ⟶ V) :
    F.map (sliceRepresentativeMap F rT rS h).op (sliceUniversalSection F rS) =
      sliceUniversalSection F rT := by
  change ((Over.forget V).op ⋙ F).map
      ((rS.homEquiv (X := Over.mk (T.hom ≫ h))).symm
        (sliceUniversalSection F (U := U) (T := T) rT)).op
        (rS.homEquiv (𝟙 S)) = _
  rw [← rS.homEquiv_eq, rS.homEquiv.apply_symm_apply]

/-- A map to a slice representative is determined by its base map and pulled-back universal section. -/
theorem sliceRepresentative_hom_ext {Z : C} (a b : Z ⟶ T.left)
    (hab : a ≫ T.hom = b ≫ T.hom)
    (hs : F.map a.op (sliceUniversalSection F rT) = F.map b.op (sliceUniversalSection F rT)) :
    a = b := by
  let a' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  let b' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk b hab.symm
  have heq : a' = b' := rT.homEquiv.injective (by
    rw [rT.homEquiv_eq a', rT.homEquiv_eq b']
    exact hs)
  exact congrArg (fun k => k.left) heq

theorem sliceRepresentativeMap_id : sliceRepresentativeMap F rT rT (𝟙 U) = 𝟙 T.left := by
  apply sliceRepresentative_hom_ext F rT
  · rw [sliceRepresentativeMap_over]
    simp
  · rw [sliceRepresentativeMap_section]
    simp

theorem sliceRepresentativeMap_comp
    (rQ : ((Over.forget W).op ⋙ F).RepresentableBy Q) (h : U ⟶ V) (k : V ⟶ W) :
    sliceRepresentativeMap F rT rS h ≫ sliceRepresentativeMap F rS rQ k =
      sliceRepresentativeMap F rT rQ (h ≫ k) := by
  apply sliceRepresentative_hom_ext F rQ
  · rw [Category.assoc, sliceRepresentativeMap_over, ← Category.assoc,
      sliceRepresentativeMap_over, sliceRepresentativeMap_over, Category.assoc]
  · rw [op_comp, CategoryTheory.Functor.map_comp]
    change F.map (sliceRepresentativeMap F rT rS h).op
        (F.map (sliceRepresentativeMap F rS rQ k).op (sliceUniversalSection F rQ)) = _
    rw [sliceRepresentativeMap_section, sliceRepresentativeMap_section, sliceRepresentativeMap_section]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceRepresentativeMaps.Construction
