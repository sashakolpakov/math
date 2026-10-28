import OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceRepresentativeMaps

/-! # Slice Section Maps -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceSectionMaps.Construction

noncomputable section

/-!
# Completion: maps to local representatives determined by actual sections

The inverse representing bijections give maps for any section, and those
maps commute with restriction and the canonical transition morphisms.
-/

open _root_.CategoryTheory Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)
  {U V : C} {T : Over U} {S : Over V}
  (rT : ((Over.forget U).op ⋙ F).RepresentableBy T)

/-- The actual morphism represented by a section on an object of the slice. -/
def sliceSectionMap (A : Over U) (s : F.obj (op A.left)) : A.left ⟶ T.left :=
  ((rT.homEquiv (X := A)).symm s).left

theorem sliceSectionMap_over (A : Over U) (s : F.obj (op A.left)) :
    sliceSectionMap F rT A s ≫ T.hom = A.hom := Over.w _

theorem sliceSectionMap_section (A : Over U) (s : F.obj (op A.left)) :
    F.map (sliceSectionMap F rT A s).op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rT) = s := by
  change ((Over.forget U).op ⋙ F).map ((rT.homEquiv (X := A)).symm s).op (rT.homEquiv (𝟙 T)) = _
  rw [← rT.homEquiv_eq, rT.homEquiv.apply_symm_apply]

theorem sliceSectionMap_naturality {A B : Over U} (g : A ⟶ B) (s : F.obj (op B.left)) :
    g.left ≫ sliceSectionMap F rT B s = sliceSectionMap F rT A (F.map g.left.op s) := by
  exact congrArg (fun k => k.left) (rT.comp_homEquiv_symm s g)

/-- Changing the base of a slice commutes with the canonical transition map. -/
theorem sliceSectionMap_transition
    (rS : ((Over.forget V).op ⋙ F).RepresentableBy S)
    (h : U ⟶ V) (A : Over U) (s : F.obj (op A.left)) :
    sliceSectionMap F rT A s ≫ SliceRepresentativeMaps.Construction.sliceRepresentativeMap F rT rS h =
      sliceSectionMap F rS ((Over.map h).obj A) s := by
  apply SliceRepresentativeMaps.Construction.sliceRepresentative_hom_ext F rS
  · rw [Category.assoc, SliceRepresentativeMaps.Construction.sliceRepresentativeMap_over, ← Category.assoc,
      sliceSectionMap_over, sliceSectionMap_over]
    rfl
  · rw [op_comp, CategoryTheory.Functor.map_comp]
    change F.map (sliceSectionMap F rT A s).op
        (F.map (SliceRepresentativeMaps.Construction.sliceRepresentativeMap F rT rS h).op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rS)) = _
    rw [SliceRepresentativeMaps.Construction.sliceRepresentativeMap_section, sliceSectionMap_section]
    exact (sliceSectionMap_section F rS ((Over.map h).obj A) s).symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceSectionMaps.Construction
