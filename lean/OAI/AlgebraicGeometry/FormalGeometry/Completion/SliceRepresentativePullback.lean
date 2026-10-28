import OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceRepresentativeMaps
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered

/-! # Slice Representative Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceRepresentativePullback.Construction

noncomputable section

/-!
# Completion: the canonical transition squares of slice representatives are pullbacks

The original representing bijections solve the pullback universal property.
Thus representatives over a diagram of base objects form compatible geometric
data, with no pullback condition assumed.
-/

open _root_.CategoryTheory Limits Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)
  {U V : C} {T : Over U} {S : Over V}
  (rT : ((Over.forget U).op ⋙ F).RepresentableBy T)
  (rS : ((Over.forget V).op ⋙ F).RepresentableBy S)

/-- Pulling back the universal section supplies the unique candidate for a pullback lift. -/
def sliceRepresentativeLift {Z : C} (x : Z ⟶ U) (y : Z ⟶ S.left) : Z ⟶ T.left :=
  ((rT.homEquiv (X := Over.mk x)).symm
    (F.map y.op (SliceRepresentativeMaps.Construction.sliceUniversalSection F (U := V) (T := S) rS))).left

theorem sliceRepresentativeLift_over {Z : C} (x : Z ⟶ U) (y : Z ⟶ S.left) :
    sliceRepresentativeLift F rT rS x y ≫ T.hom = x := Over.w _

theorem sliceRepresentativeLift_section {Z : C} (x : Z ⟶ U) (y : Z ⟶ S.left) :
    F.map (sliceRepresentativeLift F rT rS x y).op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rT) =
      F.map y.op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rS) := by
  change ((Over.forget U).op ⋙ F).map
    ((rT.homEquiv (X := Over.mk x)).symm
      (F.map y.op (SliceRepresentativeMaps.Construction.sliceUniversalSection F (U := V) (T := S) rS))).op
      (rT.homEquiv (𝟙 T)) = _
  rw [← rT.homEquiv_eq, rT.homEquiv.apply_symm_apply]

theorem sliceRepresentativeLift_transition (h : U ⟶ V) {Z : C}
    (x : Z ⟶ U) (y : Z ⟶ S.left) (hxy : y ≫ S.hom = x ≫ h) :
    sliceRepresentativeLift F rT rS x y ≫ SliceRepresentativeMaps.Construction.sliceRepresentativeMap F rT rS h = y := by
  apply SliceRepresentativeMaps.Construction.sliceRepresentative_hom_ext F rS
  · rw [Category.assoc, SliceRepresentativeMaps.Construction.sliceRepresentativeMap_over, ← Category.assoc,
      sliceRepresentativeLift_over, hxy]
  · rw [op_comp, CategoryTheory.Functor.map_comp]
    change F.map (sliceRepresentativeLift F rT rS x y).op
        (F.map (SliceRepresentativeMaps.Construction.sliceRepresentativeMap F rT rS h).op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rS)) = _
    rw [SliceRepresentativeMaps.Construction.sliceRepresentativeMap_section, sliceRepresentativeLift_section]

/-- The canonical transition square is the actual categorical pullback. -/
theorem sliceRepresentativeMap_isPullback (h : U ⟶ V) :
    IsPullback (SliceRepresentativeMaps.Construction.sliceRepresentativeMap F rT rS h) T.hom S.hom h := by
  apply IsPullback.of_isLimit' ⟨SliceRepresentativeMaps.Construction.sliceRepresentativeMap_over F rT rS h⟩
  refine PullbackCone.IsLimit.mk (SliceRepresentativeMaps.Construction.sliceRepresentativeMap_over F rT rS h)
    (fun c => sliceRepresentativeLift F rT rS c.snd c.fst)
    (fun c => sliceRepresentativeLift_transition F rT rS h _ _ c.condition)
    (fun c => sliceRepresentativeLift_over F rT rS c.snd c.fst) ?_
  intro c m hm₁ hm₂
  apply SliceRepresentativeMaps.Construction.sliceRepresentative_hom_ext F rT
  · rw [hm₂, sliceRepresentativeLift_over]
  · calc
      F.map m.op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rT) =
          F.map m.op (F.map (SliceRepresentativeMaps.Construction.sliceRepresentativeMap F rT rS h).op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rS)) := by
        rw [SliceRepresentativeMaps.Construction.sliceRepresentativeMap_section]
      _ = F.map (m ≫ SliceRepresentativeMaps.Construction.sliceRepresentativeMap F rT rS h).op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rS) := by
        rw [op_comp, Functor.map_comp_apply]
      _ = F.map c.fst.op (SliceRepresentativeMaps.Construction.sliceUniversalSection F rS) := by rw [hm₁]
      _ = _ := (sliceRepresentativeLift_section F rT rS c.snd c.fst).symm

variable {I : Type u'} [Category.{v'} I] (B : I ⥤ C) (T : ∀ i, Over (B.obj i))
  (rep : ∀ i, ((Over.forget (B.obj i)).op ⋙ F).RepresentableBy (T i))

/-- Slice representatives over a diagram form their canonical transition diagram. -/
def sliceRepresentativeDiagram : I ⥤ C where
  obj i := (T i).left
  map {i j} h := SliceRepresentativeMaps.Construction.sliceRepresentativeMap F (rep i) (rep j) (B.map h)
  map_id i := by rw [CategoryTheory.Functor.map_id, SliceRepresentativeMaps.Construction.sliceRepresentativeMap_id]
  map_comp h k := by rw [CategoryTheory.Functor.map_comp, SliceRepresentativeMaps.Construction.sliceRepresentativeMap_comp]

/-- The structural maps of the transition diagram. -/
def sliceRepresentativeDiagramToBase : sliceRepresentativeDiagram F B T rep ⟶ B where
  app i := (T i).hom
  naturality i j h := SliceRepresentativeMaps.Construction.sliceRepresentativeMap_over F (rep i) (rep j) (B.map h)

/-- Every transition square is a pullback, as required by relative geometric gluing. -/
theorem sliceRepresentativeDiagram_equifibered :
    (sliceRepresentativeDiagramToBase F B T rep).Equifibered := by
  intro i j h
  exact sliceRepresentativeMap_isPullback F (rep i) (rep j) (B.map h)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SliceRepresentativePullback.Construction
