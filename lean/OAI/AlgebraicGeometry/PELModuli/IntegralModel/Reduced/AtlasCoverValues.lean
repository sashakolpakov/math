import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.RepresentationAtlas

/-! # Atlas Cover Values -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasCoverValues

noncomputable section

section

/-! The actual local universal values agree on every test of the glued
atlas intersection, by the constructed cartesian intersection square. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace ReducedRepresentationAtlas
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, OpenRepresentations.ReducedOpenRepresentation F (U i))

theorem chart_intersection_over (i j : I) :
    IsPullback ((D i).inclusion (D j))
      ((D i).comparison (D j) ≫ (D j).inclusion (D i)) (RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i) (RepresentationAtlas.ReducedRepresentationAtlas.chartOver D j) := by
  apply IsPullback.of_map_of_faithful (Over.forget S)
  exact RepresentationAtlas.ReducedRepresentationAtlas.chart_intersection D i j

theorem localValues_match (i j : I) {T : Over S} (f : T ⟶ (D i).space) (g : T ⟶ (D j).space)
    (h : f ≫ RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i = g ≫ RepresentationAtlas.ReducedRepresentationAtlas.chartOver D j) :
    F.map f.op (D i).sectionValue = F.map g.op (D j).sectionValue := by
  let H := chart_intersection_over D i j
  let q := H.lift f g h
  have hf : q ≫ (D i).inclusion (D j) = f := H.lift_fst f g h
  have hg : q ≫ (D i).comparison (D j) ≫ (D j).inclusion (D i) = g := H.lift_snd f g h
  rw [← hf, ← hg]
  simp only [op_comp, F.map_comp, types_comp_apply, OpenRepresentations.ReducedOpenRepresentation.comparison_value]

end ReducedRepresentationAtlas

end

/-! Local universal values viewed over the actual open cover of the
glued scheme, with agreement after all compatible test maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace ReducedRepresentationAtlas
variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, OpenRepresentations.ReducedOpenRepresentation F (U i))

def chartTest (i : I) : Over (RepresentationAtlas.ReducedRepresentationAtlas.scheme D) := Over.mk (RepresentationAtlas.ReducedRepresentationAtlas.chart D i)

def chartComparison (i : I) : (Over.map (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D)).obj (chartTest D i) ≅ (D i).space :=
  Over.isoMk (Iso.refl (D i).space.left) (by
    change 𝟙 _ ≫ (D i).space.hom = RepresentationAtlas.ReducedRepresentationAtlas.chart D i ≫ RepresentationAtlas.ReducedRepresentationAtlas.structureMap D
    rw [Category.id_comp, RepresentationAtlas.ReducedRepresentationAtlas.chart_structureMap])

def chartValue (i : I) : F.obj (op ((Over.map (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D)).obj (chartTest D i))) :=
  F.map (chartComparison D i).hom.op (D i).sectionValue

theorem chartValues_match (i j : I) (T : Over (RepresentationAtlas.ReducedRepresentationAtlas.scheme D))
    (f : T ⟶ chartTest D i) (g : T ⟶ chartTest D j) :
    F.map ((Over.map (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D)).map f).op (chartValue D i) =
      F.map ((Over.map (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D)).map g).op (chartValue D j) := by
  let f' := (Over.map (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D)).map f ≫ (chartComparison D i).hom
  let g' := (Over.map (RepresentationAtlas.ReducedRepresentationAtlas.structureMap D)).map g ≫ (chartComparison D j).hom
  have h : f' ≫ RepresentationAtlas.ReducedRepresentationAtlas.chartOver D i = g' ≫ RepresentationAtlas.ReducedRepresentationAtlas.chartOver D j := by
    apply Over.OverMorphism.ext
    change (f.left ≫ 𝟙 _) ≫ RepresentationAtlas.ReducedRepresentationAtlas.chart D i = (g.left ≫ 𝟙 _) ≫ RepresentationAtlas.ReducedRepresentationAtlas.chart D j
    simp only [Category.comp_id]
    exact f.w.trans g.w.symm
  have hv := localValues_match D i j f' g' h
  simpa only [f', g', chartValue, op_comp, F.map_comp, types_comp_apply] using hv

end ReducedRepresentationAtlas

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.AtlasCoverValues
