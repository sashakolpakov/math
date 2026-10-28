import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasIs

/-! # Atlas Cover Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AtlasCoverValues.RepresentationAtlas

noncomputable section

/-! Local universal values viewed over the actual open cover of the
glued scheme, with agreement after all compatible test maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, Open.Representations.OpenRepresentation F (U i))

def chartTest (i : I) : Over (RepresentationAtlasIs.RepresentationAtlas.scheme D) := Over.mk (RepresentationAtlasIs.RepresentationAtlas.chart D i)

def chartComparison (i : I) : (Over.map (RepresentationAtlasIs.RepresentationAtlas.structureMap D)).obj (chartTest D i) ≅ (D i).space :=
  Over.isoMk (Iso.refl (D i).space.left) (by
    change 𝟙 _ ≫ (D i).space.hom = RepresentationAtlasIs.RepresentationAtlas.chart D i ≫ RepresentationAtlasIs.RepresentationAtlas.structureMap D
    rw [Category.id_comp, RepresentationAtlasIs.RepresentationAtlas.chart_structureMap])

def chartValue (i : I) : F.obj (op ((Over.map (RepresentationAtlasIs.RepresentationAtlas.structureMap D)).obj (chartTest D i))) :=
  F.map (chartComparison D i).hom.op (D i).sectionValue

theorem chartValues_match (i j : I) (T : Over (RepresentationAtlasIs.RepresentationAtlas.scheme D))
    (f : T ⟶ chartTest D i) (g : T ⟶ chartTest D j) :
    F.map ((Over.map (RepresentationAtlasIs.RepresentationAtlas.structureMap D)).map f).op (chartValue D i) =
      F.map ((Over.map (RepresentationAtlasIs.RepresentationAtlas.structureMap D)).map g).op (chartValue D j) := by
  let f' := (Over.map (RepresentationAtlasIs.RepresentationAtlas.structureMap D)).map f ≫ (chartComparison D i).hom
  let g' := (Over.map (RepresentationAtlasIs.RepresentationAtlas.structureMap D)).map g ≫ (chartComparison D j).hom
  have h : f' ≫ RepresentationAtlasIs.RepresentationAtlas.chartOver D i = g' ≫ RepresentationAtlasIs.RepresentationAtlas.chartOver D j := by
    apply Over.OverMorphism.ext
    change (f.left ≫ 𝟙 _) ≫ RepresentationAtlasIs.RepresentationAtlas.chart D i = (g.left ≫ 𝟙 _) ≫ RepresentationAtlasIs.RepresentationAtlas.chart D j
    simp only [Category.comp_id]
    exact f.w.trans g.w.symm
  have hv := RepresentationAtlasIs.RepresentationAtlas.localValues_match D i j f' g' h
  simpa only [f', g', chartValue, op_comp, F.map_comp, types_comp_apply] using hv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AtlasCoverValues.RepresentationAtlas
