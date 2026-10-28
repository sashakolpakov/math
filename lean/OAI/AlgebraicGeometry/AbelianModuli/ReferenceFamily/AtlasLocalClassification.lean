import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RepresentationAtlasIs

/-! # Atlas Local Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AtlasLocalClassification.RepresentationAtlas

noncomputable section

/-! Once a global universal value restricts to the local universal values,
its classifier is bijective on every test contained in a base chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable {S : Scheme.{0}} {F : (Over S)ᵒᵖ ⥤ Type} {I : Type} {U : I → S.Opens}
    (D : ∀ i, Open.Representations.OpenRepresentation F (U i))

instance chartOver_mono (i : I) : Mono (RepresentationAtlasIs.RepresentationAtlas.chartOver D i) :=
  (Over.forget S).mono_of_mono_map (show Mono (RepresentationAtlasIs.RepresentationAtlas.chartOver D i).left from inferInstanceAs (Mono (RepresentationAtlasIs.RepresentationAtlas.chart D i)))

def factorToChart (i : I) {T : Over S} (hT : ∀ t : T.left, T.hom t ∈ U i)
    (f : T ⟶ RepresentationAtlasIs.RepresentationAtlas.over D) : T ⟶ (D i).space := by
  have hr : Set.range f.left ⊆ Set.range (RepresentationAtlasIs.RepresentationAtlas.chart D i) := by
    rintro _ ⟨t, rfl⟩
    apply (Set.ext_iff.mp (RepresentationAtlasIs.RepresentationAtlas.chart_range D i) (f.left t)).mpr
    change RepresentationAtlasIs.RepresentationAtlas.structureMap D (f.left t) ∈ U i
    have ht : RepresentationAtlasIs.RepresentationAtlas.structureMap D (f.left t) = T.hom t := congrArg (fun q : T.left ⟶ S => q t) f.w
    exact ht ▸ hT t
  let q := IsOpenImmersion.lift (RepresentationAtlasIs.RepresentationAtlas.chart D i) f.left hr
  have hq : q ≫ RepresentationAtlasIs.RepresentationAtlas.chart D i = f.left := IsOpenImmersion.lift_fac (RepresentationAtlasIs.RepresentationAtlas.chart D i) f.left hr
  refine Over.homMk q ?_
  exact (congrArg (fun h => q ≫ h) (RepresentationAtlasIs.RepresentationAtlas.chart_structureMap D i).symm).trans
    ((Category.assoc q (RepresentationAtlasIs.RepresentationAtlas.chart D i) (RepresentationAtlasIs.RepresentationAtlas.structureMap D)).symm.trans
      ((congrArg (fun h => h ≫ RepresentationAtlasIs.RepresentationAtlas.structureMap D) hq).trans f.w))

theorem factorToChart_chart (i : I) {T : Over S} (hT : ∀ t : T.left, T.hom t ∈ U i)
    (f : T ⟶ RepresentationAtlasIs.RepresentationAtlas.over D) : factorToChart D i hT f ≫ RepresentationAtlasIs.RepresentationAtlas.chartOver D i = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (RepresentationAtlasIs.RepresentationAtlas.chart D i) f.left _

def chartHomEquiv (i : I) (T : Over S) (hT : ∀ t : T.left, T.hom t ∈ U i) :
    (T ⟶ RepresentationAtlasIs.RepresentationAtlas.over D) ≃ (T ⟶ (D i).space) where
  toFun := factorToChart D i hT
  invFun f := f ≫ RepresentationAtlasIs.RepresentationAtlas.chartOver D i
  left_inv := factorToChart_chart D i hT
  right_inv f := (cancel_mono (RepresentationAtlasIs.RepresentationAtlas.chartOver D i)).mp (factorToChart_chart D i hT (f ≫ RepresentationAtlasIs.RepresentationAtlas.chartOver D i))

theorem classifies_on_base_open (u : F.obj (op (RepresentationAtlasIs.RepresentationAtlas.over D))) (i : I)
    (hu : F.map (RepresentationAtlasIs.RepresentationAtlas.chartOver D i).op u = (D i).sectionValue)
    (T : Over S) (hT : ∀ t : T.left, T.hom t ∈ U i) :
    Function.Bijective (fun f : T ⟶ RepresentationAtlasIs.RepresentationAtlas.over D => F.map f.op u) := by
  have hb := ((D i).classifies T hT).comp (chartHomEquiv D i T hT).bijective
  convert hb using 1
  funext f
  change F.map f.op u = F.map (factorToChart D i hT f).op (D i).sectionValue
  rw [← hu, ← F.map_comp_apply]
  exact congrArg (fun q : T ⟶ RepresentationAtlasIs.RepresentationAtlas.over D => F.map q.op u) (factorToChart_chart D i hT f).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AtlasLocalClassification.RepresentationAtlas
