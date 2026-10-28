import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LocalizedComponentSection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentAlbaneseBaseChange

/-! # Localized Component Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! Actual arithmetic sections turn the localized diagram into IntegralModel's
component data, retaining each specified complex Albanese property. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {K : Type} [Field K] [NumberField K] {T : Over (Spec (.of K))} {r : ℕ}
    {D : Components.ComponentAlbaneseData T r} {κ : K →+* ℂ} (W : LocalizedComponentDiagramExists.LocalizedComponentDiagram D κ)
    (B : Base.ArithmeticBaseExtension W.base.extension.carrier W.base.embedding)
    (φ : W.base.R →+* B.R)
    (j : 𝟙_ (Over B.base) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj W.unitModel)

def LocalizedComponentDiagramExists.LocalizedComponentDiagram.componentData (T' : Over B.base) : Components.ComponentAlbaneseData T' r where
  S i := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (W.source i)
  A i := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).mapCommGrp.obj (W.target i)
  x₀ i := j ≫ (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map (W.point i)
  a i := (Over.pullback (Spec.map (CommRingCat.ofHom φ))).map (W.map i)

theorem LocalizedComponentDiagramExists.LocalizedComponentDiagram.componentData_geometry (T' : Over B.base) (i : Fin r) :
    let V := W.componentData B φ j T'
    Smooth (V.S i).hom ∧ IsProper (V.S i).hom ∧ GeometricallyConnected (V.S i).hom ∧
      Smooth (V.A i).X.hom ∧ IsProper (V.A i).X.hom ∧ GeometricallyConnected (V.A i).X.hom := by
  let g := Spec.map (CommRingCat.ofHom φ)
  have : Smooth (W.source i).hom := (W.sourceGeometry i).1
  have : IsProper (W.source i).hom := (W.sourceGeometry i).2.1
  have : GeometricallyConnected (W.source i).hom := (W.sourceGeometry i).2.2
  have : Smooth (W.target i).X.hom := (W.targetGeometry i).1
  have : IsProper (W.target i).X.hom := (W.targetGeometry i).2.1
  have : GeometricallyConnected (W.target i).X.hom := (W.targetGeometry i).2.2
  exact ⟨inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd (W.source i).hom g)),
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (W.source i).hom g)),
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd (W.source i).hom g)),
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd (W.target i).X.hom g)),
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (W.target i).X.hom g)),
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd (W.target i).X.hom g))⟩

theorem LocalizedComponentDiagramExists.LocalizedComponentDiagram.componentData_isComplexAlbanese
    (hφ : B.toField.comp φ = (algebraMap W.base.extension.carrier B.extension.carrier).comp W.base.toField)
    (T' : Over B.base) (i : Fin r)
    (hD : D.IsComplexAlbanese (Spec.map (CommRingCat.ofHom κ)) i) :
    (W.componentData B φ j T').IsComplexAlbanese B.complexPoint i := by
  let g := Spec.map (CommRingCat.ofHom φ)
  let F := Over.pullback g
  let G := Over.pullback B.complexPoint
  let H := Over.pullback W.base.complexPoint
  let J := Over.pullback (Spec.map (CommRingCat.ofHom κ))
  let c : F ⋙ G ≅ H := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso g B.complexPoint W.base.complexPoint
    (W.base.tower_coefficient_complexPoint B φ hφ)
  let V := W.componentData B φ j T'
  let eX : V.complexSurface B.complexPoint i ≅ D.complexSurface (Spec.map (CommRingCat.ofHom κ)) i :=
    c.app (W.source i) ≪≫ W.sourceIso i
  let eA : (V.complexAbelian B.complexPoint i).X ≅
      (D.complexAbelian (Spec.map (CommRingCat.ofHom κ)) i).X :=
    c.app (W.target i).X ≪≫ W.targetIso i
  have heA : IsMonHom eA.hom := by
    let : GrpObj (F.obj (W.target i).X) := Functor.grpObjObj (F := F)
    let : GrpObj (G.obj (F.obj (W.target i).X)) := Functor.grpObjObj (F := G)
    have hc : IsMonHom (show G.obj (F.obj (W.target i).X) ⟶ H.obj (W.target i).X from
        (c.app (W.target i).X).hom) := Section.Comparisons.iterated_comparison_isMonHom F G H c (W.target i).X
    have ht : IsMonHom (W.targetIso i).hom := W.targetGroup i
    change IsMonHom ((show G.obj (F.obj (W.target i).X) ⟶ H.obj (W.target i).X from
      (c.app (W.target i).X).hom) ≫ (W.targetIso i).hom)
    exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hc ht
  have hp : V.complexBasePoint B.complexPoint i ≫ eX.hom =
      D.complexBasePoint (Spec.map (CommRingCat.ofHom κ)) i := by
    let u : G.obj (F.obj W.unitModel) ≅ J.obj (𝟙_ (Over (Spec (.of K)))) :=
      c.app W.unitModel ≪≫ W.unitIso
    have hu : Section.Comparisons.mappedSection G j ≫ u.hom = (Functor.Monoidal.εIso J).hom := by
      apply (cancel_mono (Functor.Monoidal.εIso J).inv).mp
      exact Subsingleton.elim _ _
    have hn : G.map (F.map (W.point i)) ≫ (c.app (W.source i)).hom =
        (c.app W.unitModel).hom ≫ H.map (W.point i) := c.hom.naturality (W.point i)
    change Section.Comparisons.mappedSection G (j ≫ F.map (W.point i)) ≫
      ((c.app (W.source i)).hom ≫ (W.sourceIso i).hom) = Section.Comparisons.mappedSection J (D.x₀ i)
    rw [← Section.Comparisons.mappedSection_map, Category.assoc, ← Category.assoc (G.map (F.map (W.point i))), hn]
    simp only [Category.assoc]
    rw [W.pointComparison]
    exact (by simpa only [u, Iso.trans_hom, Category.assoc, Section.Comparisons.mappedSection, Functor.Monoidal.εIso_hom] using
      congrArg (fun f => f ≫ J.map (D.x₀ i)) hu)
  have hm : V.complexMap B.complexPoint i ≫ eA.hom =
      eX.hom ≫ D.complexMap (Spec.map (CommRingCat.ofHom κ)) i := by
    have hn : G.map (F.map (W.map i)) ≫ (c.app (W.target i).X).hom =
        (c.app (W.source i)).hom ≫ H.map (W.map i) := c.hom.naturality (W.map i)
    change G.map (F.map (W.map i)) ≫ ((c.app (W.target i).X).hom ≫ (W.targetIso i).hom) =
      ((c.app (W.source i)).hom ≫ (W.sourceIso i).hom) ≫ J.map (D.a i)
    rw [← Category.assoc, hn, Category.assoc, W.mapComparison, Category.assoc]
  exact D.isComplexAlbanese_of_component_iso V (Spec.map (CommRingCat.ofHom κ)) B.complexPoint
    i eX eA hp hm hD

end

/-! The localized component coproduct has the exact complex fiber of
the original number-field scheme, through the constructed component maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {T : Over (Spec (.of K))} {r : ℕ}
    {D : Components.ComponentAlbaneseData T r} {κ : K →+* ℂ} (W : LocalizedComponentDiagramExists.LocalizedComponentDiagram D κ)
    (B : Base.ArithmeticBaseExtension W.base.extension.carrier W.base.embedding)
    (φ : W.base.R →+* B.R)
    (hφ : B.toField.comp φ = (algebraMap W.base.extension.carrier B.extension.carrier).comp W.base.toField)

def LocalizedComponentDiagramExists.LocalizedComponentDiagram.baseChangedComplexSourceIso (i : Fin r) :
    (Over.pullback B.complexPoint).obj
        ((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (W.source i)) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj (D.S i) :=
  (Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso (Spec.map (CommRingCat.ofHom φ)) B.complexPoint W.base.complexPoint
      (W.base.tower_coefficient_complexPoint B φ hφ)).app (W.source i) ≪≫ W.sourceIso i

def LocalizedComponentDiagramExists.LocalizedComponentDiagram.componentCoproductComplexIso (e : (∐ D.S) ≅ T) :
    (Over.pullback B.complexPoint).obj
        (∐ fun i => (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (W.source i)) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj T :=
  (ComponentBaseChange.baseChangeDecompositionIso B.complexPoint
      (fun i => (Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (W.source i)) (Iso.refl _)).symm ≪≫
    Sigma.mapIso (W.baseChangedComplexSourceIso B φ hφ) ≪≫
      ComponentBaseChange.baseChangeDecompositionIso (Spec.map (CommRingCat.ofHom κ)) D.S e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
