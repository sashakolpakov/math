import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseTransfer
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ComponentBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Tower

/-! # Component Albanese Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

section

/-! Compatible arithmetic base changes retain the exact complex
component Albanese property through their canonical pullback comparisons. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem Components.ComponentAlbaneseData.baseChange_isComplexAlbanese
    {B C : Scheme} (g : C ⟶ B) {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (c' : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ C)
    (h : c' ≫ g = c) (i : Fin r) (hD : D.IsComplexAlbanese c i) :
    (D.baseChange g).IsComplexAlbanese c' i := by
  let F := Over.pullback g
  let G := Over.pullback c'
  let H := Over.pullback c
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso g c' c h
  let V := D.baseChange g
  let eX : V.complexSurface c' i ≅ D.complexSurface c i := e.app (D.S i)
  let eA : (V.complexAbelian c' i).X ≅ (D.complexAbelian c i).X := e.app (D.A i).X
  have : IsMonHom eA.hom := Section.Comparisons.iterated_comparison_isMonHom F G H e (D.A i).X
  have hp : V.complexBasePoint c' i ≫ eX.hom = D.complexBasePoint c i :=
    Section.Comparisons.mappedSection_comp_naturality F G H e.hom (D.x₀ i)
  have hm : V.complexMap c' i ≫ eA.hom = eX.hom ≫ D.complexMap c i :=
    e.hom.naturality (D.a i)
  exact D.isComplexAlbanese_of_component_iso V c c' i eX eA hp hm hD

theorem Base.ArithmeticBaseExtension.tower_coefficient_complexPoint
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ)
    (D : Base.ArithmeticBaseExtension B.extension.carrier B.embedding)
    (φ : B.R →+* D.R)
    (hφ : D.toField.comp φ = (algebraMap B.extension.carrier D.extension.carrier).comp B.toField) :
    (B.compose D).complexPoint ≫ Spec.map (CommRingCat.ofHom φ) = B.complexPoint := by
  have hring : (D.embedding.comp D.toField).comp φ = B.embedding.comp B.toField := by
    rw [RingHom.comp_assoc, hφ, ← RingHom.comp_assoc, D.embedding_extends]
  have hc (A : Base.ArithmeticBaseExtension K κ) :
      A.complexPoint = Spec.map (CommRingCat.ofHom (A.embedding.comp A.toField)) :=
    (Spec.map_comp (CommRingCat.ofHom A.toField) (CommRingCat.ofHom A.embedding)).symm
  rw [hc, hc, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hring

end

/-! Component data may be attached to the actual isomorphic total scheme;
its sources, groups, points, maps and Albanese properties stay literal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Components.ComponentAlbaneseData.retarget {B : Scheme} {T : Over B} {r : ℕ}
    (D : Components.ComponentAlbaneseData T r) (T' : Over B) : Components.ComponentAlbaneseData T' r where
  S := D.S
  A := D.A
  x₀ := D.x₀
  a := D.a

theorem Components.ComponentAlbaneseData.retarget_isComplexAlbanese
    {B : Scheme} {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r) (T' : Over B)
    (c : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ B) (i : Fin r) :
    (D.retarget T').IsComplexAlbanese c i ↔ D.IsComplexAlbanese c i := Iff.rfl

theorem Components.ComponentAlbaneseData.baseChange_geometry
    {B C : Scheme} (g : C ⟶ B) {T : Over B} {r : ℕ} (D : Components.ComponentAlbaneseData T r)
    (hS : ∀ i, Smooth (D.S i).hom ∧ IsProper (D.S i).hom ∧ GeometricallyConnected (D.S i).hom)
    (hA : ∀ i, Smooth (D.A i).X.hom ∧ IsProper (D.A i).X.hom ∧ GeometricallyConnected (D.A i).X.hom)
    (i : Fin r) :
    let V := D.baseChange g
    Smooth (V.S i).hom ∧ IsProper (V.S i).hom ∧ GeometricallyConnected (V.S i).hom ∧
      Smooth (V.A i).X.hom ∧ IsProper (V.A i).X.hom ∧ GeometricallyConnected (V.A i).X.hom := by
  have : Smooth (D.S i).hom := (hS i).1
  have : IsProper (D.S i).hom := (hS i).2.1
  have : GeometricallyConnected (D.S i).hom := (hS i).2.2
  have : Smooth (D.A i).X.hom := (hA i).1
  have : IsProper (D.A i).X.hom := (hA i).2.1
  have : GeometricallyConnected (D.A i).X.hom := (hA i).2.2
  exact ⟨inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd (D.S i).hom g)),
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (D.S i).hom g)),
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd (D.S i).hom g)),
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd (D.A i).X.hom g)),
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (D.A i).X.hom g)),
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd (D.A i).X.hom g))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
