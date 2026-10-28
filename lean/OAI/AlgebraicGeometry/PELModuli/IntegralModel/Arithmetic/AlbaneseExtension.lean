import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Albanese
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionCapstone
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.MultiplicationQuotient

/-! # Albanese Extension -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AlbaneseExtension

noncomputable section

section

/-! Construct the arithmetic Albanese and its exact complex realization
directly from the native source geometry. Construction and HodgeComparison are proved inputs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {R : Type} [Field R] [NumberField R] [Algebra R ℂ]

structure ArithmeticAlbaneseRealization
    (X : Over (Spec (.of R))) (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A.toOver) where
  base : Base.ArithmeticBaseExtension R (algebraMap R ℂ)
  model : Quotients.FiniteDescent.AbelianQuotient.Construction.AbelianScheme (Spec (.of base.extension.carrier))
  map : (Over.pullback base.fieldExtension).obj X ⟶ model.toOver
  sourceIso : (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding))).obj
      ((Over.pullback base.fieldExtension).obj X) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X
  targetIso : (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding))).obj model.toOver ≅ A.toOver
  groupComparison : IsMonHom targetIso.hom
  pointed : Section.Comparisons.mappedSection (Over.pullback base.fieldExtension) x₀ ≫ map = 1
  sourcePoint : Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding)))
      (Section.Comparisons.mappedSection (Over.pullback base.fieldExtension) x₀) ≫ sourceIso.hom =
    Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀
  comparison : (Over.pullback (Spec.map (CommRingCat.ofHom base.embedding))).map map ≫ targetIso.hom =
    sourceIso.hom ≫ a

theorem arithmetic_albanese_realization_exists
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
    (x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).left
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X).hom)
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A.toOver)
      (D : ArithmeticAlbaneseRealization X x₀ A a),
      Albanese.IsAlbaneseMap (AlbaneseArithmeticIsogeny.complexSourcePresentation X P)
        (Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀) A a ∧
      D.base.denominator = N ∧
      Function.Bijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
        ((Over.pullback (Spec.map (CommRingCat.ofHom D.base.embedding))).map D.map)).hom := by
  let V := Albanese.complexSourceVariety X P
  let x : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ V.toOver :=
    Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀
  have : ConnectedSpace V.presentation.carrier := inferInstanceAs (ConnectedSpace V.carrier)
  obtain ⟨A, a, ha⟩ := ConstructionCapstone.provedConstructionInput V.presentation x
  obtain ⟨B, Y, r, eX, eY, hB, heY, hp, hs, hr⟩ :=
    EffectiveAlbaneseDescent.effective_arithmetic_albanese_descent X x₀ P A a ha N hN
  let D : ArithmeticAlbaneseRealization X x₀ A a := {
    base := B
    model := Y
    map := r
    sourceIso := eX
    targetIso := eY
    groupComparison := heY
    pointed := hp
    sourcePoint := hs
    comparison := hr }
  exact ⟨A, a, D, ha, hB,
    Albanese.arithmetic_albanese_h1_of_exact_comparison X x₀ P A a ha B Y.toOver r eX eY hr⟩

end

/-! An arithmetic Albanese realization extends to a common finite field
while retaining its actual pointed map and specified complex realization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def ArithmeticAlbaneseRealization.extend
    {R : Type} [Field R] [NumberField R] [Algebra R ℂ]
    {X : Over (Spec (.of R))} {x₀ : 𝟙_ (Over (Spec (.of R))) ⟶ X}
    {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    {a : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X ⟶ A.toOver}
    (D : ArithmeticAlbaneseRealization X x₀ A a)
    (B : Base.ArithmeticBaseExtension R (algebraMap R ℂ))
    (φ : D.base.extension.carrier →+* B.extension.carrier)
    (hφ : φ.comp (algebraMap R D.base.extension.carrier) = algebraMap R B.extension.carrier)
    (hφC : B.embedding.comp φ = D.base.embedding) :
    ArithmeticAlbaneseRealization X x₀ A a := by
  let α := Spec.map (CommRingCat.ofHom φ)
  let β := Spec.map (CommRingCat.ofHom B.embedding)
  have hα : α ≫ D.base.fieldExtension = B.fieldExtension := by
    change Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R D.base.extension.carrier)) =
        Spec.map (CommRingCat.ofHom (algebraMap R B.extension.carrier))
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hφ
  have hβ : β ≫ α = Spec.map (CommRingCat.ofHom D.base.embedding) := by
    change Spec.map (CommRingCat.ofHom B.embedding) ≫ Spec.map (CommRingCat.ofHom φ) = _
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hφC
  let F := Over.pullback D.base.fieldExtension
  let G := Over.pullback α
  let H := Over.pullback B.fieldExtension
  let Q := Over.pullback β
  let P := Over.pullback (Spec.map (CommRingCat.ofHom D.base.embedding))
  let cs : F ⋙ G ≅ H := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso D.base.fieldExtension α B.fieldExtension hα
  let ct : G ⋙ Q ≅ P := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso α β
    (Spec.map (CommRingCat.ofHom D.base.embedding)) hβ
  let : GrpObj (G.obj D.model.toOver) := Functor.grpObjObj (F := G)
  let : GrpObj (Q.obj (G.obj D.model.toOver)) := Functor.grpObjObj (F := Q)
  let Y := D.model.baseChange α
  let r : H.obj X ⟶ Y.toOver := (cs.app X).inv ≫ G.map D.map
  let cx : Q.obj (H.obj X) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))).obj X :=
    (Q.mapIso (cs.app X)).symm ≪≫ ct.app (F.obj X) ≪≫ D.sourceIso
  let cy : Q.obj Y.toOver ≅ A.toOver := ct.app D.model.toOver ≪≫ D.targetIso
  have hs : Section.Comparisons.mappedSection H x₀ ≫ (cs.app X).inv = Section.Comparisons.mappedSection G (Section.Comparisons.mappedSection F x₀) := by
    apply (cancel_mono (cs.app X).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (Section.Comparisons.mappedSection_comp_naturality F G H cs.hom x₀).symm
  have hp : Section.Comparisons.mappedSection H x₀ ≫ r = 1 := by
    change Section.Comparisons.mappedSection H x₀ ≫ ((cs.app X).inv ≫ G.map D.map) = 1
    rw [← Category.assoc, hs, Section.Comparisons.mappedSection_map, D.pointed, Section.Comparisons.mappedSection_one]
  have hcx : Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection H x₀) ≫ cx.hom =
      Section.Comparisons.mappedSection (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R ℂ)))) x₀ := by
    have h₀ : Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection H x₀) ≫ Q.map (cs.app X).inv =
        Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection G (Section.Comparisons.mappedSection F x₀)) := by
      rw [Section.Comparisons.mappedSection_map, hs]
    change Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection H x₀) ≫
      (Q.map (cs.app X).inv ≫ (ct.app (F.obj X)).hom ≫ D.sourceIso.hom) = _
    have h₁ : Section.Comparisons.mappedSection Q (Section.Comparisons.mappedSection G (Section.Comparisons.mappedSection F x₀)) ≫
        (ct.app (F.obj X)).hom = Section.Comparisons.mappedSection P (Section.Comparisons.mappedSection F x₀) :=
      Section.Comparisons.mappedSection_comp_naturality G Q P ct.hom (Section.Comparisons.mappedSection F x₀)
    rw [← Category.assoc, ← Category.assoc, h₀, h₁, D.sourcePoint]
  have hcy : IsMonHom cy.hom := by
    have hc : IsMonHom (show Q.obj (G.obj D.model.toOver) ⟶ P.obj D.model.toOver from
        (ct.app D.model.toOver).hom) :=
      Section.Comparisons.iterated_comparison_isMonHom G Q P ct D.model.toOver
    have : IsMonHom D.targetIso.hom := D.groupComparison
    change IsMonHom ((show Q.obj (G.obj D.model.toOver) ⟶ P.obj D.model.toOver from
      (ct.app D.model.toOver).hom) ≫ D.targetIso.hom)
    exact CategoryTheory.instIsMonHomComp _ _
  have hr : Q.map r ≫ cy.hom = cx.hom ≫ a := by
    have hn := ct.hom.naturality D.map
    change Q.map (G.map D.map) ≫ (ct.app D.model.toOver).hom =
      (ct.app (F.obj X)).hom ≫ P.map D.map at hn
    change Q.map ((cs.app X).inv ≫ G.map D.map) ≫
      ((ct.app D.model.toOver).hom ≫ D.targetIso.hom) =
        (Q.map (cs.app X).inv ≫ (ct.app (F.obj X)).hom ≫ D.sourceIso.hom) ≫ a
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (Q.map (G.map D.map)), hn, Category.assoc, D.comparison]
  exact {
    base := B
    model := Y
    map := r
    sourceIso := cx
    targetIso := cy
    groupComparison := hcy
    pointed := hp
    sourcePoint := hcx
    comparison := hr }

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.AlbaneseExtension
