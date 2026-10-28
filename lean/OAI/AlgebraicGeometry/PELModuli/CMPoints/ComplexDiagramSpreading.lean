import OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticComplexDiagrams

/-! # Complex Diagram Spreading -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

section

/-! Simultaneous number-field descent and arithmetic spreading of a
finite actual complex abelian diagram, with all comparisons retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem ComplexDiagramSpreading.exists_spread_complex_abelian_diagram
    (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (D : ArithmeticComplexDiagrams.FiniteComplexAbelianDiagram) (M : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (D.abelian i))
    (N : ℕ) (hN : N ≠ 0) :
    ∃ Q : ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel D M,
      ∃ R : AbelianDiagramSpreading.SpreadFiniteAbelianDiagram Q.diagram Q.embedding, N ∣ R.base.denominator := by
  obtain ⟨Q⟩ := ArithmeticComplexDiagrams.exists_arithmetic_complex_diagram_model hHilb hEnd D M
  obtain ⟨R, hR⟩ := AbelianDiagramSpreading.exists_spread_finite_abelian_diagram Q.embedding Q.diagram N hN
  exact ⟨Q, R, hR⟩

variable {D : ArithmeticComplexDiagrams.FiniteComplexAbelianDiagram} {M : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (D.abelian i)}
  (Q : ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel D M) (R : AbelianDiagramSpreading.SpreadFiniteAbelianDiagram Q.diagram Q.embedding)

def ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel.spreadComplexComparison (i : Fin D.objects) :
    ((R.abelian i).pullback R.base.complexPoint).scheme ≅ (D.abelian i).scheme :=
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso (R.abelian i).scheme R.base.generic
    (Spec.map (CommRingCat.ofHom R.base.embedding)) ≪≫
  (Over.pullback (Spec.map (CommRingCat.ofHom R.base.embedding))).mapIso (R.genericIso i) ≪≫
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso R.base (Q.abelian i).scheme ≪≫ Q.comparison i

theorem ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel.spreadComplexComparison_group (i : Fin D.objects) :
    IsMonHom (Q.spreadComplexComparison R i).hom := by
  let : IsMonHom (R.genericIso i).hom := R.genericGroup i
  let f₀ := (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso (R.abelian i).scheme R.base.generic
    (Spec.map (CommRingCat.ofHom R.base.embedding))).hom
  let f₁ := (Over.pullback (Spec.map (CommRingCat.ofHom R.base.embedding))).map (R.genericIso i).hom
  let f₂ := (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso R.base (Q.abelian i).scheme).hom
  have h₀ : IsMonHom f₀ := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso_isMonHom _ _ _
  have h₁ : IsMonHom f₁ := inferInstance
  have h₂ : IsMonHom f₂ := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_isMonHom _ _
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ f₀ _ h₀
    (@CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ f₁ _ h₁
      (@CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ f₂ _ h₂ (Q.comparison_group i)))

def ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel.spreadModelField (i : Fin D.objects) : (M i).field →+* R.base.extension.carrier :=
  (algebraMap Q.field R.base.extension.carrier).comp (Q.modelField i)

theorem ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel.spreadModelField_compatible (i : Fin D.objects) :
    R.base.embedding.comp (Q.spreadModelField R i) = (M i).field.subtype :=
  (RingHom.comp_assoc _ _ _).symm.trans
    ((congrArg (fun κ => κ.comp (Q.modelField i)) R.base.embedding_extends).trans
      (Q.field_compatible i))

def ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel.spreadGenericModelComparison (i : Fin D.objects) :
    ((R.abelian i).pullback R.base.generic).scheme ≅
      ((M i).abelian.pullback (Spec.map (CommRingCat.ofHom (Q.spreadModelField R i)))).scheme :=
  R.genericIso i ≪≫ (Over.pullback R.base.fieldExtension).mapIso (Q.modelComparison i) ≪≫
    IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (M i).abelian.scheme
      (Spec.map (CommRingCat.ofHom (Q.modelField i))) R.base.fieldExtension
      (Spec.map (CommRingCat.ofHom (Q.spreadModelField R i))) (by
        change Spec.map (CommRingCat.ofHom (algebraMap Q.field R.base.extension.carrier)) ≫
          Spec.map (CommRingCat.ofHom (Q.modelField i)) = _
        rw [← Spec.map_comp]
        rfl)

theorem ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel.spreadGenericModelComparison_group (i : Fin D.objects) :
    IsMonHom (Q.spreadGenericModelComparison R i).hom := by
  let : IsMonHom (Q.modelComparison i).hom := Q.modelComparison_group i
  let h₁ : IsMonHom ((Over.pullback R.base.fieldExtension).map (Q.modelComparison i).hom) :=
    inferInstance
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ (R.genericGroup i)
    (@CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h₁
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _))

end

/-! Every arrow of the spread diagram recovers the specified complex
arrow through the complete arithmetic and complex comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel.spreadComplexComparison_compatible
    {D : ArithmeticComplexDiagrams.FiniteComplexAbelianDiagram} {M : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (D.abelian i)}
    (Q : ArithmeticComplexDiagrams.ArithmeticComplexDiagramModel D M) (R : AbelianDiagramSpreading.SpreadFiniteAbelianDiagram Q.diagram Q.embedding)
    (a : Fin D.arrows) :
    (Over.pullback R.base.complexPoint).map (R.map a) ≫
      (Q.spreadComplexComparison R (D.target a)).hom =
        (Q.spreadComplexComparison R (D.source a)).hom ≫ D.map a := by
  let Fc := Over.pullback (Spec.map (CommRingCat.ofHom R.base.embedding))
  let Fg := Over.pullback R.base.generic
  let Ff := Over.pullback R.base.fieldExtension
  let Fq := Over.pullback (Spec.map (CommRingCat.ofHom Q.embedding))
  let c₀ i := (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso (R.abelian i).scheme R.base.generic
    (Spec.map (CommRingCat.ofHom R.base.embedding))).hom
  let c₁ i := Fc.map (R.genericIso i).hom
  let c₂ i := (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso R.base (Q.abelian i).scheme).hom
  have h₀ : CommSq ((Over.pullback R.base.complexPoint).map (R.map a))
      (c₀ (D.source a)) (c₀ (D.target a)) (Fc.map (Fg.map (R.map a))) :=
    ⟨(Over.pullbackComp (Spec.map (CommRingCat.ofHom R.base.embedding))
      R.base.generic).hom.naturality (R.map a)⟩
  have h₁ : CommSq (Fc.map (Fg.map (R.map a))) (c₁ (D.source a)) (c₁ (D.target a))
      (Fc.map (Ff.map (Q.map a))) := by
    constructor
    have h := congrArg Fc.map (R.compatible a)
    simp only [Functor.map_comp] at h
    exact h
  have h₂ : CommSq (Fc.map (Ff.map (Q.map a))) (c₂ (D.source a)) (c₂ (D.target a))
      (Fq.map (Q.map a)) :=
    ⟨(IntegralModel.Arithmetic.ComplexComparison.GroupBaseChange.arithmeticComplexNatIso R.base).hom.naturality (Q.map a)⟩
  have h₃ : CommSq (Fq.map (Q.map a)) (Q.comparison (D.source a)).hom
      (Q.comparison (D.target a)).hom (D.map a) := ⟨Q.compatible a⟩
  exact (h₀.vert_comp (h₁.vert_comp (h₂.vert_comp h₃))).w

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
