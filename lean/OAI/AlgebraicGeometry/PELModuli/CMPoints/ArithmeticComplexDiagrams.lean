import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianArithmeticModels
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CommonEmbeddedFields
import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianDiagramSpreading
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HomNumberFieldDescent

/-! # Arithmetic Complex Diagrams -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticComplexDiagrams

noncomputable section

/-! Descend a finite complex diagram using the exact number-field models
of its objects, the full Presentations inputs, and proved endomorphism rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure FiniteComplexAbelianDiagram where
  objects : ℕ
  arrows : ℕ
  dimension : Fin objects → ℕ
  abelian : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (dimension i) Foundations.Scheme.ProjectiveSpace.complexBase
  source : Fin arrows → Fin objects
  target : Fin arrows → Fin objects
  map : ∀ a, (abelian (source a)).scheme ⟶ (abelian (target a)).scheme
  group : ∀ a, IsMonHom (map a)

structure ArithmeticComplexDiagramModel (D : FiniteComplexAbelianDiagram)
    (M : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (D.abelian i)) where
  field : Type
  [fieldStructure : Field field]
  [numberField : NumberField field]
  embedding : field →+* ℂ
  modelField : ∀ i, (M i).field →+* field
  field_compatible : ∀ i, embedding.comp (modelField i) = (M i).field.subtype
  abelian : ∀ i, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (D.dimension i) (Spec (.of field))
  modelComparison : ∀ i, (abelian i).scheme ≅
    ((M i).abelian.pullback (Spec.map (CommRingCat.ofHom (modelField i)))).scheme
  modelComparison_group : ∀ i, IsMonHom (modelComparison i).hom
  map : ∀ a, (abelian (D.source a)).scheme ⟶ (abelian (D.target a)).scheme
  group : ∀ a, IsMonHom (map a)
  comparison : ∀ i, ((abelian i).pullback (Spec.map (CommRingCat.ofHom embedding))).scheme ≅
    (D.abelian i).scheme
  comparison_group : ∀ i, IsMonHom (comparison i).hom
  compatible : ∀ a, (Over.pullback (Spec.map (CommRingCat.ofHom embedding))).map (map a) ≫
      (comparison (D.target a)).hom = (comparison (D.source a)).hom ≫ D.map a

attribute [instance] ArithmeticComplexDiagramModel.fieldStructure ArithmeticComplexDiagramModel.numberField

def ArithmeticComplexDiagramModel.diagram {D : FiniteComplexAbelianDiagram}
    {M : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (D.abelian i)} (Q : ArithmeticComplexDiagramModel D M) :
    AbelianDiagramSpreading.FiniteAbelianDiagram Q.field where
  objects := D.objects
  arrows := D.arrows
  dimension := D.dimension
  abelian := Q.abelian
  source := D.source
  target := D.target
  map := Q.map
  group := Q.group

theorem exists_arithmetic_complex_diagram_model (hHilb : IntegralModel.Presentations.Hilbert.HilbertHomInput.{0}) (hEnd : IntegralModel.Presentations.Hilbert.EndomorphismEquationsInput.{0})
    (D : FiniteComplexAbelianDiagram) (M : ∀ i, AbelianArithmeticModels.AbelianNumberFieldModel (D.abelian i)) :
    Nonempty (ArithmeticComplexDiagramModel D M) := by
  obtain ⟨C, hC, iF, hiF⟩ := CommonEmbeddedFields.exists_common_embedded_numberField
    (fun i => (M i).field) (fun i => (M i).field.subtype)
  let := hC
  let A (i : Fin D.objects) := (M i).overField C (iF i)
  let ec (i : Fin D.objects) := (M i).overFieldComparison C (iF i) (hiF i)
  let f (a : Fin D.arrows) := (ec (D.source a)).hom ≫ D.map a ≫ (ec (D.target a)).inv
  have hec (i : Fin D.objects) : IsMonHom (ec i).hom :=
    AbelianArithmeticModels.AbelianNumberFieldModel.overFieldComparison_group (M i) C (iF i) (hiF i)
  have hf (a : Fin D.arrows) : IsMonHom (f a) := by
    let := hec (D.source a)
    let := hec (D.target a)
    let := D.group a
    exact inferInstanceAs (IsMonHom ((ec (D.source a)).hom ≫ D.map a ≫ (ec (D.target a)).inv))
  obtain ⟨B, fB, hfB, hcomp⟩ := HomNumberFieldDescent.finite_abelian_homomorphisms_descend hHilb hEnd C.subtype D.dimension A
    D.source D.target f hf
  let A' (i : Fin D.objects) := (A i).pullback B.fieldExtension
  let modelComparison (i : Fin D.objects) := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (M i).abelian.scheme
    (Spec.map (CommRingCat.ofHom (iF i))) B.fieldExtension
    (Spec.map (CommRingCat.ofHom ((algebraMap C B.extension.carrier).comp (iF i)))) (by
      change Spec.map (CommRingCat.ofHom (algebraMap C B.extension.carrier)) ≫
        Spec.map (CommRingCat.ofHom (iF i)) = _
      rw [← Spec.map_comp]
      rfl)
  have hModelComparison (i : Fin D.objects) : IsMonHom (modelComparison i).hom :=
    IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _
  let e (i : Fin D.objects) := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B (A i).scheme ≪≫ ec i
  have he (i : Fin D.objects) : IsMonHom (e i).hom := by
    exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B (A i).scheme).hom (ec i).hom
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso_isMonHom B (A i).scheme) (hec i)
  refine ⟨{
    field := B.extension.carrier
    embedding := B.embedding
    modelField := fun i => (algebraMap C B.extension.carrier).comp (iF i)
    field_compatible := ?_
    abelian := A'
    modelComparison := modelComparison
    modelComparison_group := hModelComparison
    map := fB
    group := hfB
    comparison := e
    comparison_group := he
    compatible := ?_ }⟩
  · intro i
    exact (RingHom.comp_assoc _ _ _).symm.trans
      ((congrArg (fun κ => κ.comp (iF i)) B.embedding_extends).trans (hiF i))
  · intro a
    have h := congrArg (fun k => k ≫ (ec (D.target a)).hom) (hcomp a)
    have hcancel : f a ≫ (ec (D.target a)).hom = (ec (D.source a)).hom ≫ D.map a :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => (ec (D.source a)).hom ≫ k)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => D.map a ≫ k) (ec (D.target a)).inv_hom_id).trans
              (Category.comp_id _))))
    exact (Category.assoc _ _ _).symm.trans
      (h.trans ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.arithmeticComplexIso B
          (A (D.source a)).scheme).hom ≫ k) hcancel).trans (Category.assoc _ _ _).symm)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ArithmeticComplexDiagrams
