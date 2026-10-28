import OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianModelDimension
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HomDescent
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Descent

/-! # Abelian Arithmetic Models -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianArithmeticModels

noncomputable section

/-! Dimension-correct arithmetic models of the actual CM abelian schemes,
with their group comparisons preserved when passing to one common field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

structure AbelianNumberFieldModel {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) where
  field : Subfield ℂ
  [numberField : NumberField field]
  abelian : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of field))
  comparison : (abelian.pullback (Spec.map (CommRingCat.ofHom field.subtype))).scheme ≅ A.scheme
  group : IsMonHom comparison.hom

attribute [instance] AbelianNumberFieldModel.numberField AbelianNumberFieldModel.group

theorem exists_abelian_numberField_model
    {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (V : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (eV : V.toOver ≅ A.scheme) [IsMonHom eV.hom]
    (hV : ArithmeticGeometry.Descent.CMVariety.AbelianFiber.HasNumberFieldModel V) : Nonempty (AbelianNumberFieldModel A) := by
  obtain ⟨F, hF, B, hB, hs, hp, hc, hcomm, e, he⟩ := hV
  let := hF
  let := hB
  let := hs
  let := hp
  let := hc
  let := hcomm
  let := he
  let eb := e ≪≫ eV
  let M := AbelianModelDimension.abelianSchemeOfComplexModel B (Spec.map (CommRingCat.ofHom F.subtype)) A eb
  exact ⟨⟨F, M, eb, inferInstanceAs (IsMonHom (e.hom ≫ eV.hom))⟩⟩

namespace AbelianNumberFieldModel

variable {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase} (M : AbelianNumberFieldModel A)
  (C : Subfield ℂ) [NumberField C] (i : M.field →+* C)
  (hi : C.subtype.comp i = M.field.subtype)

def overField : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of C)) :=
  M.abelian.pullback (Spec.map (CommRingCat.ofHom i))

def overFieldComparison :
    ((M.overField C i).pullback (Spec.map (CommRingCat.ofHom C.subtype))).scheme ≅ A.scheme :=
  IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso M.abelian.scheme
    (Spec.map (CommRingCat.ofHom i)) (Spec.map (CommRingCat.ofHom C.subtype))
    (Spec.map (CommRingCat.ofHom M.field.subtype)) (by
      rw [← Spec.map_comp]
      exact congrArg (fun j => Spec.map (CommRingCat.ofHom j)) hi) ≪≫ M.comparison

instance overFieldComparison_group : IsMonHom (M.overFieldComparison C i hi).hom := by
  let hbase : Spec.map (CommRingCat.ofHom C.subtype) ≫ Spec.map (CommRingCat.ofHom i) =
      Spec.map (CommRingCat.ofHom M.field.subtype) := by
    rw [← Spec.map_comp]
    exact congrArg (fun j => Spec.map (CommRingCat.ofHom j)) hi
  let e := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso M.abelian.scheme
    (Spec.map (CommRingCat.ofHom i)) (Spec.map (CommRingCat.ofHom C.subtype))
    (Spec.map (CommRingCat.ofHom M.field.subtype)) hbase
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ e.hom M.comparison.hom
    (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _) M.group

end AbelianNumberFieldModel

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.AbelianArithmeticModels
