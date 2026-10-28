import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.SheafComposition

/-! # Scalar Sheaf Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarSheafUnit.SectionScalarChange

noncomputable section

/-! Normalization of coefficient change against the native sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  (X : Over (Spec (CommRingCat.of S)))

theorem sheafComplexIso_inv_unit :
    (Int.sheafificationComplexAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)).unit.app
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)) ≫
      ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X).inv =
    (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ X).hom ≫
      ((PresheafScalarChange.SectionScalarChange.presheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S X)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  let J := Opens.grothendieckTopology X.left
  let a := sheafificationAdjunction J (ModuleCat S)
  let b := sheafificationAdjunction J (ModuleCat R)
  let P := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf S X n
  let Q := AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) n
  let F := PresheafScalarChange.SectionScalarChange.presheafRestriction σ X
  let L := presheafToSheaf J (ModuleCat R)
  let U := sheafToPresheaf J (ModuleCat R)
  let e := PresheafScalarChange.SectionScalarChange.formsPresheafIso σ X n
  let c := (sheafComposeNatIso J (ModuleCat.restrictScalars σ.toRingHom) a b).app P
  change b.unit.app Q ≫ U.map (L.map e.hom ≫ c.hom) = e.hom ≫ F.map (a.unit.app P)
  erw [U.map_comp, ← Category.assoc]
  have he : b.unit.app Q ≫ U.map (L.map e.hom) = e.hom ≫ b.unit.app (F.obj P) :=
    (b.unit.naturality e.hom).symm
  erw [he, Category.assoc]
  exact congrArg (fun k => e.hom ≫ k)
    (sheafComposeNatTrans_fac J (ModuleCat.restrictScalars σ.toRingHom) a b P)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarSheafUnit.SectionScalarChange
