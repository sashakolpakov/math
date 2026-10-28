import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarSheafUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientDiagramTwo

/-! # Scalar Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarNaturality.SectionScalarChange

noncomputable section

section

/-! Coefficient change commutes with the actual sheafified direct-image map of forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

theorem sheafDirectImage_inverse_square :
    Int.sheafDirectImage (ScalarImage.SectionScalarChange.restrictMap σ f) ≫
      ((Int.directImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X).inv =
    (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).inv ≫
      ((SheafScalarChange.SectionScalarChange.sheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Int.sheafDirectImage f) := by
  let XR := ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X
  let YR := ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom Y
  let UR := (sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let UX := (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let US := (sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat S)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let FY := (PresheafScalarChange.SectionScalarChange.presheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ)
  let FX := (PresheafScalarChange.SectionScalarChange.presheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ)
  let CY := (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ)
  let DR := (Int.directImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)
  let DP := (Int.directImagePresheaf (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)
  let DS := (Int.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)
  let ηRY := (Int.sheafificationComplexAdjunction YR).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R YR)
  let ηRX := (Int.sheafificationComplexAdjunction XR).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R XR)
  let ηSY := (Int.sheafificationComplexAdjunction Y).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S Y)
  let ηSX := (Int.sheafificationComplexAdjunction X).unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex S X)
  let eY := SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y
  let eX := SheafScalarChange.SectionScalarChange.sheafComplexIso σ X
  let pY := PresheafScalarChange.SectionScalarChange.presheafComplexIso σ Y
  let pX := PresheafScalarChange.SectionScalarChange.presheafComplexIso σ X
  let dR := Int.sheafDirectImage (ScalarImage.SectionScalarChange.restrictMap σ f)
  let dS := Int.sheafDirectImage f
  let pR := Int.presheafPullback (ScalarImage.SectionScalarChange.restrictMap σ f)
  let pS := Int.presheafPullback f
  have hR : ηRY ≫ UR.map dR = pR ≫ DP.map ηRX := SheafComposition.sheafDirectImage_unit (ScalarImage.SectionScalarChange.restrictMap σ f)
  have hS : ηSY ≫ US.map dS = pS ≫ DS.map ηSX := SheafComposition.sheafDirectImage_unit f
  have hY : ηRY ≫ UR.map eY.inv = pY.hom ≫ FY.map ηSY := ScalarSheafUnit.SectionScalarChange.sheafComplexIso_inv_unit σ Y
  have hX : ηRX ≫ UX.map eX.inv = pX.hom ≫ FX.map ηSX := ScalarSheafUnit.SectionScalarChange.sheafComplexIso_inv_unit σ X
  have hp : pR ≫ DP.map pX.hom = pY.hom ≫ FY.map pS := ScalarImage.SectionScalarChange.presheafPullback_square σ f
  apply ((Int.sheafificationComplexAdjunction YR).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R YR)
    (DR.obj (((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S X)))).injective
  change ηRY ≫ UR.map (dR ≫ DR.map eX.inv) = ηRY ≫ UR.map (eY.inv ≫ CY.map dS)
  have hl := (CoefficientDiagramTwo.CoefficientDiagram.unit_image_comp UR ηRY dR (DR.map eX.inv)).trans
    (congrArg (fun k => k ≫ UR.map (DR.map eX.inv)) hR)
  have hr := (CoefficientDiagramTwo.CoefficientDiagram.unit_image_comp UR ηRY eY.inv (CY.map dS)).trans
    (congrArg (fun k => k ≫ UR.map (CY.map dS)) hY)
  have hm := CoefficientDiagramTwo.CoefficientDiagram.two_step_square pR (DP.map ηRX) (DP.map (UX.map eX.inv))
    (DP.map pX.hom) (DP.map (FX.map ηSX)) pY.hom (FY.map ηSY) (FY.map (US.map dS))
    (FY.map pS)
    (CoefficientDiagramTwo.CoefficientDiagram.map_square DP ηRX (UX.map eX.inv) pX.hom (FX.map ηSX) hX)
    (CoefficientDiagramTwo.CoefficientDiagram.map_square FY ηSY (US.map dS) pS (DS.map ηSX) hS) hp
  exact hl.trans (hm.trans hr.symm)

theorem sheafDirectImage_square :
    ((SheafScalarChange.SectionScalarChange.sheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Int.sheafDirectImage f) ≫
      ((Int.directImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X).hom =
    (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).hom ≫ Int.sheafDirectImage (ScalarImage.SectionScalarChange.restrictMap σ f) :=
  ScalarImage.SectionScalarChange.inverse_square (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).symm
    (((Int.directImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X)).symm _ _ (sheafDirectImage_inverse_square σ f)

end

/-! Native inverse-image pullback naturality under an equivalence of coefficient fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

theorem coefficientUnit_directImage (K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S X) ℕ) :
    ((Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ X).unit.app K) =
      (ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ Y).unit.app
        (((Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj K) := rfl

theorem sheafDirectImage_mate_square :
    Int.sheafDirectImage f ≫
        ((Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ X).homEquiv _ _ (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X).hom) =
      (ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ Y).homEquiv _ _ (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).hom ≫
        ((ScalarImage.SectionScalarChange.inverseScalars σ Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (Int.sheafDirectImage (ScalarImage.SectionScalarChange.restrictMap σ f)) := by
  let DS := (Int.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)
  let DR := (Int.directImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)
  let IY := (ScalarImage.SectionScalarChange.inverseScalars σ Y).mapHomologicalComplex (ComplexShape.up ℕ)
  let IX := (ScalarImage.SectionScalarChange.inverseScalars σ X).mapHomologicalComplex (ComplexShape.up ℕ)
  let CY := (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ)
  let cY := ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ Y
  let cX := ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ X
  let eX := SheafScalarChange.SectionScalarChange.sheafComplexIso σ X
  let eY := SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y
  let dS := Int.sheafDirectImage f
  let dR := Int.sheafDirectImage (ScalarImage.SectionScalarChange.restrictMap σ f)
  have hu : dS ≫ DS.map (cX.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S X)) =
      cY.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S Y) ≫ IY.map (CY.map dS) := cY.unit.naturality dS
  have hs := CoefficientDiagramTwo.CoefficientDiagram.map_square IY (CY.map dS) (DR.map eX.hom) eY.hom dR
    (sheafDirectImage_square σ f)
  have hl := (congrArg (fun k => dS ≫ DS.map k) (cX.homEquiv_unit _ _ eX.hom)).trans
    (congrArg (fun k => dS ≫ k) (DS.map_comp (cX.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S X)) (IX.map eX.hom)))
  have hr := congrArg (fun k => k ≫ IY.map dR) (cY.homEquiv_unit _ _ eY.hom)
  have hm := CoefficientDiagramTwo.CoefficientDiagram.mate_paste dS (DS.map (cX.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S X)))
    (cY.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S Y)) (IY.map (CY.map dS)) (IY.map (DR.map eX.hom))
    (IY.map eY.hom) (IY.map dR) hu hs
  exact hl.trans (hm.trans hr.symm)

theorem sheafPullback_square :
    ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Int.sheafPullback f) ≫ (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X).hom =
      (ScalarImage.SectionScalarChange.imageScalarComplexIso σ f).hom.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S Y) ≫
        ((Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).hom ≫ Int.sheafPullback (ScalarImage.SectionScalarChange.restrictMap σ f) := by
  let a := Int.imageComplexAdjunction f
  let b := ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ X
  let c := ScalarImage.SectionScalarChange.coefficientComplexAdjunction σ Y
  let d := Int.imageComplexAdjunction (ScalarImage.SectionScalarChange.restrictMap σ f)
  apply ((a.comp b).homEquiv (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex S Y)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X))).injective
  have hl := AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.comp_homEquiv_map_comp a b
    (Int.sheafPullback f) (SheafScalarChange.SectionScalarChange.sheafComplexIso σ X).hom
  erw [SheafComposition.sheafPullback_normalization f] at hl
  have hr := AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.comp_homEquiv_map_comp c d
    (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).hom (Int.sheafPullback (ScalarImage.SectionScalarChange.restrictMap σ f))
  erw [SheafComposition.sheafPullback_normalization (ScalarImage.SectionScalarChange.restrictMap σ f)] at hr
  have he := AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.leftAdjointUniq_homEquiv (a.comp b) (c.comp d)
    (((Int.inverseImage (ScalarImage.SectionScalarChange.restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (SheafScalarChange.SectionScalarChange.sheafComplexIso σ Y).hom ≫ Int.sheafPullback (ScalarImage.SectionScalarChange.restrictMap σ f))
  exact hl.trans ((sheafDirectImage_mate_square σ f).trans (he.trans hr).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarNaturality.SectionScalarChange
