import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntegerTransportNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyAdditive
import OAI.AlgebraicGeometry.ComplexMultiplication.HomFunctorDerived
import OAI.AlgebraicGeometry.ComplexMultiplication.HomDerivedPrecomp
import OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedHomSourceNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality

/-! # Hypercohomology Class Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyClassNaturality

noncomputable section

/-! # Original Hom-complex classes and genuine inverse image

The original class-to-hypercohomology map commutes with actual inverse image
under the actual scheme-point map, with its original integer source transport.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint
open _root_.CochainComplex.HomComplex Localization

variable {X Y : Over (Spec (.of ℂ))}

local instance CMOriginalHypercohomologyClassNaturality.localInstance1 (Z : Over (Spec (.of ℂ))) : HasDerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Z) :=
  HasDerivedCategory.standard _

local instance CMOriginalHypercohomologyClassNaturality.localInstance2 (f : X ⟶ Y) : (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.CommShift ℤ :=
  inferInstanceAs
    (((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine source transport square remains the same in the derived category. -/
theorem originalIntegerDerivedSource_square (f : X ⟶ Y) :
    (DerivedCategory.Q.map (AnalyticInverseImage.originalIntegerComplexInverseImageIso f).inv ≫
        (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategoryFactors.inv.app
          (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y)) ≫
      (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategory.map
        (DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle Y).hom) =
    DerivedCategory.Q.map (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom ≫
      (DerivedCategory.Q.map (HomPullback.originalIntegerSingleInverseImageIso f).inv ≫
        (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategoryFactors.inv.app
          (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y)))) := by
  let F := AnalyticInverseImage.originalAnalyticSheafInverseImage f
  let Φ := AnalyticInverseImage.originalAnalyticInverseImageLocalizer f
  let G := F.mapDerivedCategory
  let : G.CommShift ℤ := inferInstanceAs (F.mapDerivedCategory.CommShift ℤ)
  let e : Φ.functor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ G :=
    F.mapDerivedCategoryFactors.symm
  let : NatTrans.CommShift e.hom ℤ := inferInstanceAs
    (NatTrans.CommShift F.mapDerivedCategoryFactors.inv ℤ)
  let cY := (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle Y).hom
  let cX := (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom
  let eI := AnalyticInverseImage.originalIntegerComplexInverseImageIso f
  let eS := HomPullback.originalIntegerSingleInverseImageIso f
  have hn := e.hom.naturality cY
  change DerivedCategory.Q.map (Φ.functor.map cY) ≫ e.hom.app _ =
    e.hom.app _ ≫ G.map (DerivedCategory.Q.map cY) at hn
  change
      (DerivedCategory.Q.map eI.inv ≫ e.hom.app (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y)) ≫
          G.map (DerivedCategory.Q.map cY) =
        DerivedCategory.Q.map cX ≫
          (DerivedCategory.Q.map eS.inv ≫ e.hom.app
            (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))))
  calc
    _ = DerivedCategory.Q.map eI.inv ≫
        (DerivedCategory.Q.map (Φ.functor.map cY) ≫ e.hom.app _) := by
      rw [Category.assoc, hn]
    _ = _ := by
      rw [← Functor.map_comp_assoc]
      have hc : eI.inv ≫ Φ.functor.map cY = cX ≫ eS.inv :=
        IntegerTransportNaturality.originalIntegerComplexInverseImageIso_inv_comp f
      rw [hc, Functor.map_comp, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Mapping original classes through inverse image gives the actual derived functor. -/
theorem originalHomComplexClassInverseImage_derived (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (z : CohomologyClass
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K n) :
    HomPostcomp.cohomologyClassToDerived
        (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))
        ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n
          (HomPullback.originalHomComplexClassInverseImage f K n z) =
      DerivedCategory.Q.map (HomPullback.originalIntegerSingleInverseImageIso f).inv ≫
        (ShiftedHom.mk₀ 0 rfl
          ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategoryFactors.inv.app
            (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))))).comp
          (((HomPostcomp.cohomologyClassToDerived _ K n z).map
              (AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategory).comp
            (ShiftedHom.mk₀ 0 rfl
              ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapDerivedCategoryFactors.hom.app K))
                (zero_add n)) (add_zero n) := by
  change HomPostcomp.cohomologyClassToDerived _ _ n
    (Algebra.Homology.HomComplexPrecomp.CochainComplex.HomComplex.precompClass (HomPullback.originalIntegerSingleInverseImageIso f).inv _ n
      (HomFunctorMap.HomComplex.functorMapClass (AnalyticInverseImage.originalAnalyticSheafInverseImage f) _ K n z)) = _
  rw [HomDerivedPrecomp.cohomologyClassToDerived_precomp, HomFunctorDerived.cohomologyClassToDerived_functorMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual inverse image commutes with the original class-to-hypercohomology map. -/
theorem originalHypercohomologyPullback_homComplexClass (f : X ⟶ Y)
    (K : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) ℤ) (n : ℤ)
    (z : CohomologyClass
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))) K n) :
    HypercohomologyPullback.originalHypercohomologyPullback f K n
        (GlobalNaturality.homComplexClassToHypercohomology Y K n z) =
      GlobalNaturality.homComplexClassToHypercohomology X
        ((AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj K) n
          (HomPullback.originalHomComplexClassInverseImage f K n z) := by
  let F := AnalyticInverseImage.originalAnalyticSheafInverseImage f
  let Φ := AnalyticInverseImage.originalAnalyticInverseImageLocalizer f
  let G := F.mapDerivedCategory
  let : G.CommShift ℤ := inferInstanceAs (F.mapDerivedCategory.CommShift ℤ)
  let e : Φ.functor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ G :=
    F.mapDerivedCategoryFactors.symm
  let : NatTrans.CommShift e.hom ℤ := inferInstanceAs
    (NatTrans.CommShift F.mapDerivedCategoryFactors.inv ℤ)
  let cY := (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle Y).hom
  let cX := (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexIntIsoSingle X).hom
  let eI := AnalyticInverseImage.originalIntegerComplexInverseImageIso f
  let eS := HomPullback.originalIntegerSingleInverseImageIso f
  let T : ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))
      (DerivedCategory.Q.obj K) n →
      ShiftedHom (DerivedCategory.Q.obj (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (Φ.functor.obj K)) n :=
    fun γ => (ShiftedHom.mk₀ 0 rfl
      (DerivedCategory.Q.map eI.inv ≫ e.hom.app (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))).comp
        ((γ.map G).comp (ShiftedHom.mk₀ 0 rfl (e.inv.app K)) (zero_add n)) (add_zero n)
  have hL :
      (SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (HypercohomologyPullback.originalHypercohomologyPullback f K n
          (GlobalNaturality.homComplexClassToHypercohomology Y K n z)) =
      T ((SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms Y) DerivedCategory.Q)
        (GlobalNaturality.homComplexClassToHypercohomology Y K n z)) := by
    let γ := (SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms Y) DerivedCategory.Q)
      (GlobalNaturality.homComplexClassToHypercohomology Y K n z)
    have hi :
        (DerivedCategory.Q : CochainComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) ℤ ⥤
          DerivedCategory (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map (𝟙 (Φ.functor.obj K)) =
        𝟙 (DerivedCategory.Q.obj (Φ.functor.obj K)) := DerivedCategory.Q.map_id _
    have ht : e.inv.app K ≫ DerivedCategory.Q.map (𝟙 (Φ.functor.obj K)) = e.inv.app K :=
      (congrArg (fun q : DerivedCategory.Q.obj (Φ.functor.obj K) ⟶
          DerivedCategory.Q.obj (Φ.functor.obj K) => e.inv.app K ≫ q) hi).trans
        (Category.comp_id _)
    have h₀ := HypercohomologyAdditive.originalHypercohomologyPullback_equiv f K n G e
      (GlobalNaturality.homComplexClassToHypercohomology Y K n z)
    exact h₀.trans (congrArg (fun t : G.obj (DerivedCategory.Q.obj K) ⟶
        DerivedCategory.Q.obj (Φ.functor.obj K) =>
      (ShiftedHom.mk₀ 0 rfl
        (DerivedCategory.Q.map eI.inv ≫ e.hom.app (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))).comp
          ((γ.map G).comp (ShiftedHom.mk₀ 0 rfl t) (zero_add n)) (add_zero n)) ht)
  have h := ShiftedHomSourceNaturality.shiftedHomSourceNaturality G
    (DerivedCategory.Q.map eI.inv ≫ e.hom.app (ComplexPoint.Basic.ComplexSchemePoint.constantIntegerSheafComplexInt Y))
    (DerivedCategory.Q.map cX)
    (DerivedCategory.Q.map eS.inv ≫ e.hom.app
      (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))))
    (e.inv.app K) (DerivedCategory.Q.map cY) (originalIntegerDerivedSource_square f) n
    (HomPostcomp.cohomologyClassToDerived _ K n z)
  have hM : T (DerivedCategory.Q.map cY ≫ HomPostcomp.cohomologyClassToDerived _ K n z) =
      DerivedCategory.Q.map cX ≫ HomPostcomp.cohomologyClassToDerived _ (Φ.functor.obj K) n
        (HomPullback.originalHomComplexClassInverseImage f K n z) := by
    have hD := originalHomComplexClassInverseImage_derived f K n z
    have hm : T (DerivedCategory.Q.map cY ≫ HomPostcomp.cohomologyClassToDerived _ K n z) =
        DerivedCategory.Q.map cX ≫
          (DerivedCategory.Q.map eS.inv ≫
            (ShiftedHom.mk₀ 0 rfl (e.hom.app
              (Cohomology.GlobalSections.TopCat.Sheaf.integerConstantSingleComplex (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))))).comp
                (((HomPostcomp.cohomologyClassToDerived _ K n z).map G).comp
                  (ShiftedHom.mk₀ 0 rfl (e.inv.app K)) (zero_add n)) (add_zero n)) := by
      simpa only [T, ShiftedHom.mk₀_comp, Category.assoc] using h
    exact hm.trans
      (congrArg (fun q => DerivedCategory.Q.map cX ≫ q) hD).symm
  apply (SmallShiftedHom.equiv (ComplexPoint.Basic.ComplexSchemePoint.analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  exact hL.trans
    ((congrArg T (GlobalNaturality.homComplexClassToHypercohomology_equiv Y K n z)).trans
      (hM.trans (GlobalNaturality.homComplexClassToHypercohomology_equiv X _ n _).symm))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.HypercohomologyClassNaturality
