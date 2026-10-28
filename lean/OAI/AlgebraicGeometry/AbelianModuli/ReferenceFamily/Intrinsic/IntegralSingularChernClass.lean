import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralSheafChernClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.SheafSingularImage
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalIntegerBettiComparison

/-! # Integral Singular Chern Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralSingularChernClass

noncomputable section

/-! The original algebraic first Chern class is the rationalization of
an actual integral singular class, with its normalization unchanged. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem originalIntegralRationalConstantMap_inv (Y : TopCat.{0}) :
    (IntegralSheafCoefficients.originalIntegralConstantIso Y).inv ≫
      LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient Y =
    DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalConstantSheaf Y ≫ (IntegralSheafCoefficients.originalRationalConstantIso Y).inv := by
  calc
    _ = (IntegralSheafCoefficients.originalIntegralConstantIso Y).inv ≫
        (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient Y ≫
          (IntegralSheafCoefficients.originalRationalConstantIso Y).hom) ≫ (IntegralSheafCoefficients.originalRationalConstantIso Y).inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := by
      rw [IntegralSheafCoefficients.originalIntegralRationalConstantMap]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier)
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]
  [StronglyLocallyContractibleSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]
  [LocallyPathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]

theorem exists_nativeIntegralSingularChernClass :
    ∃ c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℤ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2,
      AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.integralRationalCoefficient (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2 c =
        (ModuleForgetCocycleClasses.rationalIntegerCohomologyIso (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2).hom
          (ChernClasses.lineBundleChernClass X L) := by
  let Y := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let H := Sheaf.functorH (Opens.grothendieckTopology Y) 2
  let Q : AddCommGrpCat.{0} := AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.obj
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y 2)
  let Z : AddCommGrpCat.{0} := IntegerSingularSheafComparison.integerModuleForget.obj
    (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℚ) Y 2)
  let I : AddCommGrpCat.{0} := H.obj (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf Y)
  let R : AddCommGrpCat.{0} := H.obj (DivisorClass.Chern.Rational.HolomorphicPeriod.rationalConstantAbelianSheaf Y)
  let IZ : AddCommGrpCat.{0} := H.obj (IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf (ModuleCat.of ℤ ℤ) Y)
  let RZ : AddCommGrpCat.{0} := H.obj (IntegerSingularSheafComparison.integerLocallyConstantAbelianSheaf (ModuleCat.of ℤ ℚ) Y)
  let i : I ⟶ IZ := H.map (IntegralSheafCoefficients.originalIntegralConstantIso Y).inv
  let a : IZ ⟶ RZ := H.map (LocallyConstantCoefficientExact.integerLocallyConstantSheafMap TorusIntegralInjection.integralRationalCoefficient Y)
  let r : I ⟶ R := H.map (DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalConstantSheaf Y)
  let e : R ⟶ RZ := H.map (IntegralSheafCoefficients.originalRationalConstantIso Y).inv
  let q : Q ⟶ R := (DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafIso Y 1).hom
  let j : Z ⟶ RZ := IntegerSingularSheafComparison.integerSingularBettiSheafMap (ModuleCat.of ℤ ℚ) Y 1
  let f : Q ⟶ Z := (ModuleForgetCocycleClasses.rationalIntegerCohomologyIso Y 2).hom
  let c : Q := ChernClasses.lineBundleChernClass X L
  let s : I := IntegralSheafChernClass.nativeIntegralSheafChernClass X L
  have hnat : f ≫ j = q ≫ e := RationalIntegerBettiComparison.rationalIntegerCohomologyIso_betti Y 1
  have hn : j (f c) = e (q c) :=
    congrArg (fun h : Q ⟶ RZ => h c) hnat
  have hc : r s = q c := IntegralSheafChernClass.nativeIntegralSheafChernClass_rationalize X L
  have hs : i ≫ a = r ≫ e := (H.map_comp _ _).symm.trans
    ((congrArg H.map (originalIntegralRationalConstantMap_inv Y)).trans (H.map_comp _ _))
  have he : a (i s) = e (r s) := ConcreteCategory.congr_hom hs s
  have hb : j (f c) = a (i s) := hn.trans ((congrArg e hc.symm).trans he.symm)
  exact Integral.SheafSingularImage.singularIntegral_lift_of_sheafIntegral Y 1 (f c) (i s) hb

def nativeIntegralSingularChernClass :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℤ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2 :=
  (exists_nativeIntegralSingularChernClass X L).choose

theorem nativeIntegralSingularChernClass_rationalize :
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.integralRationalCoefficient (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2
        (nativeIntegralSingularChernClass X L) =
      (ModuleForgetCocycleClasses.rationalIntegerCohomologyIso (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2).hom
        (ChernClasses.lineBundleChernClass X L) :=
  (exists_nativeIntegralSingularChernClass X L).choose_spec

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralSingularChernClass
