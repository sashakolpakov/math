import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De

/-! # Hypercohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Hypercohomology

noncomputable section

/-! Hypercohomology of the independent holomorphic complex and its actual comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def analyticHolomorphicCohomology (n : ℕ) : ModuleCat.{1} ℂ :=
  ModuleCat.of ℂ
    ((DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (Analytic.De.analyticConstantSheaf X) ⟶
      (DerivedCategory.Q.obj (Int.analyticHolomorphicSheafComplexInt X))⟦(n : ℤ)⟧)

def holomorphicConstantResolutionIso :
    DerivedCategory.Q.obj (Int.analyticHolomorphicSheafComplexInt X) ≅
      (DerivedCategory.singleFunctor (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) 0).obj (Analytic.De.analyticConstantSheaf X) :=
  IntQuasiIso.derivedHolomorphicSmoothIso X ≪≫ (Analytic.De.analyticDeRhamResolutionIso X).symm

def holomorphicConstantCohomologyIso (n : ℕ) :
    analyticHolomorphicCohomology X n ≅ Analytic.De.analyticConstantCohomology X n :=
  (Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).mapIso
      (holomorphicConstantResolutionIso X))).toModuleIso

theorem holomorphicConstantCohomologyIso_apply (n : ℕ) (a : analyticHolomorphicCohomology X n) :
    (holomorphicConstantCohomologyIso X n).hom a =
      a ≫ (shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).map
        (holomorphicConstantResolutionIso X).hom := by
  change (Linear.homCongr ℂ (Iso.refl _)
    ((shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).mapIso
      (holomorphicConstantResolutionIso X))) a = _
  erw [Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]
  rfl

def derivedAlgebraicToHolomorphicForms :
    (Analytic.De.derivedAnalytificationInverseImage X).obj
        (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)) ⟶
      DerivedCategory.Q.obj (Int.analyticHolomorphicSheafComplexInt X) :=
  (Analytic.De.analytificationInverseImage X).mapDerivedCategoryFactors.hom.app (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) ≫
    DerivedCategory.Q.map (Int.algebraicToHolomorphicSheafMapInt X)

theorem derivedAlgebraicToHolomorphicForms_factorization :
    derivedAlgebraicToHolomorphicForms X ≫ (holomorphicConstantResolutionIso X).hom =
      Analytic.De.derivedAlgebraicToAnalyticConstant X := by
  change (_ ≫ DerivedCategory.Q.map (Int.algebraicToHolomorphicSheafMapInt X)) ≫
    ((IntQuasiIso.derivedHolomorphicSmoothIso X).hom ≫ (Analytic.De.analyticDeRhamResolutionIso X).inv) = _
  erw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map (Int.algebraicToHolomorphicSheafMapInt X)),
    IntQuasiIso.derivedHolomorphicSmoothIso_factorization]
  erw [← Category.assoc]
  rfl

def algebraicToHolomorphicCohomologyMap (n : ℕ) :
    Algebraic.Sheaves.algebraicDeRham X n ⟶ analyticHolomorphicCohomology X n :=
  ModuleCat.ofHom
    { toFun := fun a =>
        (Analytic.De.derivedAnalytificationConstantIso X).inv ≫
          (Analytic.De.derivedAnalytificationInverseImage X).map a ≫
          ((Analytic.De.derivedAnalytificationInverseImage X).commShiftIso (n : ℤ)).hom.app
            (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)) ≫
          (shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).map
            (derivedAlgebraicToHolomorphicForms X)
      map_add' := by
        intro a b
        simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro c a
        simp only [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply] }

theorem algebraicToHolomorphicCohomologyMap_factorization (n : ℕ) :
    algebraicToHolomorphicCohomologyMap X n ≫ (holomorphicConstantCohomologyIso X n).hom =
      Analytic.De.algebraicToAnalyticCohomologyMap X n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (holomorphicConstantCohomologyIso X n).hom
    (algebraicToHolomorphicCohomologyMap X n a) = _
  rw [holomorphicConstantCohomologyIso_apply]
  change (_ ≫ _ ≫ _ ≫ (shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).map
      (derivedAlgebraicToHolomorphicForms X)) ≫
      (shiftFunctor (DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X)) (n : ℤ)).map
        (holomorphicConstantResolutionIso X).hom = _
  simp only [Category.assoc, ← Functor.map_comp, derivedAlgebraicToHolomorphicForms_factorization]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Hypercohomology
