import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.BettiSheafMaps
import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalCoefficientSheafification

/-! # Betti Complex Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiComplexSheaf

noncomputable section

/-! The original rational Betti-to-sheaf map commutes with the original complex coefficient inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem complexForgetHomologyIso_inv_naturality
    {K L : CochainComplex (ModuleCat.{0} ℂ) ℕ} (f : K ⟶ L) (n : ℕ) :
    Complex.SheafForget.complexModuleForget.map (HomologicalComplex.homologyMap f n) ≫ (ModuleGlobalSectionsForget.complexForgetHomologyIso L n).inv =
      (ModuleGlobalSectionsForget.complexForgetHomologyIso K n).inv ≫
        HomologicalComplex.homologyMap ((Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).map f) n := by
  apply (ModuleGlobalSectionsForget.complexForgetHomologyIso K n).eq_inv_comp.mpr
  rw [← Category.assoc, ← ModuleGlobalSectionsForget.complexForgetHomologyIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem rationalToComplexAbelianCochainMap_homology_inv (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n) ≫
        (ModuleGlobalSectionsForget.complexForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) X) n).inv =
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n).inv ≫
        HomologicalComplex.homologyMap (ComplexPresheaf.rationalToComplexAbelianCochainMap X) n := by
  apply (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) n).eq_inv_comp.mpr
  rw [← Category.assoc, ← GlobalCoefficientSheafification.rationalToComplexAbelianCochainMap_homology, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem rationalSmoothGlobalSheafification :
    ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℚ (TopCat.of M) (ModuleCat.of ℚ ℚ) ≫
      ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSections (TopCat.of M)).mapHomologicalComplex (.up ℕ)).map (SmoothSheafComparison.rationalManifoldSmoothSheafMap E M) =
    ComplexPresheaf.rationalToComplexAbelianCochainMap (TopCat.of M) ≫
      (Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).map (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) ≫
      SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M := by
  rw [SmoothSheafComparison.rationalManifoldSmoothSheafMap, Functor.map_comp, ← Category.assoc,
    GlobalCoefficientSheafification.moduleSingularToAbelianSections_rationalComplex, Category.assoc, SmoothGlobalSheafification.manifoldSmoothToAbelianSections_restriction]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem nativeComplexBettiToSheaf_sections (n : ℕ) :
    Intrinsic.BettiSheafMaps.nativeComplexBettiToSheaf E M n =
      (ModuleGlobalSectionsForget.complexForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of M)) (n + 1)).inv ≫
        HomologicalComplex.homologyMap
          ((Complex.SheafForget.complexModuleForget.mapHomologicalComplex (.up ℕ)).map
            (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) ≫ SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M) (n + 1) ≫
          Intrinsic.AugmentationNaturality.nativeSectionCohomologyMapOfZero (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)
            (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M) n := by
  unfold Intrinsic.BettiSheafMaps.nativeComplexBettiToSheaf Intrinsic.BettiSheafMaps.nativeSmoothCohomologyToSheaf
  rw [← Category.assoc, complexForgetHomologyIso_inv_naturality]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc]

variable [MetrizableSpace M] [StronglyLocallyContractibleSpace M] [LocallyPathConnectedSpace M]

theorem rationalBettiCechSheafIso_complex (n : ℕ) :
    AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.map (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (TopCat.of M) (n + 1)) ≫ Intrinsic.BettiSheafMaps.nativeComplexBettiToSheaf E M n =
      (BettiCechSheafComparison.rationalBettiCechSheafIso (TopCat.of M) n).hom ≫
        (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of M)) (n + 1)).map
          (ComplexPeriod.rationalConstantComplexSheafMap (TopCat.of M)) := by
  rw [nativeComplexBettiToSheaf_sections, ← Category.assoc, rationalToComplexAbelianCochainMap_homology_inv]
  rw [Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (ComplexPresheaf.rationalToComplexAbelianCochainMap (TopCat.of M)) (n + 1)),
    ← HomologicalComplex.homologyMap_comp, ← rationalSmoothGlobalSheafification,
    HomologicalComplex.homologyMap_comp]
  simp only [Category.assoc]
  rw [SmoothSheafComparison.rationalManifoldSmoothSheafMap_native, Intrinsic.BettiSheafMaps.rationalBettiCechSheafIso_hom_sections]
  simp only [Category.assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiComplexSheaf
