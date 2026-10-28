import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothGlobalSheafification
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.Gamma

/-! # Betti Sheaf Maps -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.BettiSheafMaps

noncomputable section

/-! Actual Betti-to-sheaf maps expressed through original global cochain maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) [MetrizableSpace X] [StronglyLocallyContractibleSpace X] [LocallyPathConnectedSpace X]

theorem rationalBettiCechSheafIso_hom_sections (n : ℕ) :
    (Rational.BettiCechSheafComparison.rationalBettiCechSheafIso X n).hom =
      (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) (n + 1)).inv ≫
        HomologicalComplex.homologyMap (ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℚ X (ModuleCat.of ℚ ℚ)) (n + 1) ≫
          AugmentationNaturality.nativeSectionCohomologyMapOfZero (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
            (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X) (Rational.BettiSheafComparison.rationalConstantAbelianZeroIso X) n := by
  have hc : HomologicalComplex.homologyMap (ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℚ X (ModuleCat.of ℚ ℚ)) (n + 1) ≫
      SectionCohomologyMap.nativeSectionCohomologyMap (Rational.BettiSheafComparison.rationalAbelianSingularResolution X) (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X) n =
    HomologicalComplex.homologyMap (Singular.GammaAugmentation.rationalSingularToGamma X) (n + 1) ≫
      (GammaSectionsComparison.nativeFlasqueCohomologyIso (Rational.BettiSheafComparison.rationalAbelianSingularResolution X)
        (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X) (Rational.BettiSheafComparison.rationalAbelianSingularResolution_exact X) n).hom := by
    rw [SectionNaturality.nativeSectionCohomologyMap_eq_flasque _ (Rational.BettiSheafComparison.rationalAbelianSingularResolution_flasque X),
      ← Category.assoc, ← HomologicalComplex.homologyMap_comp,
      ← ModuleGlobalSectionsForget.rationalSingularToGamma_eq_sections, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Singular.Gamma.rationalBettiCechSheafIso_hom]
  unfold AugmentationNaturality.nativeSectionCohomologyMapOfZero GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Category.assoc (HomologicalComplex.homologyMap (ModuleGlobalSectionsForget.moduleSingularToAbelianSections ℚ X (ModuleCat.of ℚ ℚ)) (n + 1)), hc]
  rw [Category.assoc]

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def nativeSmoothCohomologyToSheaf (n : ℕ) :
    Complex.SheafForget.complexModuleForget.obj ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).homology (n + 1)) ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of M)) (n + 1)).obj
        (Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf (TopCat.of M)) :=
  (ModuleGlobalSectionsForget.complexForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1)).inv ≫
    HomologicalComplex.homologyMap (SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M) (n + 1) ≫
      AugmentationNaturality.nativeSectionCohomologyMapOfZero (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)
        (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M) n

def nativeComplexBettiToSheaf (n : ℕ) :
    Complex.SheafForget.complexModuleForget.obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) (n + 1)) ⟶
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of M)) (n + 1)).obj
        (Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf (TopCat.of M)) :=
  Complex.SheafForget.complexModuleForget.map (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) (n + 1)) ≫
    nativeSmoothCohomologyToSheaf E M n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.BettiSheafMaps
