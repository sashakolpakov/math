import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationDerivedNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.IntegratedSingularExt

/-! # Integrated Singular Derived Class -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegratedSingularDerivedClass.Integration

noncomputable section

/-! Matching the actual integration image identifies a singular class
with the original derived class of a closed smooth form. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [StronglyLocallyContractibleSpace M] [MetrizableSpace M]

local instance integratedDerivedHasDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) :=
  HasDerivedCategory.standard _
local instance integratedDerivedHasExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) :=
  hasExt_of_hasDerivedCategory _

theorem integratedSingular_derivedClass (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) (TopCat.of M) n)
    (hb : HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) n b =
      HomologicalComplex.homologyMap (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) n
        (CochainClasses.Homology.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n a (IntegrationCocycleNormalization.smoothFormCochain_closed E M n a ha))) :
    (SingularExtNaturality.singularLocallyConstantExtEquiv (TopCat.of M) n b).hom =
      Filtered.DerivedInclusion.Hodge.smoothGlobalDerivedClass E M n a ha ≫ (IntegrationDerivedNormalization.smoothLocallyConstantResolutionIso E M).inv⟦(n : ℤ)⟧' := by
  have h := IntegratedSingularExt.Integration.integratedSingular_ext E M n
    (CochainClasses.Homology.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n a (IntegrationCocycleNormalization.smoothFormCochain_closed E M n a ha)) b hb
  have hh := congrArg (fun q : CategoryTheory.Abelian.Ext.{1}
      (C := ConstantSheafSections.ComplexSheaves (TopCat.of M)) (ConstantSheafSections.standardConstantSheaf (TopCat.of M))
      (InjectiveExtPullback.locallyConstantCoefficients (TopCat.of M)) n => q.hom) h
  exact hh.trans (IntegrationDerivedNormalization.smoothForm_injectiveExt_derivedClass E M n a ha)

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegratedSingularDerivedClass.Integration
