import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationDerivedNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.IntegratedSingularDerivedClass
import OAI.AlgebraicGeometry.Comparison.Betti.CochainClassNormalization
import OAI.AlgebraicGeometry.Betti.ProjectiveComponentClassMeaning
import OAI.AlgebraicTopology.DeRham.Comparison.Projective

/-! # Integration Derived Class -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntegrationDerivedClass

noncomputable section

/-! The original projective integration-normalized Betti class has exactly
the derived class of the same closed smooth form. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem manifoldFormClass_eq_derivedCochainClass (n : ℕ) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M n a =
      CochainClasses.Homology.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n a.val
        (IntegrationCocycleNormalization.smoothFormCochain_closed E M n a.val a.property) := by
  rw [Betti.ProjectiveComponentClassMeaning.manifoldDeRhamFormClass_eq_cochainClass]
  exact (CochainClassNormalization.Homology.cochainClass_eq_native (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n
    (Betti.ProjectiveComponentClassMeaning.manifoldClosedFormCocycle E M n a)).symm

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance projectiveIntegrationLocallyContractible : StronglyLocallyContractibleSpace V.analyticSpace :=
  AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel V.analyticSpace

local instance projectivePointIntegrationLocallyContractible :
    StronglyLocallyContractibleSpace (Betti.Scheme.schemePointSpace V.toOver) :=
  inferInstanceAs (StronglyLocallyContractibleSpace V.analyticSpace)

local instance projectivePointIntegrationMetrizable : MetrizableSpace (Betti.Scheme.schemePointSpace V.toOver) :=
  inferInstanceAs (MetrizableSpace V.analyticSpace)

local instance projectiveIntegrationHasDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (Betti.Scheme.schemePointSpace V.toOver)) :=
  HasDerivedCategory.standard _
local instance projectiveIntegrationHasExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves (Betti.Scheme.schemePointSpace V.toOver)) :=
  hasExt_of_hasDerivedCategory _

local instance projectiveTopIntegrationHasDerived : HasDerivedCategory.{1}
    (ConstantSheafSections.ComplexSheaves (TopCat.of V.analyticSpace)) := HasDerivedCategory.standard _
local instance projectiveTopIntegrationHasExt : HasExt.{1}
    (ConstantSheafSections.ComplexSheaves (TopCat.of V.analyticSpace)) := hasExt_of_hasDerivedCategory _

theorem projective_integration_derivedClass (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n) :
    (SingularExtNaturality.singularLocallyConstantExtEquiv (TopCat.of V.analyticSpace) n
      ((V.deRhamBettiIso n).hom (V.deRhamClass n a))).hom =
      Filtered.DerivedInclusion.Hodge.smoothGlobalDerivedClass V.analyticModel V.analyticSpace n a.val a.property ≫
        (IntegrationDerivedNormalization.smoothLocallyConstantResolutionIso V.analyticModel V.analyticSpace).inv⟦(n : ℤ)⟧' := by
  let c := CochainClasses.Homology.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex V.analyticModel V.analyticSpace) n
    a.val (IntegrationCocycleNormalization.smoothFormCochain_closed V.analyticModel V.analyticSpace n a.val a.property)
  have hc : V.deRhamClass n a = c :=
    manifoldFormClass_eq_derivedCochainClass V.analyticModel V.analyticSpace n a
  have hb := (ConcreteCategory.congr_hom (V.deRhamBettiIso_hom_comp n) (V.deRhamClass n a)).trans
    (congrArg (HomologicalComplex.homologyMap
      (AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap V.analyticModel V.analyticSpace) n) hc)
  exact IntegratedSingularDerivedClass.Integration.integratedSingular_derivedClass V.analyticModel V.analyticSpace n a.val a.property
    ((V.deRhamBettiIso n).hom (V.deRhamClass n a)) hb

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntegrationDerivedClass
