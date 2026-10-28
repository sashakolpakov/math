import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationInjectiveSections
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedInclusion
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveExtPullback

/-! # Integration Cocycle Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.IntegrationCocycleNormalization

noncomputable section

/-! Actual global integration gives the original closed-form cocycle in
the Hom complex of the fixed injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Filtered.DerivedInclusion.Hodge

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

local instance : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := HasDerivedCategory.standard _
local instance : HasExt.{1} (ConstantSheafSections.ComplexSheaves (TopCat.of M)) := hasExt_of_hasDerivedCategory _

def smoothFormsToInjectiveHom : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M ⟶
    InjectiveHomPullback.injectiveHomSectionsComplex (TopCat.of M) :=
  IntegrationInjectiveSections.smoothFormsToInjectiveSections E M ≫ (InjectiveHomPullback.injectiveHomSectionsIso (TopCat.of M)).inv

theorem smoothFormsToInjectiveHom_f (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    (smoothFormsToInjectiveHom E M).f n a =
      Filtered.DerivedInclusion.Hodge.smoothGlobalCocycle E M n a ≫
        (IntegrationSheafMap.integrationSheafMap E M ≫ Smooth.SingularInjective.Integration.smoothSingularToInjective E M).f n := by
  have h := ConstantSheafSections.constantHomSectionsLinearEquiv_symm_naturality
    (show (Filtered.DerivedInclusion.Hodge.smoothSheafTerm E M n).obj.obj (op ⊤) from Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ a)
    ((IntegrationSheafMap.integrationSheafMap E M ≫ Smooth.SingularInjective.Integration.smoothSingularToInjective E M).f n)
  exact h.symm

theorem smoothFormCochain_closed (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) : (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).d n (n + 1) a = 0 := by
  rw [Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex_d]
  exact ha

theorem smoothFormInjectiveCocycle_closed (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    (InjectiveHomPullback.injectiveHomSectionsComplex (TopCat.of M)).d n (n + 1)
      (Filtered.DerivedInclusion.Hodge.smoothGlobalCocycle E M n a ≫ (IntegrationSheafMap.integrationSheafMap E M ≫ Smooth.SingularInjective.Integration.smoothSingularToInjective E M).f n) = 0 := by
  have h := CochainClasses.Homology.cochain_map_closed (smoothFormsToInjectiveHom E M) n a
    (smoothFormCochain_closed E M n a ha)
  simp only [smoothFormsToInjectiveHom_f] at h
  convert h using 1
  rfl

theorem smoothForm_injectiveExt_class (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    InjectiveExtPullback.injectiveHomologyExtEquiv (TopCat.of M) n
      (HomologicalComplex.homologyMap (smoothFormsToInjectiveHom E M) n
        (CochainClasses.Homology.cochainClass (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) n a (smoothFormCochain_closed E M n a ha))) =
      InjectiveResolution.extMk.{1} (C := ConstantSheafSections.ComplexSheaves (TopCat.of M))
        (InjectiveExtPullback.complexInjectiveResolution (TopCat.of M))
        (Filtered.DerivedInclusion.Hodge.smoothGlobalCocycle E M n a ≫ (IntegrationSheafMap.integrationSheafMap E M ≫ Smooth.SingularInjective.Integration.smoothSingularToInjective E M).f n)
          (n + 1) rfl (smoothFormInjectiveCocycle_closed E M n a ha) := by
  erw [CochainClasses.Homology.cochainClass_naturality, InjectiveExtPullback.injectiveHomologyExtEquiv_class]
  simp only [smoothFormsToInjectiveHom_f]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.IntegrationCocycleNormalization
