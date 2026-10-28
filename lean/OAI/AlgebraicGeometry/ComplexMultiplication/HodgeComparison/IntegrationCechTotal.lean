import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalConstantIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCechAugmentation

/-! # Integration Cech Total -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction

noncomputable section

/-! Integration on the actual Čech total complexes, with its literal
global augmentation and rational constant-section formulas. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {I : Type} (U : I → Opens M)

def manifoldIntegrationCechTotalMap :
    Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) U ⟶ AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.manifoldSmoothCechTotal E M U (ModuleCat.of ℂ ℂ) :=
  AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalMap U (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M)

theorem manifoldIntegrationCechTotalMap_iota (p q n : ℕ) (h : p + q = n)
    (c : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) U q p) :
    (manifoldIntegrationCechTotalMap E M U).f n (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U p q n h c) =
      AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)) p q n h
        (AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f q) p c) :=
  ConcreteCategory.congr_hom
    (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion_map U (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M) p q n h) c

theorem manifoldIntegrationCechCoefficients_global (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f n) 0
      (Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation U n form) =
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechColumnAugmentation E M U (ModuleCat.of ℂ ℂ)).f n
      ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).f n form) := by
  funext a
  have hmap := congrArg (fun f : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M ⟶
    AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) => f.f n)
      (AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration_onOpen E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))
  have hI := ConcreteCategory.congr_hom hmap
    (show (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).X n from form)
  have hC := AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechColumnAugmentation_apply E M U (ModuleCat.of ℂ ℂ)
    n ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).f n form) a
  exact hI.trans hC.symm

theorem manifoldIntegrationCechTotalMap_global_apply (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    (manifoldIntegrationCechTotalMap E M U).f n
      ((Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) U).f n form) =
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E M U (ModuleCat.of ℂ ℂ)).f n
      ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).f n form) := by
  have hI := manifoldIntegrationCechTotalMap_iota E M U 0 n n (Nat.zero_add n)
    (Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation U n form)
  have hC := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation_f E M U (ModuleCat.of ℂ ℂ) n)
      ((AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M).f n form)
  exact hI.trans ((congrArg
    (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ))
      0 n n (Nat.zero_add n)) (manifoldIntegrationCechCoefficients_global E M U n form)).trans hC.symm)

theorem manifoldIntegrationCechTotalMap_global :
    Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) U ≫ manifoldIntegrationCechTotalMap E M U =
      AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M ≫
        AlgebraicTopology.Cohomology.Singular.SmoothCechDoubleComplex.globalManifoldSmoothCechAugmentation E M U (ModuleCat.of ℂ ℂ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact manifoldIntegrationCechTotalMap_global_apply E M U n form

theorem manifoldIntegrationCechCoefficients_rational (n : ℕ)
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain
      (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf (TopCat.of M)) U n) :
    AlgebraicTopology.DeRham.Comparison.SmoothCechDoubleComplex.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M).f 0) n
      (ProjectivePhaseDefect.CM.Construction.rationalCechManifoldForm (E := E) U n c) =
    RationalSmoothCech.CM.Construction.rationalSmoothCechCoefficients E M U n 0
      (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation (TopCat.of M) U n c) := by
  funext a
  exact RationalConstantIntegration.CM.Construction.rationalLocallyConstantManifoldForm_integration E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (c a)

theorem manifoldIntegrationCechTotalMap_rational (n : ℕ)
    (c : DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain
      (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantPresheaf (TopCat.of M)) U n) :
    (manifoldIntegrationCechTotalMap E M U).f n
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion U n 0 n (Nat.add_zero n)
        (ProjectivePhaseDefect.CM.Construction.rationalCechManifoldForm (E := E) U n c)) =
    (RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap E M U).f n
      ((DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechToTotal (TopCat.of M) U).f n c) := by
  have hI := manifoldIntegrationCechTotalMap_iota E M U n 0 n (Nat.add_zero n)
    (ProjectivePhaseDefect.CM.Construction.rationalCechManifoldForm (E := E) U n c)
  have hR := RationalSmoothCechAugmentation.CM.Construction.rationalSmoothCechTotalMap_iota E M U n 0 n (Nat.add_zero n)
    (DivisorClass.Chern.Cech.Obj.RationalCech.locallyConstantCechEvaluation (TopCat.of M) U n c)
  exact hI.trans ((congrArg
    (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalInclusion U (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ))
      n 0 n (Nat.add_zero n)) (manifoldIntegrationCechCoefficients_rational E M U n c)).trans hR.symm)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegrationCechTotal.CM.Construction
