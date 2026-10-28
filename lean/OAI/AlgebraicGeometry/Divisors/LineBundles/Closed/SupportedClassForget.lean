import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass

/-! # Supported Class Forget -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedClassForget.BundleCycles

noncomputable section

/-! Forgetting the support of the canonical class of a finite cycle gives its ordinary canonical graded cycle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

theorem schemeClosedRelativeGenerator_forget (x : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X F d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (2 * p)
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator X F d p hd x) =
    Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (irreducibleSetEquivPoints.symm x.val.val) p
      ((congrArg (fun n => n + p) x.val.property).trans hd) := by
  have h := CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo X F d x) (2 * p)
  rw [AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_id, Category.comp_id] at h
  exact ConcreteCategory.congr_hom h _

theorem schemeClosedRelativeClassMap_forget (c : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X F d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (2 * p)
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X F d p hd c) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hd (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X F d c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]; rfl
  | add c e hc he => simp only [map_add, hc, he]; rfl
  | single x r =>
    have hx : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X F d (Finsupp.single x r) = Finsupp.single x.val r :=
      Finsupp.mapDomain_single
    rw [hx, Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single, Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_single, map_smul]
    exact congrArg (fun b => r • b) (schemeClosedRelativeGenerator_forget X F d p hd x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedClassForget.BundleCycles
