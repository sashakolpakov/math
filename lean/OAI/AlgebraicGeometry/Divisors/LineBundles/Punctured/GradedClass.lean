import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.SupportedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.Point
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedClassZero

/-! # Graded Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.GradedClass.BundleCycles

noncomputable section

/-! The canonical class of every finite punctured specialization input is the actual Betti pullback of the original finite cycle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.left.IdealSheafData)
  [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral (ProductCharts.BundleCycles.puncturedDeformationOver X I).left] [Smooth (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom]
  [AlgebraicGeometry.IsNoetherian (ProductCharts.BundleCycles.puncturedDeformationOver X I).left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProductCharts.BundleCycles.puncturedDeformationOver X I))]
  (d p : ℕ) (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (he : (d + 1) + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom)

theorem puncturedInputPoint_absoluteClass (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (ProductCharts.BundleCycles.puncturedProjectionOver X I)
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (irreducibleSetEquivPoints.symm x.val) p
        ((congrArg (fun n => n + p) x.property).trans hd)) =
    Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass (ProductCharts.BundleCycles.puncturedDeformationOver X I)
      (irreducibleSetEquivPoints.symm (Point.BundleCycles.puncturedInputPoint X I d x).val) p
      ((congrArg (fun n => n + p) (Point.BundleCycles.puncturedInputPoint X I d x).property).trans he) := by
  have hs := Point.BundleCycles.puncturedInputPoint_support X I d x
  have hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (SupportExtension.BundleCycles.puncturedExtendedSupport I (irreducibleSetEquivPoints.symm x.val))
      (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (ProductCharts.BundleCycles.puncturedDeformationOver X I).hom := by
    rw [hs]
    exact (congrArg (fun n => n + p) (Point.BundleCycles.puncturedInputPoint X I d x).property).trans he
  exact (SupportedClass.BundleCycles.schemeAbsoluteCycleClass_puncturedProjection X I (irreducibleSetEquivPoints.symm x.val) p
    ((congrArg (fun n => n + p) x.property).trans hd) hc).trans
      (Finite.GradedClassZero.BundleCycles.schemeAbsoluteCycleClass_congrSupport (X := ProductCharts.BundleCycles.puncturedDeformationOver X I) _ _ hs p _ _)

theorem schemeGradedAbsoluteClass_puncturedInput
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (ProductCharts.BundleCycles.puncturedProjectionOver X I)
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hd c) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (ProductCharts.BundleCycles.puncturedDeformationOver X I) (d + 1) p he
      (Global.SpecializationComparison.BundleCycles.puncturedSpecializationCycleInput I X.hom d c) := by
  classical
  let K : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (2 * p) →ₗ[ℚ]
      Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) (ProductCharts.BundleCycles.puncturedDeformationOver X I) (2 * p) :=
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) (ProductCharts.BundleCycles.puncturedProjectionOver X I)).hom
  change K (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hd c) = _
  induction c using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    exact (map_zero (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (ProductCharts.BundleCycles.puncturedDeformationOver X I) (d + 1) p he)).symm
  | add c e hc hce =>
    simp only [map_add, hc, hce]
    exact (map_add (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass (ProductCharts.BundleCycles.puncturedDeformationOver X I) (d + 1) p he) _ _).symm
  | single x r =>
    rw [Point.BundleCycles.puncturedSpecializationCycleInput_single, Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single,
      Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single, map_smul]
    exact congrArg (fun b => r • b) (puncturedInputPoint_absoluteClass X I d p hd he x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.GradedClass.BundleCycles
