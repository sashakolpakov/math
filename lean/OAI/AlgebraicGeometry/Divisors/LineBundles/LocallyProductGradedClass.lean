import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductCycleGrading
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductAbsoluteClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.PrincipalCycleClassZero

/-! # Locally Product Graded Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductGradedClass.BundleCycles

noncomputable section

/-! Canonical classes of full finite integral-fiber extensions equal genuine Betti pullbacks for morphisms with constructed open product charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
  [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
  [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (f : E ⟶ X) [Smooth f.left] [GeometricallyIntegral f.left]
  (charts : ∀ z : E.left, Open.ProductChart.BundleCycles.SchemeOpenProductChart f z) (d e p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (he : e + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom)

theorem locallyProductGradedPoint_class (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass X (irreducibleSetEquivPoints.symm x.val) p ((congrArg (fun n => n + p) x.property).trans hd)) =
    Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass E (irreducibleSetEquivPoints.symm (LocallyProductCycleGrading.BundleCycles.locallyProductGradedPoint f charts d e p hd he x).val) p
      ((congrArg (fun n => n + p) (LocallyProductCycleGrading.BundleCycles.locallyProductGradedPoint f charts d e p hd he x).property).trans he) := by
  let B := irreducibleSetEquivPoints.symm x.val
  let C := Integral.PulledSupport.BundleCycles.integralPulledSupport f.left B
  have hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom :=
    (congrArg (fun n => n + p) x.property).trans hd
  have hc := LocallyProductSupportedClass.BundleCycles.locallyProductSupport_codimension f charts B C (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe f.left B) p hp
  exact (LocallyProductAbsoluteClass.BundleCycles.schemeCycleClass_locally_product f charts B C (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe f.left B) p hp hc).trans
    (Scheme.GradedAbsoluteClass.BundleCycles.schemeCycleClass_congrSupport E _ _ (LocallyProductCycleGrading.BundleCycles.locallyProductGradedPoint_support f charts d e p hd he x) p _ _)

theorem locallyProductGradedExtension_class (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass E e p he (LocallyProductCycleGrading.BundleCycles.locallyProductGradedExtension f charts d e p hd he c) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hd c) := by
  classical
  let K : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (p + p) →ₗ[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) E (p + p) :=
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f).hom
  change _ = K (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hd c)
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c b hc hb => simp only [map_add, hc, hb]
  | single x r =>
    rw [LocallyProductCycleGrading.BundleCycles.locallyProductGradedExtension_single, Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass_single,
      Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass_single, map_smul]
    exact congrArg (fun b => r • b) (locallyProductGradedPoint_class f charts d e p hd he x).symm

include charts in
theorem locallyProductFiberPointChow_class [IsSeparated E.hom]
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    Scheme.PrincipalCycleClassZero.BundleCycles.schemeDimensionChowCycleClass E e p he
      (Point.CycleChow.BundleCycles.pointCycleToChowQ E.hom e (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension f.left (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.hom d c))) =
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hd c) := by
  rw [LocallyProductCycleGrading.BundleCycles.locallyProductGradedExtension_pointChow f charts d e p hd he]
  exact locallyProductGradedExtension_class f charts d e p hd he c

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductGradedClass.BundleCycles
