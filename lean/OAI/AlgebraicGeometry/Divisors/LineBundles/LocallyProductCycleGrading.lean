import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductSupportedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Locally Product Cycle Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductCycleGrading.BundleCycles

noncomputable section

/-! Actual integral-fiber extension preserves codimension on open product charts, and therefore occupies the exact complementary target dimension grade. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
  [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
  [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (f : E ⟶ X) [Smooth f.left] [GeometricallyIntegral f.left]
  (charts : ∀ z : E.left, Open.ProductChart.BundleCycles.SchemeOpenProductChart f z) (d e p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (he : e + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom)

def locallyProductGradedPoint (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint E.hom e :=
  ⟨Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint f.left x.val, by
    let B := irreducibleSetEquivPoints.symm x.val
    have hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom :=
      (congrArg (fun n => n + p) x.property).trans hd
    have h := LocallyProductSupportedClass.BundleCycles.locallyProductSupport_codimension f charts B (Integral.PulledSupport.BundleCycles.integralPulledSupport f.left B)
      (Integral.PulledSupport.BundleCycles.integralPulledSupport_coe f.left B) p hp
    have hs := Integral.PulledSupport.BundleCycles.integralPulledSupport_eq_pointClosure f.left B
    simp only [B, OrderIso.apply_symm_apply] at hs
    rw [hs] at h
    omega⟩

def locallyProductGradedExtension :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint E.hom e →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (locallyProductGradedPoint f charts d e p hd he)

omit [Smooth E.hom] [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem locallyProductGradedExtension_single (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) (r : ℚ) :
    locallyProductGradedExtension f charts d e p hd he (Finsupp.single x r) =
      Finsupp.single (locallyProductGradedPoint f charts d e p hd he x) r := Finsupp.mapDomain_single

omit [Smooth E.hom] [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem locallyProductGradedPoint_support (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d) :
    Integral.PulledSupport.BundleCycles.integralPulledSupport f.left (irreducibleSetEquivPoints.symm x.val) =
      irreducibleSetEquivPoints.symm (locallyProductGradedPoint f charts d e p hd he x).val := by
  change Integral.PulledSupport.BundleCycles.integralPulledSupport f.left (irreducibleSetEquivPoints.symm x.val) =
    irreducibleSetEquivPoints.symm (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint f.left x.val)
  simpa only [OrderIso.apply_symm_apply] using
    Integral.PulledSupport.BundleCycles.integralPulledSupport_eq_pointClosure f.left (irreducibleSetEquivPoints.symm x.val)

omit [Smooth E.hom] [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem locallyProductGradedExtension_forget (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion E.hom e (locallyProductGradedExtension f charts d e p hd he c) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension f.left (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.hom d c) := by
  change Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding E.hom e)
    (Finsupp.mapDomain (locallyProductGradedPoint f charts d e p hd he) c) =
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint f.left)
        (Finsupp.mapDomain (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding X.hom d) c)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

omit [Smooth E.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem locallyProductGradedExtension_pointChow (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ E.hom e (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension f.left (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion X.hom d c)) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ E.hom e (locallyProductGradedExtension f charts d e p hd he c) := by
  rw [← locallyProductGradedExtension_forget f charts d e p hd he]
  exact Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion E.hom e _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductCycleGrading.BundleCycles
