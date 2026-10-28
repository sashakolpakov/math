import OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductSupportedClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteProjection

/-! # Locally Product Absolute Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductAbsoluteClass.BundleCycles

noncomputable section

/-! The canonical ordinary class commutes with morphisms having actual open product charts, after forgetting supports. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {E X : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral E.left] [Smooth E.hom]
  [AlgebraicGeometry.IsNoetherian E.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E)]
  [IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  (f : E ⟶ X) (charts : ∀ z : E.left, Open.ProductChart.BundleCycles.SchemeOpenProductChart f z)
  (B : IrreducibleCloseds X.left) (C : IrreducibleCloseds E.left)
  (hC : (C : Set E.left) = f.left ⁻¹' (B : Set X.left)) (p : ℕ)
  (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C E.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension E.hom)

include charts hC in
theorem schemeAbsoluteCycleClass_locally_product :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) f (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X B p hp) =
      Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass E C p hc := by
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo f B C hC) (2 * p)) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X B p hp)
  exact h.symm.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints E))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion E C))ᶜ (2 * p))
    (LocallyProductSupportedClass.BundleCycles.schemeSupportedCycleClass_locally_product f charts B C hC p hp hc))

include charts hC in
theorem schemeCycleClass_locally_product :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass X B p hp) =
      Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass E C p hc := by
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f
    (cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X n : Type)) (two_mul p))
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X B p hp)) = _
  rw [Scheme.AbsoluteProjection.BundleCycles.schemeBettiMap_cast (ModuleCat.of ℚ ℚ) f (two_mul p)]
  exact congrArg (cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) E n : Type)) (two_mul p)))
    (schemeAbsoluteCycleClass_locally_product f charts B C hC p hp hc)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocallyProductAbsoluteClass.BundleCycles
