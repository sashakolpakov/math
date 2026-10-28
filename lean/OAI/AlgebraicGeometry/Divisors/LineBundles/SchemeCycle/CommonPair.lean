import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleImageImmersion
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedImageCodimension
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.CommonNeighborhood

/-! # Common Pair -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonPair.BundleCycles

noncomputable section

/-! Construct common normal charts inside the canonical neighborhoods of the source cycle and its actual closed image, in arbitrary codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
  CycleClass.Thom.Scheme.ProperSupport.Constructions CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso
  CycleClass.Thom.Closed.SupportAnalyticImage.Constructions CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions
  CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (Z : IrreducibleCloseds X.left)
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))

def schemeClosedImageRegularPoint : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z)) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso.regularSupportImageIso i Z).hom x

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeClosedImageRegularPoint_ambient :
    CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (schemeClosedImageRegularPoint i Z x) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) :=
  CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.regularMap_apply i Z x

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosedImageChart_contains : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) ∈
    (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq) (schemeClosedImageRegularPoint i Z x)).openNeighborhood := by
  rw [← schemeClosedImageRegularPoint_ambient i Z x]
  exact (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq) (schemeClosedImageRegularPoint i Z x)).point_mem_neighborhood

def schemeCycleCommonOuterPair : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel (Fin p → ℂ)
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x) :=
  Classical.choose (CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions.exists_subpair_source_ambient
    ((CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x))
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).openNeighborhood
    (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).point_mem_neighborhood
    (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq) (schemeClosedImageRegularPoint i Z x)).openNeighborhood
    (schemeClosedImageChart_contains i Z p hp q hq x))

theorem schemeCycleCommonOuterPair_spec :
    (schemeCycleCommonOuterPair i Z p hp q hq x).ambientChart =
      ((CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x)).ambientChart ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (schemeCycleCommonOuterPair i Z p hp q hq x).neighborhood ⊆ (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).neighborhood ∧
    (schemeCycleCommonOuterPair i Z p hp q hq x).neighborhood ⊆
      (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq) (schemeClosedImageRegularPoint i Z x)).neighborhood :=
  Classical.choose_spec (CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions.exists_subpair_source_ambient
    ((CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z x))
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isEmbedding (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).openNeighborhood
    (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair X Z q hq x).point_mem_neighborhood
    (Scheme.SupportAmbientNormalPair.BundleCycles.schemeSupportAmbientPair Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq) (schemeClosedImageRegularPoint i Z x)).openNeighborhood
    (schemeClosedImageChart_contains i Z p hp q hq x))

theorem schemeCycleCommonOuterPair_mdifferentiable :
    (schemeCycleCommonOuterPair i Z p hp q hq x).ambientChart.MDifferentiable 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      𝓘(ℂ, (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ)) := by
  rw [(schemeCycleCommonOuterPair_spec i Z p hp q hq x).1]
  exact (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularFixedNormalPair_ambientChart_mdifferentiable _

theorem schemeCycleCommonOuterPair_analytic :
    ContMDiffOn 𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ))
      𝓘(ℂ, (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ)) ω
      (schemeCycleCommonOuterPair i Z p hp q hq x).ambientChart (schemeCycleCommonOuterPair i Z p hp q hq x).ambientChart.source := by
  rw [(schemeCycleCommonOuterPair_spec i Z p hp q hq x).1]
  exact CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_contMDiff (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) _

theorem schemeCycleCommonOuterPair_symm_analytic :
    ContMDiffOn 𝓘(ℂ, (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularAnalyticModel × (Fin p → ℂ))
      𝓘(ℂ, (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)) ω
      (schemeCycleCommonOuterPair i Z p hp q hq x).ambientChart.symm (schemeCycleCommonOuterPair i Z p hp q hq x).ambientChart.target := by
  rw [(schemeCycleCommonOuterPair_spec i Z p hp q hq x).1]
  exact CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions.regularFixedNormalPair_symm_contMDiff (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonPair.BundleCycles
