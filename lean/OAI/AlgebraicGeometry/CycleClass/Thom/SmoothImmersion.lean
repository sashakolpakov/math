import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Smooth Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions

noncomputable section

/-! The actual regular-locus map of a smooth algebraic support is a
closed complex immersion in the whole ambient projective variety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions

abbrev projectiveManifold (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Closed.ComplexImmersion.Constructions.ComplexManifold where
  complexDimension := V.complexDimension
  analyticSpace := TopCat.of V.analyticSpace
  chartedSpace := inferInstance
  manifold := inferInstance
  metrizable := inferInstance

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
  [Smooth Z.structureMap]

theorem analyticSingularBoundary_eq_empty : Z.analyticSingularBoundary = ∅ := by
  have h : Geometric.StratumDimension.supportSingularBoundary Z.val V.structureMap = ∅ := by
    unfold Geometric.StratumDimension.supportSingularBoundary
    change Z.inclusion '' Geometric.SingularLocus.singularLocus Z.structureMap = ∅
    rw [Geometric.SingularLocus.singularLocus_eq_empty_of_smooth, Set.image_empty]
  change V.analyticUnderlying ⁻¹' Geometric.StratumDimension.supportSingularBoundary Z.val V.structureMap = ∅
  rw [h, Set.preimage_empty]

theorem regular_range_eq_support :
    Set.range Z.regularAnalyticToAmbient = Set.range Z.analyticInclusion := by
  rw [← Z.range_analyticInclusion_sdiff_boundary, analyticSingularBoundary_eq_empty,
    Set.sdiff_empty]

theorem regular_closed : Topology.IsClosedEmbedding Z.regularAnalyticToAmbient :=
  ⟨Z.isEmbedding_regularAnalyticToAmbient, by
    rw [regular_range_eq_support]
    exact Z.isClosedEmbedding_analyticInclusion.isClosed_range⟩

def smoothCycleImmersion : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (projectiveManifold V) p where
  regularComplexDimension := Z.regularComplexDimension
  regularAnalyticSpace := TopCat.of Z.regularAnalyticSpace
  chartedSpace := inferInstance
  manifold := inferInstance
  regularComplementTopCatMap := TopCat.ofHom
    ⟨Z.regularAnalyticToAmbient, Z.continuous_regularAnalyticToAmbient⟩
  holomorphic :=
    (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff Z.regularAmbientOpen Z.regularComplementInclusion ω).mpr
      (Z.contMDiff_regularComplementInclusion ω)
  differential_injective := fun x => by
    change Function.Injective (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel)
      Z.regularAnalyticToAmbient x)
    exact (congrArg (fun L : Z.regularAnalyticModel →L[ℂ] V.analyticModel => Function.Injective L)
      (Z.mfderiv_regularComplementInclusion_eq_ambient x)).mp
        (Z.mfderiv_regularComplementInclusion_injective x)
  closed := regular_closed Z
  regularComplexDimension_add_codimension := Z.regularComplexDimension_add_codimension

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions
