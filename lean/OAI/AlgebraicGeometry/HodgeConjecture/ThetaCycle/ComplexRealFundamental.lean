import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartLocalClass
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralEvaluation

/-! # Complex Real Fundamental -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexRealFundamental.CM

noncomputable section

/-! ThetaCycle: the geometric real chart simplex classes are the restrictions
of a fixed, explicitly constructed multiple of the canonical complex
fundamental class. The integer is derived from the actual model simplex. -/

open _root_.CategoryTheory Set
open scoped _root_.Manifold ContDiff

def realSimplexComplexMultiplicity (p : ℕ)
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ)) : ℤ :=
  RechartLocalClass.CM.rechartedModelCoefficient p e (AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry.positiveLocalClass (2 * p))

variable {p : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin p → ℂ) M]
  [T2Space M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

theorem real_chart_simplex_class_eq_multiple
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ))
    (a : OpenPartialHomeomorph M (Fin p → ℂ)) (ha : a ∈ atlas (Fin p → ℂ) M)
    (x : M) (hx : x ∈ a.source) :
    AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartLocalClass (a.trans e.toHomeomorph.toOpenPartialHomeomorph) x
      (by simpa only [mfld_simps] using hx) =
      realSimplexComplexMultiplicity p e • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x := by
  let c := a.trans e.toHomeomorph.toOpenPartialHomeomorph
  have hxc : x ∈ c.source := by simpa only [c, mfld_simps] using hx
  have hq : RechartLocalClass.CM.centeredChartLocalIso c x hxc (2 * p) =
      CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso (X := TopCat.of M)
        (Y := TopCat.of (Fin (2 * p) → ℝ)) c x hxc (2 * p) ≪≫
        CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin (2 * p) → ℝ) (c x) (2 * p) :=
    Iso.ext (RechartLocalClass.CM.centered_chart_iso_translation c x hxc (2 * p))
  have h := RechartLocalClass.CM.linear_recharted_local_class_eq_multiple e a ha x hx (AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry.positiveLocalClass (2 * p))
  change (RechartLocalClass.CM.centeredChartLocalIso c x hxc (2 * p)).inv _ = _ at h
  rw [hq] at h
  simpa only [AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartLocalClass, AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.positiveCoordinateClass, realSimplexComplexMultiplicity,
    Iso.trans_inv] using! h

variable [CompactSpace M]

def rechartedIntegralCycle
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ)) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of M)).homology (2 * p) :=
  realSimplexComplexMultiplicity p e • CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M

theorem recharted_integral_cycle_restrict_chart
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ))
    (a : OpenPartialHomeomorph M (Fin p → ℂ)) (ha : a ∈ atlas (Fin p → ℂ) M)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ a.source) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) (2 * p)
      (rechartedIntegralCycle (M := M) e) =
      AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartCompactClass (a.trans e.toHomeomorph.toOpenPartialHomeomorph) K hK
        (by simpa only [mfld_simps] using hKs) := by
  apply CycleClass.Geometric.ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext p K hK
  intro x hx
  have hcomp := congrArg (fun f => HomologicalComplex.homologyMap f (2 * p))
    (CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint_projection (TopCat.of M) K x hx)
  simp only [HomologicalComplex.homologyMap_comp] at hcomp
  have h := ConcreteCategory.congr_hom hcomp (rechartedIntegralCycle (M := M) e)
  change CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p)
      (HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) (2 * p)
        (rechartedIntegralCycle (M := M) e)) = _ at h
  rw [h, AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry.chartCompactClass_atPoint, real_chart_simplex_class_eq_multiple e a ha x (hKs hx)]
  change HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) {x}ᶜ) (2 * p)
    (realSimplexComplexMultiplicity p e • CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass p M) = _
  rw [map_zsmul, CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass_atPoint]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexRealFundamental.CM
