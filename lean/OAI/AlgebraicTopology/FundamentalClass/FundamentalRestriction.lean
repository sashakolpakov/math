import OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation
import OAI.AlgebraicTopology.FundamentalClass.RelativeCoefficients

/-! # Fundamental Restriction -/

namespace OAI.AlgebraicTopology.FundamentalClass.FundamentalRestriction.IntegrationConstruction

noncomputable section

/-! Restrict the specified global fundamental class to a compact set in one
chart. Its value is the chart's geometric class with its locally constant sign. -/

open _root_.CategoryTheory Set
open OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation.Geometry OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [T2Space M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [CompactSpace M]

theorem integralFundamentalClass_restrict_chart (o : IntegrationOrientation.Orientation d M)
    (center : M) (K : Set M) (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (Fin d → ℝ) center).source) (sign : ℤˣ)
    (hsign : ∀ x (hx : x ∈ K), o.chartSign center ⟨x, hKs hx⟩ = sign) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) d
      (IntegrationOrientation.integralFundamentalClass o) =
      (sign : ℤ) • IntegrationOrientation.Geometry.chartCompactClass (chartAt (Fin d → ℝ) center) K hK hKs := by
  apply RealSupport.IntegrationGeometry.realManifold_compactSupport_point_ext d K hK
  intro x hx
  have h : AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx d
      (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) d
        (IntegrationOrientation.integralFundamentalClass o)) = o.localClass x := by
    change HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint (TopCat.of M) K x hx) d
      (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) Kᶜ) d
        (IntegrationOrientation.integralFundamentalClass o)) = _
    have hcomp := congrArg (fun f => HomologicalComplex.homologyMap f d)
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint_projection (TopCat.of M) K x hx)
    simp only [HomologicalComplex.homologyMap_comp] at hcomp
    exact (ConcreteCategory.congr_hom hcomp (IntegrationOrientation.integralFundamentalClass o)).trans
      (IntegrationOrientation.integralFundamentalClass_atPoint o x)
  rw [h, map_zsmul, IntegrationOrientation.Geometry.chartCompactClass_atPoint, ← hsign x hx]
  exact (o.signed_chartClass center x (hKs hx)).symm

theorem fundamentalClass_restrict_chart (o : IntegrationOrientation.Orientation d M)
    (center : M) (K : Set M) (hK : IsCompact K)
    (hKs : K ⊆ (chartAt (Fin d → ℝ) center).source) (sign : ℤˣ)
    (hsign : ∀ x (hx : x ∈ K), o.chartSign center ⟨x, hKs hx⟩ = sign) :
    HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ (TopCat.of M) Kᶜ) d
      (IntegrationOrientation.fundamentalClass o) =
      RelativeCoefficients.IntegrationConstruction.relativeCoefficientHomology (TopCat.of M) Kᶜ d
        ((sign : ℤ) • IntegrationOrientation.Geometry.chartCompactClass (chartAt (Fin d → ℝ) center) K hK hKs) := by
  rw [IntegrationOrientation.fundamentalClass, ← RelativeCoefficients.IntegrationConstruction.relativeCoefficientHomology_projection,
    integralFundamentalClass_restrict_chart o center K hK hKs sign hsign]

end

end OAI.AlgebraicTopology.FundamentalClass.FundamentalRestriction.IntegrationConstruction
