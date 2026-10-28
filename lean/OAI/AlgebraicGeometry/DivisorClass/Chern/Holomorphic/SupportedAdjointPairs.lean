import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedCovariantAdjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.VariableMetricIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs

/-! # Supported Adjoint Pairs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual metric pairings of supported native local adjoints, with the original bundle frames and cutoff. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint_pair_inFrame
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1))
    (x : (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) :
    h.globalFormPair V n (h.weightedCovariantChartAdjoint V e he i n f hf hs b) a x.val =
      f x.val * ((h.weight i ⟨x.val, x.property.2⟩ : ℂ) * Projective.CovectorPair.projectiveTangentCovectorPair V n x.val
        (h.chartCovariantAdjointFrame V e i n b x.val) (a.val i ⟨x.val, trivial, x.property.2⟩)) := by
  rw [h.globalFormPair_inFrame V n _ a i x.val x.property.2,
    h.weightedCovariantChartAdjoint_inFrame V e he i n f hf hs b x,
    Projective.CovectorPair.projectiveTangentCovectorPair_smul_left, Complex.star_def, Complex.conj_conj]
  ring

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.weightedCovariantChartAdjoint_pair_zero
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ (n + 1))
    (x : V.analyticSpace) (hx : x ∉ tsupport f) :
    h.globalFormPair V n (h.weightedCovariantChartAdjoint V e he i n f hf hs b) a x = 0 := by
  have hxx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  rw [h.globalFormPair_inFrame V n _ a x x hxx,
    h.weightedCovariantChartAdjoint_zero V e he i n f hf hs b x ⟨x, trivial, hxx⟩ hx,
    Holomorphic.AdjointPointPairs.projectiveTangentCovectorPair_zero_left, mul_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
