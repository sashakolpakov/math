import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothTopology
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ChartIntegration
import OAI.Analysis.HodgeTheory.TopForms

/-! # Top Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TopPairing.CM

noncomputable section

/-! ThetaCycle: continuity of the actual PolarizedPairing integral in the smooth topology. -/

open scoped _root_.Manifold ContDiff _root_.Topology BigOperators
open Set Function Filter _root_.MeasureTheory

open OAI.Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [CompactSpace M]
  {n : ℕ}

local instance : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E

/-- Joint continuity holds for the genuine chart-defined wedge integral. -/
theorem top_pairing_continuous (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E) :
    let _ := SmoothTopology.CM.smoothFormTopology E M n
    Continuous (fun p : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n × Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n =>
      Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith D b p.1 p.2) := by
  let _ := SmoothTopology.CM.smoothFormTopology E M n
  apply continuous_finsetSum
  intro i _
  simp only [Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingIntegrand, Function.comp_apply]
  apply ChartIntegration.CM.chart_integral_continuous volume b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph
    (chartAt E i.val) (D.partition i) (D.partition i).contMDiff.continuous (D.subordinate i)
  have hα := (continuous_eval_const (b : Fin n → E)).comp_continuousOn
    (SmoothTopology.CM.smooth_chart_family_continuousOn ⟨chartAt E i.val, chart_mem_atlas E i.val⟩
      (fun p : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n × Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n => p.1) continuous_fst)
  have hβ := (continuous_eval_const (b : Fin n → E)).comp_continuousOn
    (SmoothTopology.CM.smooth_chart_family_continuousOn ⟨chartAt E i.val, chart_mem_atlas E i.val⟩
      (fun p : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n × Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n => p.2) continuous_snd)
  simpa only [Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.topWedgeCoefficient_eq, Pi.mul_def, Function.comp_def, Function.uncurry_def]
    using continuousOn_const.mul (hα.mul hβ)

/-- The right-conjugate integral is continuous, using the actual coefficient
conjugation formula rather than a supplied topology for conjugation. -/
theorem conjugate_top_pairing_continuous (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition E M)
    (b : Module.Basis (Fin n) ℂ E) (α : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    let _ := SmoothTopology.CM.smoothFormTopology E M n
    Continuous (fun β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n =>
      Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingWith D b α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β)) := by
  let _ := SmoothTopology.CM.smoothFormTopology E M n
  apply continuous_finsetSum
  intro i _
  simp only [Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.topPairingIntegrand, Function.comp_apply]
  apply ChartIntegration.CM.chart_integral_continuous volume b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph
    (chartAt E i.val) (D.partition i) (D.partition i).contMDiff.continuous (D.subordinate i)
  have hα : ContinuousOn (fun p : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n × E =>
      α.val.inChart (chartAt E i.val) p.2 b) (univ ×ˢ (chartAt E i.val).target) :=
    (Analysis.HodgeTheory.TopForms.Constructions.PolarizedPairing.chartCoefficient_continuousOn α b i.val).comp continuous_snd.continuousOn
      (fun _ hp => hp.2)
  have hβ := (continuous_eval_const (b : Fin n → E)).comp_continuousOn
    (SmoothTopology.CM.smooth_chart_family_continuousOn ⟨chartAt E i.val, chart_mem_atlas E i.val⟩
      (fun β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n => β) continuous_id)
  change ContinuousOn (fun p : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n × E =>
    Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.topWedgeCoefficient (n := n) (α.val.inChart (chartAt E i.val) p.2 b)
      (star (p.1.val.inChart (chartAt E i.val) p.2 b))) _
  simpa only [Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.topWedgeCoefficient_eq, Pi.mul_def, Function.comp_def]
    using continuousOn_const.mul (hα.mul hβ.star)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TopPairing.CM
