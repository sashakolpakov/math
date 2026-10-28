import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MixedTopWedge
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartPartition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfacePairing
import OAI.AlgebraicTopology.Kunneth.ManifoldWedge

/-! # Surface Wedge Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceWedgeCoordinates.CM

noncomputable section

section

/-! ThetaCycle: chart coefficients of the actual native manifold wedge,
after the exact real-model transport. -/

open OAI.AlgebraicTopology.Kunneth.ManifoldWedge.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped _root_.Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M]
  [IsManifold 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞ M]

theorem surface_wedge_real_chart_coefficient
    (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 β.val)
    (a : OpenPartialHomeomorph M HeckeCycles.GeometricSource.CM.BallChart) (ha : a ∈ atlas HeckeCycles.GeometricSource.CM.BallChart M)
    (y : Fin 4 → ℝ) (hy : (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2).symm y ∈ a.target) :
    let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    (RealModelForms.CM.linearRechartForms e 4 (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β))).val.inChart
      (a.trans e.toHomeomorph.toOpenPartialHomeomorph) y (Pi.basisFun ℝ (Fin 4)) =
      -Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.topWedgeCoefficient (n := 2)
        (α.val.inChart a (e.symm y) (Pi.basisFun ℂ (Fin 2)))
        ((ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β).val.inChart a (e.symm y) (Pi.basisFun ℂ (Fin 2))) := by
  let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  have h := RealModelForms.CM.linear_rechart_forms_in_chart e 4
    (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β)) a ha y hy
  have hv := congrArg (fun v : Analysis.DifferentialForms.Manifold.Basic.FormValue (Fin 4 → ℝ) 4 => v (Pi.basisFun ℝ (Fin 4))) h
  rw [AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge, AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.rawManifoldWedge_inChart, ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm,
    ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateRawForm_inChart] at hv
  change _ = AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (α.val.inChart a (e.symm y))
    (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap (β.val.inChart a (e.symm y)))
    (fun i => e.symm (Pi.basisFun ℝ (Fin 4) i)) at hv
  rw [MixedTopWedge.CM.mixed_pure_top_wedge_real_coefficient _ _ (hα a ha _ hy) (hβ a ha _ hy)] at hv
  refine hv.trans ?_
  have hc : (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β).val.inChart a (e.symm y)
      (Pi.basisFun ℂ (Fin 2)) = star (β.val.inChart a (e.symm y) (Pi.basisFun ℂ (Fin 2))) := rfl
  rw [hc, Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.topWedgeCoefficient_eq]
  norm_num [e]

end

/-! ThetaCycle: the exact mixed wedge comparison respects the actual chart
cutoffs, including extension by zero outside the chart target. -/

open Set OAI.AlgebraicTopology.Kunneth.ManifoldWedge.Constructions
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped _root_.Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace HeckeCycles.GeometricSource.CM.BallChart M]
  [IsManifold 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞ M]

theorem surface_wedge_real_chart_cutoff
    (α β : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart M 2)
    (hα : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 α.val)
    (hβ : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart M 2 0 β.val)
    (a : OpenPartialHomeomorph M HeckeCycles.GeometricSource.CM.BallChart) (ha : a ∈ atlas HeckeCycles.GeometricSource.CM.BallChart M)
    (ρ : M → ℝ) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
    let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
    let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
    Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff (a.trans e.toHomeomorph.toOpenPartialHomeomorph) ρ
      (fun y => (RealModelForms.CM.linearRechartForms e 4 (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge α (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β))).val.inChart
        (a.trans e.toHomeomorph.toOpenPartialHomeomorph) y (Pi.basisFun ℝ (Fin 4))) (e z) =
      -Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff a ρ (fun z => Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.topWedgeCoefficient (n := 2)
        (α.val.inChart a z (Pi.basisFun ℂ (Fin 2)))
        ((ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm β).val.inChart a z (Pi.basisFun ℂ (Fin 2)))) z := by
  let e := Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2
  let _ := RealModelCharts.CM.linearRechartedSpace (M := M) e
  let _ := RealModelCharts.CM.linear_recharted_manifold (M := M) e ∞
  let c := a.trans e.toHomeomorph.toOpenPartialHomeomorph
  have ht : e z ∈ c.target ↔ z ∈ a.target := by
    simpa only [c, mfld_simps] using!
      (show e.symm (e z) ∈ a.target ↔ z ∈ a.target by rw [e.symm_apply_apply])
  have hs : c.symm (e z) = a.symm z := by
    simpa only [c, mfld_simps] using! congrArg a.symm (e.symm_apply_apply z)
  dsimp only
  by_cases hz : z ∈ a.target
  · have h := surface_wedge_real_chart_coefficient α β hα hβ a ha (e z)
      (by simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hz)
    simp only [e, ContinuousLinearEquiv.symm_apply_apply] at h
    change Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff c ρ _ (e z) = -Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff a ρ _ z
    rw [Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, indicator_of_mem (ht.mpr hz), h, hs,
      Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, indicator_of_mem hz, smul_neg]
  · change Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff c ρ _ (e z) = -Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff a ρ _ z
    rw [Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, indicator_of_notMem (mt ht.mp hz), Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff,
      indicator_of_notMem hz, neg_zero]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SurfaceWedgeCoordinates.CM
