import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric

/-! # Bilinear Metric Transport -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricTransport.Constructions

noncomputable section

/-! The general induced covector metric is invariant under actual
invertible changes of tangent coordinates and independent of its basis. -/

variable {E F ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def positiveMetricTransport
    (B : E →L[ℝ] E →L[ℝ] ℝ) (C : F →L[ℝ] F →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hBp : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hC : ∀ u v, C u v = C v u) (hCp : ∀ u : F, u ≠ 0 → 0 < C u u)
    (L : E ≃L[ℝ] F) (hL : ∀ u v, B u v = C (L u) (L v)) :
    ExteriorPair.Constructions.RealMetricFiber E (ExteriorPair.Constructions.positiveBilinearCore B hB hBp) ≃ₗᵢ[ℝ]
      ExteriorPair.Constructions.RealMetricFiber F (ExteriorPair.Constructions.positiveBilinearCore C hC hCp) :=
  ((ExteriorPair.Constructions.realMetricFiberContinuousEquiv (ExteriorPair.Constructions.positiveBilinearCore B hB hBp)).trans
    (L.trans (ExteriorPair.Constructions.realMetricFiberContinuousEquiv (ExteriorPair.Constructions.positiveBilinearCore C hC hCp)).symm)).toLinearEquiv.isometryOfInner
      (fun u v => (hL u.val v.val).symm)

theorem positiveMetricCoordinateForm_transport
    (B : E →L[ℝ] E →L[ℝ] ℝ) (C : F →L[ℝ] F →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hBp : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hC : ∀ u v, C u v = C v u) (hCp : ∀ u : F, u ≠ 0 → 0 < C u u)
    (L : E ≃L[ℝ] F) (hL : ∀ u v, B u v = C (L u) (L v))
    (n : ℕ) (a : DifferentialForms.Manifold.Basic.FormValue F n) :
    BilinearFormMetric.Constructions.positiveMetricCoordinateForm B hB hBp n (a.compContinuousLinearMap L.toContinuousLinearMap) =
      (BilinearFormMetric.Constructions.positiveMetricCoordinateForm C hC hCp n a).compContinuousLinearMap
        (positiveMetricTransport B C hB hBp hC hCp L hL).toContinuousLinearEquiv.toContinuousLinearMap := by
  ext v
  rfl

variable [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]

theorem bilinearFormMetricPair_transport (b : Module.Basis ι ℝ E) (c : Module.Basis κ ℝ F)
    (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ) (C : F →L[ℝ] F →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hBp : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hC : ∀ u v, C u v = C v u) (hCp : ∀ u : F, u ≠ 0 → 0 < C u u)
    (L : E ≃L[ℝ] F) (hL : ∀ u v, B u v = C (L u) (L v)) (a d : DifferentialForms.Manifold.Basic.FormValue F n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a.compContinuousLinearMap L.toContinuousLinearMap)
      (d.compContinuousLinearMap L.toContinuousLinearMap) = BilinearFormMetric.Constructions.bilinearFormMetricPair c n C a d := by
  rw [BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hBp,
    BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic c n C hC hCp,
    positiveMetricCoordinateForm_transport B C hB hBp hC hCp L hL,
    positiveMetricCoordinateForm_transport B C hB hBp hC hCp L hL, ExteriorPair.Constructions.formMetricPair_pullback]

end

end OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricTransport.Constructions
