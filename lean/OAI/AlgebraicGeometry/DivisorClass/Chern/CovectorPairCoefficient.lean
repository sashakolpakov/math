import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorSmooth

/-! # Covector Pair Coefficient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorPairCoefficient

noncomputable section

/-! The original weighted covector pairing and the adjoint of any fiber operator, in the fixed real Hilbert coordinates used by the weak equation. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace

variable {E D ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

def covectorPairCoefficient (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n :=
  r • Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.realMatrixOperator (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b n B)⁻¹

def covectorOperatorCoordinates (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n :=
  ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).comp
    (L.comp ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm.toContinuousLinearMap.restrictScalars ℝ))

theorem covectorOperatorCoordinates_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    covectorOperatorCoordinates b n L (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a) = Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L a) := by
  change Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (L ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem covectorPairCoefficient_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    inner ℝ (covectorPairCoefficient b n B r (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a))
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c) = r * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c).re := by
  rw [covectorPairCoefficient, _root_.smul_apply, real_inner_smul_left,
    Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.euclidean_real_inner_eq_re, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner]

def covectorWeakActionCoefficient (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) (L : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n :=
  (covectorOperatorCoordinates b n L).adjoint.comp (covectorPairCoefficient b n B r)

theorem covectorWeakActionCoefficient_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) (L : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    inner ℝ (covectorWeakActionCoefficient b n B r L (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a))
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c) = r * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (L c)).re := by
  rw [covectorWeakActionCoefficient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, covectorOperatorCoordinates_apply, covectorPairCoefficient_pair]

theorem covectorPairCoefficient_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (r : D → ℝ) {U : Set D}
    (hB : ContDiffOn ℝ ∞ B U) (hr : ContDiffOn ℝ ∞ r U)
    (hBs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => covectorPairCoefficient b n (B x) (r x)) U :=
  hr.smul (Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.realMatrixOperator_smoothOn _ (Analysis.HodgeTheory.Decomposition.MetricCoefficients.Constructions.matrixInverse_entry_smoothOn
    (fun x => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b n (B x)) (Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearExteriorGram_entry_smooth b n B hB)
    (fun x hx => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) (hBs x hx) (hpos x hx))))

theorem covectorOperatorCoordinates_smoothOn_of_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (L : D → Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set D}
    (hL : ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n, ContDiffOn ℝ ∞ (fun x => L x a) U) :
    ContDiffOn ℝ ∞ (fun x => covectorOperatorCoordinates b n (L x)) U := by
  apply contDiffOn_clm_apply.mpr
  intro v
  exact ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
    (hL ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm v))

theorem covectorWeakActionCoefficient_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) (r : D → ℝ)
    (L : D → Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set D}
    (hB : ContDiffOn ℝ ∞ B U) (hr : ContDiffOn ℝ ∞ r U)
    (hL : ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n, ContDiffOn ℝ ∞ (fun x => L x a) U)
    (hBs : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => covectorWeakActionCoefficient b n (B x) (r x) (L x)) U := by
  have hC := covectorOperatorCoordinates_smoothOn_of_apply b n L hL
  have hAdj : ContDiff ℝ ∞ (ContinuousLinearMap.adjoint :
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) →
        Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) :=
    (ContinuousLinearMap.adjoint : (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n) ≃ₗᵢ[ℝ]
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)).toContinuousLinearEquiv.contDiff
  exact (hAdj.comp_contDiffOn hC).clm_comp
    (covectorPairCoefficient_smoothOn b n B r hB hr hBs hpos)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorPairCoefficient
