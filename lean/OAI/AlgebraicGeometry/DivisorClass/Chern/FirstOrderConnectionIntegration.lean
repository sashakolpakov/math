import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm

/-! # First Order Connection Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FirstOrderConnectionIntegration

noncomputable section

/-! Integration by parts on an actual chart with a smooth zero-order connection term and compact test support. -/

open _root_.MeasureTheory
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem firstOrderConnection_integration_on (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (directions : ι → E) (symbol : ι → F →L[ℝ] G) (weight : E → G →L[ℝ] G)
    (S : E → F →L[ℝ] G) {U : Set E} (hU : IsOpen U)
    (hweight : ContDiffOn ℝ ∞ weight U) (hS : ContDiffOn ℝ ∞ S U)
    (a : E → F) (b : E → G) (ha : ContDiff ℝ ∞ a) (hb : ContDiffOn ℝ ∞ b U)
    (hac : HasCompactSupport a) (hs : tsupport a ⊆ U) :
    (∫ x, inner ℝ (weight x (b x)) (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.firstOrderCoordinateOperator directions symbol a x + S x (a x)) ∂μ) =
      ∫ x, inner ℝ (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.formalAdjointNumerator directions symbol weight b x + (S x).adjoint (weight x (b x))) (a x) ∂μ := by
  have hMv := hweight.clm_apply hb
  have hSi : ContDiffOn ℝ ∞ (fun x => (S x).adjoint) U :=
    (ContinuousLinearMap.adjoint : (F →L[ℝ] G) ≃ₗᵢ[ℝ] (G →L[ℝ] F)).toContinuousLinearEquiv.contDiff.comp_contDiffOn hS
  have hSZ := Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smooth_inner_test_integrable μ _ a hU (hSi.clm_apply hMv) ha hac hs
  have hSZ' : Integrable (fun x => inner ℝ (weight x (b x)) (S x (a x))) μ := by
    simpa only [ContinuousLinearMap.adjoint_inner_left] using hSZ
  have hN := Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smooth_inner_test_integrable μ _ a hU
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.formalAdjointNumerator_smoothOn directions symbol weight b hU hweight hb) ha hac hs
  have hi (i : ι) : Integrable (fun x => inner ℝ ((symbol i).adjoint (weight x (b x)))
      (fderiv ℝ a x (directions i))) μ :=
    Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.smooth_inner_test_integrable μ _ _ hU ((symbol i).adjoint.contDiff.comp_contDiffOn hMv)
      (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative a ha (directions i)) (hac.fderiv_apply ℝ (directions i))
      ((tsupport_fderiv_apply_subset ℝ (directions i)).trans hs)
  have hD : Integrable (fun x => inner ℝ (weight x (b x)) (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.firstOrderCoordinateOperator directions symbol a x)) μ := by
    have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
    simpa only [Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.firstOrderCoordinateOperator, inner_sum, ContinuousLinearMap.adjoint_inner_left] using hsum
  simp_rw [inner_add_right, inner_add_left]
  rw [integral_add hD hSZ', integral_add hN hSZ,
    Analysis.HodgeTheory.Decomposition.LocalAdjointForm.Constructions.firstOrderCoordinateOperator_integration_on μ directions symbol weight hU hweight a b ha hb hac hs]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => ((S x).adjoint_inner_left (a x) (weight x (b x))).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FirstOrderConnectionIntegration
