import OAI.Analysis.HodgeTheory.Decomposition.Form
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Local Adjoint -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions

noncomputable section

/-! Local integration by parts and the explicit formal-adjoint numerator
for a first-order differential operator with fixed symbol matrices. -/

open scoped ContDiff BigOperators
open _root_.MeasureTheory

section Support

variable {D F : Type*} [TopologicalSpace D] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem compactSupport_inner_right (w u : D → F) (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => inner ℝ (w x) (u x)) := by
  apply hu.mono
  intro x hx
  change inner ℝ (w x) (u x) ≠ 0 at hx
  change u x ≠ 0
  intro hzero
  rw [hzero, inner_zero_right] at hx
  exact hx rfl

end Support

section Integration

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
theorem smooth_inner_compact_integrable (w u : E → F)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) :
    Integrable (fun x => inner ℝ (w x) (u x)) μ :=
  (hw.continuous.inner hu.continuous).integrable_of_hasCompactSupport (compactSupport_inner_right w u huc)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem smooth_directional_derivative (u : E → F) (hu : ContDiff ℝ ∞ u) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ u x v) :=
  (hu.fderiv_right (by simp)).clm_apply contDiff_const

/-- Integration by parts has no boundary term for an actual compactly supported smooth test field. -/
theorem integral_inner_directional (w u : E → F)
    (hw : ContDiff ℝ ∞ w) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u) (v : E) :
    (∫ x, inner ℝ (w x) (fderiv ℝ u x v) ∂μ) =
      -(∫ x, inner ℝ (fderiv ℝ w x v) (u x) ∂μ) := by
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ)
    (smooth_inner_compact_integrable μ _ u (smooth_directional_derivative w hw v) hu huc)
    (smooth_inner_compact_integrable μ w _ hw (smooth_directional_derivative u hu v) (huc.fderiv_apply ℝ v))
    (smooth_inner_compact_integrable μ w u hw hu huc)
    (fun x _ => (hw.differentiable (by simp)).differentiableAt)
    (fun x _ => (hu.differentiable (by simp)).differentiableAt)

end Integration

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

def firstOrderCoordinateOperator (directions : ι → E) (symbol : ι → F →L[ℝ] G)
    (u : E → F) (x : E) : G :=
  ∑ i, symbol i (fderiv ℝ u x (directions i))

/-- The differentiated weighted transpose appearing in the formal adjoint. -/
def formalAdjointNumerator (directions : ι → E) (symbol : ι → F →L[ℝ] G)
    (weight : E → G →L[ℝ] G) (v : E → G) (x : E) : F :=
  -∑ i, fderiv ℝ (fun y => (symbol i).adjoint (weight y (v y))) x (directions i)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem formalAdjointNumerator_smoothOn (directions : ι → E) (symbol : ι → F →L[ℝ] G)
    (weight : E → G →L[ℝ] G) (v : E → G) {U : Set E} (hU : IsOpen U)
    (hweight : ContDiffOn ℝ ∞ weight U) (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (formalAdjointNumerator directions symbol weight v) U := by
  intro x hx
  have hw (i : ι) : ContDiffAt ℝ ∞ (fun y => (symbol i).adjoint (weight y (v y))) x :=
    (symbol i).adjoint.contDiff.contDiffAt.comp x
      ((hweight.contDiffAt (hU.mem_nhds hx)).clm_apply (hv.contDiffAt (hU.mem_nhds hx)))
  have hd (i : ι) : ContDiffAt ℝ ∞
      (fun y => fderiv ℝ (fun z => (symbol i).adjoint (weight z (v z))) y (directions i)) x :=
    ((hw i).fderiv_right (by simp)).clm_apply contDiffAt_const
  have h : ContDiffAt ℝ ∞ (formalAdjointNumerator directions symbol weight v) x := by
    unfold formalAdjointNumerator
    fun_prop
  exact h.contDiffWithinAt

/-- The formal-adjoint numerator is derived by integration of the actual directional derivatives. -/
theorem firstOrderCoordinateOperator_integration (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (directions : ι → E) (symbol : ι → F →L[ℝ] G) (weight : E → G →L[ℝ] G)
    (hweight : ContDiff ℝ ∞ weight) (u : E → F) (v : E → G)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (huc : HasCompactSupport u) :
    (∫ x, inner ℝ (weight x (v x)) (firstOrderCoordinateOperator directions symbol u x) ∂μ) =
      ∫ x, inner ℝ (formalAdjointNumerator directions symbol weight v x) (u x) ∂μ := by
  let w (i : ι) (x : E) : F := (symbol i).adjoint (weight x (v x))
  have hw (i : ι) : ContDiff ℝ ∞ (w i) := (symbol i).adjoint.contDiff.comp (hweight.clm_apply hv)
  have hi (i : ι) : Integrable (fun x => inner ℝ (w i x) (fderiv ℝ u x (directions i))) μ :=
    smooth_inner_compact_integrable μ _ _ (hw i) (smooth_directional_derivative u hu (directions i))
      (huc.fderiv_apply ℝ (directions i))
  have hi' (i : ι) : Integrable (fun x => inner ℝ (fderiv ℝ (w i) x (directions i)) (u x)) μ :=
    smooth_inner_compact_integrable μ _ _ (smooth_directional_derivative (w i) (hw i) (directions i)) hu huc
  calc
    (∫ x, inner ℝ (weight x (v x)) (firstOrderCoordinateOperator directions symbol u x) ∂μ) =
        ∫ x, ∑ i, inner ℝ (w i x) (fderiv ℝ u x (directions i)) ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [firstOrderCoordinateOperator, inner_sum, w, ContinuousLinearMap.adjoint_inner_left]
    _ = ∑ i, ∫ x, inner ℝ (w i x) (fderiv ℝ u x (directions i)) ∂μ :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = ∑ i, -(∫ x, inner ℝ (fderiv ℝ (w i) x (directions i)) (u x) ∂μ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_inner_directional μ (w i) u (hw i) hu huc (directions i)
    _ = -(∫ x, ∑ i, inner ℝ (fderiv ℝ (w i) x (directions i)) (u x) ∂μ) := by
      rw [integral_finsetSum _ (fun i _ => hi' i), Finset.sum_neg_distrib]
    _ = ∫ x, inner ℝ (formalAdjointNumerator directions symbol weight v x) (u x) ∂μ := by
      simp only [formalAdjointNumerator, inner_neg_left, sum_inner, integral_neg, w]

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions
