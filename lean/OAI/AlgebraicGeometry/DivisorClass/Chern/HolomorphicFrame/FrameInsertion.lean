import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.InsertionBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntegralPairZero
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization

/-! # Frame Insertion -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.FrameInsertion

noncomputable section

/-! The original compact frame insertion extends to a genuine bounded map from base L² forms into the actual bundle Hilbert completion. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (i : V.analyticSpace) (n : ℕ) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))

def holomorphicMetricSmoothFrameInsertion :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n :=
  (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n).comp (Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs)

theorem holomorphicMetricSmoothFrameInsertion_bound :
    ∃ C : ℝ, ∀ a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      ‖holomorphicMetricSmoothFrameInsertion V h i n f hf hs a‖ ≤ C * ‖Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2 V n a‖ := by
  obtain ⟨C, hC, hb⟩ := h.frameInsertion_integral_bound V i f hf hs
  refine ⟨Real.sqrt C, fun a => ?_⟩
  apply HolomorphicMetric.Equivalence.nonneg_le_sqrt_mul_of_sq_le (norm_nonneg _) (norm_nonneg _) hC.le
  change ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n (Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a)‖ ^ 2 ≤ _
  rw [Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq, norm_sq_eq_re_inner (𝕜 := ℂ), Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2_inner]
  exact hb n a

def holomorphicMetricFrameL2Insertion : Analysis.HodgeTheory.Decomposition.Form.Constructions.ProjectiveL2Forms V n →L[ℂ] Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n :=
  (holomorphicMetricSmoothFrameInsertion V h i n f hf hs).extendOfNorm (Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2 V n)

theorem holomorphicMetricFrameL2Insertion_on_smooth
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    holomorphicMetricFrameL2Insertion V h i n f hf hs (Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2 V n a) =
      Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n (Insertion.holomorphicLineSmoothFrameInsertion u i n f hf hs a) :=
  LinearMap.extendOfNorm_eq (Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2_dense V n)
    (holomorphicMetricSmoothFrameInsertion_bound V h i n f hf hs) a

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.FrameInsertion
