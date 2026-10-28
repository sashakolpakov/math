import OAI.Analysis.PDE.Schauder.Calculus.Schauder.JetForcing

/-! A local Schauder bound with a constant independent of the solution's Hessian. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem cutoff_schauder_lower_jet_estimate {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (hPD : ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u →
      ∀ (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
        (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α),
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) →
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x) →
      (∀ x ∈ Function.support χ, nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
      ∃ W : GlobalC2Holder m α, globalC2Value W = (fun x => χ x * u x) ∧
        ‖W‖ ≤ C * (‖F‖ + ‖U‖ + ‖V‖) := by
  let A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α := OAI.Analysis.Normed.Function.Holder.HolderMap.constant 1 - B
  let T := smallMatrixSolutionOperator hm hα hα1 B hB hsmall
  obtain ⟨C₀, hC₀, hbound⟩ := cutoffJetForcing_bound hα.le hα1.le A χ hχ hχc
  refine ⟨(‖T‖ + 1) * C₀, by positivity, ?_⟩
  intro u hu F U V hU hV heq
  let G : SupportedHolder m α R :=
    ⟨cutoffJetForcing hα.le hα1.le A χ hχ hχc F U V, by
      intro x hx
      exact cutoffJetForcing_zero hα.le hα1.le A χ hχ hχc F U V x (fun h => hx (hχR h))⟩
  obtain ⟨W, hW, hn⟩ := compact_C2_small_coefficient_holder hm hα hα1 B hB hsmall hPD
    (fun x => χ x * u x) ((hχ.of_le (by norm_num)).mul hu) hχc.mul_right G (by
      intro x
      exact cutoffJetForcing_equation hα.le hα1.le A χ u hχ hχc hu F U V hU hV heq x)
  refine ⟨W, hW, ?_⟩
  have hgn : ‖G‖ ≤ C₀ * (‖F‖ + ‖U‖ + ‖V‖) := hbound F U V
  calc
    ‖W‖ ≤ ‖T‖ * ‖G‖ := hn
    _ ≤ ‖T‖ * (C₀ * (‖F‖ + ‖U‖ + ‖V‖)) := mul_le_mul_of_nonneg_left hgn (norm_nonneg _)
    _ ≤ (‖T‖ + 1) * C₀ * (‖F‖ + ‖U‖ + ‖V‖) := by
      nlinarith [norm_nonneg F, norm_nonneg U, norm_nonneg V]

end OAI.Analysis.PDE.Schauder
