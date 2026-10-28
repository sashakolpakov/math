import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformCutoff
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformInverse

/-! Uniform cutoff Schauder estimates on a small coefficient ball. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem uniform_cutoff_schauder {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R) :
    ∃ C > 0, ∀ (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
      (_ : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0),
      2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ ≤ 1 / 2 →
      (∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef) →
      ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u →
      ∀ (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
        (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α),
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) →
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x) →
      (∀ x ∈ Function.support χ, nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
      ∃ W : GlobalC2Holder m α, globalC2Value W = (fun x => χ x * u x) ∧
        ‖W‖ ≤ C * (‖F‖ + (1 + ‖B‖) * (‖U‖ + ‖V‖)) := by
  let I : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α := OAI.Analysis.Normed.Function.Holder.HolderMap.constant 1
  let P := poissonHolderOperator hm hα hα1 R
  obtain ⟨C₀, hC₀, hbound⟩ := cutoffJetForcing_uniform_bound hα.le hα1.le χ hχ hχc
  let C := (2 * ‖P‖ + 1) * C₀ * (‖I‖ + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro B hB hhalf hPD u hu F U V hU hV heq
  have hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖P‖ < 1 := lt_of_le_of_lt hhalf (by norm_num)
  let A := I - B
  let T := smallMatrixSolutionOperator hm hα hα1 B hB hsmall
  let G : SupportedHolder m α R :=
    ⟨cutoffJetForcing hα.le hα1.le A χ hχ hχc F U V, by
      intro x hx
      exact cutoffJetForcing_zero hα.le hα1.le A χ hχ hχc F U V x (fun h => hx (hχR h))⟩
  obtain ⟨W, hW, hn⟩ := compact_C2_small_coefficient_holder hm hα hα1 B hB hsmall hPD
    (fun x => χ x * u x) ((hχ.of_le (by norm_num)).mul hu) hχc.mul_right G (by
      intro x
      exact cutoffJetForcing_equation hα.le hα1.le A χ u hχ hχc hu F U V hU hV heq x)
  refine ⟨W, hW, ?_⟩
  have hT : ‖T‖ ≤ 2 * ‖P‖ := smallMatrixSolutionOperator_norm_le hm hα hα1 B hB hsmall hhalf
  have hA : ‖A‖ ≤ (‖I‖ + 1) * (1 + ‖B‖) := by
    apply (norm_sub_le I B).trans
    nlinarith only [norm_nonneg I, norm_nonneg B, mul_nonneg (norm_nonneg I) (norm_nonneg B)]
  have hG : ‖G‖ ≤ C₀ * (‖I‖ + 1) * (‖F‖ + (1 + ‖B‖) * (‖U‖ + ‖V‖)) := by
    apply (hbound A F U V).trans
    have hj : 0 ≤ ‖U‖ + ‖V‖ := by positivity
    have hi : 1 ≤ ‖I‖ + 1 := by linarith [norm_nonneg I]
    have hf : ‖F‖ ≤ (‖I‖ + 1) * ‖F‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (norm_nonneg F)
    have ha := mul_le_mul_of_nonneg_right hA hj
    calc
      C₀ * (‖F‖ + ‖A‖ * (‖U‖ + ‖V‖)) ≤
          C₀ * ((‖I‖ + 1) * ‖F‖ + ((‖I‖ + 1) * (1 + ‖B‖)) * (‖U‖ + ‖V‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hf ha) hC₀.le
      _ = _ := by ring
  calc
    ‖W‖ ≤ ‖T‖ * ‖G‖ := hn
    _ ≤ (2 * ‖P‖) * (C₀ * (‖I‖ + 1) * (‖F‖ + (1 + ‖B‖) * (‖U‖ + ‖V‖))) :=
      mul_le_mul hT hG (norm_nonneg G) (by positivity)
    _ ≤ C * (‖F‖ + (1 + ‖B‖) * (‖U‖ + ‖V‖)) := by
      dsimp only [C]
      have hh : 0 ≤ C₀ * (‖I‖ + 1) * (‖F‖ + (1 + ‖B‖) * (‖U‖ + ‖V‖)) := by positivity
      nlinarith only [hh]

end OAI.Analysis.PDE.Schauder
