import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceForcing
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformEstimate

/-! Uniform C²,α control of genuine difference quotients of a classical solution. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Weak

local instance diffEstimateMatrixNG (m : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance diffEstimateMatrixNS (m : ℕ) : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
local instance diffEstimateMatrixDerivativeNG (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))
local instance diffEstimateMatrixDerivativeNS (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem difference_solution_schauder_bound {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hhalf : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ ≤ 1 / 2)
    (hPD : ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef)
    (hBc : ContDiff ℝ 1 (OAI.Analysis.Normed.Function.Holder.HolderMap.value B))
    (DB : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) α)
    (hDB : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DB x = fderiv ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap.value B) x)
    (u f : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    (Df V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hDf : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value Df x = fderiv ℝ f x)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    (heq : ∀ x, nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = f x)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R) :
    ∃ C > 0, ∀ (v : EuclideanSpace ℝ (Fin m)) (h : ℝ), h ≠ 0 →
      ∃ W : GlobalC2Holder m α,
        globalC2Value W = (fun x => χ x * OAI.Analysis.PDE.Weak.differenceQuotient v h u x) ∧ ‖W‖ ≤ C * ‖v‖ := by
  obtain ⟨C₀, hC₀, hest⟩ := uniform_cutoff_schauder hm hα hα1 χ hχ hχc hχR
  let M := ‖Df‖ + 2 * ((m : ℝ) * m) * ‖DB‖ * ‖H‖ + (1 + ‖B‖) * (‖V‖ + ‖H‖)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨C₀ * M + 1, by positivity, ?_⟩
  intro v h hh
  let F := differenceEquationForcing hα.le (OAI.Analysis.Normed.Function.Holder.HolderMap.value B) hBc DB hDB f hf Df hDf H v hh
  let U := differenceHolder hα.le u (hu.of_le (by norm_num)) V hV v hh
  let G := differenceHolder hα.le (fderiv ℝ u) (hu.fderiv_right (m := 1) (by norm_num)) H hH v hh
  have hU (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = OAI.Analysis.PDE.Weak.differenceQuotient v h u x := rfl
  have hG (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value G x = fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x := by
    exact (fderiv_differenceQuotient u (hu.differentiable (by norm_num)) v h x).symm
  have hF (x) : nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y)
      (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x := by
    erw [differenceEquationForcing_value, hH]
    exact nondivergence_differenceQuotient (OAI.Analysis.Normed.Function.Holder.HolderMap.value B) u f hu v h x (heq x) (heq _)
  obtain ⟨W, hW, hn⟩ := hest B hB hhalf hPD (OAI.Analysis.PDE.Weak.differenceQuotient v h u)
    (contDiff_differenceQuotient u hu v h) F U G hU hG (fun x _ => hF x)
  refine ⟨W, hW, ?_⟩
  have hfN : ‖F‖ ≤ (‖Df‖ + 2 * ((m : ℝ) * m) * ‖DB‖ * ‖H‖) * ‖v‖ :=
    norm_differenceEquationForcing_le hα.le (OAI.Analysis.Normed.Function.Holder.HolderMap.value B) hBc DB hDB f hf Df hDf H v hh
  have huN : ‖U‖ ≤ ‖V‖ * ‖v‖ := norm_differenceHolder_le hα.le u _ V hV v hh
  have hgN : ‖G‖ ≤ ‖H‖ * ‖v‖ := norm_differenceHolder_le hα.le (fderiv ℝ u) _ H hH v hh
  calc
    ‖W‖ ≤ C₀ * (‖F‖ + (1 + ‖B‖) * (‖U‖ + ‖G‖)) := hn
    _ ≤ C₀ * ((‖Df‖ + 2 * ((m : ℝ) * m) * ‖DB‖ * ‖H‖) * ‖v‖ +
        (1 + ‖B‖) * (‖V‖ * ‖v‖ + ‖H‖ * ‖v‖)) := by gcongr
    _ = C₀ * M * ‖v‖ := by dsimp only [M]; ring
    _ ≤ (C₀ * M + 1) * ‖v‖ := by nlinarith only [norm_nonneg v]

end OAI.Analysis.PDE.Schauder
