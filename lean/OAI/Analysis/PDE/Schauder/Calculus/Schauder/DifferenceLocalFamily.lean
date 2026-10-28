import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceLocalLimit
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.UniformEstimate

/-! The nonlinear bootstrap interface: varying finite-difference coefficients need no derivatives. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Weak

theorem local_difference_family_schauder_bound {m : ℕ} (hm : 3 ≤ m) {α R δ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (_ : 0 < δ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    (v : EuclideanSpace ℝ (Fin m))
    (B : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (hB : ∀ h, h ≠ 0 → |h| < δ → ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x = 0)
    (hhalf : ∀ h, h ≠ 0 → |h| < δ → 2 * ((m : ℝ) * m * ‖B h‖) * ‖poissonHolderOperator hm hα hα1 R‖ ≤ 1 / 2)
    (hPD : ∀ h, h ≠ 0 → |h| < δ → ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x).PosDef)
    {N K : ℝ} (hBN : ∀ h, h ≠ 0 → |h| < δ → ‖B h‖ ≤ N) (hFK : ∀ h, h ≠ 0 → |h| < δ → ‖F h‖ ≤ K)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R)
    (heq : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ Function.support χ,
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) y) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (F h) x) :
    ∃ C > 0, ∀ h : ℝ, h ≠ 0 → |h| < δ → ∃ W : GlobalC2Holder m α,
      globalC2Value W = (fun x => χ x * OAI.Analysis.PDE.Weak.differenceQuotient v h u x) ∧ ‖W‖ ≤ C := by
  obtain ⟨C₀, hC₀, hest⟩ := uniform_cutoff_schauder hm hα hα1 χ hχ hχc hχR
  let M := C₀ * (|K| + (1 + |N|) * (‖V‖ * ‖v‖ + ‖H‖ * ‖v‖))
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨M + 1, by linarith only [hM], ?_⟩
  intro h hh hδh
  let U := differenceHolder hα.le u (hu.of_le (by norm_num)) V hV v hh
  let G := differenceHolder hα.le (fderiv ℝ u) (hu.fderiv_right (m := 1) (by norm_num)) H hH v hh
  have hU (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = OAI.Analysis.PDE.Weak.differenceQuotient v h u x := rfl
  have hG (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value G x = fderiv ℝ (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x :=
    (fderiv_differenceQuotient u (hu.differentiable (by norm_num)) v h x).symm
  obtain ⟨W, hW, hn⟩ := hest (B h) (hB h hh hδh) (hhalf h hh hδh) (hPD h hh hδh)
    (OAI.Analysis.PDE.Weak.differenceQuotient v h u) (contDiff_differenceQuotient u hu v h) (F h) U G hU hG (heq h hh hδh)
  refine ⟨W, hW, ?_⟩
  have hUbound : ‖U‖ ≤ ‖V‖ * ‖v‖ := norm_differenceHolder_le hα.le u _ V hV v hh
  have hGbound : ‖G‖ ≤ ‖H‖ * ‖v‖ := norm_differenceHolder_le hα.le (fderiv ℝ u) _ H hH v hh
  have hBbound : ‖B h‖ ≤ |N| := (hBN h hh hδh).trans (le_abs_self _)
  have hFbound : ‖F h‖ ≤ |K| := (hFK h hh hδh).trans (le_abs_self _)
  have hm : ‖W‖ ≤ M := by
    apply hn.trans
    dsimp only [M]
    gcongr
  exact hm.trans (by linarith)

theorem directional_C2_of_local_small_equations {m : ℕ} (hm : 3 ≤ m) {α R δ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hδ : 0 < δ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    (v : EuclideanSpace ℝ (Fin m))
    (B : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (F : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (hB : ∀ h, h ≠ 0 → |h| < δ → ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x = 0)
    (hhalf : ∀ h, h ≠ 0 → |h| < δ → 2 * ((m : ℝ) * m * ‖B h‖) * ‖poissonHolderOperator hm hα hα1 R‖ ≤ 1 / 2)
    (hPD : ∀ h, h ≠ 0 → |h| < δ → ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) x).PosDef)
    {N K : ℝ} (hBN : ∀ h, h ≠ 0 → |h| < δ → ‖B h‖ ≤ N) (hFK : ∀ h, h ≠ 0 → |h| < δ → ‖F h‖ ≤ K)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R)
    (heq : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ Function.support χ,
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B h) y) (OAI.Analysis.PDE.Weak.differenceQuotient v h u) x =
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (F h) x) :
    ContDiff ℝ 2 (fun x => χ x * fderiv ℝ u x v) := by
  obtain ⟨C, _, hC⟩ := local_difference_family_schauder_bound hm hα hα1 hδ u hu V hV H hH v B F
    hB hhalf hPD hBN hFK χ hχ hχc hχR heq
  exact contDiff_directional_derivative_of_local_schauder_bound hα hδ u χ
    (hu.differentiable (by norm_num)) v hC

end OAI.Analysis.PDE.Schauder
