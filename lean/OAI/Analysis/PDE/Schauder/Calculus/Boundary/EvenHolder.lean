import OAI.Analysis.PDE.Schauder.Calculus.Boundary.EvenExtension
import OAI.Analysis.Normed.Function.Holder.Banach.Construct

/-! A compactly supported halfspace Hölder datum has a global extension with an
explicit norm bound. The exponent and the Hölder constant are preserved. -/

noncomputable section
open Set Metric InnerProductSpace
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem evenNormalExtension_norm_le (e : E) (he : ‖e‖ = 1) (f : E → ℝ)
    {R α H : ℝ} (hR : 0 ≤ R) (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hs : ∀ x, R < ‖x‖ → f x = 0)
    (hh : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      |f x - f y| ≤ H * ‖x - y‖ ^ α) (x : E) :
    ‖f (normalFold e x)‖ ≤ H * (2 * R + 1) ^ α := by
  by_cases hx : R < ‖x‖
  · rw [hs _ (by simpa only [norm_normalFold] using hx), norm_zero]
    positivity
  have hxR : ‖normalFold e x‖ ≤ R := by simpa only [norm_normalFold] using le_of_not_gt hx
  let z := (R + 1) • e
  have hnz : ‖z‖ = R + 1 := by
    simp only [z, norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg (by linarith : 0 ≤ R + 1)]
  have hz : 0 ≤ inner ℝ e z := by
    simp only [z, real_inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
    linarith
  have hzero : f z = 0 := hs z (by rw [hnz]; linarith)
  have hd : ‖normalFold e x - z‖ ≤ 2 * R + 1 :=
    (norm_sub_le _ _).trans (by rw [hnz]; linarith)
  have h := hh _ (normalFold_nonneg e x he) z hz
  rw [hzero, sub_zero, ← Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hd hα) hH)

omit [FiniteDimensional ℝ E] in
theorem exists_halfspace_holder_extension (e : E) (he : ‖e‖ = 1) (f : E → ℝ)
    (hf : Continuous f) {R α H : ℝ} (hR : 0 ≤ R) (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hs : ∀ x, R < ‖x‖ → f x = 0)
    (hh : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α,
      (∀ x, 0 ≤ inner ℝ e x → OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = f x) ∧
      (∀ x, R < ‖x‖ → OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = 0) ∧
      ‖F‖ ≤ (1 + (2 * R + 1) ^ α) * H := by
  let U := H * (2 * R + 1) ^ α
  have hU : 0 ≤ U := mul_nonneg hH (Real.rpow_nonneg (by linarith) _)
  have hsup : ∀ x, ‖f (normalFold e x)‖ ≤ U :=
    evenNormalExtension_norm_le e he f hR hα hH hs hh
  let V : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f (normalFold e x)) (hf.comp (normalFold_lipschitz e he).continuous) U hsup
  have hV : ∀ x y, ‖V x - V y‖ ≤ H * (dist x y) ^ α := by
    intro x y
    simpa only [V, BoundedContinuousFunction.coe_ofNormedAddCommGroup, Real.norm_eq_abs,
      dist_eq_norm] using evenNormalExtension_holder e he f hα hH hh x y
  let F := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα V hV
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x hx
    change f (normalFold e x) = f x
    simp only [normalFold, ite_eq_left hx]
  · intro x hx
    change f (normalFold e x) = 0
    exact hs _ (by simpa only [norm_normalFold] using hx)
  · have hnV : ‖V‖ ≤ U :=
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hU hsup
    calc
      ‖F‖ ≤ max ‖V‖ H := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα V hH hV
      _ ≤ max U H := max_le_max hnV le_rfl
      _ ≤ U + H := max_le (le_add_of_nonneg_right hH) (le_add_of_nonneg_left hU)
      _ = (1 + (2 * R + 1) ^ α) * H := by dsimp [U]; ring

end OAI.Analysis.PDE.Schauder
