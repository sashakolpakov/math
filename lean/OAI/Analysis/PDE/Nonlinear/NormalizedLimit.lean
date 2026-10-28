import OAI.Analysis.PDE.Nonlinear.RegularityLimit
import OAI.Analysis.PDE.Nonlinear.FamilyFreeze
import OAI.Analysis.PDE.Nonlinear.Dilation

/-! Local regularity of a limit under uniformly Hölder, converging elliptic coefficients. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

theorem normalized_family_limit_C2 {m : ℕ} (hm : 3 ≤ m) {α ρ δ₀ M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hδ₀ : 0 < δ₀) (hM : 0 ≤ M)
    (A : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hA : ∀ h, ‖A h‖ ≤ M) (x₀ : EuclideanSpace ℝ (Fin m))
    (hAlim : Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀) (𝓝 0) (𝓝 1))
    (u : ℝ → EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : ∀ h, h ≠ 0 → |h| < δ₀ → ContDiff ℝ 2 (u h))
    (U : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (F : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (hU : ∀ h, h ≠ 0 → |h| < δ₀ → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (U h) x = u h x)
    (hV : ∀ h, h ≠ 0 → |h| < δ₀ → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (V h) x = fderiv ℝ (u h) x)
    {N₀ N₁ Nf : ℝ} (hUN : ∀ h, h ≠ 0 → |h| < δ₀ → ‖U h‖ ≤ N₀)
    (hVN : ∀ h, h ≠ 0 → |h| < δ₀ → ‖V h‖ ≤ N₁)
    (hFN : ∀ h, h ≠ 0 → |h| < δ₀ → ‖F h‖ ≤ Nf)
    (hPD : ∀ h, h ≠ 0 → |h| < δ₀ → ∀ x ∈ ball x₀ ρ, (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x).PosDef)
    (heq : ∀ h, h ≠ 0 → |h| < δ₀ → ∀ x ∈ ball x₀ ρ,
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h)) (u h) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F h) x)
    (w : EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : ∀ x, Tendsto (fun h => u h x) (𝓝[≠] 0) (𝓝 (w x))) :
    ContDiffAt ℝ 2 w x₀ := by
  classical
  let K := 2 * ((m : ℝ) * m) * ‖OAI.Analysis.PDE.Schauder.poissonHolderOperator hm hα hα1 2‖
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  obtain ⟨ε, hε, hεK⟩ := exists_pos_mul_lt (show (0 : ℝ) < 1 / 2 by norm_num) K
  obtain ⟨r, hr, hrρ, δ, hδ, hb⟩ := exists_uniform_small_localized_family
    hα hα1 hε (show 0 < ρ / 4 by positivity) hM A 1 x₀ hA hAlim
  let d := min δ δ₀
  have hd : 0 < d := lt_min hδ hδ₀
  let t : ℕ → ℝ := fun k => (d / 2) * (1 / ((k : ℝ) + 1))
  have htpos (k) : 0 < t k := by dsimp only [t]; positivity
  have htne (k) : t k ≠ 0 := ne_of_gt (htpos k)
  have htsmall (k) : |t k| < d := by
    rw [abs_of_pos (htpos k)]
    have hone : 1 / ((k : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      simp only [one_mul]
      linarith only [Nat.cast_nonneg (α := ℝ) k]
    have hh := mul_le_mul_of_nonneg_left hone (show 0 ≤ d / 2 by positivity)
    dsimp only [t]
    nlinarith only [hh, hd]
  have htδ (k) : |t k| < δ := (htsmall k).trans_le (min_le_left _ _)
  have htδ₀ (k) : |t k| < δ₀ := (htsmall k).trans_le (min_le_right _ _)
  have htlim : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun k => ?_)⟩
    · simpa only [mul_zero] using (tendsto_const_nhds (x := d / 2)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · simpa only [mem_compl_iff, mem_singleton_iff] using htne k
  choose B hBval hBnorm hBs using fun k => hb (t k) (htδ k)
  let φ := fun y : EuclideanSpace ℝ (Fin m) => x₀ + r • y
  have hnear (y : EuclideanSpace ℝ (Fin m)) (hy : ‖y‖ ≤ 2) : φ y ∈ ball x₀ ρ := by
    change ‖x₀ + r • y - x₀‖ < ρ
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hy hr.le).trans_lt (by linarith only [hrρ, hρ])
  have hBhalf (k) : 2 * ((m : ℝ) * m * ‖B k‖) * ‖OAI.Analysis.PDE.Schauder.poissonHolderOperator hm hα hα1 2‖ ≤ 1 / 2 := by
    calc
      _ = K * ‖B k‖ := by dsimp only [K]; ring
      _ ≤ K * ε := mul_le_mul_of_nonneg_left (hBnorm k).le hK
      _ ≤ 1 / 2 := hεK.le
  have hBPD (k) (y : EuclideanSpace ℝ (Fin m)) : (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B k) y).PosDef := by
    rw [hBval k y]
    apply OAI.Analysis.PDE.Schauder.posDef_identity_cutoff _ (OAI.Analysis.PDE.Schauder.radialCutoff_nonneg 1 y) (OAI.Analysis.PDE.Schauder.radialCutoff_le_one 1 y)
    intro hy
    apply hPD (t k) (htne k) (htδ₀ k) _ (hnear y ?_)
    by_contra hh
    exact hy (OAI.Analysis.PDE.Schauder.radialCutoff_zero zero_lt_one (by linarith only [lt_of_not_ge hh]))
  let χ : EuclideanSpace ℝ (Fin m) → ℝ := OAI.Analysis.PDE.Schauder.radialCutoff (1 / 4)
  have hχ : ContDiff ℝ 3 χ := (OAI.Analysis.PDE.Schauder.contDiff_radialCutoff _).of_le (by simp)
  have hχc : HasCompactSupport χ := OAI.Analysis.PDE.Schauder.hasCompactSupport_radialCutoff (by norm_num)
  have hχnorm (y) (hy : y ∈ Function.support χ) : ‖y‖ ≤ 1 / 2 := by
    change χ y ≠ 0 at hy
    by_contra hh
    exact hy (OAI.Analysis.PDE.Schauder.radialCutoff_zero (show (0 : ℝ) < 1 / 4 by norm_num) (by linarith only [lt_of_not_ge hh]))
  have hχR : tsupport χ ⊆ closedBall 0 2 := by
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    simp only [mem_closedBall, dist_zero_right]
    linarith only [hχnorm y hy]
  let u' := fun k y => u (t k) (φ y)
  let U' := fun k => OAI.Analysis.PDE.Schauder.holderAffinePullback hα.le (U (t k)) x₀ r
  let V' := fun k => r • OAI.Analysis.PDE.Schauder.holderAffinePullback hα.le (V (t k)) x₀ r
  let F' := fun k => r ^ 2 • OAI.Analysis.PDE.Schauder.holderAffinePullback hα.le (F (t k)) x₀ r
  have hu' (k) : ContDiff ℝ 2 (u' k) :=
    (hu (t k) (htne k) (htδ₀ k)).comp (contDiff_const.add (contDiff_id.const_smul r))
  have hU' (k) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (U' k) x = u' k x := hU (t k) (htne k) (htδ₀ k) (φ x)
  have hV' (k) (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (V' k) x = fderiv ℝ (u' k) x := by
    change r • OAI.Analysis.Normed.Function.Holder.HolderMap.value (V (t k)) (φ x) = _
    rw [hV (t k) (htne k) (htδ₀ k)]
    exact (fderiv_dilation _ ((hu (t k) (htne k) (htδ₀ k)).differentiable (by norm_num)) x₀ x r).symm
  have hUN' (k) : ‖U' k‖ ≤ (1 + |r| ^ α) * N₀ :=
    (norm_holderAffinePullback_le hα.le _ x₀ r).trans
      (mul_le_mul_of_nonneg_left (hUN (t k) (htne k) (htδ₀ k)) (by positivity))
  have hVN' (k) : ‖V' k‖ ≤ |r| * ((1 + |r| ^ α) * N₁) := by
    change ‖r • OAI.Analysis.PDE.Schauder.holderAffinePullback hα.le (V (t k)) x₀ r‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_holderAffinePullback_le hα.le _ x₀ r).trans
      (mul_le_mul_of_nonneg_left (hVN (t k) (htne k) (htδ₀ k)) (by positivity))) (abs_nonneg r)
  have hFN' (k) : ‖F' k‖ ≤ |r ^ 2| * ((1 + |r| ^ α) * Nf) := by
    change ‖r ^ 2 • OAI.Analysis.PDE.Schauder.holderAffinePullback hα.le (F (t k)) x₀ r‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_holderAffinePullback_le hα.le _ x₀ r).trans
      (mul_le_mul_of_nonneg_left (hFN (t k) (htne k) (htδ₀ k)) (by positivity))) (abs_nonneg _)
  have heq' (k) (y) (hy : y ∈ Function.support χ) :
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (fun z => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B k) z) (u' k) y = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F' k) y := by
    have hBid : 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value (B k) y = OAI.Analysis.Normed.Function.Holder.HolderMap.value (A (t k)) (φ y) := by
      rw [hBval k y, OAI.Analysis.PDE.Schauder.radialCutoff_one zero_lt_one (by linarith only [hχnorm y hy]), one_smul, sub_sub_cancel]
    calc
      _ = OAI.Analysis.PDE.Schauder.nondivergenceOperator (fun z => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A (t k)) (φ z)) (u' k) y := by
        exact congrArg (fun D : Matrix (Fin m) (Fin m) ℝ => ∑ i, ∑ j,
          D i j * fderiv ℝ (fderiv ℝ (u' k)) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) hBid
      _ = r ^ 2 * OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A (t k))) (u (t k)) (φ y) :=
        OAI.Analysis.PDE.Schauder.nondivergence_dilate _ _ (hu (t k) (htne k) (htδ₀ k)) x₀ y r
      _ = r ^ 2 * OAI.Analysis.Normed.Function.Holder.HolderMap.value (F (t k)) (φ y) := by
        rw [heq (t k) (htne k) (htδ₀ k) _ (hnear y (by linarith only [hχnorm y hy]))]
      _ = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F' k) y := rfl
  have hc := cutoff_limit_C2_of_uniform_equations hm hα hα1 u' hu' U' V' hU' hV' B F'
    hBs hBhalf hBPD (fun k => (hBnorm k).le) hFN' hUN' hVN' χ hχ hχc hχR heq'
    (fun y => w (φ y)) (fun y => (hw (φ y)).comp htlim)
  exact contDiffAt_of_dilated_cutoff w x₀ hr hc

end OAI.Analysis.PDE.Nonlinear
