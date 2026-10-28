import OAI.Analysis.PDE.Nonlinear.NormalizedLimit
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.EllipticLocal

/-! The finite-difference limit theorem for arbitrary positive frozen coefficients. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

local instance ellipticLimitMatrixMapNormedGroup (m : ℕ) :
    NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup ((Fin m → Fin m → ℝ) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem elliptic_family_limit_C2 {m : ℕ} (hm : 3 ≤ m) {α ρ δ M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (A : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hA : ∀ h, ‖A h‖ ≤ M) (x₀ : EuclideanSpace ℝ (Fin m))
    (A₀ : Matrix (Fin m) (Fin m) ℝ) (hA₀ : A₀.PosDef)
    (hAlim : Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀) (𝓝 0) (𝓝 A₀))
    (u : ℝ → EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : ∀ h, h ≠ 0 → |h| < δ → ContDiff ℝ 2 (u h))
    (U : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (F : ℝ → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (hU : ∀ h, h ≠ 0 → |h| < δ → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (U h) x = u h x)
    (hV : ∀ h, h ≠ 0 → |h| < δ → ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (V h) x = fderiv ℝ (u h) x)
    {N₀ N₁ Nf : ℝ} (hUN : ∀ h, h ≠ 0 → |h| < δ → ‖U h‖ ≤ N₀)
    (hVN : ∀ h, h ≠ 0 → |h| < δ → ‖V h‖ ≤ N₁)
    (hFN : ∀ h, h ≠ 0 → |h| < δ → ‖F h‖ ≤ Nf)
    (hPD : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ ball x₀ ρ, (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x).PosDef)
    (heq : ∀ h, h ≠ 0 → |h| < δ → ∀ x ∈ ball x₀ ρ,
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h)) (u h) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F h) x)
    (w : EuclideanSpace ℝ (Fin m) → ℝ)
    (hw : ∀ x, Tendsto (fun h => u h x) (𝓝[≠] 0) (𝓝 (w x))) :
    ContDiffAt ℝ 2 w x₀ := by
  obtain ⟨L, P, Q, hP, hQ, hPQ, hQP, hQA⟩ := OAI.Analysis.PDE.Schauder.exists_normalization_matrices A₀ hA₀
  let φ := fun y : EuclideanSpace ℝ (Fin m) => x₀ + L y
  let ρ' := ρ / (‖L.toContinuousLinearMap‖ + 1)
  have hρ' : 0 < ρ' := div_pos hρ (by positivity)
  have hnear (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ ball 0 ρ') : φ y ∈ ball x₀ ρ := by
    have hy' : ‖y‖ < ρ' := by simpa only [mem_ball, dist_zero_right] using hy
    change ‖x₀ + L y - x₀‖ < ρ
    rw [add_sub_cancel_left]
    calc
      _ ≤ ‖L.toContinuousLinearMap‖ * ‖y‖ := L.toContinuousLinearMap.le_opNorm y
      _ ≤ (‖L.toContinuousLinearMap‖ + 1) * ‖y‖ := by nlinarith only [norm_nonneg y]
      _ < (‖L.toContinuousLinearMap‖ + 1) * ρ' := mul_lt_mul_of_pos_left hy' (by positivity)
      _ = ρ := by dsimp only [ρ']; field_simp
  let c := 1 + ‖L.toContinuousLinearMap‖ ^ α
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  let T := OAI.Analysis.PDE.Schauder.matrixCongruenceCLM Q
  let J : (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ _ _ _).flip L.toContinuousLinearMap
  let A' := fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM T (OAI.Analysis.PDE.Schauder.holderLinearAffinePullback hα.le (A h) x₀ L.toContinuousLinearMap)
  let U' := fun h => OAI.Analysis.PDE.Schauder.holderLinearAffinePullback hα.le (U h) x₀ L.toContinuousLinearMap
  let V' := fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM J (OAI.Analysis.PDE.Schauder.holderLinearAffinePullback hα.le (V h) x₀ L.toContinuousLinearMap)
  let F' := fun h => OAI.Analysis.PDE.Schauder.holderLinearAffinePullback hα.le (F h) x₀ L.toContinuousLinearMap
  let u' := fun h y => u h (φ y)
  have hA' (h) : ‖A' h‖ ≤ ‖T‖ * (c * M) := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le T _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
    exact (norm_holderLinearAffinePullback_le hα.le _ x₀ _).trans
      (mul_le_mul_of_nonneg_left (hA h) hc)
  have hAlim' : Tendsto (fun h => OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h) 0) (𝓝 0) (𝓝 1) := by
    have ht := T.continuous.continuousAt.tendsto.comp hAlim
    have he (h) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h) 0 = T (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) x₀) := by
      change T (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h) (x₀ + L 0)) = _
      rw [map_zero, add_zero]
    simp_rw [he]
    have hT : T A₀ = 1 := hQA
    simpa only [Function.comp_def, hT] using ht
  have hU' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (U' h) y = u' h y :=
    hU h hh hd (φ y)
  have hV' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (V' h) y = fderiv ℝ (u' h) y := by
    change (OAI.Analysis.Normed.Function.Holder.HolderMap.value (V h) (φ y)).comp L.toContinuousLinearMap = _
    rw [hV h hh hd]
    simpa only [φ, u'] using!
      (fderiv_linearAffine _ ((hu h hh hd).differentiable (by norm_num)) x₀ y L.toContinuousLinearMap).symm
  have hUN' (h) (hh : h ≠ 0) (hd : |h| < δ) : ‖U' h‖ ≤ c * N₀ :=
    (norm_holderLinearAffinePullback_le hα.le _ x₀ _).trans
      (mul_le_mul_of_nonneg_left (hUN h hh hd) hc)
  have hVN' (h) (hh : h ≠ 0) (hd : |h| < δ) : ‖V' h‖ ≤ ‖J‖ * (c * N₁) := by
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le J _).trans (mul_le_mul_of_nonneg_left
      ((norm_holderLinearAffinePullback_le hα.le _ x₀ _).trans
        (mul_le_mul_of_nonneg_left (hVN h hh hd) hc)) (norm_nonneg J))
  have hFN' (h) (hh : h ≠ 0) (hd : |h| < δ) : ‖F' h‖ ≤ c * Nf :=
    (norm_holderLinearAffinePullback_le hα.le _ x₀ _).trans
      (mul_le_mul_of_nonneg_left (hFN h hh hd) hc)
  have hPD' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) (hy : y ∈ ball 0 ρ') :
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h) y).PosDef :=
    OAI.Analysis.PDE.Schauder.posDef_congruence_of_inverse P Q _ hPQ hQP (hPD h hh hd _ (hnear y hy))
  have heq' (h) (hh : h ≠ 0) (hd : |h| < δ) (y) (hy : y ∈ ball 0 ρ') :
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h)) (u' h) y = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F' h) y := by
    have ht := OAI.Analysis.PDE.Schauder.nondivergence_conjugated_affine (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h)) (u h) (hu h hh hd) P Q hPQ x₀ y
    have htransport : OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A' h)) (u' h) y =
        OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value (A h)) (u h) (φ y) := by
      simpa only [hP] using! ht
    rw [htransport]
    exact heq h hh hd _ (hnear y hy)
  have hreg := normalized_family_limit_C2 hm hα hα1 hρ' hδ
    (mul_nonneg (norm_nonneg T) (mul_nonneg hc hM)) A' hA' 0 hAlim'
    u' (fun h hh hd => (hu h hh hd).comp (contDiff_const.add L.contDiff))
    U' V' F' hU' hV' hUN' hVN' hFN' hPD' heq' (fun y => w (φ y)) (fun y => hw (φ y))
  exact contDiffAt_of_linearAffine w x₀ L hreg

end OAI.Analysis.PDE.Nonlinear
