import OAI.Analysis.PDE.Schauder.Dirichlet.AffineDrift

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_scaled_affine_forcing_le {α r N : ℝ} (hα : 0 ≤ α)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (_ : 0 ≤ N)
    (F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (x₀ : E) (T : E →L[ℝ] E) (hT : ‖T‖ ≤ N) :
    ‖(r^2) • holderLinearAffinePullback hα F x₀ T‖ ≤ (1 + N^α) * ‖F‖ := by
  have hpull := OAI.Analysis.PDE.Nonlinear.norm_holderLinearAffinePullback_le hα F x₀ T
  have hr2 : |r^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ 1 * ((1 + N^α) * ‖F‖) := by
      apply mul_le_mul hr2 _ (norm_nonneg _) (by positivity)
      exact hpull.trans (by gcongr)
    _ = _ := one_mul _

theorem norm_scaled_affine_drift_le {α r N J Nb : ℝ} (hα : 0 ≤ α)
    (hN : 0 ≤ N) (hJ : 0 ≤ J) (_ : 0 ≤ Nb)
    (b : OAI.Analysis.Normed.Function.Holder.HolderMap E E α) (hb : ‖b‖ ≤ Nb) (x₀ : E) (T : E ≃L[ℝ] E)
    (hT : ‖T.toContinuousLinearMap‖ ≤ N) (hTi : ‖T.symm.toContinuousLinearMap‖ ≤ J) :
    ‖affineDriftHolder hα b x₀ T (r^2)‖ ≤ r^2 * J * (1 + N^α) * Nb := by
  apply (norm_affineDriftHolder_le hα b x₀ T (r^2)).trans
  rw [abs_of_nonneg (sq_nonneg r)]
  gcongr

theorem schauder_pullback_constant_bound {K Q D ε H M F F' : ℝ}
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hF : 0 ≤ F) (hF' : F' ≤ Q*F) :
    K * ((ε/(K+1))*H + D*(F'+M)) ≤ ε*H + ((K+1)*D*(Q+1))*(F+M) := by
  have hKe : K * (ε/(K+1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hforcing : K*D*(F'+M) ≤ ((K+1)*D*(Q+1))*(F+M) := by
    calc
      _ ≤ K*D*(Q*F+M) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (K+1)*D*(Q*F+M) := by gcongr; linarith
      _ ≤ (K+1)*D*((Q+1)*(F+M)) := by
        gcongr
        nlinarith
      _ = _ := by ring
  nlinarith [mul_le_mul_of_nonneg_right hKe hH]

end OAI.Analysis.PDE.Schauder
