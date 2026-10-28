import OAI.Analysis.PDE.Elliptic.Boundary.LogRecovery
import OAI.Analysis.PDE.Elliptic.Boundary.Normal

/-! Normal-normal recovery is stable under a bounded inverse chart and an
explicit lower-order change-of-coordinate error. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def hessianCongruence (Q H : E →L[ℝ] E) : E →L[ℝ] E := Q.adjoint.comp (H.comp Q)

theorem hessianCongruence_rankOne (Q : E →L[ℝ] E) (v : E) :
    hessianCongruence Q (rankOne ℝ v v) = rankOne ℝ (Q.adjoint v) (Q.adjoint v) := by
  ext x
  simp only [hessianCongruence, ContinuousLinearMap.comp_apply, rankOne_apply, map_smul]
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem hessianCongruence_norm (Q H : E →L[ℝ] E) :
    ‖hessianCongruence Q H‖ ≤ ‖Q‖ ^ 2 * ‖H‖ := by
  apply (Q.adjoint.opNorm_comp_le (H.comp Q)).trans
  rw [ContinuousLinearMap.adjoint.norm_map]
  have hh := mul_le_mul_of_nonneg_left (H.opNorm_comp_le Q) (norm_nonneg Q)
  nlinarith

theorem hessianCongruence_sub (Q H K : E →L[ℝ] E) :
    hessianCongruence Q (H - K) = hessianCongruence Q H - hessianCongruence Q K := by
  ext x; simp [hessianCongruence]

theorem hessianCongruence_smul (Q H : E →L[ℝ] E) (t : ℝ) :
    hessianCongruence Q (t • H) = t • hessianCongruence Q H := by
  ext x; simp [hessianCongruence]

theorem chart_rankOne_remainder_bound (D H Q : E →L[ℝ] E) (v : E) (t : ℝ)
    {C Err Rem : ℝ} (hC : 0 ≤ C) (hQ : ‖Q‖ ≤ C)
    (hErr : ‖D - hessianCongruence Q H‖ ≤ Err)
    (hRem : ‖H - t • rankOne ℝ v v‖ ≤ Rem) :
    ‖D - t • rankOne ℝ (Q.adjoint v) (Q.adjoint v)‖ ≤ Err + C ^ 2 * Rem := by
  have hid : D - t • rankOne ℝ (Q.adjoint v) (Q.adjoint v) =
      (D - hessianCongruence Q H) + hessianCongruence Q (H - t • rankOne ℝ v v) := by
    rw [hessianCongruence_sub, hessianCongruence_smul, hessianCongruence_rankOne]
    abel
  rw [hid]
  apply (norm_add_le _ _).trans
  apply add_le_add hErr
  apply (hessianCongruence_norm Q _).trans
  exact mul_le_mul (by nlinarith [norm_nonneg Q]) hRem (norm_nonneg _) (sq_nonneg C)

theorem log_hessian_chart_recovery {n : ℕ} {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x y v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (Q J H : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) {t lam N C Err Rem F : ℝ}
    (hlam : 0 < lam) (hN : 0 ≤ N) (hC : 0 < C) (hv : ‖v‖ = 1)
    (hQJ : Q.comp J = ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4))
    (hQ : ‖Q‖ ≤ C) (hJ : ‖J‖ ≤ C)
    (hfx : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hgy : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)).PosDef)
    (hA : ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) w))
    (hB : ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y) w))
    (hAn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)‖ ≤ N)
    (hBn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)‖ ≤ N)
    (hErr : ‖(fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x) - hessianCongruence Q H‖ ≤ Err)
    (hRem : ‖H - t • rankOne ℝ v v‖ ≤ Rem)
    (hlog : |Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))| ≤ F) :
    ‖fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x‖ ≤
      C ^ 2 * ((F + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * N * (Err + C ^ 2 * Rem)) /
        (lam / C ^ 2)) + (Err + C ^ 2 * Rem) := by
  let ξ := Q.adjoint v
  let R := (fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x) - t • rankOne ℝ ξ ξ
  have hR : ‖R‖ ≤ Err + C ^ 2 * Rem := chart_rankOne_remainder_bound _ H Q v t hC.le hQ hErr hRem
  have hadj : J.adjoint.comp Q.adjoint = ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) := by
    have hh := congrArg (ContinuousLinearMap.adjoint :
      (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) → _) hQJ
    simpa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using hh
  have hlo : 1 ≤ C * ‖ξ‖ := by
    simpa only [hv] using inverse_lower_norm Q.adjoint J.adjoint hadj
      (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hJ) v
  have hhi : ‖ξ‖ ≤ C := by
    have hh := (Q.adjoint.le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hQ) (norm_nonneg v))
    simpa only [hv, mul_one] using hh
  have hc : lam / C ^ 2 ≤ lam * ‖ξ‖ ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hC)).mpr
    have hh : 1 ≤ C ^ 2 * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg (C * ‖ξ‖ - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hh hlam.le]
  have ht := log_hessian_normal_recovery hf hg x y ξ R (div_pos hlam (sq_pos_of_pos hC)) hN
    hfx hgy (hc.trans (hA ξ)) (hc.trans (hB ξ)) hAn hBn (by dsimp [R]; abel)
  have ht' : |t| ≤ (F + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * N * (Err + C ^ 2 * Rem)) /
      (lam / C ^ 2) := ht.trans (div_le_div_of_nonneg_right
        (add_le_add hlog (mul_le_mul_of_nonneg_left hR (by positivity))) (by positivity))
  have hdecomp : fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x = t • rankOne ℝ ξ ξ + R := by
    dsimp [R]; abel
  rw [hdecomp]
  apply (norm_add_le _ _).trans
  apply add_le_add _ hR
  rw [norm_smul, norm_rankOne]
  have hs : ‖ξ‖ * ‖ξ‖ ≤ C ^ 2 := by nlinarith [norm_nonneg ξ]
  exact (mul_le_mul_of_nonneg_left hs (abs_nonneg t)).trans
    (by simpa [mul_comm] using mul_le_mul_of_nonneg_left ht' (sq_nonneg C))

end OAI.Analysis.PDE.Elliptic
