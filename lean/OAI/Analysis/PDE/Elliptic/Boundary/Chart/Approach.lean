import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Hessian
import OAI.Analysis.PDE.Elliptic.Boundary.FlatApproach

/-! Normal-component recovery for interior-to-boundary approach estimates.
The points need not both lie on the boundary. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

theorem chart_hessian_approach_from_remainder {n : ℕ} [Nonempty (Fin n)]
    {u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (hG : ContDiff ℝ 3 G)
    {v z z' : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} {V lam α M K D h : ℝ}
    (hv : ‖v‖ = 1) (hV : 0 < V) (hlam : 0 < lam) (hα : α ≤ 1)
    (_ : 0 ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hz : z ∈ closedHalfBall v) (hz' : z' ∈ closedHalfBall v)
    (hh : 0 < h) (hh1 : h ≤ 1) (hdist : ‖z - z'‖ ≤ h)
    (hu1 : ∀ y ∈ closedHalfBall v, ‖fderiv ℝ u (G y)‖ ≤ V)
    (hu2 : ∀ y ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (G y)‖ ≤ V)
    (hG1 : ∀ y ∈ closedHalfBall v, ‖fderiv ℝ G y‖ ≤ V)
    (hG2 : ∀ y ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 G y‖ ≤ V)
    (hG3 : ∀ y ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 3 G y‖ ≤ V)
    (Q : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (hQ : ‖Q‖ ≤ V)
    (hJQ : (fderiv ℝ G z).comp Q = ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4))
    (hQJ : Q.comp (fderiv ℝ G z) = ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4))
    (hrem : ∃ t : ℝ,
      ‖(fderiv ℝ (gradient (fun y => u (G y) - B (G y))) z -
        fderiv ℝ (gradient (fun y => u (G y) - B (G y))) z') -
          t • rankOne ℝ v v‖ ≤ M * h ^ α)
    (hBack : ‖fderiv ℝ (gradient (fun y => B (G y))) z -
      fderiv ℝ (gradient (fun y => B (G y))) z'‖ ≤ K * ‖z - z'‖)
    (hpos : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))).PosDef)
    (hpos' : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z'))).PosDef)
    (hlo : ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z)) w))
    (hlo' : ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z')) w))
    (hA : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))‖ ≤ V)
    (hA' : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z'))‖ ≤ V)
    (hlog : |Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z')))| ≤ D * ‖z - z'‖) :
    let R := 3 * V ^ 5 + V ^ 4 + V ^ 2 * (M + K)
    ‖fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')‖ ≤
      (V ^ 2 * ((D + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * V * R) / (lam / V ^ 2)) + R) *
        h ^ α := by
  have hdist_s : ‖z - z'‖ ≤ h ^ α :=
    hdist.trans (Real.self_le_rpow_of_le_one hh.le hh1 hα)
  have hbackground := hBack.trans (mul_le_mul_of_nonneg_left hdist_s hK)
  obtain ⟨t, ht⟩ := hrem
  have hpu : ContDiff ℝ 2 (fun y => u (G y)) := hu.comp (hG.of_le (by norm_num))
  have hpB : ContDiff ℝ 2 (fun y => B (G y)) := hB.comp (hG.of_le (by norm_num))
  have hid : (fderiv ℝ (gradient (fun y => u (G y))) z -
      fderiv ℝ (gradient (fun y => u (G y))) z') - t • rankOne ℝ v v =
      ((fderiv ℝ (gradient (fun y => u (G y) - B (G y))) z -
        fderiv ℝ (gradient (fun y => u (G y) - B (G y))) z') - t • rankOne ℝ v v) +
      (fderiv ℝ (gradient (fun y => B (G y))) z - fderiv ℝ (gradient (fun y => B (G y))) z') := by
    rw [hessianOperator_sub hpu hpB, hessianOperator_sub hpu hpB]
    abel
  have ht' : ‖(fderiv ℝ (gradient (fun y => u (G y))) z -
      fderiv ℝ (gradient (fun y => u (G y))) z') - t • rankOne ℝ v v‖ ≤ (M + K) * h ^ α := by
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add ht hbackground).trans_eq (by ring))
  have herr := chart_hessian_change_error_bound hu hG (convex_closedHalfBall v) hV.le
    hu1 hu2 hG1 hG2 hG3 hz hz' Q hQ hJQ
  have herr' := herr.trans (mul_le_mul_of_nonneg_left hdist_s (by positivity : 0 ≤ 3 * V ^ 5 + V ^ 4))
  have hlog' := hlog.trans (mul_le_mul_of_nonneg_left hdist_s hD)
  have hb := log_hessian_chart_recovery hu hu (G z') (G z) v Q (fderiv ℝ G z)
    (fderiv ℝ (gradient (fun y => u (G y))) z - fderiv ℝ (gradient (fun y => u (G y))) z')
    hlam hV.le hV hv hQJ hQ (hG1 z hz) hpos' hpos hlo' hlo hA' hA herr' ht' hlog'
  dsimp only
  convert hb using 1 ; ring

end OAI.Analysis.PDE.Elliptic
