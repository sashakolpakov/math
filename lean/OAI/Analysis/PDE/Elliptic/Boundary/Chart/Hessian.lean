import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Error
import OAI.Analysis.PDE.Elliptic.Boundary.BackgroundRemainder
import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Mixed

/-! Recovery of the full physical Hessian from the proved mixed boundary
estimate.  The change-of-coordinate and background terms are lower order. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ComplexOrder

theorem chart_hessian_holder_from_mixed {n : ℕ} [Nonempty (Fin n)]
    {u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (hG : ContDiff ℝ 3 G)
    {v z z' : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} {V lam α M K D : ℝ}
    (hv : ‖v‖ = 1) (hV : 0 < V) (hlam : 0 < lam) (hα : α ≤ 1)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hz : ‖z‖ ≤ 1 / 8) (hz' : ‖z'‖ ≤ 1 / 8)
    (hvz : inner ℝ v z = 0) (hvz' : inner ℝ v z' = 0)
    (hu1 : ∀ y ∈ closedHalfBall v, ‖fderiv ℝ u (G y)‖ ≤ V)
    (hu2 : ∀ y ∈ closedHalfBall v, ‖fderiv ℝ (gradient u) (G y)‖ ≤ V)
    (hG1 : ∀ y ∈ closedHalfBall v, ‖fderiv ℝ G y‖ ≤ V)
    (hG2 : ∀ y ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 2 G y‖ ≤ V)
    (hG3 : ∀ y ∈ closedHalfBall v, ‖iteratedFDeriv ℝ 3 G y‖ ≤ V)
    (Q : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hQ : ‖Q‖ ≤ V)
    (hJQ : (fderiv ℝ G z).comp Q = ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4))
    (hQJ : Q.comp (fderiv ℝ G z) = ContinuousLinearMap.id ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4))
    (hzero : ∀ y, ‖y‖ ≤ 1 → inner ℝ v y = 0 → u (G y) = B (G y))
    (hm : ∀ e, ‖e‖ ≤ 1 → inner ℝ v e = 0 →
      |fderiv ℝ (fderiv ℝ (fun y => u (G y) - B (G y))) z v e -
        fderiv ℝ (fderiv ℝ (fun y => u (G y) - B (G y))) z' v e| ≤ M * ‖z - z'‖ ^ α)
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
    let R := 3 * V ^ 5 + V ^ 4 + V ^ 2 * (4 * M + K)
    ‖fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')‖ ≤
      (V ^ 2 * ((D + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * V * R) / (lam / V ^ 2)) + R) *
        ‖z - z'‖ ^ α := by
  have hzc : z ∈ closedHalfBall v := ⟨by linarith, hvz.ge⟩
  have hz'c : z' ∈ closedHalfBall v := ⟨by linarith, hvz'.ge⟩
  have hdist : ‖z - z'‖ ≤ 1 := (norm_sub_le _ _).trans (by linarith)
  have hpow := Real.self_le_rpow_of_le_one (norm_nonneg (z - z')) hdist hα
  let s := ‖z - z'‖ ^ α
  have hs : 0 ≤ s := Real.rpow_nonneg (norm_nonneg _) _
  have hdist_s : ‖z - z'‖ ≤ s := hpow
  have hbackground : ‖fderiv ℝ (gradient (fun y => B (G y))) z -
      fderiv ℝ (gradient (fun y => B (G y))) z'‖ ≤ K * s :=
    hBack.trans (mul_le_mul_of_nonneg_left hdist_s hK)
  obtain ⟨t, ht⟩ := flat_hessian_remainder_with_background
    (u := fun y => u (G y)) (B := fun y => B (G y))
    (hu.comp (hG.of_le (by norm_num))) (hB.comp (hG.of_le (by norm_num))) hv
    (by linarith) (by linarith) hvz hvz' hzero (mul_nonneg hM hs) hm hbackground
  have ht' : ‖(fderiv ℝ (gradient (fun y => u (G y))) z -
      fderiv ℝ (gradient (fun y => u (G y))) z') - t • rankOne ℝ v v‖ ≤ (4 * M + K) * s := by
    convert ht using 1 ; dsimp [s] ; ring
  have herr := chart_hessian_change_error_bound hu hG (convex_closedHalfBall v) hV.le
    hu1 hu2 hG1 hG2 hG3 hzc hz'c Q hQ hJQ
  have herr' := herr.trans (mul_le_mul_of_nonneg_left hdist_s (by positivity : 0 ≤ 3 * V ^ 5 + V ^ 4))
  have hlog' := hlog.trans (mul_le_mul_of_nonneg_left hdist_s hD)
  have hb := log_hessian_chart_recovery hu hu (G z') (G z) v Q (fderiv ℝ G z)
    (fderiv ℝ (gradient (fun y => u (G y))) z - fderiv ℝ (gradient (fun y => u (G y))) z')
    hlam hV.le hV hv hQJ hQ (hG1 z hzc) hpos' hpos hlo' hlo hA' hA herr' ht' hlog'
  dsimp only
  convert hb using 1 ; dsimp [s] ; ring

end OAI.Analysis.PDE.Elliptic
