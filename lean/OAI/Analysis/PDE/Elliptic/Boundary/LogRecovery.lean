import OAI.Analysis.PDE.Elliptic.Boundary.EllipticRecovery
import OAI.Analysis.PDE.Dirichlet.LogSupport
import OAI.Analysis.PDE.Dirichlet.RealOperator

/-! The normal-normal recovery inequality for the actual Moore determinant. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore InnerProductSpace
open scoped Matrix ComplexOrder

theorem log_hessian_support {n : ℕ} {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hfx : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hgy : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)).PosDef) :
    Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) ≤
      traceRight (fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x)
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) := by
  have hsym : (fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric :=
    (fderiv_gradient_isSymmetric hg y).sub (fderiv_gradient_isSymmetric hf x)
  change _ ≤ traceRight _ (symmetricTraceDual _ _)
  rw [symmetricTraceDual_represents _ _ _ hsym, OAI.Analysis.PDE.Dirichlet.logOperatorFunctional_apply]
  have he : OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots
      (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix (fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x)) =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y - OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x := by
    rw [map_sub, OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix_fderiv_gradient hg,
      OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix_fderiv_gradient hf]
    exact (OAI.Analysis.PDE.Dirichlet.hessianMatrixLinear OAI.Analysis.Calculus.Quaternion.fourSlots).map_sub (OAI.Analysis.PDE.Dirichlet.realHessian g y) (OAI.Analysis.PDE.Dirichlet.realHessian f x)
  rw [he]
  exact OAI.Analysis.PDE.Dirichlet.log_mooreDet_support _ _ hfx hgy

theorem log_hessian_normal_recovery {n : ℕ} {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x y v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (R : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) {t lam N : ℝ}
    (hlam : 0 < lam) (hN : 0 ≤ N)
    (hfx : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hgy : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)).PosDef)
    (hA : lam ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) v))
    (hB : lam ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y) v))
    (hAn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)‖ ≤ N)
    (hBn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)‖ ≤ N)
    (hdecomp : fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x = t • rankOne ℝ v v + R) :
    |t| ≤ (|Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))| +
      Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * N * ‖R‖) / lam := by
  apply (le_div_iff₀ hlam).mpr
  have ha := log_hessian_support hf hg x y hfx hgy
  have hb := log_hessian_support hg hf y x hgy hfx
  rw [hdecomp] at ha
  have hreverse : fderiv ℝ (gradient f) x - fderiv ℝ (gradient g) y =
      -(t • rankOne ℝ v v + R) := by rw [← hdecomp]; abel
  rw [hreverse] at hb
  have hb' : -(Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))) ≤
      traceRight (-(t • rankOne ℝ v v + R))
        (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)) := by linarith
  have hh := normal_entry_recovery _ _ R v hlam.le hN hA hB hAn hBn ha hb'
  nlinarith

theorem log_hessian_full_recovery {n : ℕ} {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x y v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (R : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) {t lam N : ℝ}
    (hlam : 0 < lam) (hN : 0 ≤ N) (hv : ‖v‖ = 1)
    (hfx : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hgy : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)).PosDef)
    (hA : lam ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) v))
    (hB : lam ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y) v))
    (hAn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)‖ ≤ N)
    (hBn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)‖ ≤ N)
    (hdecomp : fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x = t • rankOne ℝ v v + R) :
    ‖fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x‖ ≤
      (|Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)) -
        Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))| +
        Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * N * ‖R‖) / lam + ‖R‖ := by
  have ht := log_hessian_normal_recovery hf hg x y v R hlam hN hfx hgy hA hB hAn hBn hdecomp
  rw [hdecomp]
  apply (norm_add_le _ _).trans
  simpa [norm_smul, norm_rankOne, hv] using add_le_add_right ht ‖R‖

/-- Any Hölder bound for the tangential/mixed remainder and for log density
therefore controls the entire real Hessian, including its normal entry. -/
theorem log_hessian_holder_recovery {n : ℕ} {f g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x y v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (R : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) {t lam N K F s : ℝ}
    (hlam : 0 < lam) (hN : 0 ≤ N) (hv : ‖v‖ = 1)
    (hfx : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)).PosDef)
    (hgy : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)).PosDef)
    (hA : lam ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x) v))
    (hB : lam ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y) v))
    (hAn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)‖ ≤ N)
    (hBn : ‖OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)‖ ≤ N)
    (hdecomp : fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x = t • rankOne ℝ v v + R)
    (hR : ‖R‖ ≤ K * s)
    (hlog : |Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g y)) -
      Real.log (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x))| ≤ F * s) :
    ‖fderiv ℝ (gradient g) y - fderiv ℝ (gradient f) x‖ ≤
      ((F + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * N * K) / lam + K) * s := by
  apply (log_hessian_full_recovery hf hg x y v R hlam hN hv hfx hgy hA hB hAn hBn hdecomp).trans
  calc
    _ ≤ (F * s + Module.finrank ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) * N * (K * s)) / lam + K * s := by
      gcongr
    _ = _ := by ring

end OAI.Analysis.PDE.Elliptic
