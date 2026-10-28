import OAI.Analysis.PDE.Green.NormalPairing
import OAI.Analysis.PDE.Green.CellQuaternion

/-! The current Green estimate with the actual quaternionic lateral flux. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem quaternion_current_second_green_cell_bound {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    {ε G W : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hW : ∀ k : ℕ, (∫ x in euclideanCoordinates c ⁻¹' Icc a b,
      normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hrow : ∀ x, r x = 0 → ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ᵥ* A x‖ ≤ ε)
    (hgrad : ∀ x, r x = 0 → ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ ≤ G)
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u v)) :
    ‖(∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) -
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      v x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)‖ ≤ (n : ℝ) * ε * G * W := by
  have hK (p q : Fin n × Fin s) :
      ContDiff ℝ 1 (fun x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) :=
    (realCoefficientCLM e p q).contDiff.comp hA
  have hKs (p q : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q = OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) q p :=
    (congrFun (congrFun (OAI.Analysis.Calculus.Quaternion.realCoefficients_isSymm e (A x) (hAh x)) p) q).symm
  have hd (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (q : Fin n × Fin s) :
      (∑ p, fderiv ℝ (fun y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0 := by
    simp_rw [fderiv_realCoefficient e _ _ (hA.differentiable (by norm_num) x)]
    exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero e _ (hdiv x) q
  have hn (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (hx : r x = 0) :
      ‖normalRealFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) r u x‖ ≤
        (n : ℝ) * ε * G := normalRealFlux_bound e A r u x (hrow x hx) (hgrad x hx)
  have h := real_operator_second_green_cell_bound c a b hab
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) hK hu hv hr hKs hd hrne huz
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hε) hG) hW hn hface
  have hform (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hf : ContDiff ℝ 2 f) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e f x) =
      ∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q * OAI.Analysis.PDE.Dirichlet.realHessian f x p q :=
    realTrace_hessianMap (A x) e (OAI.Analysis.PDE.Dirichlet.realHessian f x) (OAI.Analysis.PDE.Dirichlet.realHessian_isSymm hf.contDiffAt)
  simpa only [hform u hu, hform v hv, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.PDE.Dirichlet.coordinateVector] using h

end OAI.Analysis.PDE.Green
