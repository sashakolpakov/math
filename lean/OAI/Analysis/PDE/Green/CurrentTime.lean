import OAI.Analysis.PDE.Green.SmallQuaternion
import OAI.Analysis.PDE.Green.TimeTest

/-! The quantitative current Green identity for tests in the extended time. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem current_time_test_bound {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (c : (Fin (n + 1) × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → Matrix (Fin (n + 1)) (Fin (n + 1)) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A) (hAh : ∀ x, (A x).IsHermitian)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hu : ContDiff ℝ 2 u) (hη : ContDiff ℝ 2 η) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    {ε G W : ℝ} (hε : 0 ≤ ε) (hG : 0 ≤ G)
    (hW : ∀ k : ℕ, (∫ x in euclideanCoordinates c ⁻¹' Icc a b,
      normalCutoffWeight (r x) k * ‖η (timeProjection n s x)‖) ≤ W)
    (hrow : ∀ x, r x = 0 → ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ᵥ* A x‖ ≤ ε)
    (hgrad : ∀ x, r x = 0 → ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ ≤ G)
    (hface : CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u (fun x => η (timeProjection n s x)))) :
    ‖(∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      Laplacian.laplacian η (timeProjection n s x) * (u x * (A x 0 0).re)) -
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      η (timeProjection n s x) * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)‖ ≤
        (n + 1 : ℕ) * ε * G * W := by
  have h := quaternion_current_second_green_cell_bound e c a b hab hA hAh hdiv hu
    (hη.comp (timeProjection n s).contDiff) hr hrne huz hε hG hW hrow hgrad hface
  have hid (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) :
      u x * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => η (timeProjection n s y)) x) =
        Laplacian.laplacian η (timeProjection n s x) * (u x * (A x 0 0).re) := by
    rw [realTrace_mul_time_test e he hη]
    ring
  simpa only [Function.comp_def, hid] using h

end OAI.Analysis.PDE.Green
