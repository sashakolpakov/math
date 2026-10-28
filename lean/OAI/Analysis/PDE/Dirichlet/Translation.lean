import OAI.Analysis.PDE.Dirichlet.Boundary.Patch

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

section Normed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem second_fderiv_translation (f : E → F) (a x : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ f (a + y))) x = fderiv ℝ (fderiv ℝ f) (a + x) := by
  have hD : fderiv ℝ (fun y ↦ f (a + y)) = fun y ↦ fderiv ℝ f (a + y) :=
    funext fun y ↦ fderiv_comp_add_left a
  rw [hD, fderiv_comp_add_left]

theorem affineDerivative_translation (f : E → ℝ) (a e x : E) (A : E →L[ℝ] E) :
    affineDerivative (fun y ↦ f (a + y)) e A x =
      affineDerivative f (e - A a) A (a + x) := by
  simp only [affineDerivative, fderiv_comp_add_left]
  have heq : e - A a + A (a + x) = e + A x := by rw [map_add]; abel
  rw [heq]

end Normed

theorem quaternionHessian_translation {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (f : CoordinateSpace n s → ℝ) (a x : CoordinateSpace n s) :
    quaternionHessian e (fun y ↦ f (a + y)) x = quaternionHessian e f (a + x) := by
  have heq : realHessian (fun y ↦ f (a + y)) x = realHessian f (a + x) := by
    apply Matrix.ext
    intro i j
    change fderiv ℝ (fderiv ℝ (fun y ↦ f (a + y))) x (coordinateVector i) (coordinateVector j) = _
    rw [second_fderiv_translation]
    rfl
  exact congrArg (OAI.Analysis.Calculus.Quaternion.hessianMap e) heq

theorem mooreLinearization_translation {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (f : CoordinateSpace n 4 → ℝ) (a x : CoordinateSpace n 4) :
    mooreLinearization (fun y ↦ A (a + y)) (fun y ↦ f (a + y)) x =
      mooreLinearization A f (a + x) := by
  simp only [mooreLinearization, quaternionHessian_translation]

end OAI.Analysis.PDE.Dirichlet
