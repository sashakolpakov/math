import OAI.Analysis.PDE.Concentration.CurrentCovariance

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion
open scoped Matrix

theorem second_fderiv_comp_linear_on
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : F → ℝ} {U : Set F} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : E} (hx : L x ∈ U) (v w : E) :
    (fderiv ℝ (fderiv ℝ (f ∘ L)) x v) w =
      (fderiv ℝ (fderiv ℝ f) (L x) (L v)) (L w) := by
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 2 hpre hx,
    iteratedFDerivWithin_of_isOpen 2 hU hx] at h
  have he := congrArg (fun T => T ![v, w]) h
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem realHessian_linear_comp_on {n s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (Q : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (hx : OAI.Analysis.PDE.Dirichlet.realMatrixAction Q x ∈ U) :
    OAI.Analysis.PDE.Dirichlet.realHessian (f ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction Q) x =
      Qᵀ * OAI.Analysis.PDE.Dirichlet.realHessian f (OAI.Analysis.PDE.Dirichlet.realMatrixAction Q x) * Q := by
  apply Matrix.ext
  intro i j
  change (fderiv ℝ (fderiv ℝ (f ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction Q)) x (OAI.Analysis.PDE.Dirichlet.coordinateVector i))
    (OAI.Analysis.PDE.Dirichlet.coordinateVector j) = _
  rw [second_fderiv_comp_linear_on (OAI.Analysis.PDE.Dirichlet.realMatrixAction Q) hU hf hx,
    ← OAI.Analysis.PDE.Dirichlet.realHessian_bilinear]
  simp only [realMatrixAction_coordinateVector, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem quaternionHessian_slot_comp_on {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (R : Matrix (Fin n) (Fin n) ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hx : OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x ∈ U) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (f ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R)) x =
      (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * OAI.Analysis.PDE.Dirichlet.quaternionHessian e f (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x) * OAI.Analysis.PDE.Dirichlet.realLift R := by
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian
  rw [realHessian_linear_comp_on hU hf _ _ hx, hessianMap_slotLift_congruence]

end OAI.Analysis.PDE.Concentration
