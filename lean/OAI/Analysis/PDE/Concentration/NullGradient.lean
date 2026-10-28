import OAI.Analysis.PDE.Concentration.NullHessian
import OAI.Analysis.PDE.Concentration.Physical.Vector

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion
open scoped Matrix

theorem quaternionGradient_slot_comp {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (R : Matrix (Fin n) (Fin n) ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (hf : DifferentiableAt ℝ f (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x)) :
    OAI.Analysis.PDE.Dirichlet.quaternionGradient e (f ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R)) x =
      (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ *ᵥ OAI.Analysis.PDE.Dirichlet.quaternionGradient e f (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x) := by
  have hd := (hf.hasFDerivAt.comp x (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R)).hasFDerivAt).fderiv
  funext a
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionGradient, OAI.Analysis.Calculus.Quaternion.gradientMap, OAI.Analysis.PDE.Dirichlet.realGradient, hd,
    ContinuousLinearMap.comp_apply, slot_action_coordinateVector, map_sum, map_smul,
    Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, OAI.Analysis.PDE.Dirichlet.realLift_apply]
  simp only [smul_eq_mul, Finset.sum_smul,
    Quaternion.star_smul, star_one, smul_mul_assoc, one_mul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem quaternionGradient_nullImaginary {d : ℕ} {f : (OAI.Analysis.Calculus.Current.Index d → ℂ) → ℝ}
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hf : DifferentiableAt ℝ f (nullImaginaryProjection d x)) :
    OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (f ∘ nullImaginaryProjection d) x =
      OAI.Analysis.Calculus.Quaternion.imaginaryGradient f (nullImaginaryProjection d x) ∘ nullIndexEquiv d := by
  have hd := (hf.hasFDerivAt.comp x (nullImaginaryProjection d).hasFDerivAt).fderiv
  funext a
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionGradient, OAI.Analysis.Calculus.Quaternion.gradientMap, OAI.Analysis.PDE.Dirichlet.realGradient, hd,
    ContinuousLinearMap.comp_apply, nullImaginaryProjection_coordinateVector,
    Function.comp_apply, OAI.Analysis.Calculus.Quaternion.imaginaryGradient]

theorem quaternionGradient_physical_null {d : ℕ} {f : (OAI.Analysis.Calculus.Current.Index d → ℂ) → ℝ}
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hf : DifferentiableAt ℝ f (physicalToNullCurrentPoint d x).2) :
    OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (fun y => f (physicalToNullCurrentPoint d y).2) x =
      physicalVector (OAI.Analysis.Calculus.Quaternion.imaginaryGradient f (physicalToNullCurrentPoint d x).2) := by
  change OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots
    ((f ∘ nullImaginaryProjection d) ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d))) x = _
  have hf' : DifferentiableAt ℝ f
      (nullImaginaryProjection d (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x)) := hf
  have hc : DifferentiableAt ℝ (f ∘ nullImaginaryProjection d)
      (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x) :=
    hf'.comp _ (nullImaginaryProjection d).differentiableAt
  rw [quaternionGradient_slot_comp OAI.Analysis.Calculus.Quaternion.threeSlots _ _ hc,
    quaternionGradient_nullImaginary _ hf']
  rfl

end OAI.Analysis.PDE.Concentration
